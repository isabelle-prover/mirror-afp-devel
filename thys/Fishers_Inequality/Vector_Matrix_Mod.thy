(* Title: Vector_Matrix_Mod.thy
   Author: Chelsea Edmonds
*)

section \<open> Matrices/Vectors mod x \<close>
text \<open> This section formalises operations and properties mod some integer x on integer matrices and 
vectors. Much of this file was no longer needed for fishers once the generic idea of lifting a 0-1 matrix
was introduced, however it is left as an example for future work on matrices mod n, beyond 0-1 matrices  \<close>
theory Vector_Matrix_Mod imports Matrix_Vector_Extras
Berlekamp_Zassenhaus.Finite_Field Berlekamp_Zassenhaus.More_Missing_Multiset  
begin

text \<open>Simple abbreviations for main mapping functions \<close>
abbreviation to_int_mat :: "'a :: finite mod_ring mat \<Rightarrow> int mat" where
  "to_int_mat \<equiv> map_mat to_int_mod_ring"

abbreviation to_int_vec :: "'a :: finite mod_ring vec \<Rightarrow> int vec" where
"to_int_vec \<equiv> map_vec to_int_mod_ring"

interpretation of_int_mod_ring_hom_sr: semiring_hom of_int_mod_ring
proof (unfold_locales)
  show "\<And>x y. of_int_mod_ring (x + y) = of_int_mod_ring x + of_int_mod_ring y"
    by (transfer,presburger)
  show "of_int_mod_ring 1 = 1" by (metis of_int_hom.hom_one of_int_of_int_mod_ring)
  show "\<And>x y. of_int_mod_ring (x * y) = of_int_mod_ring x * of_int_mod_ring y"
    by (transfer, simp add: mod_mult_eq) 
qed

text \<open>NOTE: The context directly below is copied from Matrix Vector Extras, as for some reason 
they can't be used locally if not? Ideally remove in future if possible \<close>

context inj_zero_hom
begin

lemma  vec_hom_zero_iff[simp]: "(map_vec hom x = 0\<^sub>v n) = (x = 0\<^sub>v n)"
proof -
  {
    fix i
    assume i: "i < n" "dim_vec x = n"
    hence "map_vec hom x $ i = 0 \<longleftrightarrow> x $ i = 0"
      using index_map_vec(1)[of i x] by simp
  } note main = this
  show ?thesis unfolding vec_eq_iff by (simp, insert main, auto)
qed

lemma  mat_hom_inj: "map_mat hom A = map_mat hom B \<Longrightarrow> A = B"
  unfolding mat_eq_iff by auto

lemma  vec_hom_inj: "map_vec hom v = map_vec hom w \<Longrightarrow> v = w"
  unfolding vec_eq_iff by auto

lemma  vec_hom_set_distinct_iff: 
  fixes xs :: "'a vec list"
  shows "distinct xs \<longleftrightarrow> distinct (map (map_vec hom) xs)"
  using vec_hom_inj by (induct xs) (auto)
end

subsection \<open> Basic Mod Context \<close>

locale mat_mod = fixes m :: int
assumes non_triv_m: "m > 1"
begin 

text \<open>First define the mod operations on vectors \<close>
definition vec_mod :: "int vec \<Rightarrow> int vec" where
"vec_mod v \<equiv> map_vec (\<lambda> x . x mod m) v"

(* Parse tree ambiguity is caused by bad definitions in the MPoly theory files. Issue raised
on Isabelle Mailing List *)

lemma vec_mod_dim[simp]: "dim_vec (vec_mod v) = dim_vec v"
  using vec_mod_def by simp

lemma vec_mod_index[simp]: "i < dim_vec v \<Longrightarrow> (vec_mod v) $ i = (v $ i) mod m"
  using vec_mod_def by simp

lemma vec_mod_index_same[simp]: "i < dim_vec v \<Longrightarrow> v $ i < m \<Longrightarrow> v $ i \<ge> 0 \<Longrightarrow> (vec_mod v) $ i = v $ i"
  by simp

lemma vec_setI2: "i < dim_vec v \<Longrightarrow> v $ i \<in> set\<^sub>v v"
  by (simp add: vec_setI) 

lemma vec_mod_eq: "set\<^sub>v v \<subseteq> {0..<m} \<Longrightarrow> vec_mod v = v"
  apply (intro eq_vecI, simp_all)
  using vec_setI2 vec_mod_index_same by (metis atLeastLessThan_iff subset_iff zmod_trivial_iff) 

lemma vec_mod_set_vec_same:"set\<^sub>v v \<subseteq> {0..<m} \<Longrightarrow> set\<^sub>v (vec_mod v) = set\<^sub>v v"
  using vec_mod_eq by auto

text \<open>Define the mod operation on matrices \<close>

definition mat_mod :: "int mat \<Rightarrow> int mat"  where 
"mat_mod M \<equiv> map_mat (\<lambda> x. x mod m) M"

lemma mat_mod_dim[simp]: "dim_row (mat_mod M) = dim_row M" "dim_col (mat_mod M) = dim_col M"
  using mat_mod_def by simp_all

lemma mat_mod_index [simp]:  "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> (mat_mod M) $$ (i, j) = (M $$ (i, j)) mod m"
  by(simp add: mat_mod_def)

lemma mat_mod_index_same[simp]: "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> M $$ (i, j) < m \<Longrightarrow> 
    M $$ (i, j) \<ge> 0 \<Longrightarrow> mat_mod M $$ (i, j) = M $$ (i, j)"
  by (simp add: mat_mod_def)

lemma elements_matI2: "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<in> elements_mat A"
  by auto

lemma mat_mod_elements_in: 
  assumes "x \<in> elements_mat M"
  shows "x mod m \<in> elements_mat (mat_mod M)"
proof - 
  obtain i j where "M $$ (i, j) = x" and ilt: "i < dim_row M" and jlt: "j < dim_col M" using assms by auto
  then have "mat_mod M $$ (i, j) = x mod m" by simp
  thus ?thesis using ilt jlt
    by (metis elements_matI2 mat_mod_dim(1) mat_mod_dim(2)) 
qed

lemma mat_mod_elements_map: 
  assumes "x \<in> elements_mat M"
  shows "elements_mat (mat_mod M) = (\<lambda> x. x mod m) ` (elements_mat M)"
proof (auto simp add: mat_mod_elements_in)
  fix x assume "x \<in> elements_mat (local.mat_mod M)"
  then obtain i j where "(mat_mod M) $$ (i, j) = x" and "i < dim_row (mat_mod M)" and "j < dim_col (mat_mod M)" by auto
  then show "x \<in> (\<lambda>x. x mod m) ` elements_mat M"
    by auto  
qed

lemma mat_mod_eq_cond:
  assumes "elements_mat M \<subseteq> {0..<m}"
  shows "mat_mod M = M"
proof (intro eq_matI, simp_all)
  fix i j assume "i < dim_row M" "j < dim_col M"
  then have "M $$ (i, j) \<in> {0..<m}"
    using assms elements_matI2 by blast 
  then show "M $$ (i, j) mod m = M $$ (i, j)"
    by (simp) 
qed

lemma mat_mod_eq_elements_cond: "elements_mat M \<subseteq> {0..<m} \<Longrightarrow> elements_mat (mat_mod M) = elements_mat M"
  using mat_mod_eq_cond by auto

lemma mat_mod_vec_mod_row:  "i < dim_row A \<Longrightarrow> row (mat_mod A) i = vec_mod (row A i)"
  unfolding mat_mod_def vec_mod_def by (simp) 

lemma mat_mod_vec_mod_col:  "j < dim_col A \<Longrightarrow> col (mat_mod A) j = vec_mod (col A j)"
  unfolding mat_mod_def vec_mod_def by (simp) 

lemma count_vec_mod_eq: "set\<^sub>v v \<subseteq> {0..<m} \<Longrightarrow> count_vec v x = count_vec (vec_mod v) x"
  using vec_mod_eq by (simp) 

lemma elems_mat_setv_row_0m: "i < dim_row M \<Longrightarrow> elements_mat M \<subseteq> {0..<m} \<Longrightarrow> set\<^sub>v (row M i) \<subseteq> {0..<m}"
  by (metis row_elems_subset_mat subset_trans)

lemma elems_mat_setv_col_0m: "j < dim_col M \<Longrightarrow> elements_mat M \<subseteq> {0..<m} \<Longrightarrow> set\<^sub>v (col M j) \<subseteq> {0..<m}"
  by (metis col_elems_subset_mat subset_trans)

lemma mat_mod_count_row_eq:  "i < dim_row M \<Longrightarrow> elements_mat M \<subseteq> {0..<m} \<Longrightarrow> 
    count_vec (row (mat_mod M) i) x = count_vec (row M i) x"
  using count_vec_mod_eq mat_mod_vec_mod_row elems_mat_setv_row_0m by simp

lemma mat_mod_count_col_eq: "j < dim_col M \<Longrightarrow> elements_mat M \<subseteq> {0..<m} \<Longrightarrow> 
    count_vec (col (mat_mod M) j) x = count_vec (col M j) x"
  using count_vec_mod_eq mat_mod_vec_mod_col elems_mat_setv_col_0m by simp

lemma mod_mat_one: "mat_mod (1\<^sub>m n) = (1\<^sub>m n)"
  by (intro eq_matI, simp_all add: mat_mod_def non_triv_m)

lemma mod_mat_zero: "mat_mod (0\<^sub>m nr nc) = (0\<^sub>m nr nc)"
  by (intro eq_matI, simp_all add: mat_mod_def non_triv_m)

lemma vec_mod_unit: "vec_mod (unit_vec n i) = (unit_vec n i)"
  by (intro eq_vecI, simp_all add: unit_vec_def vec_mod_def non_triv_m)

lemma vec_mod_zero: "vec_mod (0\<^sub>v n) = (0\<^sub>v n)"
  by (intro eq_vecI, simp_all add: non_triv_m)

lemma mat_mod_cond_iff: "elements_mat M \<subseteq> {0..<m} \<Longrightarrow> P M \<longleftrightarrow> P (mat_mod M)"
  by (simp add: mat_mod_eq_cond)

end

subsection \<open>Mod Type \<close>
text \<open> The below locale takes lemmas from the Poly Mod Finite Field theory in the Berlekamp Zassenhaus
AFP entry, however has removed any excess material on polynomials mod, and only included the general 
factors. Ideally, this could be used as the base locale for both in the future \<close>

locale mod_type =
  fixes m :: int and ty :: "'a :: nontriv itself"
  assumes m: "m = CARD('a)"
begin

lemma m1: "m > 1" using nontriv[where 'a = 'a] by (auto simp:m)

definition M :: "int \<Rightarrow> int" where "M x = x mod m" 

lemma M_0[simp]: "M 0 = 0"
  by (auto simp add: M_def)

lemma M_M[simp]: "M (M x) = M x"
  by (auto simp add: M_def)

lemma M_plus[simp]: "M (M x + y) = M (x + y)" "M (x + M y) = M (x + y)"
  by (auto simp add: M_def mod_simps)
  
lemma M_minus[simp]: "M (M x - y) = M (x - y)" "M (x - M y) = M (x - y)" 
  by (auto simp add: M_def mod_simps)

lemma M_times[simp]: "M (M x * y) = M (x * y)" "M (x * M y) = M (x * y)"
  by (auto simp add: M_def mod_simps)

lemma M_1[simp]: "M 1 = 1" unfolding M_def
  using m1 by auto

lemma M_sum: "M (sum (\<lambda> x. M (f x)) A) = M (sum f A)"
proof (induct A rule: infinite_finite_induct) 
  case (insert x A)
  from insert(1-2) have "M (\<Sum>x\<in>insert x A. M (f x)) = M (f x + M ((\<Sum>x\<in>A. M (f x))))" by simp
  also have "M ((\<Sum>x\<in>A. M (f x))) = M ((\<Sum>x\<in>A. f x))" using insert by simp
  finally show ?case using insert by simp
qed auto

definition inv_M :: "int \<Rightarrow> int" where
  "inv_M x = (if x + x \<le> m then x else x - m)" 

lemma M_inv_M_id[simp]: "M (inv_M x) = M x" 
  unfolding inv_M_def M_def by simp

definition M_Rel :: "int \<Rightarrow> 'a mod_ring \<Rightarrow> bool"
  where "M_Rel x x' \<equiv> (M x = to_int_mod_ring x')"

lemma to_int_mod_ring_plus: "to_int_mod_ring ((x :: 'a mod_ring) + y) = M (to_int_mod_ring x + to_int_mod_ring y)"
  unfolding M_def using m by (transfer, auto)

lemma to_int_mod_ring_times: "to_int_mod_ring ((x :: 'a mod_ring) * y) = M (to_int_mod_ring x * to_int_mod_ring y)"
  unfolding M_def using m by (transfer, auto)

lemma eq_M_Rel[transfer_rule]: "(M_Rel ===> M_Rel ===> (=)) (\<lambda> x y. M x = M y) (=)"
  unfolding M_Rel_def rel_fun_def by auto

lemma one_M_Rel[transfer_rule]: "M_Rel 1 1"
  unfolding M_Rel_def M_def
  unfolding m by auto

lemma zero_M_Rel[transfer_rule]: "M_Rel 0 0"
  unfolding M_Rel_def M_def 
  unfolding m by auto

lemma M_to_int_mod_ring: "M (to_int_mod_ring (x :: 'a mod_ring)) = to_int_mod_ring x"
  unfolding M_def unfolding m by (transfer, auto)


lemma right_total_M_Rel[transfer_rule]: "right_total M_Rel"
  unfolding right_total_def M_Rel_def using M_to_int_mod_ring by blast

lemma left_total_M_Rel[transfer_rule]: "left_total M_Rel"
  unfolding left_total_def M_Rel_def[abs_def] 
proof
  fix x
  show "\<exists> x' :: 'a mod_ring. M x = to_int_mod_ring x'"  unfolding M_def unfolding m
    by (rule exI[of _ "of_int x"], transfer, simp)
qed

lemma bi_total_M_Rel[transfer_rule]: "bi_total M_Rel" 
  using right_total_M_Rel left_total_M_Rel by (metis bi_totalI)

lemma to_int_mod_ring_of_int_M: "to_int_mod_ring (of_int x :: 'a mod_ring) = M x" unfolding M_def
  unfolding m by transfer auto

lemma UNIV_M_Rel[transfer_rule]: "rel_set M_Rel {0..<m} UNIV"
  unfolding rel_set_def M_Rel_def[abs_def] M_def 
  by (auto simp: M_def m, goal_cases, metis to_int_mod_ring_of_int_mod_ring, (transfer, auto)+)

end

subsection \<open> Mat mod type \<close>
text \<open> Define a context to work on matrices and vectors of type @{typ "'a mod_ring"} \<close>

locale mat_mod_type = mat_mod + mod_type
begin

lemma to_int_mod_ring_plus: "to_int_mod_ring ((x :: 'a mod_ring) + y) = (to_int_mod_ring x + to_int_mod_ring y) mod m"
   using m by (transfer, auto)

lemma to_int_mod_ring_times: "to_int_mod_ring ((x :: 'a mod_ring) * y) = (to_int_mod_ring x * to_int_mod_ring y) mod m"
  using m by (transfer, auto)

text \<open> Set up transfer relation for matrices and vectors \<close>
definition MM_Rel :: "int mat \<Rightarrow> 'a mod_ring mat \<Rightarrow> bool"
  where "MM_Rel f f' \<equiv> (mat_mod f = to_int_mat f')"

definition MV_Rel :: "int vec \<Rightarrow> 'a mod_ring vec \<Rightarrow> bool"
  where "MV_Rel v v' \<equiv> (vec_mod v = to_int_vec v')"

lemma to_int_mat_index[simp]: "i < dim_row N \<Longrightarrow> j < dim_col N \<Longrightarrow> (to_int_mat N $$ (i, j)) = to_int_mod_ring (N $$ (i, j))"
  by simp

lemma to_int_vec_index[simp]: "i < dim_vec v  \<Longrightarrow> (to_int_vec v $i) = to_int_mod_ring (v $i)"
  by simp

lemma eq_dim_row_MM_Rel[transfer_rule]: "(MM_Rel ===> (=)) dim_row dim_row "
  by (metis (mono_tags) MM_Rel_def index_map_mat(2) mat_mod_dim(1) rel_funI)

lemma lt_dim_row_MM_Rel[transfer_rule]: "(MM_Rel ===> (=) ===> (=)) (\<lambda> M i. i < dim_row M) (\<lambda> M i. i < dim_row M)"
  using eq_dim_row_MM_Rel unfolding MM_Rel_def rel_fun_def by auto

lemma eq_dim_col_MM_Rel[transfer_rule]: "(MM_Rel ===> (=)) dim_col dim_col "
  unfolding MM_Rel_def rel_fun_def
  by (metis index_map_mat(3) mat_mod_dim(2)) 

lemma lt_dim_col_MM_Rel[transfer_rule]: "(MM_Rel ===> (=) ===> (=)) (\<lambda> M j. j < dim_col M) (\<lambda> M j. j < dim_col M)"
  using eq_dim_col_MM_Rel unfolding MM_Rel_def rel_fun_def by auto

lemma eq_dim_vec_MV_Rel[transfer_rule]: "(MV_Rel ===> (=)) dim_vec dim_vec"
  unfolding MV_Rel_def rel_fun_def using index_map_vec(2) vec_mod_dim by metis

lemma lt_dim_vec_MV_Rel[transfer_rule]: "(MV_Rel ===> (=) ===> (=)) (\<lambda> v j. j < dim_vec v) (\<lambda> v j. j < dim_vec v)"
  unfolding MV_Rel_def rel_fun_def using index_map_vec(2) vec_mod_dim by metis

lemma eq_MM_Rel[transfer_rule]: "(MM_Rel ===> MM_Rel ===> (=)) (\<lambda> f f' . mat_mod f = mat_mod f') (=) "
  unfolding MM_Rel_def rel_fun_def using to_int_mod_ring_hom.mat_hom_inj by (auto)

lemma eq_MV_Rel[transfer_rule]: "(MV_Rel ===> MV_Rel ===> (=)) (\<lambda> v v' . vec_mod v = vec_mod v') (=) " 
  unfolding MV_Rel_def rel_fun_def using to_int_mod_ring_hom.vec_hom_inj by auto


lemma index_MV_Rel[transfer_rule]: "(MV_Rel ===> (=) ===> M_Rel) 
    (\<lambda> v i. if i < dim_vec v then v $ i else 0) (\<lambda> v i. if i < dim_vec v then v $ i else 0)"
  using lt_dim_vec_MV_Rel unfolding MV_Rel_def M_Rel_def M_def rel_fun_def 
  by (simp, metis to_int_vec_index vec_mod_index)

lemma index_MM_Rel[transfer_rule]: "(MM_Rel ===> (=) ===> (=) ===> M_Rel) 
    (\<lambda> M i j. if (i < dim_row M \<and> j < dim_col M) then M $$ (i, j) else 0)
   (\<lambda> M i j. if (i < dim_row M \<and> j < dim_col M) then M $$ (i, j) else 0)"
  using lt_dim_row_MM_Rel lt_dim_col_MM_Rel unfolding  M_Rel_def M_def rel_fun_def 
  by (simp, metis mat_mod_index to_int_mat_index MM_Rel_def)

lemma index_MM_Rel_explicit: 
  assumes "MM_Rel N N'"
  assumes "i < dim_row N" "j < dim_col N"
  shows "(N $$ (i, j)) mod m = to_int_mod_ring (N' $$ (i, j))"
proof -
  have eq: "(to_int_mat N') $$ (i, j) = to_int_mod_ring (N' $$ (i, j))"
    by (metis MM_Rel_def assms(1) assms(2) assms(3) index_map_mat mat_mod.mat_mod_dim mat_mod_axioms) 
  have "mat_mod N = to_int_mat N'" using assms by (simp add: MM_Rel_def)
  then have "(mat_mod N) $$ (i, j) = (to_int_mat N') $$ (i, j)"
    by simp 
  thus ?thesis using mat_mod_index eq
    using assms(2) assms(3) by auto 
qed

lemma one_MV_Rel[transfer_rule]: "MV_Rel (unit_vec n i) (unit_vec n i)"
  unfolding MV_Rel_def vec_mod_unit non_triv_m unit_vec_def 
  by (intro eq_vecI, simp_all add: non_triv_m)

lemma one_MM_Rel[transfer_rule]: "MM_Rel (1\<^sub>m n) (1\<^sub>m n)"
  unfolding MM_Rel_def mod_mat_one
  by (intro eq_matI, simp_all)

lemma zero_MM_Rel[transfer_rule]: "MM_Rel (0\<^sub>m nr nc) (0\<^sub>m nr nc)"
  unfolding MM_Rel_def
  by (intro eq_matI, simp_all)

lemma zero_MV_Rel[transfer_rule]: "MV_Rel (0\<^sub>v n) (0\<^sub>v n)"
  unfolding MV_Rel_def by (intro eq_vecI, simp_all)

lemma right_unique_MV_Rel[transfer_rule]: "right_unique MV_Rel"
  unfolding right_unique_def MV_Rel_def 
  using to_int_mod_ring_hom.vec_hom_inj by auto

lemma right_unique_MM_Rel[transfer_rule]: "right_unique MM_Rel"
  unfolding right_unique_def MM_Rel_def 
  using to_int_mod_ring_hom.mat_hom_inj by auto

lemma mod_to_int_mod_ring: "(to_int_mod_ring (x :: 'a mod_ring)) mod m = to_int_mod_ring x"
  unfolding m by (transfer, auto)

lemma mat_mod_to_int_mat: "mat_mod (to_int_mat (N :: 'a mod_ring mat)) = to_int_mat N"
  using mod_to_int_mod_ring by (intro eq_matI, simp_all)

lemma vec_mod_to_int_vec: "vec_mod (to_int_vec (v :: 'a mod_ring vec)) = to_int_vec v"
  using mod_to_int_mod_ring by (intro eq_vecI, simp_all)

lemma right_total_MM_Rel[transfer_rule]: "right_total MM_Rel"
  unfolding right_total_def MM_Rel_def
proof
  fix M :: "'a mod_ring mat"
  show "\<exists>x. mat_mod x = to_int_mat M"
    by (intro exI[of _ "to_int_mat M"], simp add: mat_mod_to_int_mat)
qed

lemma right_total_MV_Rel[transfer_rule]: "right_total MV_Rel"
  unfolding right_total_def MV_Rel_def
proof
  fix v :: "'a mod_ring vec"
  show "\<exists>x. vec_mod x = to_int_vec v"
    by (intro exI[of _ "to_int_vec v"], simp add: vec_mod_to_int_vec)
qed

lemma to_int_mod_ring_of_int_mod: "to_int_mod_ring (of_int x :: 'a mod_ring) = x mod m"
  unfolding m by transfer auto

lemma vec_mod_v_representative: "vec_mod v = to_int_vec (map_vec of_int v :: 'a mod_ring vec)"
  unfolding mat_mod_def by (auto simp: to_int_mod_ring_of_int_mod)

lemma mat_mod_N_representative: "mat_mod N = to_int_mat (map_mat of_int N :: 'a mod_ring mat)"
  unfolding mat_mod_def by (auto simp: to_int_mod_ring_of_int_mod)

lemma left_total_MV_Rel[transfer_rule]: "left_total MV_Rel"
  unfolding left_total_def MV_Rel_def[abs_def] using vec_mod_v_representative by blast

lemma left_total_MM_Rel[transfer_rule]: "left_total MM_Rel"
  unfolding left_total_def MM_Rel_def[abs_def] using mat_mod_N_representative by blast

lemma bi_total_MV_Rel[transfer_rule]: "bi_total MV_Rel"
  using right_total_MV_Rel left_total_MV_Rel by (metis bi_totalI)

lemma bi_total_MM_Rel[transfer_rule]: "bi_total MM_Rel"
  using right_total_MM_Rel left_total_MM_Rel by (metis bi_totalI)

lemma domain_MV_rel[transfer_domain_rule]: "Domainp MV_Rel = (\<lambda> f. True)"
proof
  fix v :: "int vec"
  show "Domainp MV_Rel v = True" unfolding MV_Rel_def[abs_def] Domainp.simps
    by (auto simp: vec_mod_v_representative)
qed

lemma domain_MM_rel[transfer_domain_rule]: "Domainp MM_Rel = (\<lambda> f. True)"
proof
  fix N :: "int mat"
  show "Domainp MM_Rel N = True" unfolding MM_Rel_def[abs_def] Domainp.simps
    by (auto simp: mat_mod_N_representative)
qed

lemma mem_MV_Rel[transfer_rule]: 
  "(MV_Rel ===> rel_set MV_Rel ===> (=)) (\<lambda> x Y. \<exists>y \<in> Y. vec_mod x = vec_mod y) (\<in>)"
proof (intro rel_funI iffI)
  fix x y X Y assume xy: "MV_Rel x y" and XY: "rel_set MV_Rel X Y"
  { assume "\<exists>x' \<in> X. vec_mod x = vec_mod x'"
    then obtain x' where x'X: "x' \<in> X" and xx': "vec_mod x = vec_mod x'" by auto
    with xy have x'y: "MV_Rel x' y" by (auto simp: MV_Rel_def)
    from rel_setD1[OF XY x'X] obtain y' where "MV_Rel x' y'" and "y' \<in> Y" by auto
    with x'y
     show "y \<in> Y" using to_int_mod_ring_hom.vec_hom_inj by (auto simp: MV_Rel_def)
  }
  assume "y \<in> Y"
  from rel_setD2[OF XY this] obtain x' where x'X: "x' \<in> X" and x'y: "MV_Rel x' y" by auto
  from xy x'y have "vec_mod x = vec_mod x'" by (auto simp: MV_Rel_def)
  with x'X show "\<exists>x' \<in> X. vec_mod x = vec_mod x'" by auto
qed

lemma mem_MM_Rel[transfer_rule]: 
  "(MM_Rel ===> rel_set MM_Rel ===> (=)) (\<lambda> x Y. \<exists>y \<in> Y. mat_mod x = mat_mod y) (\<in>)"
proof (intro rel_funI iffI)
  fix x y X Y assume xy: "MM_Rel x y" and XY: "rel_set MM_Rel X Y"
  { assume "\<exists>x' \<in> X. mat_mod x = mat_mod x'"
    then obtain x' where x'X: "x' \<in> X" and xx': "mat_mod x = mat_mod x'" by auto
    with xy have x'y: "MM_Rel x' y" by (auto simp: MM_Rel_def)
    from rel_setD1[OF XY x'X] obtain y' where "MM_Rel x' y'" and "y' \<in> Y" by auto
    with x'y
     show "y \<in> Y" using to_int_mod_ring_hom.mat_hom_inj by (auto simp: MM_Rel_def)
  }
  assume "y \<in> Y"
  from rel_setD2[OF XY this] obtain x' where x'X: "x' \<in> X" and x'y: "MM_Rel x' y" by auto
  from xy x'y have "mat_mod x = mat_mod x'" by (auto simp: MM_Rel_def)
  with x'X show "\<exists>x' \<in> X. mat_mod x = mat_mod x'" by auto
qed

lemma conversep_MM_Rel_OO_MM_Rel [simp]: "MM_Rel\<inverse>\<inverse> OO MM_Rel = (=)"
  using mat_mod_to_int_mat apply (intro ext, auto simp: OO_def MM_Rel_def)
  using to_int_mod_ring_hom.mat_hom_inj by auto 

lemma MM_Rel_OO_conversep_MM_Rel [simp]: "MM_Rel OO MM_Rel\<inverse>\<inverse> = (\<lambda> M M' . mat_mod M = mat_mod M')"
  by (intro ext, auto simp: OO_def MM_Rel_def mat_mod_N_representative)

lemma conversep_MM_Rel_OO_eq_m [simp]: "MM_Rel\<inverse>\<inverse> OO (\<lambda> M M' . mat_mod M = mat_mod M') = MM_Rel\<inverse>\<inverse>"
  by (intro ext, auto simp: OO_def MM_Rel_def)

lemma eq_m_OO_MM_Rel [simp]: "(\<lambda> M M' . mat_mod M = mat_mod M') OO MM_Rel = MM_Rel"
  by (intro ext, auto simp: OO_def MM_Rel_def)

lemma eq_mset_MM_Rel [transfer_rule]: 
  "(rel_mset MM_Rel ===> rel_mset MM_Rel ===> (=)) (rel_mset (\<lambda> M M' . mat_mod M = mat_mod M')) (=)"
proof (intro rel_funI iffI)
  fix A B X Y
  assume AX: "rel_mset MM_Rel A X" and BY: "rel_mset MM_Rel B Y"
  {
    assume AB: "rel_mset (\<lambda> M M' . mat_mod M = mat_mod M') A B"
    from AX have "rel_mset MM_Rel\<inverse>\<inverse> X A" by (simp add: multiset.rel_flip)
    note rel_mset_OO[OF this AB]
    note rel_mset_OO[OF this BY]
    then show "X = Y" by (simp add: multiset.rel_eq)
  }
  assume "X = Y"
  with BY have "rel_mset MM_Rel\<inverse>\<inverse> X B" by (simp add: multiset.rel_flip)
  from rel_mset_OO[OF AX this]
  show "rel_mset (\<lambda> M M' . mat_mod M = mat_mod M') A B" by simp
qed

lemma vec_mset_MV_Rel[transfer_rule]: 
  "(MV_Rel  ===> (=)) (\<lambda> v. vec_mset (vec_mod v)) (\<lambda> v. image_mset (to_int_mod_ring) (vec_mset v))"
  unfolding MV_Rel_def rel_fun_def 
proof (intro allI impI subset_antisym subsetI)
  fix x :: "int vec" fix  y :: "'a mod_ring vec"
  assume assm: "vec_mod x = to_int_vec y"
  have "image_mset to_int_mod_ring (vec_mset y) = vec_mset (to_int_vec y)"
    using inj_zero_hom.vec_hom_mset to_int_mod_ring_hom.inj_zero_hom_axioms by auto 
  then show " vec_mset (vec_mod x) = image_mset to_int_mod_ring (vec_mset y)" using assm by simp
qed

lemma vec_count_MV_Rel_direct: 
  assumes "MV_Rel v1 v2"
  shows "count_vec v2 i = count_vec (vec_mod v1) (to_int_mod_ring i)"
proof-
  have eq_vecs: "to_int_vec v2 = vec_mod v1" using assms unfolding MV_Rel_def by simp
  have "count_vec v2 i = count (vec_mset v2) i" by simp
  also have 1: "... = count (image_mset to_int_mod_ring (vec_mset v2)) (to_int_mod_ring i)"  
    using count_image_mset_inj by (metis to_int_mod_ring_hom.inj_f) 
  also have 2: "... = count (vec_mset (vec_mod v1)) (to_int_mod_ring i)" using assms
    by (simp add: eq_vecs inj_zero_hom.vec_hom_mset to_int_mod_ring_hom.inj_zero_hom_axioms) 
  finally show "count_vec v2 i = count_vec (vec_mod v1) (to_int_mod_ring i)"
    by (simp add: 1 2 ) 
qed

lemma MM_Rel_MV_Rel_row: "MM_Rel A B \<Longrightarrow> i < dim_row A \<Longrightarrow> MV_Rel (row A i) (row B i)"
  unfolding MM_Rel_def MV_Rel_def
  by (metis index_map_mat(2) mat_mod_dim(1) mat_mod_vec_mod_row row_map_mat) 

lemma MM_Rel_MV_Rel_col:  "MM_Rel A B \<Longrightarrow> j < dim_col A \<Longrightarrow> MV_Rel (col A j) (col B j)"
  unfolding MM_Rel_def MV_Rel_def 
  using  index_map_mat(3) mat_mod_dim(2) mat_mod_vec_mod_col col_map_mat by (metis) 

end
end