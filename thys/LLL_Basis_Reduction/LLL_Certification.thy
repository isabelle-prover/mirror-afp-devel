(*
    Authors:    René Thiemann
                BSD
*)

section \<open>Certification of External LLL Invocations\<close>

text \<open>Instead of using a fully verified algorithm, we also provide a technique to invoke
an external LLL solver. In order to check its result, we not only need the reduced basic,
but also the matrices which translate between the input basis and the reduced basis. 
Then we can easily check whether the resulting lattices are indeed identical and just have
to start the verified algorithm on the already reduced basis.
This invocation will then usually just require one computation of Gram--Schmidt in order
to check that the basis is already reduced. Alternatively, one could also through an error
message in case the basis is not reduced.\<close>

theory LLL_Certification
  imports
    LLL_Mu_Integer_Impl
begin

context vec_module
begin

lemma mat_mult_sub_lattice: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and gs: "set gs \<subseteq> carrier_vec n" 
  and A: "A \<in> carrier_mat (length fs) (length gs)" 
  and prod: "mat_of_rows n fs = map_mat of_int A * mat_of_rows n gs" 
  shows "lattice_of fs \<subseteq> lattice_of gs" 
proof 
  let ?m = "length fs"
  let ?m' = "length gs" 
  let ?i = "of_int :: int \<Rightarrow> 'a" 
  let ?I = "map_mat ?i" 
  let ?A = "?I A" 
  have gsC: "mat_of_rows n gs \<in> carrier_mat ?m' n" by auto
  from A have A: "?A \<in> carrier_mat ?m ?m'" by auto
  from fs have fsi[simp]: "\<And> i. i < ?m \<Longrightarrow> fs ! i \<in> carrier_vec n" by auto
  hence fsi'[simp]: "\<And> i. i < ?m \<Longrightarrow> dim_vec (fs ! i) = n" by simp
  from gs have fsi[simp]: "\<And> i. i < ?m' \<Longrightarrow> gs ! i \<in> carrier_vec n" by auto
  hence gsi'[simp]: "\<And> i. i < ?m' \<Longrightarrow> dim_vec (gs ! i) = n" by simp
  fix v
  assume "v \<in> lattice_of fs" 
  from in_latticeE[OF this]
  obtain c where v: "v = M.sumlist (map (\<lambda>i. ?i (c i) \<cdot>\<^sub>v fs ! i) [0..<?m])" by auto
  let ?c = "vec ?m (\<lambda> i. ?i (c i))" 
  let ?d = "A\<^sup>T *\<^sub>v vec ?m c" 
  note v
  also have "\<dots> = mat_of_cols n fs *\<^sub>v ?c" 
    by (rule eq_vecI, auto intro!: dim_sumlist sum.cong 
      simp: sumlist_nth scalar_prod_def mat_of_cols_def)
  also have "mat_of_cols n fs = (mat_of_rows n fs)\<^sup>T" 
    by (simp add: transpose_mat_of_rows)
  also have "\<dots> = (?A * mat_of_rows n gs)\<^sup>T" unfolding prod ..
  also have "\<dots> = (mat_of_rows n gs)\<^sup>T * ?A\<^sup>T" 
    by (rule transpose_mult[OF A gsC])
  also have "(mat_of_rows n gs)\<^sup>T = mat_of_cols n gs" 
    by (simp add: transpose_mat_of_rows)
  finally have "v = (mat_of_cols n gs * ?A\<^sup>T) *\<^sub>v ?c" .
  also have "\<dots> = mat_of_cols n gs *\<^sub>v (?A\<^sup>T *\<^sub>v ?c)" 
    by (rule assoc_mult_mat_vec, insert A, auto)
  also have "?A\<^sup>T = ?I (A\<^sup>T)" by fastforce
  also have "?c = map_vec ?i (vec ?m c)" by auto
  also have "?I (A\<^sup>T) *\<^sub>v \<dots> = map_vec ?i ?d" 
    using A by (simp add: of_int_hom.mult_mat_vec_hom)
  finally have "v = mat_of_cols n gs *\<^sub>v map_vec ?i ?d" .
  define d where "d = ?d" 
  have d: "d \<in> carrier_vec ?m'" unfolding d_def using A by auto
  have "v = mat_of_cols n gs *\<^sub>v map_vec ?i d" unfolding d_def by fact
  also have "\<dots> =  M.sumlist (map (\<lambda>i. ?i (d $ i) \<cdot>\<^sub>v gs ! i) [0..<?m'])" 
    by (rule sym, rule eq_vecI, insert d, auto intro!: dim_sumlist sum.cong 
      simp: sumlist_nth scalar_prod_def mat_of_cols_def)
  finally show "v \<in> lattice_of gs" 
    by (intro in_latticeI, auto)
qed
end

context LLL_with_assms
begin

text \<open>This is the key lemma. It permits to change from the initial basis
@{term fs_init} to an arbitrary @{term gs} that has been computed by some
external tool. Here, two change-of-basis matrices U1 and U2 are required 
to certify the change via the conditions prod1 and prod2.\<close>

lemma LLL_change_basis: assumes gs: "set gs \<subseteq> carrier_vec n" 
  and len': "length gs = m" 
  and U1: "U1 \<in> carrier_mat m m" 
  and U2: "U2 \<in> carrier_mat m m" 
  and prod1: "mat_of_rows n fs_init = U1 * mat_of_rows n gs" 
  and prod2: "mat_of_rows n gs = U2 * mat_of_rows n fs_init" 
shows "lattice_of gs = lattice_of fs_init" "LLL_with_assms n m gs \<alpha>" 
proof -
  let ?i = "of_int :: int \<Rightarrow> int" 
  have "U1 = map_mat ?i U1" by (intro eq_matI, auto)
  with prod1 have prod1: "mat_of_rows n fs_init = map_mat ?i U1 * mat_of_rows n gs" by simp
  have "U2 = map_mat ?i U2" by (intro eq_matI, auto)
  with prod2 have prod2: "mat_of_rows n gs = map_mat ?i U2 * mat_of_rows n fs_init" by simp
  have "lattice_of gs \<subseteq> lattice_of fs_init" 
    by (rule mat_mult_sub_lattice[OF gs fs_init _ prod2], auto simp: U2 len len')
  moreover have "lattice_of gs \<supseteq> lattice_of fs_init"
    by (rule mat_mult_sub_lattice[OF fs_init gs _ prod1], auto simp: U1 len len')
  ultimately show "lattice_of gs = lattice_of fs_init" by blast
  show "LLL_with_assms n m gs \<alpha>"
  proof
    show "4/3 \<le> \<alpha>" by (rule \<alpha>)
    show "length gs = m" by fact
    show "lin_indep gs" using lin_dep 
      oops
end

end
