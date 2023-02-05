theory CVP_vec

imports 
  Main 
  Reduction (*TODO adapt when in AFP*)
  Lattice_int
  Subset_Sum
  infnorm
begin



section \<open>CVP in $\ell_\infty$\<close>


text \<open>The closest vector problem.\<close>
definition is_closest_vec :: "int_lattice \<Rightarrow> int vec \<Rightarrow> int vec \<Rightarrow> bool" where
  "is_closest_vec L b v \<equiv> (is_lattice L) \<and> 
    (\<forall>x\<in>L. linf_norm_vec  (x - b) \<ge>  linf_norm_vec (v - b) \<and> v\<in>L)"

text \<open>The decision problem associated with solving CVP exactly.\<close>
definition gap_cvp :: "(int_lattice \<times> int vec \<times> int) set" where
  "gap_cvp \<equiv> {(L, b, r). (is_lattice L) \<and> (\<exists>v\<in>L. linf_norm_vec (v - b) \<le> r)}"



text \<open>Reduction function for CVP to subset sum\<close>

definition gen_basis :: "int vec \<Rightarrow> int mat" where
  "gen_basis as = mat (dim_vec as + 2) (dim_vec as) (\<lambda> (i, j). if i \<in> {0,1} then as$j 
    else (if i = j + 2 then 2 else 0))"


definition gen_t :: "int vec \<Rightarrow> int \<Rightarrow> int vec" where
  "gen_t as s = vec (dim_vec as + 2) ((\<lambda> i. 1)(0:= s+1, 1:= s-1))"


definition reduce_cvp_subset_sum :: 
  "((int vec) * int) \<Rightarrow> (int_lattice * (int vec) * int)" where
  "reduce_cvp_subset_sum \<equiv> (\<lambda> (as,s).
    (gen_lattice (gen_basis as), gen_t as s, (1::int)))"


text \<open>Lemmas for Proof\<close>

lemma vec_lambda_eq[intro]: "(\<forall>i<n. a i = b i) \<longrightarrow> vec n a = vec n b"
by auto

lemma eq_fun_applic: assumes "x = y" shows "f x = f y"
using assms by auto


lemma sum_if_zero:
  assumes "finite A" "i\<in>A"
  shows "(\<Sum>j\<in>A. (if i = j then a j else 0)) = a i"
proof -
  have "(\<Sum>x\<in>A. if x = i then a x else 0) =
  (if i = i then a i else 0) + (\<Sum>x\<in>A - {i}. if x = i then a x else 0)"
  using sum.remove[OF assms, of "(\<lambda>x. if x = i then a x else 0)"] by auto
  then show ?thesis by (simp add: assms(1))
qed

lemma set_compr_elem: 
  assumes "finite A" "a\<in>A"
  shows "{f i | i. i\<in>A} = {f a} \<union> {f i | i. i\<in>A-{a}}"
by (safe, use assms in \<open>auto\<close>)

lemma Bx_rewrite: 
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "(gen_basis as) *\<^sub>v x = 
    vec (dim_vec as + 2) (\<lambda> i. if i \<in> {0,1} then (x \<bullet> as) 
    else (2 * x$(i-2)))"
    (is "?init_vec = ?goal_vec")
proof -
  define n::nat where n_def: "n = dim_vec as"
  have "vec n (\<lambda>j.  (as $ j)) \<bullet>  x = (x \<bullet> as)"
    unfolding n_def scalar_prod_def using x_dim by (simp add: mult.commute)
  moreover have "vec (dim_vec as) (\<lambda>j. if i = Suc (Suc j) then 2 else 0) \<bullet> x = 2 * x $ (i - 2)"
    if "i < Suc (Suc (dim_vec as))" "0 < i" "i \<noteq> Suc 0" for i
  proof -
    have "(\<Sum>ia = 0..<dim_vec x.
      vec (dim_vec as) (\<lambda>j.  (if i = Suc (Suc j) then 2 else 0)) $ ia * x $ ia) =
      (\<Sum>ia<n.  (if i = ia+2 then 2 * (x $ ia) else 0))"
      by (intro sum.cong, auto simp add: n_def x_dim)
    also have "\<dots> = (\<Sum>ib\<in>{2..<n+2}. 
         (if i = ib then 2 * (x $ (ib-2)) else 0))" 
    proof - 
      have eq: "(\<lambda>ib.  (if i = ib then 2 * x $ (ib - 2) else 0)) \<circ> (+) 2
          = (\<lambda>ia.  (if i = ia + 2 then 2 * x $ ia else 0))"
      by auto
      then show ?thesis
        by (subst sum.atLeastLessThan_shift_0[
            of "(\<lambda>ib.  (if i = ib then 2 * x $ (ib - 2) else 0))" 2 "n+2"])
          (subst eq, use lessThan_atLeast0 in \<open>auto\<close>)
    qed
    also have "\<dots> = 2 *  (x $ (i-2))" 
    proof - 
      have finite: "finite {2..<n+2}" by auto
      have is_in: "i \<in> {2..<n+2}" using that by (auto simp add: n_def)
      show ?thesis 
      by (subst sum_if_zero[OF finite is_in, of "(\<lambda>k.2 * (x $ (k-2)))"], auto)
    qed
    finally show ?thesis unfolding scalar_prod_def by auto
  qed
  ultimately show ?thesis 
    unfolding gen_basis_def reduce_cvp_subset_sum_def gen_t_def
    by (intro eq_vecI, auto simp add: n_def)
qed


lemma Bx_s_rewrite: 
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "(gen_basis as) *\<^sub>v x - (gen_t as s) = 
    vec (dim_vec as + 2) (\<lambda> i. if i = 0 then  (x \<bullet> as - s - 1) else (
      if i = 1 then  (x \<bullet> as - s + 1) else  (2 * x$(i-2) - 1)))"
    (is "?init_vec = ?goal_vec")
unfolding gen_t_def by (subst  Bx_rewrite[OF assms], auto)


lemma linf_norm_vec_Bx_s:
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "linf_norm_vec ((gen_basis as) *\<^sub>v x - (gen_t as s)) = 
    Max (insert 0 ({ \<bar>x \<bullet> as - s - 1\<bar>} \<union> { \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      { \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<dim_vec as+2 }))"
proof -
  let ?init_vec = "(gen_basis as) *\<^sub>v x - (gen_t as s)"
  let ?goal_vec = "vec (dim_vec as + 2) (\<lambda> i. if i = 0 then  (x \<bullet> as - s - 1) else (
      if i = 1 then  (x \<bullet> as - s + 1) else  (2 * x$(i-2) - 1)))"
  define n where n_def: "n = dim_vec as"
  have "linf_norm_vec ?init_vec = linf_norm_vec ?goal_vec" using Bx_s_rewrite[OF x_dim] by auto
  also have "\<dots> = Max (insert 0 {\<bar>?goal_vec $i\<bar> | i. i<n+2})" 
    unfolding linf_norm_vec_Max n_def by auto
  also have "\<dots> = Max (insert 0 ({ \<bar>x \<bullet> as - s - 1\<bar>} \<union> 
                       { \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
                       { \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2}))"
  proof -
    have "{\<bar>?goal_vec $i\<bar> | i. i<n+2} = 
      {\<bar>?goal_vec $0\<bar>} \<union> {\<bar>?goal_vec $1\<bar>} \<union> {\<bar>?goal_vec $i\<bar> | i. 1<i \<and> i<n+2}" 
    proof -
      have "{\<bar>?goal_vec $i\<bar> | i. i\<in>{0..<n+2}} = 
       {\<bar>?goal_vec $0\<bar>} \<union> {\<bar>?goal_vec $i\<bar> | i. i\<in>{1..<n+2}}"   
      by (subst set_compr_elem[of "{0..<n+2}" 0 "(\<lambda>i. \<bar>?goal_vec $i\<bar>)"], auto)
      also have "\<dots> = {\<bar>?goal_vec $0\<bar>} \<union> {\<bar>?goal_vec $1\<bar>} \<union> 
        {\<bar>?goal_vec $i\<bar> | i. i\<in>{2..<n+2}}"
      by (subst set_compr_elem[of _ 1], auto)
      finally show ?thesis by auto
    qed
    also have "\<dots> = { \<bar>x \<bullet> as - s - 1\<bar>} \<union> { \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      {\<bar>?goal_vec $i\<bar> | i. 1<i \<and> i<n+2}" by auto
    also have "{\<bar>?goal_vec $i\<bar> | i. 1<i \<and> i<n+2} = 
      { \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2}"
    proof -
      have "\<bar>?goal_vec $i\<bar> =  \<bar>2*x$(i-2)-1\<bar>" if "1<i \<and> i<n+2" for i 
      using that n_def by force
      then show ?thesis using n_def by force
    qed
    finally have eq: "{\<bar>?goal_vec $i\<bar> | i. i<n+2} = 
      { \<bar>x \<bullet> as - s - 1\<bar>} \<union> { \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      { \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2}" by blast
    then show ?thesis by auto
  qed
  finally show ?thesis using n_def by blast
qed



text \<open>\<open>gen_basis\<close> actually generates a basis which is spans the \<open>int_lattice\<close> (by definition) and 
  is linearly independent.\<close>


lemma is_indep_gen_basis:
  "is_indep (gen_basis as)"
unfolding is_indep_int_def 
proof (safe, goal_cases)
case (1 z)
  let ?n = "dim_vec as"
  have z_dim: "dim_vec z = ?n" using 1(2) unfolding gen_basis_def by auto
  have dim_row: "dim_row (gen_basis as) = ?n + 2" unfolding gen_basis_def by auto
  have eq: "(real_of_int_mat (gen_basis as)) *\<^sub>v z = vec (?n + 2) (\<lambda> i. if i \<in> {0,1} 
    then (z \<bullet> (real_of_int_vec as)) else (2 * z$(i-2)))" 
  (is "(real_of_int_mat (gen_basis as)) *\<^sub>v z = ?goal_vec")
  proof -
    have scal_prod_com: "z \<bullet> real_of_int_vec as = real_of_int_vec as \<bullet> z"
      using comm_scalar_prod[of "real_of_int_vec as" ?n z] z_dim
      by (metis carrier_dim_vec index_map_vec(2) real_of_int_vec_def)
    have *: "row (of_int_hom.mat_hom (mat (?n+2) (?n) (\<lambda>x. 
      (case x of (i, j) \<Rightarrow> if i = 0 \<or> i = Suc 0 then as $ j
                           else if i = j + 2 then 2 else 0)))) i = 
      (if i\<in>{0,1} then real_of_int_vec as else vec ?n (\<lambda>j. if i = j + 2 then 2 else 0))"
    (is "?row = ?vec") 
    if "i<?n+2" for i 
    using that by (auto simp add: real_of_int_vec_def)
    moreover have "vec (dim_vec as) (\<lambda>j. if i = Suc (Suc j) then 2 else 0) \<bullet> z = 2 * z $ (i - 2)" 
      if "i < Suc (Suc (dim_vec as))" "0 < i" "i \<noteq> Suc 0" for i
    proof (goal_cases)
    case 1
      have plus_2: "(i-2 = j) = (i = j+2)" for j using 1 that by auto
      have finite: "finite {0..<?n}" and elem: "i-2 \<in> {0..<?n}" using that 1 by auto
      have vec: "vec (dim_vec as) (\<lambda>j. if i = j+2 then 2 else 0) $ ia = 
        (if i = ia+2 then 2 else 0)" if "ia<?n" for ia
        using index_vec that by blast
      then have "(\<Sum>ia = 0..<dim_vec z.
        vec (dim_vec as) (\<lambda>j. if i = Suc (Suc j) then 2 else 0) $ ia * z $ ia) =
        (\<Sum>ia = 0..<dim_vec as. (if i = ia+2 then 2 else 0) * z $ ia)"
        using z_dim by auto
      also have "\<dots> = (\<Sum>ia = 0..<dim_vec as. (if i = ia+2 then 2 * z $ ia else 0))"
        proof -
          have "(\<forall>n. (0 = (if i = n + 2 then 2 else 0) * z $ n \<or> n + 2 = i) \<and> 
            (2 * z $ n = (if i = n + 2 then 2 else 0) * z $ n \<or> n + 2 \<noteq> i)) \<or> 
            (\<Sum>n = 0..<dim_vec as. (if i = n + 2 then 2 else 0) * z $ n) = 
            (\<Sum>n = 0..<dim_vec as. if i = n + 2 then 2 * z $ n else 0)" by simp
          then show ?thesis by (metis (no_types))
        qed
      also have "\<dots> = 2*z$(i-2)" using sum_if_zero[OF finite elem, of "(\<lambda>j. 2*z$j)"]
        using plus_2 by auto
      finally show ?case unfolding scalar_prod_def by blast
    qed
    ultimately have "?row i \<bullet> z = 
      (if i \<in> {0,1} then (real_of_int_vec as) \<bullet> z else 2 * z $ (i - 2))"
    if "i<?n+2" for i
    using that by (subst *[OF that], auto)
    then have "?row i \<bullet> z = 
      (if i \<in> {0,1} then z \<bullet> real_of_int_vec as else 2 * z $ (i - 2))"
    if "i<?n+2" for i using that by (subst scal_prod_com)
    then show ?thesis 
      unfolding real_of_int_mat_def gen_basis_def mult_mat_vec_def by auto
  qed
  have "\<dots> = 0\<^sub>v (?n + 2)" using 1(1) dim_row by (subst eq[symmetric], auto) 
  then have "2 * z$(i-2) = 0" if "1<i" and "i<?n +2" for i 
    using that by (smt (verit, best) cancel_comm_monoid_add_class.diff_cancel 
      empty_iff index_vec index_zero_vec(1) insert_iff not_less_zero zero_less_diff)
  then have "z$i = 0" if "i<?n" for i using that by force
  then show ?case using 1 z_dim unfolding gen_basis_def by auto
qed








text \<open>The CVP is NP-hard in $\ell_\infty$.\<close>

lemma well_defined_reduction: 
  assumes "(as, s) \<in> subset_sum"
  shows "reduce_cvp_subset_sum (as, s) \<in> gap_cvp"
proof -
  obtain x where
    x_dim: "dim_vec x = dim_vec as" and
    x_binary: "\<forall>i<dim_vec x. x $ i \<in> {0, 1}" and 
    x_lin_combo: "x \<bullet> as = s" 
    using assms unfolding subset_sum_def by blast
  define L where L_def: "L = fst (reduce_cvp_subset_sum (as, s))"
  define b where b_def: "b = fst (snd (reduce_cvp_subset_sum (as, s)))"
  define r where r_def: "r = snd (snd (reduce_cvp_subset_sum (as, s)))"
  have "r = 1" by (simp add: r_def reduce_cvp_subset_sum_def Pair_inject prod.exhaust_sel)
  (*have "(L,b,r) = reduce_cvp_subset_sum (as, s)" using L_def b_def r_def by auto*)
  define B where "B = gen_basis as"
  define n where n_def: "n = dim_vec as"
  have init_eq_goal: "B *\<^sub>v x - b = 
    vec (n+2) (\<lambda> i. if i = 0 then  (x \<bullet> as - s - 1) else (
      if i = 1 then  (x \<bullet> as - s + 1) else  (2 * x$(i-2) - 1)))"
    (is "?init_vec = ?goal_vec")
  unfolding B_def b_def reduce_cvp_subset_sum_def
  by (auto simp add: Bx_s_rewrite[OF x_dim[symmetric]] n_def)
  have "linf_norm_vec (B *\<^sub>v x - b) = 
    Max (insert 0 ({ \<bar>x \<bullet> as - s - 1\<bar>} \<union> { \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      { \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2 }))"
  unfolding B_def b_def reduce_cvp_subset_sum_def 
  by (auto simp add: linf_norm_vec_Bx_s[OF x_dim[symmetric]] n_def)
  also have  "\<dots> \<le> r"
  proof -
    have elem: "x$(i-2)\<in>{0,1}" if "1<i \<and> i<n+2" for i 
      using that x_binary x_dim n_def
      by (smt (verit) add_diff_cancel_right' diff_diff_left diff_less_mono2 
      less_add_same_cancel2 less_imp_add_positive less_one linorder_neqE_nat 
      nat_1_add_1 not_add_less2)
    then have "\<bar>2*x$(i-2)-1\<bar> = 1" if "1<i \<and> i<n+2" for i 
      using elem[OF that] by auto
    then have "{ \<bar>2 * x $ (i - 2) - 1\<bar> |i. 1 < i \<and> i < n + 2} \<subseteq> {1}" 
      by (safe, auto)
    then show ?thesis using x_lin_combo \<open>r=1\<close> by auto
  qed
  finally have "linf_norm_vec (?init_vec) \<le> r" by blast
  moreover have "B *\<^sub>v x\<in>L" 
  proof -
    have "dim_vec x = dim_col (gen_basis as)" unfolding gen_basis_def using x_dim by auto
    then show ?thesis
      unfolding L_def reduce_cvp_subset_sum_def gen_lattice_def B_def by auto
  qed
  ultimately have witness: "\<exists>v\<in>L. linf_norm_vec (v - b) \<le> r" by auto
  have is_indep: "is_indep  B" 
    unfolding B_def using is_indep_gen_basis[of as] by simp
  have L_int_lattice: "is_lattice L" unfolding L_def reduce_cvp_subset_sum_def 
    using is_lattice_gen_lattice[OF is_indep] unfolding B_def by auto
  show ?thesis unfolding gap_cvp_def using L_int_lattice witness L_def b_def r_def by force
qed

text \<open>NP-hardness part of reduction.\<close>
lemma NP_hardness_reduction:
  assumes "reduce_cvp_subset_sum (as, s) \<in> gap_cvp"
  shows "(as, s) \<in> subset_sum"
proof -
  define n where "n = dim_vec as"
  define B where "B = gen_basis as"
  define L where "L = gen_lattice B"
  define b where "b = gen_t as s"
  have ex_v: "\<exists>v\<in>L. linf_norm_vec (v - b) \<le> 1" and is_int_lattice: "is_lattice L"
    using assms unfolding gap_cvp_def reduce_cvp_subset_sum_def L_def B_def b_def by auto
  then obtain v where v_in_L:"v\<in>L" and ineq:"linf_norm_vec (v - b) \<le> 1" by blast
  have "\<exists>zs::int vec. v = B *\<^sub>v zs \<and> dim_vec zs = dim_vec as"
  using v_in_L unfolding L_def gen_lattice_def B_def gen_basis_def by auto
  then obtain zs::"int vec" where v_def: "v = B *\<^sub>v  zs" 
    and zs_dim: "dim_vec zs = dim_vec as" by blast
  have init_eq_goal: "v - b = 
    vec (n+2) (\<lambda> i. if i = 0 then  (zs \<bullet> as - s - 1) else (
      if i = 1 then  (zs \<bullet> as - s + 1) else  (2 * zs$(i-2) - 1)))"
    (is "?init_vec = ?goal_vec")
  unfolding v_def B_def b_def using Bx_s_rewrite[OF zs_dim[symmetric]] n_def by simp
  have linf_norm_vec_ineq: "linf_norm_vec (v-b) = Max (insert 0 ({ \<bar>zs \<bullet> as - s - 1\<bar>} \<union> 
    { \<bar>zs \<bullet> as - s + 1\<bar>} \<union> { \<bar>2*zs$(i-2)-1\<bar> | i. 1<i \<and> i<n+2 }))"
  unfolding v_def B_def b_def using linf_norm_vec_Bx_s[OF zs_dim[symmetric]] n_def by simp
  have Max_le_1: "Max (insert 0 ({ \<bar>zs \<bullet> as - s - 1\<bar>} \<union> 
    { \<bar>zs \<bullet> as - s + 1\<bar>} \<union>  { \<bar>2*zs$(i-2)-1\<bar> | i. 1<i \<and> i<n+2 }))\<le>1"
  using ineq by (subst linf_norm_vec_ineq[symmetric])
  have "\<bar>2*zs$(i-2)-1\<bar>\<le>1" if "1<i \<and> i<n+2" for i using Max_le_1 that by auto
  then have "zs$(i-2) = 0 \<or> zs$(i-2) = 1" if "1<i \<and> i<n+2" for i
    using that by force
  then have "zs$i = 0 \<or> zs$i = 1" if "i<n" for i using that
    by (metis One_nat_def Suc_less_eq add_2_eq_Suc' add_diff_cancel_right' zero_less_Suc)
  then have "\<forall>i<n. zs $ i \<in> {0, 1}" by simp 
  moreover have "zs \<bullet> as = s" using Max_le_1 by auto
  ultimately have "(\<forall>i<dim_vec zs. zs $ i \<in> {0, 1}) \<and> zs \<bullet> as = s \<and> dim_vec zs = dim_vec as"
     using zs_dim n_def by auto
  then show ?thesis unfolding subset_sum_def gap_cvp_def by auto
qed


text \<open>The CVP is NP-hard in $\ell_\infty$.\<close>

lemma "is_reduction reduce_cvp_subset_sum subset_sum gap_cvp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case using well_defined_reduction by auto
next
  case (2 as s)
  then show ?case using NP_hardness_reduction by auto
qed





end
