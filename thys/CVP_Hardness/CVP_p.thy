theory CVP_p

imports 
  Main 
  Reduction (*TODO adapt when in AFP*)
  Lattice_int
  Subset_Sum
begin

section \<open>CVP in $\ell_p$ for $p\geq 1$\<close>

text \<open>This file provides the reduction proof of Subset Sum to CVP in $\ell_p$.
  Proof can be easily instantiated for any $p\geq 1$ using the locale variables.\<close>

definition pth_p_norm_vec :: "nat \<Rightarrow> ('a::{abs, power, comm_monoid_add}) vec \<Rightarrow> 'a" where
  "pth_p_norm_vec p v = (\<Sum>i<dim_vec v. \<bar>v$i\<bar>^p)"


locale fixed_p =
fixes p::nat (*p\<ge>1 is necessary to define a proper norm*)
assumes p_def: "p\<ge>1"
begin

definition "p_norm_vec \<equiv> pth_p_norm_vec p"


text \<open>The CVP  in $\ell_p$\<close>

definition is_closest_vec :: "int_lattice \<Rightarrow> int vec \<Rightarrow> int vec \<Rightarrow> bool" where
  "is_closest_vec L b v \<equiv> (is_lattice L) \<and> 
    (\<forall>x\<in>L. p_norm_vec (x - b) \<ge> p_norm_vec (v - b) \<and> v\<in>L)"

text \<open>The decision problem associated with solving CVP exactly.\<close>
definition gap_cvp :: "(int_lattice \<times> int vec \<times> real) set" where
  "gap_cvp \<equiv> {(L, b, r). (is_lattice L) \<and> (\<exists>v\<in>L. of_int (p_norm_vec (v - b)) \<le> r^p)}"

(*Reminder: p_norm_vec is the p-th power of the p_norm!*)

text \<open>Reduction function for Subset Sum to CVP in euclidean norm\<close>

definition gen_basis_p :: "int vec \<Rightarrow> int mat" where
  "gen_basis_p as = mat (dim_vec as + 1) (dim_vec as) (\<lambda> (i, j). if i = 0 then as$j 
    else (if i = j + 1 then 2 else 0))"


definition gen_t_p :: "int vec \<Rightarrow> int \<Rightarrow> int vec" where
  "gen_t_p as s = vec (dim_vec as + 1) ((\<lambda> i. 1)(0:= s))"


definition reduce_cvp_subset_sum_p :: 
  "((int vec) * int) \<Rightarrow> (int_lattice * (int vec) * real)" where
  "reduce_cvp_subset_sum_p \<equiv> (\<lambda> (as,s).
    (gen_lattice (gen_basis_p as), gen_t_p as s, root p (dim_vec as)))"


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
  shows "(gen_basis_p as) *\<^sub>v x = 
    vec (dim_vec as + 1) (\<lambda> i. if i = 0 then (x \<bullet> as) 
    else (2 * x$(i-1)))"
    (is "?init_vec = ?goal_vec")
proof -
  define n::nat where n_def: "n = dim_vec as"
  have "vec n (\<lambda>j. (as $ j)) \<bullet>  x = (x \<bullet> as)"
    unfolding n_def scalar_prod_def using x_dim by (simp add: mult.commute)
  moreover have "vec (dim_vec as) (\<lambda>j. if i = Suc j then 2 else 0) \<bullet> x =
         2 * x $ (i - Suc 0)" if "i < Suc (dim_vec as)" "0 < i" for i
  proof -
    have "(\<Sum>ia = 0..<dim_vec x.
      vec (dim_vec as) (\<lambda>j.  (if i = (Suc j) then 2 else 0)) $ ia * x $ ia) =
      (\<Sum>ia<n.  (if i = ia+1 then 2 * (x $ ia) else 0))"
      by (intro sum.cong, auto simp add: n_def x_dim)
    also have "\<dots> = (\<Sum>ib\<in>{1..<n+1}. 
         (if i = ib then 2 * (x $ (ib-1)) else 0))" 
    proof - 
      have eq: "(\<lambda>ib.  (if i = ib then 2 * x $ (ib - 1) else 0)) \<circ> (+) 1
          = (\<lambda>ia.  (if i = ia + 1 then 2 * x $ ia else 0))"
      by auto
      then show ?thesis
        by (subst sum.atLeastLessThan_shift_0[
            of "(\<lambda>ib.  (if i = ib then 2 * x $ (ib - 1) else 0))" 1 "n+1"])
          (subst eq, use lessThan_atLeast0 in \<open>auto\<close>)
    qed
    also have "\<dots> = 2 *  (x $ (i-1))" 
    proof - 
      have finite: "finite {1..<n+1}" by auto
      have is_in: "i \<in> {1..<n+1}" using that by (auto simp add: n_def)
      show ?thesis 
      by (subst sum_if_zero[OF finite is_in, of "(\<lambda>k. 2 * (x $ (k-1)))"], auto)
    qed
    finally show ?thesis unfolding scalar_prod_def by auto
  qed
  ultimately show ?thesis 
    unfolding gen_basis_p_def reduce_cvp_subset_sum_p_def gen_t_p_def
    by (intro eq_vecI, auto simp add: n_def)
qed


lemma Bx_s_rewrite: 
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "(gen_basis_p as) *\<^sub>v x - (gen_t_p as s) = 
    vec (dim_vec as + 1) (\<lambda> i. if i = 0 then  (x \<bullet> as - s) else  (2 * x$(i-1) - 1))"
    (is "?init_vec = ?goal_vec")
unfolding gen_t_p_def by (subst  Bx_rewrite[OF assms], auto)


lemma p_norm_vec_Bx_s:
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "p_norm_vec ((gen_basis_p as) *\<^sub>v x - (gen_t_p as s)) = 
     \<bar>x \<bullet> as - s\<bar>^p + (\<Sum>i=1..<dim_vec as +1. \<bar>2*x$(i-1)-1\<bar>^p)"
proof -
  let ?init_vec = "(gen_basis_p as) *\<^sub>v x - (gen_t_p as s)"
  let ?goal_vec = "vec (dim_vec as + 1) (\<lambda> i. if i = 0 then (x \<bullet> as - s)
       else  (2 * x$(i-1) - 1))"
  have "p_norm_vec ?init_vec = p_norm_vec ?goal_vec" using Bx_s_rewrite[OF x_dim] by auto
  also have "\<dots> = (\<Sum>i\<in>{0..<dim_vec as+1}. \<bar>?goal_vec$i\<bar>^p)" 
    unfolding p_norm_vec_def pth_p_norm_vec_def by (metis atLeast0LessThan dim_vec)
  also have "\<dots> = \<bar>x \<bullet> as - s\<bar>^p + (\<Sum>i\<in>{1..<dim_vec as+1}. \<bar>2*x$(i-1)-1\<bar>^p)"
  proof -
    have subs: "{0}\<subseteq>{0..<dim_vec as+1}" by auto
    have "{0..<dim_vec as +1} = {0} \<union> {1..<dim_vec as +1}" by auto
    then show ?thesis by (subst sum.subset_diff[OF subs],auto)
  qed
  finally show ?thesis by blast
qed

text \<open>\<open>gen_basis_p\<close> actually generates a basis which spans the \<open>int_lattice\<close> (by definition) and 
  is linearly independent.\<close>


lemma is_indep_gen_basis_p:
  "is_indep (gen_basis_p as)"
unfolding is_indep_int_def 
proof (safe, goal_cases)
case (1 z)
  let ?n = "dim_vec as"
  have z_dim: "dim_vec z = ?n" using 1(2) unfolding gen_basis_p_def by auto
  have dim_row: "dim_row (gen_basis_p as) = ?n + 1" unfolding gen_basis_p_def by auto
  have eq: "(real_of_int_mat (gen_basis_p as)) *\<^sub>v z = vec (?n + 1) (\<lambda> i. if i = 0 
    then z \<bullet> (real_of_int_vec as) else (2 * z$(i-1)))" 
  (is "(real_of_int_mat (gen_basis_p as)) *\<^sub>v z = ?goal_vec")
  proof -
    have scal_prod_com: "z \<bullet> real_of_int_vec as = real_of_int_vec as \<bullet> z"
      using comm_scalar_prod[of "real_of_int_vec as" ?n z] z_dim
      by (metis carrier_dim_vec index_map_vec(2) real_of_int_vec_def)
    have *: "row (of_int_hom.mat_hom (mat (?n+1) (?n) (\<lambda>x. 
      (case x of (i, j) \<Rightarrow> if i = 0 then as $ j
                           else if i = j + 1 then 2 else 0)))) i = 
      (if i=0 then real_of_int_vec as else vec ?n (\<lambda>j. if i = j + 1 then 2 else 0))"
    (is "?row = ?vec") 
    if "i<?n+1" for i 
    using that by (auto simp add: real_of_int_vec_def)
    moreover have "vec (dim_vec as) (\<lambda>j. if i = Suc j then 2 else 0) \<bullet> z =
      2 * z $ (i - Suc 0)" if "i < Suc (dim_vec as)" "0<i" for i
    proof -
      have plus_2: "(i-1 = j) = (i = j+1)" for j using 1 that by auto
      have finite: "finite {0..<?n}" and elem: "i-1 \<in> {0..<?n}" using that 1 by auto
      have vec: "vec (dim_vec as) (\<lambda>j. if i = j+1 then 2 else 0) $ ia = 
        (if i = ia+1 then 2 else 0)" if "ia<?n" for ia
        using index_vec that by blast
      then have "(\<Sum>ia = 0..<dim_vec z.
        vec (dim_vec as) (\<lambda>j. if i = Suc j then 2 else 0) $ ia * z $ ia) =
        (\<Sum>ia = 0..<dim_vec as. (if i = ia+1 then 2 else 0) * z $ ia)"
        using z_dim by auto
      also have "\<dots> = (\<Sum>ia = 0..<dim_vec as. (if i = ia+1 then 2 * z $ ia else 0))"
        proof -
          have "(\<forall>n. (0 = (if i = n + 1 then 2 else 0) * z $ n \<or> n + 1 = i) \<and> 
            (2 * z $ n = (if i = n + 1 then 2 else 0) * z $ n \<or> n + 1 \<noteq> i)) \<or> 
            (\<Sum>n = 0..<dim_vec as. (if i = n + 1 then 2 else 0) * z $ n) = 
            (\<Sum>n = 0..<dim_vec as. if i = n + 1 then 2 * z $ n else 0)" by simp
          then show ?thesis by (metis (no_types))
        qed
      also have "\<dots> = 2*z$(i- Suc 0)" 
        using plus_2 by (smt (verit, ccfv_SIG) One_nat_def sum_if_zero[OF finite elem, 
          of "(\<lambda>j. 2*z$j)"] sum.cong)
      finally show ?thesis unfolding scalar_prod_def by blast
    qed
    ultimately have row_prod: "?row i \<bullet> z = 
      (if i = 0 then (real_of_int_vec as) \<bullet> z else 2 * z $ (i - 1))"
    if "i<?n+1" for i
    using that by (subst *[OF that], auto)
    have "?row i \<bullet> z = (if i = 0 then (z \<bullet> real_of_int_vec as) else 2 * z $ (i - 1))"
    if "i<?n+1" for i using that row_prod that by (subst scal_prod_com) auto
    then show ?thesis 
      unfolding real_of_int_mat_def gen_basis_p_def mult_mat_vec_def by auto
  qed
  have "\<dots> = 0\<^sub>v (?n + 1)" using 1(1) dim_row by (subst eq[symmetric], auto) 
  then have "2 * z$(i-1) = 0" if "0<i" and "i<?n +1" for i 
    using that by (smt (verit, best) cancel_comm_monoid_add_class.diff_cancel 
      empty_iff index_vec index_zero_vec(1) insert_iff not_less_zero zero_less_diff)
  then have "z$i = 0" if "i<?n" for i using that by force
  then show ?case using 1 z_dim unfolding gen_basis_p_def by auto
qed








text \<open>Well-definedness of the reduction function.\<close>

lemma well_defined_reduction: 
  assumes "(as, s) \<in> subset_sum"
  shows "reduce_cvp_subset_sum_p (as, s) \<in> gap_cvp"
proof -
  obtain x where
    x_dim: "dim_vec x = dim_vec as" and
    x_binary: "\<forall>i<dim_vec x. x $ i \<in> {0, 1}" and 
    x_lin_combo: "x \<bullet> as = s" 
    using assms unfolding subset_sum_def by blast
  define L where L_def: "L = fst (reduce_cvp_subset_sum_p (as, s))"
  define b where b_def: "b = fst (snd (reduce_cvp_subset_sum_p (as, s)))"
  define r where r_def: "r = snd (snd (reduce_cvp_subset_sum_p (as, s)))"
  (*have "(L,b,r) = reduce_cvp_subset_sum_p (as, s)" using L_def b_def r_def by auto*)
  define B where "B = gen_basis_p as"
  define n where n_def: "n = dim_vec as"
  have "r = root p n" unfolding n_def
    by (simp add: r_def reduce_cvp_subset_sum_p_def)
  then have r_alt: "r^p = n" using p_def by auto
  have init_eq_goal: "B *\<^sub>v x - b = 
    vec (n+1) (\<lambda> i. if i = 0 then (x \<bullet> as - s) else (2 * x$(i-1) - 1))"
    (is "?init_vec = ?goal_vec")
  unfolding B_def b_def reduce_cvp_subset_sum_p_def
  by (auto simp add: Bx_s_rewrite[OF x_dim[symmetric]] n_def)
  have "p_norm_vec (B *\<^sub>v x - b) = 
    \<bar>x \<bullet> as - s\<bar>^p + (\<Sum>i=1..<n+1. \<bar>2*x$(i-1)-1\<bar>^p)"
  unfolding B_def b_def reduce_cvp_subset_sum_p_def 
  by (auto simp add: p_norm_vec_Bx_s[OF x_dim[symmetric]] n_def)
  also have  "\<dots> \<le> r^p" (is "?left \<le> r^p")
  proof -
    have elem: "x$(i-1)\<in>{0,1}" if "0<i \<and> i<n+1" for i 
      using that x_binary x_dim n_def
      by (smt (verit) add_diff_cancel_right' diff_diff_left diff_less_mono2 
      less_add_same_cancel2 less_imp_add_positive less_one linorder_neqE_nat 
      nat_1_add_1 not_add_less2)
    then have eq_1:  "\<bar>2*x$(i-1)-1\<bar>^p = 1" if "0<i \<and> i<n+1" for i 
      using elem[OF that] by auto
    have eq_0: "\<bar>x \<bullet> as - s\<bar> ^ p = 0" using x_lin_combo p_def by auto
    have "?left = real_of_int ((\<Sum>i = 1..<n + 1. 1))" using eq_0 eq_1 by auto
    then have "?left \<le> n" by auto
    then show ?thesis using r_alt by linarith
  qed
  finally have "p_norm_vec (?init_vec) \<le> r^p" by blast
  moreover have "B *\<^sub>v x\<in>L" 
  proof -
    have "dim_vec x = dim_col (gen_basis_p as)" unfolding gen_basis_p_def using x_dim by auto
    then show ?thesis
      unfolding L_def reduce_cvp_subset_sum_p_def gen_lattice_def B_def by auto
  qed
  ultimately have witness: "\<exists>v\<in>L. p_norm_vec (v - b) \<le> r^p" by auto
  have is_indep: "is_indep  B" 
    unfolding B_def using is_indep_gen_basis_p[of as] by simp
  have L_int_lattice: "is_lattice L" unfolding L_def reduce_cvp_subset_sum_p_def 
    using is_lattice_gen_lattice[OF is_indep] unfolding B_def by auto
  show ?thesis unfolding gap_cvp_def using L_int_lattice witness L_def b_def r_def by force
qed

text \<open>NP-hardness of reduction function.\<close>
lemma NP_hardness_reduction:
  assumes "reduce_cvp_subset_sum_p (as, s) \<in> gap_cvp"
  shows "(as, s) \<in> subset_sum"
proof -
  define n where "n = dim_vec as"
  define B where "B = gen_basis_p as"
  define L where "L = gen_lattice B"
  define b where "b = gen_t_p as s"
  define r where "r = root p n"
  have rp_eq_n: "r^p = n" unfolding r_def using p_def by (simp)
  have ex_v: "\<exists>v\<in>L. p_norm_vec (v - b) \<le> r^p" and is_int_lattice: "is_lattice L"
    using assms unfolding gap_cvp_def reduce_cvp_subset_sum_p_def L_def B_def b_def r_def n_def 
    by auto
  then obtain v where v_in_L:"v\<in>L" and ineq:"p_norm_vec (v - b) \<le> r^p" by blast
  have "\<exists>zs::int vec. v = B *\<^sub>v zs \<and> dim_vec zs = dim_vec as"
  using v_in_L unfolding L_def gen_lattice_def B_def gen_basis_p_def by auto
  then obtain zs::"int vec" where v_def: "v = B *\<^sub>v  zs" 
    and zs_dim: "dim_vec zs = dim_vec as" by blast
  have init_eq_goal: "v - b = 
    vec (n+1) (\<lambda> i. if i = 0 then (zs \<bullet> as - s) else (2 * zs$(i-1) - 1))"
    (is "?init_vec = ?goal_vec")
  unfolding v_def B_def b_def using Bx_s_rewrite[OF zs_dim[symmetric]] n_def by simp
  have p_norm_vec_ineq: "p_norm_vec (v-b) = \<bar>zs \<bullet> as - s\<bar>^p + (\<Sum>i=1..<n+1. \<bar>2*zs$(i-1)-1\<bar>^p)"
  unfolding v_def B_def b_def using p_norm_vec_Bx_s[OF zs_dim[symmetric]] n_def by simp
  define hide_sum where "hide_sum = (\<Sum>i=1..<n+1. \<bar>2*zs$(i-1)-1\<bar>^p)"
  have sum_le_rp: "\<bar>zs \<bullet> as - s\<bar>^p + hide_sum \<le> r^p"
  unfolding hide_sum_def using ineq  by (subst p_norm_vec_ineq[symmetric])
  then have sum_le_rp_int: " (\<bar>zs \<bullet> as - s\<bar> ^ p + hide_sum) \<le> int n"
    unfolding rp_eq_n by linarith
  moreover have zs_ge_n: "hide_sum \<ge> n"
  proof -
    have "\<bar>2*zs$(i-1)-1\<bar>\<ge>1" if "i\<in>{1..<n+1}" for i using that by presburger
    then have "(\<Sum>i=1..<n+1. \<bar>2*zs$(i-1)-1\<bar>^p) \<ge> (\<Sum>i=1..<n+1. 1^p)"
      by (smt (verit, ccfv_SIG) linordered_semidom_class.power_mono sum_mono)
    then show ?thesis unfolding hide_sum_def by auto
  qed
  ultimately have zs_part: "hide_sum = n" 
    unfolding rp_eq_n
    by (smt (verit, ccfv_threshold) abs_triangle_ineq2_sym abs_zero power_abs zero_less_power)
  then have "(\<Sum>i=1..<n+1. \<bar>2*zs$(i-1)-1\<bar>^p) = n" unfolding hide_sum_def by simp
  then have as_part: "\<bar>zs \<bullet> as - s\<bar>=0" 
    using sum_le_rp_int unfolding hide_sum_def
    by (smt (verit, best) zero_less_power)
  have "\<forall>i<n. zs $ i \<in> {0, 1}" 
  proof - 
    have zs_ge_1:"\<bar>2*zs$(i-1)-1\<bar>\<ge>1" if "i\<in>{1..<n+1}" for i using that by presburger
    then have zsp_ge_1:"\<bar>2*zs$(i-1)-1\<bar>^p\<ge>1" if "i\<in>{1..<n+1}" for i using that by auto
    have "\<bar>2*zs$(i-1)-1\<bar> = 1" if "i\<in>{1..<n+1}" for i
    proof (subst ccontr, goal_cases)
      case 1
      then have i_gt_1: "\<bar>2*zs$(i-1)-1\<bar> > 1" using that by presburger
      then have ip_gt_1: "\<bar>2*zs$(i-1)-1\<bar>^p > 1"
        using p_def by auto
      then have gt_n: "int (n - 1) + \<bar>2 * zs $ (i - 1) - 1\<bar> ^ p > n" by auto
      have ineq1:"(\<Sum>j=1..<n+1. \<bar>2*zs$(j-1)-1\<bar>^p) = 
        (\<Sum>j\<in>{1..<n+1}-{i}. \<bar>2*zs$(j-1)-1\<bar>^p) + (\<bar>2*zs$(i-1)-1\<bar>^p)" 
        using that by (subst sum.subset_diff[of "{i}"], auto)
      also have ineq2: "\<dots> \<ge> (\<Sum>j\<in>{1..<n+1}-{i}. 1) + (\<bar>2*zs$(i-1)-1\<bar>^p)" 
        by (smt (verit, ccfv_SIG) DiffD1 sum_mono zsp_ge_1)
      also have ineq3: "(\<Sum>j\<in>{1..<n+1}-{i}. 1) = n - 1"
        by (metis Diff_empty add_diff_cancel_right' card_Diff_insert card_atLeastLessThan 
          card_eq_sum empty_iff that)
      finally have ineq4: "(\<Sum>i=1..<n+1. \<bar>2*zs$(i-1)-1\<bar>^p) \<ge>  n - 1 + (\<bar>2*zs$(i-1)-1\<bar>^p)" 
        using ineq1 ineq2 ineq3 by (smt (z3) of_nat_1 of_nat_sum sum_mono)
      then have "(\<Sum>i=1..<n+1. \<bar>2*zs$(i-1)-1\<bar>^p) >  n" 
        by (subst order.strict_trans2[OF gt_n ineq4], simp)
      then show False using zs_part unfolding hide_sum_def  by auto
    qed auto
    then have "zs$(i-1) = 0 \<or> zs$(i-1) = 1" if "i\<in>{1..<n+1}" for i
      using that by force
    then have "zs$i = 0 \<or> zs$i = 1" if "i<n" for i using that
      by (metis One_nat_def Suc_eq_plus1 atLeastLessThan_iff diff_Suc_1 le_eq_less_or_eq 
        less_Suc0 not_less_eq)
    then show ?thesis by simp
  qed
  moreover have "zs \<bullet> as = s" using as_part by auto
  ultimately have "(\<forall>i<dim_vec zs. zs $ i \<in> {0, 1}) \<and> zs \<bullet> as = s \<and> dim_vec zs = dim_vec as"
     using zs_dim n_def by auto
  then show ?thesis unfolding subset_sum_def gap_cvp_def by auto
qed


text \<open>CVP is NP-hard in $p$-norm.\<close>

lemma "is_reduction reduce_cvp_subset_sum_p subset_sum gap_cvp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case using well_defined_reduction by auto
next
  case (2 as s)
  then show ?case using NP_hardness_reduction by auto
qed

end

end
