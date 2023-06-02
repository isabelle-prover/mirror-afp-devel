theory SVP_vec

imports 
  BHLE
begin

section \<open>SVP in $\ell_\infty$\<close>
text \<open>The reduction of SVP to BHLE in $l_\infty$ norm\<close>

text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "int_lattice  \<Rightarrow> int vec \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. \<parallel>x\<parallel>\<^sub>\<infinity> \<ge> \<parallel>v\<parallel>\<^sub>\<infinity> \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "(int_lattice \<times> int) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (dim_lattice L \<ge> 2) \<and> 
      (\<exists>v\<in>L. \<parallel>v\<parallel>\<^sub>\<infinity> \<le> r \<and> v \<noteq> 0\<^sub>v (dim_vec v))}"

text \<open>Generate a lattice to solve SVP for reduction.\<close>

text \<open>Here, the factor $K''$ from the paper \cite{EmBo81} 
  was changed to be $2\cdot\mathbf{k}\cdot(k+1)\cdot \sum_i \mathbf{| a_i |}$ 
in order for the proofs to finish.\<close>

definition gen_svp_basis :: "int vec \<Rightarrow> int \<Rightarrow> int mat" where
  "gen_svp_basis a k = mat (dim_vec a + 1) (dim_vec a + 1) 
    (\<lambda> (i, j). if (i < dim_vec a) \<and> (j< dim_vec a) then (if i = j then 1 else 0)
      else (if (i < dim_vec a) \<and> (j \<ge> dim_vec a) then 0 
      else (if (i \<ge> dim_vec a) \<and> (j < dim_vec a) then (k+1) * (a $ j)
      else 2*k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. \<bar>a $ i\<bar>) +1 )))"


text \<open>Reduction SVP to bounded homogeneous linear equation problem in $\ell_\infty$ norm.\<close>
definition reduce_svp_bhle:: "(int vec \<times> int) \<Rightarrow> (int_lattice \<times> int)" where
  "reduce_svp_bhle \<equiv> (\<lambda> (a, k). (gen_lattice (gen_svp_basis a k), k))"



text \<open>Lemmas for proof\<close>

lemma gen_svp_basis_mult: 
  assumes "dim_vec z = dim_vec a + 1"
  shows "(gen_svp_basis a k) *\<^sub>v z = vec (dim_vec a + 1) 
         (\<lambda>i. if i < dim_vec a then z$i else (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) + 
              (2*k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. \<bar>a $ i\<bar>) +1) * (z$(dim_vec a)))"
using assms proof (subst vec_eq_iff, safe, goal_cases)
case 1
  then show ?case using assms unfolding gen_svp_basis_def by auto
next
case (2 i)
  then show ?case proof (cases "i<dim_vec a")
  case True
    have "{0..<dim_vec a} = insert i {0..<dim_vec a}" using True by auto
    then have "(\<Sum>ia = 0..<dim_vec a. (if i = ia then 1 else 0) * z $ ia) = 
      (\<Sum>ia \<in> insert i {0..<dim_vec a}. (if i = ia then 1 else 0) * z $ ia)" by auto
    also have "\<dots> = z$i" by (subst sum.insert_remove, auto) 
    finally have "(\<Sum>ia = 0..<dim_vec a. (if i = ia then 1 else 0) * z $ ia) = z $ i" 
      by auto
    then show ?thesis unfolding mult_mat_vec_def gen_svp_basis_def scalar_prod_def 
      using True assms by auto
  next
  case False
    then have "i = dim_vec a" using 2 by auto
    then show ?thesis unfolding gen_svp_basis_def using assms 
      by (auto simp add: scalar_prod_def sum_distrib_left mult.commute mult.left_commute)
  qed
qed

lemma gen_svp_basis_mult_real: 
  assumes "dim_vec z = dim_vec a + 1"
  shows "real_of_int_mat (gen_svp_basis a k) *\<^sub>v z = vec (dim_vec a + 1) 
         (\<lambda>i. if i < dim_vec a then z$i else (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) + 
              (2*k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. \<bar>a $ i\<bar>) +1) * (z$(dim_vec a)))"
using assms proof (subst vec_eq_iff, safe, goal_cases)
case 1
  then show ?case using assms unfolding gen_svp_basis_def by auto
next
case (2 i)
  then show ?case proof (cases "i<dim_vec a")
  case True
    have "{0..<dim_vec a} = insert i {0..<dim_vec a}" using True by auto
    then have "(\<Sum>ia = 0..<dim_vec a. (if i = ia then 1 else 0) * z $ ia) = 
      (\<Sum>ia \<in> insert i {0..<dim_vec a}. (if i = ia then 1 else 0) * z $ ia)" by auto
    also have "\<dots> = z$i" by (subst sum.insert_remove, auto) 
    finally have "(\<Sum>ia = 0..<dim_vec a. (if i = ia then 1 else 0) * z $ ia) = z $ i" 
      by auto
    then have "(\<Sum>ia = 0..<dim_vec a. real_of_int (if i = ia then 1 else 0) * z $ ia) = z $ i" 
      by (smt (verit, best) of_int_hom.hom_one of_int_hom.hom_zero sum.cong)
    then show ?thesis unfolding mult_mat_vec_def gen_svp_basis_def scalar_prod_def 
      using True assms by auto
  next
  case False
    then have "i = dim_vec a" using 2 by auto
    then show ?thesis unfolding gen_svp_basis_def using assms 
      by (auto simp add: scalar_prod_def sum_distrib_left mult.commute mult.left_commute)
  qed
qed

lemma gen_svp_basis_mult_last: 
  assumes "dim_vec z = dim_vec a + 1"
  shows "((gen_svp_basis a k) *\<^sub>v z) $ (dim_vec a) = 
         (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) + 
              (2*k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. \<bar>a $ i\<bar>) +1) * (z$(dim_vec a))"
using gen_svp_basis_mult[OF assms] by auto

text \<open>The set generated by \<open>gen_svp_basis\<close> is indeed linearly independent.\<close>
lemma is_indep_gen_svp_basis: 
  assumes "k>0"
  shows "is_indep (gen_svp_basis a k)"
unfolding is_indep_int_def
proof (safe, goal_cases)
case (1 z)
  have dim_row_dim_vec: "dim_row (gen_svp_basis a k) = dim_vec z" 
    using 1 unfolding gen_svp_basis_def by auto
  then have suc_dim_a_dim_z: "dim_vec z = dim_vec a + 1" unfolding gen_svp_basis_def by auto
  have alt1: "(real_of_int_mat (gen_svp_basis a k) *\<^sub>v z) $ i = 0" if "i< dim_vec a +1"for i 
    using 1(1) that unfolding gen_svp_basis_def by auto
  have z_upto_last: "z$i = 0" if "i < dim_vec a" for i 
  proof -
    have elem: "(real_of_int_mat (gen_svp_basis a k) *\<^sub>v z) $ i = z $ i" 
      using gen_svp_basis_mult_real[OF suc_dim_a_dim_z] that by auto
    show ?thesis by (subst elem[symmetric]) (use alt1[of i] that in \<open>auto\<close>) 
  qed
  moreover have "z $ (dim_vec a) = 0"
  proof -
    have "0 = (real_of_int_mat (gen_svp_basis a k) *\<^sub>v z) $ (dim_vec a)" using alt1 by auto
    also have "\<dots> = (real_of_int k + 1) * (\<Sum>i = 0..<dim_vec a. z $ i * real_of_int (a $ i)) +
      (2 * real_of_int k * (real_of_int k + 1) * (\<Sum>x = 0..<dim_vec a. real_of_int (\<bar>a $ x\<bar>)) + 1) *
      z $ dim_vec a" 
      using gen_svp_basis_mult_real[OF suc_dim_a_dim_z] by auto
    also have "\<dots> =  real_of_int (2 * k * (k + 1) *  (\<Sum>x = 0..<dim_vec a. \<bar>a $ x\<bar>)  + 1 ) * (z$dim_vec a)"
      using suc_dim_a_dim_z using z_upto_last by auto
    finally have "0 = real_of_int (2 * k * (k + 1) *  (\<Sum>x = 0..<dim_vec a. \<bar>a $ x\<bar>) + 1 ) * 
                      (z$dim_vec a)" by blast
    moreover have "real_of_int (2 * k * (k + 1) *  (\<Sum>x = 0..<dim_vec a. \<bar>a $ x\<bar>) + 1 ) \<noteq> 0"
    proof (rule ccontr, goal_cases)
    case 1
      then have eq: "real_of_int (\<Sum>x = 0..<dim_vec a. \<bar>a $ x\<bar>) = - 1 / real_of_int (k * (k + 1))"
         using assms
         by (smt (verit, best) mult_minus_right of_int_hom.hom_0 pos_zmult_eq_1_iff 
          pos_zmult_eq_1_iff_lemma)
      have "k\<ge>1" using assms by auto
      have "real_of_int (\<Sum>x = 0..<dim_vec a. \<bar>a $ x\<bar>) \<in> \<int>" by auto
      moreover have "- 1 / real_of_int (k * (k + 1)) \<notin> \<int>" using \<open>k\<ge>1\<close> 
      by (smt (verit, del_insts) "1" linordered_semiring_strict_class.mult_pos_pos 
        mult_minus_right of_int_hom.hom_0 pos_zmult_eq_1_iff)
      ultimately show False using eq by auto
    qed
(*Problems here when changing 2*(k+1) to k*(k+1). 
  This is necessary since k'a only is smaller than k'' under the assumtion that z$i\<le>k, not z$i\<le>2.*)
    ultimately show ?thesis by auto
  qed
  ultimately have "z$i =  0" if "i < dim_vec z" for i using that suc_dim_a_dim_z
    by (metis discrete le_eq_less_or_eq verit_comp_simplify1(3))
  then show ?case by auto
qed



lemma insert_set_comprehension:
  "insert (f x) {f i |i. i<(x::nat)} = {f i | i. i<x+1}"
using less_SucE by fastforce

lemma bhle_k_pos:
  assumes "(a,k) \<in> bhle"
  shows "k>0"
using assms unfolding bhle_def 
proof (safe, goal_cases)
case (1 v)
  have "\<exists>i<dim_vec v. \<bar>v $ i\<bar> > 0" using 1 by auto
  then have "\<parallel>v\<parallel>\<^sub>\<infinity> > 0" unfolding linf_norm_vec_Max using 1 by (subst Max_gr_iff, auto)
  then show ?thesis using 1 by auto
qed 

lemma svp_k_pos:
  assumes "reduce_svp_bhle (a, k) \<in> gap_svp"
  shows "k>0"
proof -
  obtain v where v_in_lattice: "v\<in>gen_lattice (gen_svp_basis a k)" 
    and infnorm_v: "\<parallel>v\<parallel>\<^sub>\<infinity> \<le> k" 
    and v_nonzero:  "v \<noteq> 0\<^sub>v (dim_vec v)" 
    using assms unfolding reduce_svp_bhle_def gap_svp_def by force
  have "\<exists> i < dim_vec v. \<bar>v $ i\<bar> > 0" using v_nonzero by auto
  then have "\<parallel>v\<parallel>\<^sub>\<infinity> > 0" unfolding linf_norm_vec_Max by (subst Max_gr_iff, auto)
  then show ?thesis using infnorm_v by auto
qed


lemma svp_dim_vec_a:
  assumes "reduce_svp_bhle (a, k) \<in> gap_svp"
  shows "dim_vec a > 0"
proof -
  have "2 \<le> dim_lattice (gen_lattice (gen_svp_basis a k))" 
    using assms unfolding reduce_svp_bhle_def gap_svp_def by auto
  then have "2 \<le> dim_col (gen_svp_basis a k)" 
    using dim_lattice_gen_lattice[of "gen_svp_basis a k",OF is_indep_gen_svp_basis]
      svp_k_pos[OF assms] by auto
  then show ?thesis unfolding gen_svp_basis_def by auto
qed

lemma bhle_dim_vec_a:
  assumes "(a, k) \<in> bhle"
  shows "dim_vec a > 0"
using assms unfolding bhle_def by auto


lemma first_lt_second:
  assumes "k>0" and z_le_k:"\<And>i. i< dim_vec a \<Longrightarrow> \<bar>z $ i\<bar> \<le> k"
  shows "2 * \<bar>(k + 1) * (\<Sum>i = 0..<dim_vec a. z $ i * a $ i)\<bar>
      < (\<bar>2 * k * (k + 1) * (\<Sum>i = 0..<dim_vec a. \<bar>a $ i\<bar>) + 1\<bar>::int)"
proof - 
  have take_k1_out: "\<bar>(k + 1) * (\<Sum>i = 0..<dim_vec a. z $ i * a $ i)\<bar> = 
    (k+1) * \<bar>\<Sum>i=0..<dim_vec a. z $ i * a $ i\<bar>"
    using \<open>k>0\<close> by (smt (verit, best) mult_minus_right mult_nonneg_nonneg)
  have "\<bar>\<Sum>i = 0..<dim_vec a. z $ i * a $ i\<bar> \<le> (\<Sum>i = 0..<dim_vec a. \<bar>z $ i * a $ i\<bar>)"
    by (subst sum_abs[of "(\<lambda>i. z$i * a$i)" "{0..<dim_vec a}"],simp)
  also have "\<dots> = (\<Sum>i=0..<dim_vec a. \<bar>z $ i\<bar> * \<bar>a $ i\<bar>)"
    by (meson abs_mult)
  also have "\<dots> \<le> (\<Sum>i=0..<dim_vec a.  k * \<bar>a $ i\<bar>)" 
    by (subst sum_mono) (auto simp add: z_le_k mult_right_mono)
  also have "\<dots> = k * (\<Sum>i=0..<dim_vec a. \<bar>a $ i\<bar>)"
  by (metis mult_hom.hom_sum)
  finally have "\<bar>(\<Sum>i=0..<dim_vec a. z $ i * a $ i)\<bar> \<le> k * (\<Sum>i=0..<dim_vec a. \<bar>a $ i\<bar>)"
    by blast
  then show ?thesis using take_k1_out using \<open>0 < k\<close> by auto
qed


text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_svp:
  assumes "(a,k) \<in> bhle"
  shows "reduce_svp_bhle (a,k) \<in> gap_svp"
using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
proof (safe, goal_cases)
  case (1 x)
  have "k>0" using assms bhle_k_pos by auto
  then show ?case using is_lattice_gen_lattice is_indep_gen_svp_basis by auto
next 
  case (2 x)
  have "dim_lattice (gen_lattice (gen_svp_basis a k)) = dim_col (gen_svp_basis a k)"
    using dim_lattice_gen_lattice assms bhle_k_pos is_indep_gen_svp_basis by presburger
  also have "\<dots> =  dim_vec a + 1" unfolding gen_svp_basis_def by auto
  also have "\<dots> \<ge> 2" using bhle_dim_vec_a[OF assms] by auto                              
  finally show ?case by auto
next
  case (3 x)
  let ?x = "vec (dim_vec x + 1) (\<lambda>i. if i< dim_vec x then x$i else 0)"
  define v where "v = (gen_svp_basis a k) *\<^sub>v ?x"
  have eigen_v: "v = ?x" unfolding v_def 
  apply (subst gen_svp_basis_mult[where a= a and k=k and z=" ?x"], auto simp add: 3(2) comp_def)
  apply (subst vec_eq_iff, auto simp add: 3(1) scalar_prod_def)
  proof (goal_cases one two)
    case (one i)
    then show ?case by (auto simp add: comp_def 3(2))
  next
    case (two i)
    have "(\<Sum>i = 0..<dim_vec a. (x $ i) * (a $ i)) = 0" 
      using 3 unfolding scalar_prod_def
      by (smt (verit) mult.commute of_int_hom.hom_zero of_int_mult of_int_sum sum.cong)
    then show ?case using 3 by auto
  qed
  have "dim_vec ?x = dim_col (gen_svp_basis a k)" 
    using 3(2) unfolding gen_svp_basis_def by auto
  then have "v \<in> gen_lattice (gen_svp_basis a k)"  
    unfolding v_def gen_lattice_def by auto
  moreover have "\<parallel>v\<parallel>\<^sub>\<infinity> \<le> k" 
  proof -
    have "\<parallel>v\<parallel>\<^sub>\<infinity> \<le> \<parallel>x\<parallel>\<^sub>\<infinity>" unfolding eigen_v linf_norm_vec_Max
    proof (rule Max.boundedI, goal_cases _ _ three)
    case (three b)
      have dim_x_nonzero: "dim_vec x \<noteq> 0" using 3(3) 3(2) by auto
      then have nonempty: "(\<exists>a\<in>{\<bar>x $ i\<bar> |i. i < dim_vec x}. 0 \<le> a)"
        using abs_ge_zero by blast
      have " \<bar>x $ i\<bar> \<le> Max (insert 0 {\<bar>x $ j\<bar> |j. j < dim_vec x})" 
        if "i < dim_vec x" for i 
      using that by (subst Max_ge, auto)
      moreover have "0 \<le> Max (insert 0 {\<bar>x $ i\<bar> |i. i < dim_vec x})" using 3 nonempty
        by (subst Max_ge_iff, auto)
      ultimately show ?case using three by auto
    qed auto
    then show ?thesis using 3 by auto
  qed
  moreover have "v \<noteq> 0\<^sub>v (dim_vec v)" using 3(3) 
  proof (safe)
    assume "0 < dim_vec a" 
    assume "v = 0\<^sub>v (dim_vec v)"
    have fst: "x \<noteq> 0\<^sub>v (dim_vec x)" using 3(4) by blast
    have snd: "?x = 0\<^sub>v (dim_vec v)" using \<open>v = 0\<^sub>v (dim_vec v)\<close>  eigen_v by auto
    have "x$i = 0" if "i< dim_vec x" for i using snd
    by (smt (z3) add.commute dim_vec eigen_v index_map_vec(2) index_vec index_zero_vec(1) 
      of_int_eq_iff of_int_hom.hom_zero that 
      trans_less_add2)
  then show False using fst by auto
  qed
  ultimately show ?case by blast
qed





text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_svp:
  assumes "reduce_svp_bhle (a,k) \<in> gap_svp"
  shows "(a,k) \<in> bhle"
proof (cases "(\<Sum>i<dim_vec a. a$i) = 0")
  case True
  have a_nonempty: "dim_vec a > 0" using svp_dim_vec_a[OF assms] by auto
  have "k>0" using svp_k_pos[OF assms] by auto
  define x where "x = vec (dim_vec a) (\<lambda>i. k)"
  have "a \<bullet> x = 0" unfolding x_def scalar_prod_def 
  by (auto simp add: True sum_distrib_right[symmetric])
     (metis True lessThan_atLeast0)
  moreover have "dim_vec x = dim_vec a" unfolding x_def by auto
  moreover have "x \<noteq> 0\<^sub>v (dim_vec x)"
  proof -
    have "\<exists>i< dim_vec x. x $ i \<noteq> 0" unfolding x_def using \<open>k>0\<close> a_nonempty by auto
    then show ?thesis using vec_eq_iff[of "x" "0\<^sub>v (dim_vec x)"] by auto
  qed 
  moreover have "real_of_int (\<parallel>x\<parallel>\<^sub>\<infinity>) \<le> k"
  proof -
    have "vec (dim_vec a) (\<lambda>i. k) $ j = k" if "j < dim_vec a" for j using that by auto
    then have "Max {\<bar>vec (dim_vec a) (\<lambda>i. k) $ i\<bar> |i. i < dim_vec a} = 
               Max {\<bar>k\<bar> |i. i < dim_vec a}" by metis
    also have "\<dots> = Max {k}" using \<open>k>0\<close> a_nonempty
      by (smt (verit, best) Collect_cong singleton_conv)
    also have "\<dots> = k" by auto
    finally have "Max {\<bar>vec (dim_vec a) (\<lambda>i. k) $ i\<bar> |i. i < dim_vec a} = k" by blast
    then show ?thesis unfolding x_def linf_norm_vec_Max using \<open>k>0\<close> by auto 
  qed
  ultimately show ?thesis using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
    by fastforce 
next
  case False
  show ?thesis using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
  proof (safe, goal_cases)
    case (1 v)
    have a_nonempty: "dim_vec a > 0" using svp_dim_vec_a[OF assms] by auto  
    have "k>0"  unfolding linf_norm_vec_Max
    proof -
      have "\<exists>i<dim_vec v. \<bar>v $ i\<bar> > 0" using 1 by auto
      then have "\<parallel>v\<parallel>\<^sub>\<infinity> > 0" unfolding linf_norm_vec_Max by (subst Max_gr_iff, auto)
      then show ?thesis using 1 by auto
    qed
    then have "k\<ge>1" by auto
    obtain z where z_def:
      "v = (gen_svp_basis a k) *\<^sub>v  z" 
      "dim_vec z = dim_vec a + 1"
      using 1 unfolding gen_lattice_def gen_svp_basis_def by auto
    have dim_v_dim_a:"dim_vec v = dim_vec a + 1" 
      using 1 unfolding gen_lattice_def gen_svp_basis_def by auto
    define x where "x = vec (dim_vec a) (($) z)"
    have v_eq_z_upto_last: "v $ i = z $ i" if "i< dim_vec a" for i 
      by (subst z_def) (subst gen_svp_basis_mult; use that z_def in \<open>auto\<close>)
    have v_le_k: "\<bar>v $ i\<bar> \<le> k" if "i< dim_vec a + 1" for i
      using 1 dim_v_dim_a that unfolding linf_norm_vec_Max
      using Max_le_iff[of "{\<bar>v $ i\<bar> |i. i < dim_vec v}" k]
      by fastforce
    then have z_le_k: "\<bar>z $ i\<bar> \<le> k" if "i< dim_vec a" for i
      using v_eq_z_upto_last[OF that] that
      by (metis less_add_one less_trans)

    have v_last_zero: "v$(dim_vec a) = 0"
    proof (rule ccontr)
      assume ccontr_assms:"v $ dim_vec a \<noteq> 0"
      have v_last: "v$(dim_vec a) = 
        (k+1) * (\<Sum>i = 0..<dim_vec a. z $ i * a $ i) +
        (2*k*(k+1) * (\<Sum>x = 0..<dim_vec a. \<bar>a $ x\<bar>) + 1) * (z $ dim_vec a) "
        (is "v$(dim_vec a) = ?first + ?second")
        by (auto simp: z_def gen_svp_basis_mult_last)
      then have "?first \<noteq> 0 \<or> ?second \<noteq> 0"
        using ccontr_assms by auto
      then consider 
        (first) "?first \<noteq> 0 \<and> ?second = 0" | 
        (second) "?second \<noteq> 0 \<and> ?first = 0" |
        (both) "?first \<noteq> 0 \<and> ?second \<noteq> 0"
        by blast
      then show False 
      proof (cases)
        case first
        then have gr_1: "\<bar>\<Sum>i = 0..<dim_vec a. z $ i * a $ i\<bar> \<ge> 1" 
          using \<open>k>0\<close> by auto
        have "\<bar>v$ dim_vec a\<bar> = \<bar>?first\<bar>" using first v_last by auto
        also have "\<dots> = (k+1) * \<bar>\<Sum>i = 0..<dim_vec a. z $ i * a $ i\<bar>"
          using \<open>k>0\<close>
          by (smt (z3) mult_le_0_iff mult_minus_right)
        also have "\<dots> > k" using first gr_1 \<open>k>0\<close>
        by (smt (verit, best) mult_le_cancel_left1)
        finally have "\<bar>v$ dim_vec a\<bar> > k" by auto
        then show ?thesis using v_le_k[of "dim_vec a"] by auto
      next
        case second
        have "\<bar>z $ dim_vec a\<bar> \<ge> 1" using second by auto
        have sum_a_ge_1:"(\<Sum>x<dim_vec a. \<bar>a $ x\<bar>) \<ge>1" 
          using False atLeast0LessThan
          by (metis abs_sum_abs int_one_le_iff_zero_less not_less sum_abs zero_less_abs_iff)
        then have "2*k*(k+1)*(\<Sum>x<dim_vec a. \<bar>a $ x\<bar>) + 1 > k"
        proof -
          have "2*(k+1)*(\<Sum>x<dim_vec a. \<bar>a $ x\<bar>)\<ge>1" using \<open>k>0\<close>
            by (smt (verit, ccfv_SIG) int_distrib(2) sum_a_ge_1 zmult_zless_mono2)
          then show ?thesis using \<open>k>0\<close>
            by (smt (verit, best) pos_mult_pos_ge sum_a_ge_1)
        qed
        moreover have "\<bar>?second\<bar> \<ge> \<bar>2*k*(k+1)*(\<Sum>x<dim_vec a. \<bar>a $ x\<bar>) + 1\<bar>"
          using \<open>\<bar>z $ dim_vec a\<bar> \<ge> 1\<close> 
          by (subst abs_mult) (simp add: lessThan_atLeast0 mult_le_cancel_left1)
        ultimately have "\<bar>v $ dim_vec a\<bar> > k" using second v_last by linarith
        then show ?thesis using v_le_k[of "dim_vec a"] by auto
      next
        case both
        have z_gr_one:"\<bar>real_of_int (z$dim_vec a)\<bar>\<ge>1" using both by auto
        let ?second' = "2 * k * (k + 1) * (\<Sum>i=0..<dim_vec a. \<bar>a $ i\<bar>) + 1"
        have "(\<Sum>i = 0..<dim_vec a. z $ i * a $ i) \<noteq> 0" using both by auto
        then have one: "k < \<bar>?first\<bar>"
          by (smt (z3) mult_less_cancel_left2 mult_minus_right)
        then have first_nonzero: "\<bar>?first\<bar> \<noteq> 0" using \<open>k>0\<close> by auto
        have two'':"2 * \<bar>?first\<bar> < \<bar>?second'\<bar>"
          using first_lt_second[OF \<open>k>0\<close> z_le_k] by auto
        then have two': "\<bar>real_of_int ?second'  / real_of_int ?first\<bar> > 2" 
        proof - 
          have "0<real_of_int \<bar>?first\<bar>" using first_nonzero by presburger
          have "2 * real_of_int \<bar>?first\<bar> < real_of_int \<bar>?second'\<bar>" using two'' by linarith
          then have "2 <  real_of_int \<bar>?second'\<bar> / real_of_int \<bar>?first\<bar>" 
            by (subst pos_less_divide_eq[OF \<open>0<real_of_int \<bar>?first\<bar>\<close>], auto)
          also have "\<dots> = \<bar>real_of_int ?second' / real_of_int ?first\<bar>" by simp
          finally show ?thesis by presburger
        qed
        then have two:"\<bar>(real_of_int ?second'  / real_of_int ?first) * 
            real_of_int (z$dim_vec a)\<bar> > 2"
        proof -
          have "\<bar>(real_of_int ?second'  / real_of_int ?first) * 
            real_of_int (z$dim_vec a)\<bar> = \<bar>real_of_int ?second'  / real_of_int ?first\<bar> * 
            \<bar>real_of_int (z$dim_vec a)\<bar>" by (subst abs_mult, auto)
          also have ineq: "\<dots> \<ge> \<bar>real_of_int ?second'  / real_of_int ?first\<bar>"
            using z_gr_one by (smt (z3) mult_less_cancel_left2)
          finally have "\<bar>(real_of_int ?second'  / real_of_int ?first) * 
            real_of_int (z$dim_vec a)\<bar>\<ge> \<bar>real_of_int ?second'  / real_of_int ?first\<bar>" by blast
          then show ?thesis using two' by linarith
        qed
        have "real_of_int \<bar>v $ dim_vec a\<bar> / real_of_int \<bar>?first\<bar> \<ge> 1"
        proof -
          have "real_of_int \<bar>v $ dim_vec a\<bar> / real_of_int \<bar>?first\<bar> = 
            \<bar>real_of_int (v $ dim_vec a)\<bar> / \<bar>real_of_int ?first\<bar>"
            using of_int_abs[of "v $ dim_vec a"] of_int_abs[of "?first"] by auto
          also have "\<dots> = \<bar>real_of_int (v $ dim_vec a) / real_of_int ?first\<bar>"
            using abs_divide[symmetric] by auto
          also have "\<dots> = \<bar>(real_of_int ?first + real_of_int ?second' * real_of_int (z$dim_vec a)) / 
            real_of_int ?first\<bar>" using v_last by auto
          also have "\<dots> = \<bar>real_of_int ?first / real_of_int ?first + 
            (real_of_int ?second'  / real_of_int ?first)* real_of_int (z$dim_vec a)\<bar>"
            by (metis (no_types, lifting) add_divide_distrib times_divide_eq_left)
          also have "\<dots> = \<bar>1 + (real_of_int ?second'  / real_of_int ?first) * 
            real_of_int (z$dim_vec a)\<bar>"
            using first_nonzero by (smt (verit, del_insts) of_int_eq_0_iff one_eq_divide_iff)
          also have "\<dots> \<ge> 1" using two by linarith
          finally show "real_of_int \<bar>v $ dim_vec a\<bar> / real_of_int \<bar>?first\<bar> \<ge> 1" by blast
        qed
        then have "real_of_int \<bar>v $ dim_vec a\<bar> \<ge> real_of_int \<bar>?first\<bar>"
          by (simp add: le_divide_eq_1)
        then have "\<bar>v $ dim_vec a\<bar> \<ge> \<bar>?first\<bar>" using of_int_le_iff by blast
        then have "\<bar>v $ dim_vec a\<bar> > k" using one by auto
        then show ?thesis using v_le_k[of "dim_vec a"] by auto
      qed
    qed
    have z_last_zero: "z$dim_vec a = 0" 
    proof (rule ccontr)
      assume ccontr_assms:"z $ dim_vec a \<noteq> 0"
      then have "\<bar>z $ dim_vec a\<bar> \<ge> 1" by auto
      have "(k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) + 
        (2*k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. \<bar>a $ i\<bar>) +1) * (z$(dim_vec a)) = 0"
        (is "?first + ?second * (z$(dim_vec a)) = 0")
        using v_last_zero z_def gen_svp_basis_mult_last by auto
      then have abs_eq: "\<bar>?first\<bar> = \<bar>?second * (z$(dim_vec a))\<bar>" by linarith
      moreover have "\<bar>?first\<bar> < \<bar>?second * (z$(dim_vec a))\<bar>"
      proof - 
        have "\<bar>?first\<bar> \<le> 2*\<bar>?first\<bar>" by auto
        then have "\<bar>?first\<bar> < \<bar>?second\<bar>" using first_lt_second[OF \<open>k>0\<close> z_le_k, of a] by auto
        moreover have "\<bar>?second\<bar> \<le> \<bar>?second\<bar>*\<bar>z$dim_vec a\<bar>" 
          using \<open>\<bar>z $ dim_vec a\<bar> \<ge> 1\<close> by (simp add: mult_le_cancel_left1)
        ultimately have "\<bar>?first\<bar> < \<bar>?second\<bar>*\<bar>z$dim_vec a\<bar>" by linarith
        then show ?thesis by linarith
      qed
      ultimately show False by auto
    qed
 
    have v_real_z: "v = z" using v_eq_z_upto_last v_last_zero z_last_zero
      by (metis Suc_eq_plus1 dim_v_dim_a less_Suc_eq vec_eq_iff z_def(2))

    have "a \<bullet> x = 0" 
    proof -
      have "0 = ((gen_svp_basis a k) *\<^sub>v  z) $ (dim_vec a)" 
        using v_last_zero z_def by auto
      also have "\<dots> = (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i)" 
        by (subst gen_svp_basis_mult, auto simp add: z_def z_last_zero)
      finally have zero: "(k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) = 0" by auto
      then show ?thesis unfolding scalar_prod_def using x_def \<open>k>0\<close>
      by (smt (verit, ccfv_SIG) atLeastLessThan_iff dim_vec index_vec mult.commute
         mult_eq_0_iff of_int_hom.hom_0 sum.cong)
    qed
    moreover have "dim_vec x = dim_vec a" unfolding x_def by auto
    moreover have "x \<noteq> 0\<^sub>v (dim_vec x)" 
    proof -
      have "\<exists>i< dim_vec a + 1. v$i \<noteq> 0" using 1 unfolding gen_lattice_def gen_svp_basis_def by auto
      then have "\<exists>i< dim_vec a. v$i \<noteq> 0" using v_last_zero
        by (metis add_le_cancel_right discrete nat_less_le)
      then obtain i where "i<dim_vec a" "v$i\<noteq>0" by blast
      then have "z$i \<noteq> 0" using v_real_z z_def 
        by (auto)
      then have "\<exists>i< dim_vec a. x$i \<noteq> 0" using x_def \<open>i<dim_vec a\<close> by auto
      then show ?thesis using x_def by auto
    qed
    moreover have "\<parallel>x\<parallel>\<^sub>\<infinity> \<le> k"
    proof - 
      have "\<bar>z$i\<bar> = \<bar>vec (dim_vec a) (($) z) $ i\<bar>" if "i < dim_vec a" for i using that by auto
      then have "Max (insert 0 {\<bar>vec (dim_vec a) (($) z) $ i\<bar> |i. i < dim_vec a}) =
            Max (insert 0 {\<bar>z $ i\<bar> |i. i < dim_vec a})" 
        by (smt (z3) Collect_cong Setcompr_eq_image mem_Collect_eq)
      also have "\<dots> = Max (insert 0 {\<bar>z $ i\<bar> |i. i < dim_vec a + 1})" 
      proof -
        have "Max (insert 0 {\<bar>z $ i\<bar> |i. i < dim_vec a}) = 
          Max (insert 0 (insert ( \<bar>z$dim_vec a\<bar>) {\<bar>z $ i\<bar> |i. i < dim_vec a}))"
        proof -
          have "Max {\<bar>z $ i\<bar> |i. i < dim_vec a} \<ge> 0" 
            using \<open>dim_vec a >0\<close> by (subst Max_ge_iff, auto)
          then have "Max {\<bar>z $ i\<bar> |i. i < dim_vec a} \<ge> \<bar>z$dim_vec a\<bar>"
            using z_last_zero by simp
          then have max_subst: "Max {\<bar>z $ i\<bar> |i. i < dim_vec a} = 
              Max (insert \<bar>z $ dim_vec a\<bar> {\<bar>z $ i\<bar> |i. i < dim_vec a})" 
            using \<open>dim_vec a > 0\<close> by (subst Max_insert)+ (auto)
          then show ?thesis using \<open>dim_vec a > 0\<close> by (subst Max_insert)+ (auto)
        qed
        then show ?thesis 
          using insert_set_comprehension[of "(\<lambda>i. \<bar>z $ i\<bar>)" "dim_vec a"] by auto
      qed
      finally have "Max (insert 0 {\<bar>vec (dim_vec a) (($) z) $ i\<bar> |i. i < dim_vec a}) =
                    Max (insert 0 {\<bar>z $ i\<bar> |i. i < dim_vec a +1})"
        by blast
      then have "\<parallel>x\<parallel>\<^sub>\<infinity> = \<parallel>v\<parallel>\<^sub>\<infinity>" unfolding linf_norm_vec_Max
        using x_def z_def v_real_z  by auto
      then show ?thesis using 1 by auto
    qed
    ultimately show ?case by force
  qed
qed


text \<open>The SVP is NP-hard in $\ell_\infty$.\<close>
lemma "is_reduction reduce_svp_bhle bhle gap_svp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case using well_defined_reduction_svp by auto
next
  case (2 as s)
  then show ?case using NP_hardness_reduction_svp by auto
qed



end