(*  
    Title:      Echelon_Form_Det.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Determinant of matrices over principal ideal rings*}

theory Echelon_Form_Det
  imports Echelon_Form
begin

subsection{*Definitions*}

text{*The following definition can be improved in terms of performance, because it checks if
  there exists an element different from zero twice.*}

definition echelon_form_of_column_k_det ::
  "'b::{bezout_domain} \<times> (('b, 'c::{mod_type}) vec, 'd::{mod_type}) vec \<times> nat 
  \<times> ('b \<Rightarrow> 'b \<Rightarrow> 'b \<times> 'b \<times> 'b \<times> 'b \<times> 'b) \<Rightarrow> nat 
  \<Rightarrow> 'b \<times> (('b, 'c) vec, 'd) vec \<times> nat \<times> ('b \<Rightarrow> 'b \<Rightarrow> 'b \<times> 'b \<times> 'b \<times> 'b \<times> 'b)"
  where "echelon_form_of_column_k_det A' k 
  = (let det_P=fst A'; A = fst (snd A'); i = fst (snd(snd A')); 
  bezout = snd (snd (snd A'));
  from_nat_k = from_nat k; from_nat_i = from_nat i     
  in if ((i \<noteq> nrows A) \<and> (A $ from_nat_i $ from_nat_k = 0) \<and>
  (\<exists>m>from_nat_i. A $ m $ from_nat_k \<noteq> 0)) then 
  (-1*det_P,echelon_form_of_column_k (A,i,bezout) k) 
  else (det_P,echelon_form_of_column_k (A,i,bezout) k))"

definition "echelon_form_of_upt_k_det A' k bezout
  = (let A = (snd A'); f = (foldl echelon_form_of_column_k_det (1, A, 0, bezout) [0..<Suc k])
  in (fst f, fst (snd f)))"


definition "echelon_form_of_det" :: "'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type} 
  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> ('a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}))"
  where "echelon_form_of_det A bezout = echelon_form_of_upt_k_det (1::'a,A) (ncols A - 1) bezout"

subsection{*Properties*}

subsubsection{*Bezout Iterate*}

lemma det_bezout_iterate:
  fixes A::"'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  and Aik: "A $ i $ from_nat k \<noteq> 0"
  and n: "n<ncols A"
  shows "det (bezout_iterate A n i (from_nat k) bezout) = det A"
  using Aik n
proof (induct n arbitrary: A)
  case 0
  show ?case unfolding bezout_iterate.simps ..
next
  case (Suc n)
  show ?case
  proof (cases "Suc n \<le> to_nat i")
    case True thus ?thesis unfolding bezout_iterate.simps by simp
  next
    let ?B = "bezout_matrix A i (from_nat (Suc n)) (from_nat k) bezout"
    let ?A="(?B ** A)"
    case False    
    hence "(bezout_iterate A (Suc n) i (mod_type_class.from_nat k) bezout) 
      = bezout_iterate ?A n i (mod_type_class.from_nat k) bezout"
      unfolding bezout_iterate.simps by auto
    also have "det (...) = det ?A"
    proof (rule Suc.hyps, rule bezout_matrix_not_zero[OF ib _ Suc.prems(1)])
      show "n < ncols ?A" using Suc.prems(2) unfolding ncols_def by simp
      show "i \<noteq> from_nat (Suc n)" using False
        by (metis Suc.prems(2) eq_imp_le ncols_def to_nat_from_nat_id)
    qed
    also have "... = det A"
    proof -
      have "det ?B = 1"
      proof (rule det_bezout_matrix[OF ib _  Suc.prems(1)])          
        have "from_nat (to_nat i) < (from_nat (Suc n)::'n)"
        proof (rule from_nat_mono)
          show "to_nat i < Suc n" using False by simp
          show "Suc n < CARD('n)" using Suc.prems(2) unfolding ncols_def .
        qed
        thus "i < mod_type_class.from_nat (Suc n)" unfolding from_nat_to_nat_id .
      qed
      thus ?thesis unfolding  det_mul by auto
    qed
    finally show ?thesis .
  qed
qed


subsubsection{*Echelon Form of column k*}

lemma det_echelon_form_of_column_k_det:
  fixes A::"'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  and det: "det_P * det B = det A"
  shows "(fst (echelon_form_of_column_k_det (det_P,A,i,bezout) k)) * det B 
  = det (fst (snd (echelon_form_of_column_k_det (det_P,A,i,bezout) k)))"
proof -
  let ?interchange="(interchange_rows A (from_nat i) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))"
  let ?B="(bezout_iterate ?interchange (nrows A - Suc 0) (from_nat i) (from_nat k) bezout)"
  show ?thesis
  proof (unfold echelon_form_of_column_k_det_def Let_def echelon_form_of_column_k_def, 
      auto simp add: assms)
    fix m
    assume i: "from_nat i < m"
      and Amk: "A $ m $ from_nat k \<noteq> 0"
      and i_not_nrows: "i \<noteq> nrows A "
      and Aik: "A $ from_nat i $ from_nat k = 0"
    have "det ?B = det ?interchange"
    proof (rule det_bezout_iterate[OF ib])
      show "?interchange $ from_nat i $ from_nat k \<noteq> 0" 
        by (metis (mono_tags, lifting) Amk LeastI_ex 
          dual_order.strict_iff_order i interchange_rows_i)
      show "nrows A - Suc 0 < ncols ?interchange"  unfolding nrows_def ncols_def by simp
    qed
    also have "... = - det A" 
    proof (rule det_interchange_different_rows, rule ccontr, simp)
      assume i_least: "from_nat i = (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)"
      have "A $ from_nat i $ from_nat k \<noteq> 0"
        by (metis (poly_guards_query, lifting) Amk LeastI_ex 
          dual_linorder.linear i i_least leD)
      thus "False" using Aik by contradiction
    qed    
    finally show "- det A = det ?B" by simp
  next
    assume i: "i \<noteq> nrows A"
      and Aik: "A $ from_nat i $ from_nat k \<noteq> 0"
    have "det ?B = det ?interchange"
    proof (rule det_bezout_iterate[OF ib])
      show "?interchange $ from_nat i $ from_nat k \<noteq> 0"
        by (metis (mono_tags, lifting) Aik LeastI dual_order.order_refl interchange_rows_i)    
      show "nrows A - Suc 0 < ncols ?interchange"  unfolding nrows_def ncols_def by simp
    qed
    also have "... = det A"
      by (rule det_interchange_same_rows, rule Least_equality[symmetric], auto simp add: Aik)
    finally show "det A = det ?B" ..
  qed
qed



lemma snd_echelon_form_of_column_k_det_eq:
  shows "snd (echelon_form_of_column_k_det (n, A, i, bezout) k) 
  = echelon_form_of_column_k (A,i, bezout) k"
  unfolding echelon_form_of_column_k_det_def echelon_form_of_column_k_def Let_def snd_conv fst_conv
  by auto


subsubsection{*Echelon form up to column k*}

lemma snd_foldl_ef_det_eq: "snd (foldl echelon_form_of_column_k_det (n, A, 0, bezout) [0..<k]) 
  = foldl echelon_form_of_column_k (A, 0, bezout) [0..<k]"
proof (induct k)
  case 0
  show ?case
    by (simp add: echelon_form_of_column_k_det_def Let_def)
next
  case (Suc k)
  have Suc_rw: "[0..<(Suc k)] = [0..<k] @ [k]" by simp
  show ?case
    unfolding Suc_rw foldl_append List.foldl.simps fst_conv snd_conv
    using Suc.hyps[unfolded echelon_form_of_upt_k_det_def Let_def snd_conv, simplified]
    by (metis prod.collapse snd_echelon_form_of_column_k_det_eq) 
qed

lemma snd_echelon_form_of_upt_k_det_eq:
  shows "(snd (echelon_form_of_upt_k_det (n, A) k bezout)) = echelon_form_of_upt_k A k bezout"
  unfolding echelon_form_of_upt_k_det_def echelon_form_of_upt_k_def Let_def fst_conv snd_conv
  unfolding snd_foldl_ef_det_eq by auto

lemma is_bezout_ext_trd_echelon_form_of_column_k:
  assumes ib:"is_bezout_ext bezout"
  shows "is_bezout_ext (snd (snd (echelon_form_of_column_k (A,i,bezout) k)))"
  unfolding echelon_form_of_column_k_def Let_def snd_conv fst_conv 
  by (auto simp add: ib)

lemma is_bezout_ext_snd_fold_echelon_form_of_column_k_det:
  assumes ib:"is_bezout_ext bezout"
  shows "is_bezout_ext (snd (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<k])))"
proof (induct k)
  case 0 
  show ?case by (auto simp add: ib)
next
  case (Suc k)
  have Suc_rw: "[0..<(Suc k)] = [0..<k] @ [k]" by simp
  let ?f="(foldl echelon_form_of_column_k (A, 0, bezout) [0..<k])"
  have fold_expand: "?f = (fst ?f, fst (snd ?f), (snd (snd ?f)))" by simp
  show ?case
    unfolding Suc_rw foldl_append List.foldl.simps fst_conv snd_conv    
    by (subst (1) fold_expand, rule is_bezout_ext_trd_echelon_form_of_column_k) (rule Suc.hyps)
qed

lemma det_echelon_form_of_upt_k_det:
  fixes A::"'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "fst (echelon_form_of_upt_k_det (1::'a,A) k bezout) *  det A 
  = det (snd (echelon_form_of_upt_k_det (1::'a,A) k bezout))"
proof (induct k)
  case 0 
  show ?case
    unfolding echelon_form_of_upt_k_det_def Let_def
    by (auto, rule det_echelon_form_of_column_k_det[OF ib], simp)
next
  case (Suc k)
  let ?f="(foldl echelon_form_of_column_k_det (1,A,0,bezout) [0..<Suc k])"
  have Suc_rw: "[0..<Suc (Suc k)] = [0..<(Suc k)] @ [Suc k]" by simp
  have fold_expand: "?f = (fst ?f, fst (snd ?f), fst (snd (snd ?f)), snd(snd(snd ?f)))" by simp
  show ?case unfolding echelon_form_of_upt_k_det_def Let_def 
    unfolding Suc_rw foldl_append List.foldl.simps fst_conv snd_conv
    by (subst (1 2) fold_expand, rule det_echelon_form_of_column_k_det,
      subst (1) snd_foldl_ef_det_eq, rule is_bezout_ext_snd_fold_echelon_form_of_column_k_det[OF ib])
  (rule Suc.hyps[unfolded echelon_form_of_upt_k_det_def Let_def fst_conv snd_conv])
qed

subsubsection{*Echelon form*}

lemma det_echelon_form_of_det:
  fixes A::"'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "(fst (echelon_form_of_det A bezout)) * det A = det (snd (echelon_form_of_det A bezout))"
  using det_echelon_form_of_upt_k_det ib unfolding echelon_form_of_det_def by simp


subsubsection{*Proving that the first component is a unit*}

lemma echelon_form_of_column_k_det_unit:
  fixes A::"'a::{bezout_domain_div}^'n::{mod_type}^'n::{mod_type}"
  assumes det: "is_unit (det_P)"
  shows "is_unit (fst (echelon_form_of_column_k_det (det_P,A,i,bezout) k))"
  unfolding is_unit_def echelon_form_of_column_k_det_def Let_def fst_conv snd_conv 
  using det is_unit_def by auto

lemma echelon_form_of_upt_k_det_unit:
  fixes A::"'a::{bezout_domain_div}^'n::{mod_type}^'n::{mod_type}"
  shows "is_unit (fst (echelon_form_of_upt_k_det (1::'a,A) k bezout))"
proof (induct k)
  case 0
  show ?case unfolding echelon_form_of_upt_k_det_def Let_def fst_conv
    using echelon_form_of_column_k_det_unit[OF is_unit_1] by auto
next
  case (Suc k)
  let ?f="(foldl echelon_form_of_column_k_det (1,A,0,bezout) [0..<Suc k])"
  have Suc_rw: "[0..<Suc (Suc k)] = [0..<(Suc k)] @ [Suc k]" by simp
  have fold_expand: "?f = (fst ?f, fst (snd ?f), fst (snd (snd ?f)), snd(snd(snd ?f)))"
    by simp
  show ?case
    unfolding echelon_form_of_upt_k_det_def Let_def 
    unfolding Suc_rw foldl_append List.foldl.simps fst_conv snd_conv 
    by (subst fold_expand, rule echelon_form_of_column_k_det_unit
    [OF Suc.hyps[unfolded echelon_form_of_upt_k_det_def Let_def fst_conv snd_conv]])
qed

lemma echelon_form_of_unit:
  fixes A::"'a::{bezout_domain_div}^'n::{mod_type}^'n::{mod_type}"
  shows "is_unit (fst (echelon_form_of_det A k))"
  unfolding echelon_form_of_det_def 
  by (rule echelon_form_of_upt_k_det_unit)

subsubsection{*Final lemmas*}

corollary det_echelon_form_of_det':
  fixes A::"'a::{bezout_domain_div}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "det A = ring_inv (fst (echelon_form_of_det A bezout)) 
  * det (snd (echelon_form_of_det A bezout))"
proof -
  have "(fst (echelon_form_of_det A bezout)) * det A = det (snd (echelon_form_of_det A bezout))"
    by (rule det_echelon_form_of_det[OF ib])
  thus "det A = ring_inv (fst (echelon_form_of_det A bezout)) 
    * det (snd (echelon_form_of_det A bezout))"
    by (auto simp add: echelon_form_of_unit dest: sym)
qed


lemma ef_echelon_form_of_det:
  fixes A::"'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "echelon_form (snd (echelon_form_of_det A bezout))"
  unfolding echelon_form_of_det_def
  unfolding snd_echelon_form_of_upt_k_det_eq
  unfolding echelon_form_of_def[symmetric]
  by (rule echelon_form_echelon_form_of[OF ib])

lemma det_echelon_form:
  fixes A::"'a::{bezout_domain}^'n::{mod_type}^'n::{mod_type}"
  assumes ef: "echelon_form A"
  shows "det A = setprod (\<lambda>i. A $ i $ i) (UNIV:: 'n set)"
  using det_upperdiagonal echelon_form_imp_upper_triagular[OF ef] 
  unfolding upper_triangular_def by blast

corollary det_echelon_form_of_det_setprod:
  fixes A::"'a::{bezout_domain_div}^'n::{mod_type}^'n::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "det A = ring_inv (fst (echelon_form_of_det A bezout)) 
  * setprod (\<lambda>i. snd (echelon_form_of_det A bezout) $ i $ i) (UNIV:: 'n set)"
  using det_echelon_form_of_det'[OF ib]
  unfolding det_echelon_form[OF ef_echelon_form_of_det[OF ib]] by auto

corollary det_echelon_form_of_euclidean[code]:
  fixes A::"'a::{euclidean_ring}^'n::{mod_type}^'n::{mod_type}"
  shows "det A = ring_inv (fst (echelon_form_of_det A euclid_ext2)) 
  * setprod (\<lambda>i. snd (echelon_form_of_det A euclid_ext2) $ i $ i) (UNIV:: 'n set)"
  by (rule det_echelon_form_of_det_setprod[OF is_bezout_ext_euclid_ext2])

end
