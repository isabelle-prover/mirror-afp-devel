(*  
    Title:      Echelon_Form_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Echelon Form refined to immutable arrays*}

theory Echelon_Form_IArrays
imports
  Echelon_Form
  "../Gauss_Jordan/Gauss_Jordan_IArrays"
begin

subsection{*The algorithm over immutable arrays*}

definition "bezout_matrix_iarrays A a b j bezout =
tabulate2 (nrows_iarray A) (nrows_iarray A) 
  (let bez = bezout (A !! a !! j) (A !! b !! j);
      p = fst bez; q = fst (snd bez); u=fst(snd(snd bez));
      v=fst(snd(snd(snd bez))); d = snd (snd (snd (snd bez)))
      in (%x y. if x = a \<and> y = a then p else if x = a \<and> y = b then q 
      else if x = b \<and> y = a then u else if x = b \<and> y = b 
      then v else if x = y then 1 else 0))"


primrec bezout_iterate_iarrays :: "'a::{bezout_ring} iarray iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)) \<Rightarrow> 'a iarray iarray"
where "bezout_iterate_iarrays A 0 i j bezout = A"
    | "bezout_iterate_iarrays A (Suc n) i j bezout = (if (Suc n) \<le> i then A else
    bezout_iterate_iarrays (bezout_matrix_iarrays A i (Suc n) j bezout **i A) n i j bezout)"



definition "echelon_form_of_column_k_iarrays A' k 
  = (let A = fst A'; i = fst (snd A'); bezout = snd (snd A')
        in if (vector_all_zero_from_index (i, (column_iarray k A))) \<or> i = (nrows_iarray A)
        then (A, i, bezout) else 
           if (vector_all_zero_from_index (i+1, (column_iarray k A))) then (A, i + 1, bezout) 
           else
            let n = least_non_zero_position_of_vector_from_index (column_iarray k A) i; 
            interchange_A = interchange_rows_iarray A i n
           in
           (bezout_iterate_iarrays (interchange_A) (nrows_iarray A - 1) i k bezout, i + 1, bezout))"


definition "echelon_form_of_upt_k_iarrays A k bezout 
  = fst (foldl echelon_form_of_column_k_iarrays (A,0,bezout) [0..<Suc k])"


definition "echelon_form_of_iarrays A bezout 
  = echelon_form_of_upt_k_iarrays A (ncols_iarray A - 1) bezout"

subsection{*Properties*}

subsubsection{*Bezout Matrix for immutable arrays*}

lemma matrix_to_iarray_bezout_matrix:
  shows "matrix_to_iarray (bezout_matrix A a b j bezout) 
  = bezout_matrix_iarrays (matrix_to_iarray A) (to_nat a) (to_nat b) (to_nat j) bezout"
  (is "?lhs = ?rhs")
proof -
  have n: "nrows_iarray (IArray (map (vec_to_iarray \<circ> op $ A \<circ> from_nat) [0..<CARD('b)])) 
    = CARD('b)" unfolding nrows_iarray_def vec_to_iarray_def o_def by auto
  have rw1:"(map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)] ! to_nat a !! to_nat j) = A $ a $ j"
    by (metis (erased, lifting) from_nat_to_nat_id length_upt minus_nat.diff_0 nth_map 
      nth_upt of_fun_nth plus_nat.add_0 to_nat_less_card)
  have rw2: "(map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)] ! to_nat b !! to_nat j) = (A $ b $ j)"
    by (metis (erased, lifting) from_nat_to_nat_id length_upt minus_nat.diff_0 nth_map 
      nth_upt of_fun_nth plus_nat.add_0 to_nat_less_card)
  have rw3: "IArray (map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)]) !! to_nat a !! to_nat j = A $ a $ j"
    by (metis IArray.sub_def list_of.simps rw1) 
  have rw4: "IArray (map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)]) !! to_nat b !! to_nat j = A $ b $ j"
    by (metis IArray.sub_def list_of.simps rw2) 
  show ?thesis
    unfolding matrix_to_iarray_def bezout_matrix_iarrays_def tabulate2_def 
    apply auto unfolding n apply (rule map_ext, auto simp add: bezout_matrix_def Let_def)
    unfolding o_def vec_to_iarray_def  Let_def 
    unfolding IArray.sub_def[symmetric] rw1 rw2 rw3 rw4
    unfolding IArray.of_fun_def iarray.inject
    apply (rule map_ext) unfolding vec_lambda_beta
  proof -
    fix x xa 
    assume x: "x<CARD('b)"
    def A'==" (if from_nat x = a \<and> from_nat xa = a then fst (bezout (A $ a $ j) (A $ b $ j))
             else if from_nat x = a \<and> from_nat xa = b then fst (snd (bezout (A $ a $ j) (A $ b $ j)))
                  else if from_nat x = b \<and> from_nat xa = a then fst (snd (snd (bezout (A $ a $ j) (A $ b $ j))))
                       else if from_nat x = b \<and> from_nat xa = b then fst (snd (snd (snd (bezout (A $ a $ j) (A $ b $ j)))))
                            else if (from_nat x::'b) = from_nat xa then 1 else 0) =
            (if x = to_nat a \<and> xa = to_nat a then fst (bezout (A $ a $ j) (A $ b $ j))
             else if x = to_nat a \<and> xa = to_nat b then fst (snd (bezout (A $ a $ j) (A $ b $ j)))
                  else if x = to_nat b \<and> xa = to_nat a then fst (snd (snd (bezout (A $ a $ j) (A $ b $ j))))
                       else if x = to_nat b \<and> xa = to_nat b then fst (snd (snd (snd (bezout (A $ a $ j) (A $ b $ j)))))
                            else if x = xa then 1 else 0)"
    have rw5: "(from_nat x = a) = (x = to_nat a)" 
      by (metis `x < CARD('b)` from_nat_to_nat_id to_nat_from_nat_id)
    show" xa \<in> set [0..<CARD('b)] \<longrightarrow> A'" 
    proof auto
      assume xa: "xa < CARD('b)"
      have rw6: "(from_nat x = b) = (x = to_nat b)" 
        by (metis x from_nat_to_nat_id to_nat_from_nat_id)
      have rw7: "(from_nat xa = b) = (xa = to_nat b)" 
        by (metis xa from_nat_to_nat_id to_nat_from_nat_id)
      have rw8: "((from_nat x::'b) = (from_nat xa::'b)) = (x=xa)"
        by (metis from_nat_not_eq x xa)
      have rw9: "(from_nat xa = a) = (xa = to_nat a)"
        by (metis from_nat_to_nat_id to_nat_from_nat_id xa)
      show "A'" unfolding A'_def rw5 unfolding rw6 unfolding rw7 unfolding rw8  unfolding rw9 
        by auto
    qed
  qed
qed


subsubsection{*Bezout Iterate for immutable arrays*}

lemma matrix_to_iarray_bezout_iterate:
  assumes n: "n<nrows A"
  shows "matrix_to_iarray (bezout_iterate A n i j bezout) 
  = bezout_iterate_iarrays (matrix_to_iarray A) n (to_nat i) (to_nat j) bezout"
  using n
proof (induct n arbitrary: A)
  case 0
  thus ?case unfolding bezout_iterate_iarrays.simps bezout_iterate.simps by simp
next
  case (Suc n)
  show ?case
  proof (cases "Suc n \<le> to_nat i")
    case True
    show ?thesis 
      unfolding bezout_iterate.simps bezout_iterate_iarrays.simps
      using True by auto
  next
    case False
    let ?B="(bezout_matrix_iarrays (matrix_to_iarray A) (to_nat i) (Suc n) (to_nat j) bezout 
      **i matrix_to_iarray A)"
    let ?B2="matrix_to_iarray (bezout_matrix A i (from_nat (Suc n)) j bezout ** A)"
    have "matrix_to_iarray (bezout_iterate A (Suc n) i j bezout) 
      = matrix_to_iarray (bezout_iterate (bezout_matrix A i (from_nat (Suc n)) j bezout ** A) n i j bezout)"
      unfolding bezout_iterate.simps using False by auto
    also have "... = bezout_iterate_iarrays ?B2 n (to_nat i) (to_nat j) bezout"
    proof (rule Suc.hyps) 
      show "n < nrows (bezout_matrix A i (from_nat (Suc n)) j bezout ** A)"
        using Suc.prems unfolding nrows_def by simp
    qed
    also have "... = bezout_iterate_iarrays ?B n (to_nat i) (to_nat j) bezout"
      unfolding matrix_to_iarray_matrix_matrix_mult
      unfolding matrix_to_iarray_bezout_matrix[of A i "from_nat (Suc n)" j bezout]
      unfolding to_nat_from_nat_id[OF Suc.prems[unfolded nrows_def]] ..
    also have "... = bezout_iterate_iarrays (matrix_to_iarray A) (Suc n) (to_nat i) (to_nat j) bezout"
      unfolding bezout_iterate_iarrays.simps using False by auto
    finally show ?thesis .
  qed
qed


lemma matrix_vector_all_zero_from_index2:
  fixes A::"'a::{zero}^'columns::{mod_type}^'rows::{mod_type}"
  shows "(\<forall>m>i. A $ m $ k = 0) = vector_all_zero_from_index ((to_nat i)+1, vec_to_iarray (column k A))"
proof (cases "to_nat i = nrows A - 1")
  case True
  have "(\<forall>m>i. A $ m $ k = 0) = True" 
    by (metis One_nat_def Suc_pred True not_less_eq nrows_def to_nat_0 to_nat_less_card to_nat_mono)
  also have "... = vector_all_zero_from_index ((to_nat i)+1, vec_to_iarray (column k A))"
    unfolding vector_all_zero_from_index_def Let_def
    unfolding vec_to_iarray_def column_def
    by (auto, metis True nrows_def One_nat_def Suc_pred not_le zero_less_card_finite)
  finally show ?thesis .
next
  case False
  have i_le: "i<i+1"
    by (metis False Suc_le' add_diff_cancel_right' nrows_def suc_not_zero)
  hence "(\<forall>m>i. A $ m $ k = 0) = (\<forall>m\<ge>i+1. A $ m $ k = 0)" using i_le le_Suc by auto 
  also have "... = vector_all_zero_from_index ((to_nat i)+1, vec_to_iarray (column k A))"
    unfolding matrix_vector_all_zero_from_index
    by (metis (mono_tags, hide_lams) from_nat_suc from_nat_to_nat_id i_le not_less0 
      to_nat_0 to_nat_from_nat_id to_nat_mono to_nat_plus_one_less_card)
  finally show ?thesis .
qed

subsubsection{*Echelon form of column k for immutable arrays*}

lemma matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "matrix_to_iarray (fst (echelon_form_of_column_k (A,i,bezout) k)) 
  = fst (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k)"
proof (cases "i<nrows A")
  case False
  have i_eq: "i=nrows A" by (metis False dual_order.le_imp_less_or_eq i)
  show "matrix_to_iarray (fst (echelon_form_of_column_k (A,i,bezout) k)) 
    = fst (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k)"
    unfolding echelon_form_of_column_k_def Let_def
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding matrix_to_iarray_nrows
    unfolding i_eq matrix_to_iarray_nrows by auto
next
  case True
  let ?interchange="(interchange_rows A (from_nat i) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))"
  have all_zero: "(\<forall>m\<ge>mod_type_class.from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = vector_all_zero_from_index (i, column_iarray k (matrix_to_iarray A))"
    unfolding matrix_vector_all_zero_from_index
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  have all_zero2: " (\<forall>m>from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = (vector_all_zero_from_index (i + 1, column_iarray k (matrix_to_iarray A)))"
    unfolding matrix_vector_all_zero_from_index2
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  have n: "(nrows_iarray (matrix_to_iarray A) - Suc 0) < nrows ?interchange"
    unfolding matrix_to_iarray_nrows[symmetric]
    unfolding nrows_def by simp
  show ?thesis
    using True
    unfolding echelon_form_of_column_k_def Let_def
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding matrix_to_iarray_nrows
    unfolding all_zero all_zero2 apply auto
    unfolding matrix_to_iarray_bezout_iterate[OF n]
    unfolding matrix_to_iarray_interchange_rows
    using vec_to_iarray_least_non_zero_position_of_vector_from_index'[of "from_nat i" "from_nat k" A]
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]]
    unfolding vec_to_iarray_column'[OF k] by auto
qed


lemma snd_matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "(snd (echelon_form_of_column_k (A,i,bezout) k)) 
  = (snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k))"
proof (cases "i<nrows A")
  case False
  have i_eq: "i=nrows A" by (metis False dual_order.le_imp_less_or_eq i)
  show "(snd (echelon_form_of_column_k (A,i,bezout) k)) 
    = snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k)"
    unfolding echelon_form_of_column_k_def Let_def
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding i_eq matrix_to_iarray_nrows by auto
next
  case True
  let ?interchange="(interchange_rows A (from_nat i) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))"
  have all_zero: "(\<forall>m\<ge>mod_type_class.from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = vector_all_zero_from_index (i, column_iarray k (matrix_to_iarray A))"
    unfolding matrix_vector_all_zero_from_index
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  have all_zero2: " (\<forall>m>from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = (vector_all_zero_from_index (i + 1, column_iarray k (matrix_to_iarray A)))"
    unfolding matrix_vector_all_zero_from_index2
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  show ?thesis
    using True
    unfolding echelon_form_of_column_k_def Let_def
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding all_zero all_zero2
    unfolding matrix_to_iarray_nrows by auto
qed

corollary fst_snd_matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "fst(snd (echelon_form_of_column_k (A,i,bezout) k)) 
  = fst (snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k))"
  using snd_matrix_to_iarray_echelon_form_of_column_k[OF assms] by simp

lemma trd_matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  shows "(snd (snd (echelon_form_of_column_k (A,i,bezout) k))) 
  = snd (snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k))"
  unfolding echelon_form_of_column_k_def Let_def
  unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv by auto

subsubsection{*Echelon form up to column k for immutable arrays*}

lemma snd_snd_foldl_echelon_form_of_column_k_iarrays:
  "snd (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<k])) 
  = bezout"
proof (induct k)
  case 0 thus ?case by auto
next
  case (Suc K)
  thus ?case
    by (auto simp add: echelon_form_of_column_k_iarrays_def Let_def  Suc.hyps)
qed

lemma foldl_echelon_form_column_k_eq:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  shows matrix_to_iarray_echelon_form_of_upt_k[code_unfold]: 
  "matrix_to_iarray (echelon_form_of_upt_k A k bezout) 
  = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) k bezout"
  and fst_foldl_ef_k_eq: "fst (snd (foldl echelon_form_of_column_k_iarrays 
  (matrix_to_iarray A,0,bezout) [0..<Suc k])) 
  = fst (snd (foldl echelon_form_of_column_k (A,0,bezout) [0..<Suc k]))"
  and fst_foldl_ef_k_less: 
  "fst (snd (foldl echelon_form_of_column_k (A,0, bezout) [0..<Suc k])) \<le> nrows A"
  using assms
proof (induct k)
  show "matrix_to_iarray (echelon_form_of_upt_k A 0 bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) 0 bezout"
    unfolding echelon_form_of_upt_k_def echelon_form_of_upt_k_iarrays_def
    by (simp, metis le0 matrix_to_iarray_echelon_form_of_column_k ncols_not_0 neq0_conv)
  show "fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc 0]))
    = fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc 0]))"
    by (simp, metis le0 ncols_not_0 not_gr0 snd_matrix_to_iarray_echelon_form_of_column_k)
  show "fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc 0])) \<le> nrows A"
    apply simp
    unfolding echelon_form_of_column_k_def Let_def snd_conv fst_conv 
    unfolding nrows_def by auto
next
  fix k
  assume "(k < ncols A \<Longrightarrow> matrix_to_iarray (echelon_form_of_upt_k A k bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) k bezout)"
    and  "(k < ncols A \<Longrightarrow>
    fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k])) =
    fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc k])))"
    and hyp3: "(k < ncols A \<Longrightarrow> fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc k])) \<le> nrows A)"
    and Suc_k_less_card: "Suc k < ncols A"
  hence hyp1: "matrix_to_iarray (echelon_form_of_upt_k A k bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) k bezout"
    and hyp2: "fst (snd (foldl echelon_form_of_column_k_iarrays 
    (matrix_to_iarray A, 0, bezout) [0..<Suc k])) 
    = fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc k]))"
    and hyp3: "fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc k])) \<le> nrows A"
    by auto          
  hence hyp1_unfolded: "matrix_to_iarray (fst (foldl echelon_form_of_column_k (A,0,bezout) [0..<Suc k])) 
    = fst (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A,0,bezout) [0..<Suc k])" 
    using hyp1 unfolding echelon_form_of_upt_k_def echelon_form_of_upt_k_iarrays_def by simp
  have upt_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by auto
  let ?f="foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k]"
  let ?f2="(foldl echelon_form_of_column_k (A,0,bezout) [0..<(Suc k)])"
  have fold_rw: "?f = (fst ?f, fst (snd ?f), snd (snd ?f))" by simp
  have fold_rw': "?f2 = (fst ?f2, fst (snd ?f2), snd (snd ?f2))" by simp
  have rw: "snd (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc k])) 
    = snd (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k]))" 
    unfolding snd_snd_foldl_echelon_form_of_column_k_iarrays
    unfolding snd_snd_foldl_echelon_form_of_column_k ..
  show "fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) 
    [0..<Suc (Suc k)])) = fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc (Suc k)]))"
    unfolding upt_rw foldl_append unfolding List.foldl.simps apply (subst fold_rw) 
    apply (subst fold_rw') unfolding hyp2 unfolding hyp1_unfolded[symmetric]
    unfolding rw
  proof (rule fst_snd_matrix_to_iarray_echelon_form_of_column_k
      [symmetric, of "Suc k" "fst ?f2"])
    show "Suc k < ncols (fst ?f2)" using Suc_k_less_card unfolding ncols_def .
    show "fst (snd ?f2) \<le> nrows (fst ?f2)" using hyp3 unfolding nrows_def .      
  qed
  show "matrix_to_iarray (echelon_form_of_upt_k A (Suc k) bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) (Suc k) bezout"
    unfolding echelon_form_of_upt_k_def echelon_form_of_upt_k_iarrays_def
      upt_rw foldl_append List.foldl.simps apply (subst fold_rw) apply (subst fold_rw') 
    unfolding hyp2 hyp1_unfolded[symmetric]
    unfolding rw
  proof (rule matrix_to_iarray_echelon_form_of_column_k)
    show "Suc k < ncols (fst ?f2)" using Suc_k_less_card unfolding ncols_def .
    show "fst (snd ?f2) \<le> nrows (fst ?f2)" using hyp3 unfolding nrows_def .
  qed
  show "fst (snd (foldl echelon_form_of_column_k (A, 0, bezout) [0..<Suc (Suc k)])) \<le> nrows A"
    unfolding upt_rw foldl_append unfolding List.foldl.simps apply (subst fold_rw')
    unfolding echelon_form_of_column_k_def Let_def
    using hyp3 le_antisym not_less_eq_eq unfolding nrows_def by fastforce
qed 

subsubsection{*Echelon form up to column k for immutable arrays*}

lemma matrix_to_iarray_echelon_form_of[code_unfold]:
  "matrix_to_iarray (echelon_form_of A bezout) 
    = echelon_form_of_iarrays (matrix_to_iarray A) bezout"
  unfolding echelon_form_of_def echelon_form_of_iarrays_def
  by (metis (poly_guards_query) One_nat_def diff_less lessI matrix_to_iarray_echelon_form_of_upt_k 
    ncols_def ncols_eq_card_columns zero_less_card_finite)

end

