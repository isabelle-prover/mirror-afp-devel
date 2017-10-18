(* Author: Thiemann *)
section \<open>Combining Spectral Radius Theory with Perron Frobenius theorem\<close>

theory Spectral_Radius_Theory_2
imports 
  Perron_Frobenius_General
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
  Matrix.Utility
begin

hide_const(open) Coset.order

lemma order_of_real_char_poly: assumes A: "A \<in> carrier_mat n n" 
  shows "order (complex_of_real x) (char_poly (of_real_hom.mat_hom A)) = order x (char_poly A)" 
proof -
  let ?c = complex_of_real
  interpret c: field_hom ?c ..
  interpret p: map_poly_inj_idom_divide_hom ?c ..
  show ?thesis unfolding p.order_hom[symmetric] of_real_hom.char_poly_hom[OF A] ..
qed

lemma order_of_real_char_poly_1: assumes A: "A \<in> carrier_mat n n" 
  shows "order (1 :: complex) (char_poly (of_real_hom.mat_hom A)) = order 1 (char_poly A)"
  "order (- 1 :: complex) (char_poly (of_real_hom.mat_hom A)) = order (- 1) (char_poly A)"
  using order_of_real_char_poly[OF A, of 1] order_of_real_char_poly[OF A, of "- 1"] by auto

lemma jordan_matrix_append: "jordan_matrix (as @ bs) = 
  four_block_mat (jordan_matrix as) (0\<^sub>m (sum_list (map fst as)) (sum_list (map fst bs)))
     (0\<^sub>m (sum_list (map fst bs)) (sum_list (map fst as))) (jordan_matrix bs)"
proof (induct as)
  case (Cons a as)
  obtain n ev where a: "a = (n,ev)" by force
  let ?JB = "jordan_block n ev" 
  let ?JM = "jordan_matrix (as @ bs)" 
  let ?JA = "jordan_matrix as" 
  have id: "jordan_matrix ((a # as) @ bs) = 
    four_block_mat ?JB (0\<^sub>m (dim_row ?JB) (dim_col ?JM))
     (0\<^sub>m (dim_row ?JM) (dim_col ?JB) ) ?JM" 
    by (simp add: a jordan_matrix_Cons)
  have id': "jordan_matrix (a # as) = four_block_mat ?JB (0\<^sub>m (dim_row ?JB) (dim_col ?JA))
     (0\<^sub>m (dim_row ?JA) (dim_col ?JB)) ?JA" 
    by (simp add: a jordan_matrix_Cons)
  show ?case unfolding id Cons
    using assoc_four_block_mat[of ?JB ?JA "jordan_matrix bs"]
    by (smt id' jordan_matrix_dim(1) jordan_matrix_dim(2))
qed auto


lemma jordan_nf_four_block_mat: assumes A: "A \<in> carrier_mat na na"
  and B: "B \<in> carrier_mat nb nb" 
  and jnfA: "jordan_nf A as"
  and jnfB: "jordan_nf B bs" 
shows "jordan_nf (four_block_mat A (0\<^sub>m na nb) (0\<^sub>m nb na) B) (as @ bs)" 
proof -
  from jnfA[unfolded jordan_nf_def] 
  have simA: "similar_mat A (jordan_matrix as)" .
  from jnfB[unfolded jordan_nf_def] 
  have simB: "similar_mat B (jordan_matrix bs)" .
  from similar_matD[OF simA] A 
  have "jordan_matrix as \<in> carrier_mat na na" by auto
  with jordan_matrix_carrier[of as] have na: "na = sum_list (map fst as)" by auto
  from similar_matD[OF simB] B
  have "jordan_matrix bs \<in> carrier_mat nb nb" by auto
  with jordan_matrix_carrier[of bs] have nb: "nb = sum_list (map fst bs)" by auto
  from similar_mat_four_block_0_0[OF simA simB A B]
  have "similar_mat (four_block_mat A (0\<^sub>m na nb) (0\<^sub>m nb na) B)
   (four_block_mat (jordan_matrix as) (0\<^sub>m na nb) (0\<^sub>m nb na) (jordan_matrix bs))" .
  also have "four_block_mat (jordan_matrix as) (0\<^sub>m na nb) (0\<^sub>m nb na) (jordan_matrix bs)
    = jordan_matrix (as @ bs)" unfolding jordan_matrix_append na nb ..
  finally show ?thesis unfolding jordan_nf_def .
qed

lemma nonneg_matD: assumes "nonneg_mat A" 
  and "i < dim_row A" and "j < dim_col A"
shows "A $$ (i,j) \<ge> 0" 
  using assms unfolding nonneg_mat_def elements_mat by auto

lemma (in comm_ring_hom) similar_mat_wit_hom: assumes 
  "similar_mat_wit A B C D"
shows "similar_mat_wit (mat\<^sub>h A) (mat\<^sub>h B) (mat\<^sub>h C) (mat\<^sub>h D)" 
proof -
  obtain n where n: "n = dim_row A" by auto
  note * = similar_mat_witD[OF n assms] 
  from * have [simp]: "dim_row C = n" by auto
  note C = *(6) note D = *(7)
  note id = mat_hom_mult[OF C D] mat_hom_mult[OF D C]
  note ** = *(1-3)[THEN arg_cong[of _ _ "mat\<^sub>h"], unfolded id]
  note mult = mult_carrier_mat[of _ n n]
  note hom_mult = mat_hom_mult[of _ n n _ n]
  show ?thesis unfolding similar_mat_wit_def Let_def unfolding **(3) using **(1,2)
    by (auto simp: n[symmetric] hom_mult simp: *(4-) mult)
qed

lemma (in comm_ring_hom) similar_mat_hom: 
  "similar_mat A B \<Longrightarrow> similar_mat (mat\<^sub>h A) (mat\<^sub>h B)" 
  using similar_mat_wit_hom[of A B C D for C D]
  by (smt similar_mat_def)


lemma dim_mat_of_rows_list[simp]: "dim_row (mat_of_rows_list n xs) = length xs" 
  "dim_col (mat_of_rows_list n xs) = n" 
  "mat_of_rows_list n xs \<in> carrier_mat (length xs) n"
  unfolding mat_of_rows_list_def by auto

lemma eq_mat_dim_4: assumes "A \<in> carrier_mat 4 4" 
  and "B \<in> carrier_mat 4 4" 
  and "\<And> i j. i \<in> {0,1,2,3} \<Longrightarrow> j \<in> {0,1,2,3} \<Longrightarrow> A $$ (i,j) = B $$ (i,j)" 
shows "A = B" 
proof -
  {
    fix i :: nat
    consider "i = 0" | "i = 1" | "i = 2" | "i = 3" | "i \<ge> 4" by linarith
  } note cases_4 = this
  show ?thesis by (rule eq_matI, rename_tac i j, 
      case_tac i rule: cases_4; case_tac j rule: cases_4, insert assms, auto)
qed

lemma eq_mat_dim_2: assumes "A \<in> carrier_mat 2 2" 
  and "B \<in> carrier_mat 2 2" 
  and "\<And> i j. i \<in> {0,1} \<Longrightarrow> j \<in> {0,1} \<Longrightarrow> A $$ (i,j) = B $$ (i,j)" 
shows "A = B" 
proof -
  {
    fix i :: nat
    consider "i = 0" | "i = 1" | "i \<ge> 2" by linarith
  } note cases_2 = this
  show ?thesis by (rule eq_matI, rename_tac i j, 
      case_tac i rule: cases_2; case_tac j rule: cases_2, insert assms, auto)
qed

lemma jnf_special_shape_dim_2: assumes a: "a \<noteq> (0 :: 'a :: field_char_0)" 
  shows "similar_mat_wit (mat_of_rows_list 2 [[0,a],[1/a,0]]) (mat_of_rows_list 2 [[-1,0],[0,1]])
    (mat_of_rows_list 2 [[-a,a],[1,1]]) (mat_of_rows_list 2 [[-1/2/a,1/2], [1/2/a,1/2]])" 
  unfolding similar_mat_wit_def Let_def using a
  by (auto simp: mat_of_rows_list_def scalar_prod_def intro!: eq_mat_dim_2)

lemma det_dim_1: assumes A: "A \<in> carrier_mat n n" 
  and n: "n = 1"
shows "Determinant.det A = A $$ (0,0)" 
  by (subst laplace_expansion_column[OF A[unfolded n], of 0], insert A n, 
    auto simp: cofactor_def mat_delete_def)

lemma det_dim_2: assumes A: "A \<in> carrier_mat n n" 
  and n: "n = 2"
shows "Determinant.det A = A $$ (0,0) * A $$ (1,1) - A $$ (0,1) * A $$ (1,0)" 
proof -
  have set: "(\<Sum>i<(2 :: nat). f i) = f 0 + f 1" for f
    by (subst sum.cong[of _ "{0,1}" f f], auto)
  show ?thesis
    apply (subst laplace_expansion_column[OF A[unfolded n], of 0], insert A n, 
      auto simp: cofactor_def mat_delete_def set)
    apply (subst (1 2) det_dim_1, auto)
    done
qed

lemma jordan_nf_dim_2: fixes A :: "'a :: field mat" 
  assumes A: "A = mat_of_rows_list 2 [[a,b], [0,a]]" 
  shows "b = 0 \<Longrightarrow> jordan_nf A [(1,a),(1,a)]" 
        "b \<noteq> 0 \<Longrightarrow> jordan_nf A [(2,a)]" 
proof -
  {
    assume b: "b = 0" 
    have A: "A = jordan_matrix [(1,a),(1,a)]" 
      unfolding A b 
      by (rule eq_matI, auto simp add: jordan_matrix_def mat_of_rows_list_def)
    show "jordan_nf A [(1,a),(1,a)]" unfolding jordan_nf_def A
      by (rule similar_mat_refl[of _ 2], auto)
  }
  {
    assume b: "b \<noteq> 0" 
    have id: "mult_col_div_row b 0 A = mat_of_rows_list 2 [[a,1],[0,a]]" (is "_ = ?A")
      unfolding mult_col_div_row_def A 
      by (rule eq_matI, auto simp add: mat_multrow_gen_def mat_of_rows_list_def b)
    have "A \<in> carrier_mat 2 2" unfolding A by auto
    from mult_col_div_row_similar[OF this _ b, of 0, unfolded id]
    have sim: "similar_mat ?A A" by auto
    have A: "?A = jordan_matrix [(2,a)]" 
      by (rule eq_matI, rename_tac i j, (case_tac i; case_tac j), 
      auto simp add: jordan_matrix_def jordan_block_def mat_of_rows_list_def)
    from similar_mat_sym[OF sim]
    show "jordan_nf A [(2,a)]" unfolding jordan_nf_def A .
  }
qed

lemma char_poly_root_unity_2: fixes A :: "real mat"
  assumes A: "A \<in> carrier_mat 2 2"
  and cp: "char_poly (map_mat complex_of_real A) = root_unity 2" (is "char_poly ?A = ?rt2")
  and nonneg: "nonneg_mat A" 
shows "A $$ (0,0) = 0" "A $$ (1,1) = 0" "A $$ (1,0) * A $$ (0,1) = 1"
proof -
  let ?c = "complex_of_real" 
  interpret c: field_hom ?c ..
  interpret p: map_poly_inj_idom_divide_hom ?c ..
  let ?cp = "map_poly ?c" 
  from A have dim: "dim_row A = 2" "dim_col A = 2" by auto
  have "?cp (char_poly A) = char_poly ?A" unfolding of_real_hom.char_poly_hom[OF A] ..
  also have "\<dots> = ?cp (root_unity 2)" unfolding cp by code_simp
  finally have cp: "char_poly A = root_unity 2" by simp
  also have "\<dots> = [: -1, 0, 1:]" by code_simp
  finally have cp: "char_poly A = [: -1, 0, 1:]" .
  have cp': "char_poly A = [:A $$ (1, 1) * A $$ (0, 0) - A $$ (1, 0) * A $$ (0, 1), 
    - A $$ (1, 1) - A $$ (0, 0), 1:]" 
    unfolding char_poly_def char_poly_matrix_def 
    by (subst det_dim_2, insert A, auto)
  from arg_cong[OF cp[unfolded cp'], of "\<lambda> f. coeff f 1"]
  have sum: "A $$ (1, 1) + A $$ (0, 0) = 0" by (simp add: root_unity_def)
  from nonneg[unfolded nonneg_mat_def] elements_matI[OF A _ _ refl, of 0 0] 
    elements_matI[OF A _ _ refl, of 1 1]
  have "A $$ (0,0) \<ge> 0" "A $$ (1,1) \<ge> 0" by auto
  with sum show 0: "A $$ (0,0) = 0" "A $$ (1,1) = 0" by auto
  from cp'[unfolded 0 cp] show "A $$ (1,0) * A $$ (0,1) = 1" by simp
qed

lemma order_root_unity_2:
  assumes ord: "order (1 :: 'a :: field_char_0) p = 1" "order (-1) p = 1" 
  and deg: "degree p = 2" 
  and mon: "monic p" 
shows "p = root_unity 2" 
proof -
  from order_1[of 1 p, unfolded ord] obtain q 
      where p: "p = [:-1,1:] * q" (is "_ = ?one * _") unfolding dvd_def by auto
  have "order (-1) p = order (-1) ?one + order (-1) q" using mon 
    unfolding p by (subst order_mult, auto)
  also have "order (-1) ?one = 0" using order_root[of ?one "-1"] by simp
  finally have ord: "order (-1) q = 1" using ord by auto
  from mon p have q0: "q \<noteq> 0" by auto
  have dp: "degree p = 1 + degree q"
    unfolding p by (subst degree_mult_eq, insert q0, auto)  
  from order_1[of "-1" q, unfolded ord] obtain r where q: "q = [:1,1:] * r" (is "_ = ?mone * _") 
    unfolding dvd_def by auto
  from q0 have r0: "r \<noteq> 0" unfolding q by auto
  from r0 have dq: "degree q = 1 + degree r" unfolding q by (subst degree_mult_eq, auto)
  from deg[unfolded dp dq] have "degree r = 0" by auto
  from degree0_coeffs[OF this] obtain r0 where r: "r = [:r0:]" by auto
  from mon[unfolded p q r] have r0: "r0 = 1" by (auto split: if_splits)
  have 2: "2 = Suc (Suc 0)" by simp
  show "p = root_unity 2" unfolding p q r r0 root_unity_def by (auto simp add: 2 monom_Suc)
qed

lemma monic_root_unity[simp]: 
  "k \<noteq> 0 \<Longrightarrow> monic (root_unity k)" unfolding degree_root_unity[of k] 
  by (auto simp: root_unity_def) 

lemma monic_prod_root_unity[simp]: 
  "0 \<notin> set ks \<Longrightarrow> monic (prod_root_unity ks)" unfolding prod_root_unity_def
  by (rule monic_prod_list, auto simp del: degree_root_unity intro!: monic_root_unity, 
    rename_tac x, case_tac "x = 0", auto)

context field_hom
begin
lemma hom_swaprows: "i < dim_row A \<Longrightarrow> j < dim_row A \<Longrightarrow> 
  swaprows i j (mat\<^sub>h A) = mat\<^sub>h (swaprows i j A)" 
  unfolding mat_swaprows_def by (rule eq_matI, auto)

lemma hom_gauss_jordan_main: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc2 \<Longrightarrow>
  gauss_jordan_main (mat\<^sub>h A) (mat\<^sub>h B) i j = 
  map_prod mat\<^sub>h mat\<^sub>h (gauss_jordan_main A B i j)"
proof (induct A B i j rule: gauss_jordan_main.induct)
  case (1 A B i j)
  note IH = 1(1-4)
  note AB = 1(5-6)
  from AB have dim: "dim_row A = nr" "dim_col A = nc" by auto
  let ?h = "mat\<^sub>h" 
  let ?hp = "map_prod mat\<^sub>h mat\<^sub>h" 
  show ?case unfolding gauss_jordan_main.simps[of A B i j] gauss_jordan_main.simps[of "?h A" _ i j]
    index_map_mat Let_def if_distrib[of ?hp] dim
  proof (rule if_cong[OF refl], goal_cases)
    case 1
    note IH = IH[OF dim[symmetric] 1 refl]
    from 1 have ij: "i < nr" "j < nc" by auto
    hence hij: "(?h A) $$ (i,j) = hom (A $$ (i,j))" using AB by auto
    define ixs where "ixs = concat (map (\<lambda>i'. if A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<nr])" 
    have id: "map (\<lambda>i'. if mat\<^sub>h A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<nr] = 
       map (\<lambda>i'. if A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<nr]" 
      by (rule map_cong[OF refl], insert ij AB, auto)
    show ?case unfolding hij hom_0_iff hom_1_iff id ixs_def[symmetric]
    proof (rule if_cong[OF refl _ if_cong[OF refl]], goal_cases)
      case 1
      note IH = IH(1,2)[OF 1, folded ixs_def]
      show ?case
      proof (cases ixs)
        case Nil
        show ?thesis unfolding Nil using IH(1)[OF Nil AB] by auto
      next
        case (Cons I ix)
        hence "I \<in> set ixs" by auto      
        hence I: "I < nr" unfolding ixs_def by auto
        from AB have swap: "swaprows i I A \<in> carrier_mat nr nc" "swaprows i I B \<in> carrier_mat nr nc2" 
          by auto
        show ?thesis unfolding Cons list.simps IH(2)[OF Cons swap,symmetric] using AB ij I
          by (auto simp: hom_swaprows)
      qed
    next
      case 2
      from AB have elim: "eliminate_entries (\<lambda>i. A $$ (i, j)) A i j \<in> carrier_mat nr nc" 
          "eliminate_entries (\<lambda>i. A $$ (i, j)) B i j \<in> carrier_mat nr nc2" 
        unfolding eliminate_entries_gen_def by auto
      show ?case unfolding IH(3)[OF 2 refl elim, symmetric] 
        by (rule arg_cong2[of _ _ _ _ "\<lambda> x y. gauss_jordan_main x y (Suc i) (Suc j)"]; 
        intro eq_matI, insert AB ij, auto simp: eliminate_entries_gen_def hom_minus hom_mult)
    next
      case 3
      from AB have mult: "multrow i (inverse (A $$ (i, j))) A \<in> carrier_mat nr nc" 
        "multrow i (inverse (A $$ (i, j))) B \<in> carrier_mat nr nc2" by auto
      show ?case unfolding IH(4)[OF 3 refl mult, symmetric]
        by (rule arg_cong2[of _ _ _ _ "\<lambda> x y. gauss_jordan_main x y i j"]; 
        intro eq_matI, insert AB ij, auto simp: hom_inverse hom_mult)
    qed
  qed auto
qed

lemma hom_gauss_jordan: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc2 \<Longrightarrow>
  gauss_jordan (mat\<^sub>h A) (mat\<^sub>h B) = map_prod mat\<^sub>h mat\<^sub>h (gauss_jordan A B)"
  unfolding gauss_jordan_def using hom_gauss_jordan_main by blast

lemma hom_gauss_jordan_single[simp]: "gauss_jordan_single (mat\<^sub>h A) = mat\<^sub>h (gauss_jordan_single A)"
proof -
  let ?nr = "dim_row A" let ?nc = "dim_col A" 
  have 0: "0\<^sub>m ?nr 0 \<in> carrier_mat ?nr 0" by auto  
  have dim: "dim_row (mat\<^sub>h A) = ?nr" by auto
  have hom0: "mat\<^sub>h (0\<^sub>m ?nr 0) = 0\<^sub>m ?nr 0" by auto
  have A: "A \<in> carrier_mat ?nr ?nc" by auto
  from hom_gauss_jordan[OF A 0] A
  show ?thesis unfolding gauss_jordan_single_def dim hom0 by (metis fst_map_prod)
qed

lemma hom_pivot_positions_main_gen: assumes A: "A \<in> carrier_mat nr nc" 
  shows "pivot_positions_main_gen 0 (mat\<^sub>h A) nr nc i j = pivot_positions_main_gen 0 A nr nc i j" 
proof (induct rule: pivot_positions_main_gen.induct[of nr nc A 0])
  case (1 i j)
  note IH = this
  show ?case unfolding pivot_positions_main_gen.simps[of _ _ nr nc i j]
  proof (rule if_cong[OF refl if_cong[OF refl _ refl] refl], goal_cases)
    case 1    
    with A have id: "(mat\<^sub>h A) $$ (i,j) = hom (A $$ (i,j))" by simp
    note IH = IH[OF 1]
    show ?case unfolding id hom_0_iff
      by (rule if_cong[OF refl IH(1)], force, subst IH(2), auto)
  qed
qed

lemma hom_pivot_positions[simp]: "pivot_positions (mat\<^sub>h A) = pivot_positions A" 
  unfolding pivot_positions_def by (subst hom_pivot_positions_main_gen, auto)

lemma hom_kernel_dim[simp]: "kernel_dim (mat\<^sub>h A) = kernel_dim A" 
  unfolding kernel_dim_code by simp

lemma hom_char_matrix: assumes A: "A \<in> carrier_mat n n"
  shows "char_matrix (mat\<^sub>h A) (hom x) = mat\<^sub>h (char_matrix A x)" 
  unfolding char_matrix_def
  by (rule eq_matI, insert A, auto simp: hom_minus) 

lemma hom_dim_gen_eigenspace: assumes A: "A \<in> carrier_mat n n"
  shows "dim_gen_eigenspace (mat\<^sub>h A) (hom x) = dim_gen_eigenspace A x" 
proof (intro ext)
  fix k
  show "dim_gen_eigenspace (mat\<^sub>h A) (hom x) k = dim_gen_eigenspace A x k"
    unfolding dim_gen_eigenspace_def hom_char_matrix[OF A]
      mat_hom_pow[OF char_matrix_closed[OF A], symmetric] by simp
qed

lemma hom_compute_set_of_jordan_blocks: assumes A: "A \<in> carrier_mat n n"
  shows "compute_set_of_jordan_blocks (mat\<^sub>h A) (hom x)
  = map (map_prod id hom) (compute_set_of_jordan_blocks A x)" 
proof -
  interpret b: map_poly_inj_idom_divide_hom hom ..
  obtain k as cards xs where *: "order x (char_poly A) = k" 
    "map (dim_gen_eigenspace A x) [0..<Suc (Suc k)] = as" 
    "map (\<lambda>k. (k, 2 * as ! k - as ! (k - 1) - as ! Suc k)) [1..<Suc k] = cards" 
    "[(k, c)\<leftarrow>cards . c \<noteq> 0] = xs" by auto
  show ?thesis unfolding compute_set_of_jordan_blocks_def hom_dim_gen_eigenspace[OF A]
    char_poly_hom[OF A] b.order_hom Let_def * by (induct xs, auto)
qed
end

lemma compute_set_of_jordan_blocks_1: 
  assumes A: "A \<in> carrier_mat n n" 
  shows "fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) 1)
    = fst ` set (compute_set_of_jordan_blocks A 1)" 
  using arg_cong[OF of_real_hom.hom_compute_set_of_jordan_blocks[OF A, of 1], 
      of "\<lambda> x. fst ` set x"] by force

lemma compute_set_of_jordan_blocks_minus_1: 
  assumes A: "A \<in> carrier_mat n n" 
  shows "fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) (-1))
    = fst ` set (compute_set_of_jordan_blocks A (-1))" 
  using arg_cong[OF of_real_hom.hom_compute_set_of_jordan_blocks[OF A, of "-1"], 
      of "\<lambda> x. fst ` set x"] by force

text \<open>This criterion is tight!\<close>

lemma jnf_complexity_generic: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x \<le> 1" 
  and 1: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x = 1 \<Longrightarrow> 
    order x (char_poly A) > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A x). bsize \<le> d + 1)" 
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)" 
proof - 
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" 
    and lenn: "length as = n" by auto 
  from jordan_nf_exists[OF A cA] obtain n_xs where jnf: "jordan_nf A n_xs" ..
  have dd: "x ^ d = x ^((d + 1) - 1)" for x by simp
  show ?thesis unfolding dd
  proof (rule jordan_nf_matrix_poly_bound[OF A _ _ jnf])
    fix n x
    assume nx: "(n,x) \<in> set n_xs" 
    from jordan_nf_block_size_order_bound[OF jnf nx] 
    have no: "n \<le> order x (char_poly A)" by auto
    {
      assume "0 < n" 
      with no have "order x (char_poly A) \<noteq> 0" by auto
      hence rt: "poly (char_poly A) x = 0" unfolding order_root by auto
      from sr[OF this] show "cmod x \<le> 1" .
      note rt
    } note sr = this
    assume c1: "cmod x = 1" 
    show "n \<le> d + 1" 
    proof (rule ccontr)
      assume "\<not> n \<le> d + 1" 
      hence lt: "n > d + 1" by auto
      with sr have rt: "poly (char_poly A) x = 0" by auto
      from lt no have ord: "d + 1 < order x (char_poly A)" by auto
      from 1[OF rt c1 ord, unfolded compute_set_of_jordan_blocks[OF jnf]] nx lt
      show False by force
    qed
  qed
qed

lemma norm_bound_complex_to_real: fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat n n" 
    and bnd: "\<exists>c1 c2. \<forall>k. norm_bound ((map_mat complex_of_real A) ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)"
proof -
  let ?B = "map_mat complex_of_real A" 
  from bnd obtain c1 c2 where nb: "\<And> k. norm_bound (?B ^\<^sub>m k) (c1 + c2 * real k ^ d)" by auto
  show ?thesis
  proof (rule exI[of _ c1], rule exI[of _ c2], intro allI impI)
    fix k a
    assume "a \<in> elements_mat (A ^\<^sub>m k)"
    with pow_carrier_mat[OF A] obtain i j where a: "a = (A ^\<^sub>m k) $$ (i,j)" and ij: "i < n" "j < n"
      unfolding elements_mat by force
    from ij nb[of k] A have "norm ((?B ^\<^sub>m k) $$ (i,j)) \<le> c1 + c2 * real k ^ d"
      unfolding norm_bound_def by auto
    also have "(?B ^\<^sub>m k) $$ (i,j) = of_real a"
      unfolding of_real_hom.mat_hom_pow[OF A, symmetric] a using ij A by auto
    also have "norm (complex_of_real a) = abs a" by auto
    finally show "abs a \<le> (c1 + c2 * real k ^ d)" .
  qed
qed

text \<open>Now we will develop a tight criterion for non-negative real matrices.\<close>

lemma sum_list_approx: assumes kn: "k \<ge> (n :: nat)" and n: "n \<noteq> 0" 
  shows "0 \<notin> set ks \<Longrightarrow> n * length (filter (op dvd k) ks) \<le> sum_list ks" 
proof (induct ks)
  case (Cons x ks)
  {
    assume "k dvd x" 
    with Cons(2-) n have "x \<ge> k" by (simp add: dvd_imp_le)
    with kn have "x \<ge> n" by auto
  }
  with Cons show ?case using kn n by auto
qed auto

context 
  fixes A :: "real mat" and n :: nat and ks :: "nat list"
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  and ks: "ks = fst (decompose_prod_root_unity (char_poly A))"
begin

  
lemma jnf_perron_frobenius_generic:  
  assumes main: "\<And> x k. 
     sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>     (* length ks = multiplicity of root 1, cheap test *)
     0 \<notin> set ks \<Longrightarrow> k \<in> {1 .. max_list ks} \<Longrightarrow>  
     length [k'\<leftarrow>ks . k dvd k'] > d + 1 \<Longrightarrow> 
        (* length [k'\<leftarrow>ks . k dvd k'] is the multiplicity of x when x^k = 1 and k is minimal *)
     primitive_root_unity k x \<Longrightarrow> (* consider primitive root of unity *)
     order x (char_poly (map_mat complex_of_real A)) = length [k'\<leftarrow>ks. k dvd k'] \<Longrightarrow>
     (\<And> x. cmod x = 1 \<Longrightarrow> order x (char_poly (map_mat complex_of_real A)) = length [k\<leftarrow>ks . x ^ k = 1]) \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d + 1)" 
       (* eventually compute Jordan-blocks *)
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (cases "n = 0")
  case n: False
  let ?cA = "map_mat complex_of_real A" 
  from A have cA: "?cA \<in> carrier_mat n n" by auto
  from ks obtain f where dec: "decompose_prod_root_unity (char_poly A) = (ks, f)" (is "?t = _")
    by (cases ?t, auto)
  note pf = perron_frobenius_for_complexity_jnf[OF A n nonneg sr dec, simplified]
  show ?thesis
  proof (rule norm_bound_complex_to_real[OF A], rule jnf_complexity_generic[OF cA])
    fix x
    from pf(1) have ks0: "0 \<notin> set ks" by auto
    let ?p = "prod_root_unity ks :: real poly" 
    have "n = degree (char_poly A)" and A0: "char_poly A \<noteq> 0" 
      using degree_monic_char_poly[OF A] by auto
    have "n = degree (char_poly A)" by fact 
    also have "\<dots> = degree ?p + degree f"
      using A0 unfolding pf(2) by (subst degree_mult_eq, auto)
    also have "\<dots> \<ge> degree ?p" by auto
    also have "degree ?p = sum_list ks" using degree_prod_root_unity[OF ks0] by auto
    finally have sum_ks: "sum_list ks \<le> n" .
    assume rt: "poly (char_poly ?cA) x = 0" 
    from pf(4)[OF this] show "cmod x \<le> 1" .
    assume 1: "cmod x = 1" and d: "d + 1 < order x (char_poly ?cA)" 
    from pf(7)[OF 1 rt] ks0 obtain K where K: "K \<in> set ks" "K \<noteq> 0" "x ^ K = 1" by auto
    from primitive_root_unity_exists[OF K(2-)] obtain k where kK: "k \<le> K" and 
      k: "primitive_root_unity k x" by auto
    from primitive_root_unity_dvd[OF k]
    have min: "x ^ n = 1 \<longleftrightarrow> k dvd n" for n .
    from primitive_root_unityD[OF k] have k0: "k \<noteq> 0" and rt: "x ^ k = 1" by auto
    from order.trans[OF kK max_list[OF K(1)]] k0 have k_mem: "k \<in> {1 .. max_list ks}" by auto
    have "order x (char_poly ?cA) = length [k\<leftarrow>ks . x ^ k = 1]" using pf(6)[OF 1] by simp
    also have "[k\<leftarrow>ks. x ^ k = 1] = filter (\<lambda> k'. k dvd k') [k'\<leftarrow>ks. x ^ k' = 1]"
      by (rule sym, unfold filter_id_conv, insert min, auto)
    also have "\<dots> = filter (\<lambda> k'. x ^ k' = 1) [k'\<leftarrow>ks. k dvd k']" unfolding filter_filter 
      by (rule filter_cong, auto)
    also have "\<dots> = [k'\<leftarrow>ks. k dvd k']" 
      by (unfold filter_id_conv, insert min, auto)
    finally have order_length: "order x (char_poly ?cA) = length [k'\<leftarrow>ks. k dvd k']" .
    from d[unfolded this] have len: "d + 1 < length (filter (op dvd k) ks)" .
    also have "\<dots> \<le> length ks" by simp
    finally have len3: "d + 1 < length ks" by auto
    from main[OF sum_ks len3 ks0 k_mem len k order_length, folded order_length, OF pf(6)]      
    show "\<forall>bsize\<in>fst ` set (compute_set_of_jordan_blocks ?cA x). bsize \<le> d + 1" by auto
  qed
next
  case 0: True
  from A[unfolded this] 
  have A: "A ^\<^sub>m k = 1\<^sub>m 0" for k using A by (intro eq_matI, auto)
  show ?thesis unfolding A by (auto simp: elements_mat_def) 
qed  

lemma jnf_perron_frobenius_only_block_1:  
  assumes size: "n \<le> 2 * (d + 2) - 1" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A 1). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  show ?case
  proof (cases "k = 1")
    case True
    from 1 root_1 show ?thesis unfolding True primitive_root_unity_explicit
      using compute_set_of_jordan_blocks_1[OF A] True 
      by simp
  next
    case False
    with 1 have k: "k \<ge> 2" by auto
    from 1(5) have "2 * (d + 2) \<le> 2 * length (filter (op dvd k) ks)" by auto
    also have "\<dots> \<le> n" using sum_list_approx[OF k _ 1(3)] 1(1) by auto
    finally have "2 * (d + 2) \<le> n" by auto
    with size have False by auto
    thus ?thesis by simp
  qed
qed
    
lemma jnf_perron_frobenius_only_blocks_1_and_minus_1:  
  assumes size: "n \<le> 3 * (d + 2) - 1" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A 1). 
       bsize \<le> d + 1)" 
  and root_2: "  
     length [k'\<leftarrow>ks . 2 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A (-1)). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  from 1(4)
  consider (k1) "k = 1" | (k2) "k = 2" | (k) "k \<ge> 3" by fastforce
  thus ?case
  proof cases
    case k1
    from 1 root_1 show ?thesis unfolding k1 primitive_root_unity_explicit
      using compute_set_of_jordan_blocks_1[OF A] by auto
  next
    case k2
    from 1 root_2 show ?thesis unfolding k2 primitive_root_unity_explicit
      using compute_set_of_jordan_blocks_minus_1[OF A] by auto
  next
    case k
    from 1(5) have "3 * (d + 2) \<le> 3 * length (filter (op dvd k) ks)" by auto
    also have "\<dots> \<le> n" using sum_list_approx[OF k _ 1(3)] 1(1) by auto
    finally have "3 * (d + 2) \<le> n" by auto
    with size have False by auto
    thus ?thesis by simp
  qed
qed

lemma jnf_perron_frobenius_only_square_roots:  
  assumes size: "n \<le> 5 * (d + 2) - 1" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A 1). 
       bsize \<le> d + 1)" 
  and root_2: "  
     length [k'\<leftarrow>ks . 2 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A (-1)). 
       bsize \<le> d + 1)" 
  and root_3: "\<And> x. x \<in> {Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)} \<Longrightarrow>
     length [k'\<leftarrow>ks . 3 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d + 1)" 
  and root_4: "\<And> x. x \<in> {\<i>, - \<i>} \<Longrightarrow>
     length [k'\<leftarrow>ks . 4 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  from 1(4)
  consider (k1) "k = 1" | (k2) "k = 2" | (k3) "k = 3" | (k4) "k = 4" | (k) "k \<ge> 5" by fastforce
  thus ?case
  proof cases
    case k1
    from 1 root_1 show ?thesis unfolding k1 primitive_root_unity_explicit
      using compute_set_of_jordan_blocks_1[OF A] by auto
  next
    case k2
    from 1 root_2 show ?thesis unfolding k2 primitive_root_unity_explicit 
      using compute_set_of_jordan_blocks_minus_1[OF A] by auto
  next
    case k3
    from 1 root_3 show ?thesis unfolding k3 primitive_root_unity_explicit by auto
  next
    case k4
    from 1 root_4 show ?thesis unfolding k4 primitive_root_unity_explicit by auto
  next
    case k
    from 1(5) have "5 * (d + 2) \<le> 5 * length (filter (op dvd k) ks)" by auto
    also have "\<dots> \<le> n" using sum_list_approx[OF k _ 1(3)] 1(1) by auto
    finally have "5 * (d + 2) \<le> n" by auto
    with size have False by auto
    thus ?thesis by simp
  qed
qed

lemma jordan_block_1_greatest_up_to_4_4: assumes n4: "n \<le> 4" 
  and jnf: "jordan_nf (map_mat complex_of_real A) n_as" 
  and jb: "(k,a) \<in> set n_as" 
  and k: "k \<noteq> 0" 
  and a: "cmod a = 1"   
shows "\<exists> k'. k' \<ge> k \<and> (k',1) \<in> set n_as" 
proof (cases "a = 1")
  case True
  with jb show ?thesis by auto
next
  case a1: False
  let ?c = "complex_of_real" 
  let ?cm = "map_mat ?c" 
  let ?A = "?cm A" 
  let ?cp = "map_poly ?c" 
  have cA: "?A \<in> carrier_mat n n" using A by auto
  from split_list[OF jb] obtain nas1 nas2 where n_as: "n_as = nas1 @ (k,a) # nas2" by auto

  from degree_monic_char_poly[OF cA] have An: "degree (char_poly ?A) = n" by auto
  from jordan_nf_char_poly[OF jnf] 
  have cp: "char_poly ?A = (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" by auto
  from arg_cong[OF this, of degree] degree_monic_char_poly[OF cA]
  have "n = degree (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" by auto
  also have "\<dots> = (\<Sum>x\<leftarrow>n_as. degree (case x of (n, a) \<Rightarrow> [:- a, 1:] ^ n))" 
    by (subst degree_prod_list_eq, unfold map_map o_def, auto)
  also have "\<dots> = sum_list (map fst n_as)" by (rule sum_list_cong, auto simp: degree_linear_power)
  also have "\<dots> \<noteq> 0" unfolding n_as using k by auto
  finally have n0: "n \<noteq> 0" by auto

  let ?pks = "prod_root_unity ks :: complex poly" 

  have a_rt: "poly (char_poly ?A) a = 0" 
    unfolding arg_cong[OF cp[unfolded n_as], of "\<lambda> f. poly f a"] using k by auto

  from ks obtain f where dec: "decompose_prod_root_unity (char_poly A) = (ks,f)" (is "?tmp = _")
    by (cases ?tmp, auto)    
  note pfc = perron_frobenius_for_complexity_jnf[OF A n0 nonneg sr dec, simplified]
  from pfc(7)[OF a a_rt] obtain j where j: "j \<in> set ks" and aj: "a ^ j = 1" by auto
  from split_list[OF j] obtain ks1 ks2 where ks: "ks = ks1 @ j # ks2" by auto
  from pfc(6)[of 1, unfolded ks] have ord_1: "order 1 (char_poly ?A) \<noteq> 0" by auto
  with order_root[of "char_poly ?A" 1] have rt_1: "poly (char_poly ?A) 1 = 0" by auto
  from ord_1[unfolded jordan_nf_order[OF jnf]] obtain o1 where o1: "(o1,1) \<in> set n_as" "o1 \<noteq> 0" 
    by auto
  have deg: "n = degree ?pks + degree (?cp f)" using n0 An pfc(1) 
    unfolding An[symmetric] pfc(3) by (subst degree_mult_eq, auto)
  also have "degree ?pks = sum_list ks" using degree_prod_root_unity[OF pfc(1)] .
  also have "\<dots> + degree (?cp f) \<ge> sum_list ks" by simp
  finally have sum_n: "sum_list ks \<le> n" .

  show ?thesis
  proof (cases "k = 1")
    case True
    with o1 show ?thesis by (intro exI[of _ o1], auto)
  next
    case False
    with k have k2: "k \<ge> 2" by auto
    with jordan_nf_order[OF jnf, of a, unfolded n_as] 
    have "order a (char_poly ?A) \<ge> 2" by auto
    from this[unfolded pfc(6)[OF a]] obtain j j' ks' where id: "[k\<leftarrow>ks . a ^ k = 1] = j # j' # ks'" 
      (is "?tmp = _") by (cases ?tmp; cases "tl ?tmp", auto)
    from this[unfolded filter_eq_Cons_iff Cons_eq_filter_iff]
    obtain ks1 ks2 ks3 where ks: "ks = ks1 @ j # ks2 @ j' # ks3" by blast
    from arg_cong[OF id, of set] 
    have j: "j \<in> set ks" "a ^ j = 1" "j' \<in> set ks" "a ^ j' = 1" by auto
    with pfc(1) have j0: "j \<noteq> 0" "j' \<noteq> 0" by metis+
    from j(2,4) a1 have j1: "j \<noteq> 1" "j' \<noteq> 1" by auto
    from j0 j1 have j2: "j \<ge> 2" "j' \<ge> 2" by auto
    have "j + j' \<le> sum_list [k \<leftarrow> ks. a ^ k = 1]" unfolding id by simp
    also have "\<dots> \<le> sum_list ks" by (induct ks, auto)
    also have "\<dots> \<le> n" by fact
    finally have "j + j' \<le> n" by auto
    with j2 n4 have j2: "j = 2" "j' = 2" and n4: "n = 4" by auto
    have ks: "ks = [2,2]" using sum_n pfc(1) unfolding ks j2 n4 
      by (cases ks1, auto, cases ks2, auto, cases ks3, auto)
    from deg[unfolded ks n4] have degf: "degree f = 0" by auto
    from degree0_coeffs[OF this] obtain f0 where f: "f = [:f0:]" by auto
    have "monic ?pks" using monic_prod_root_unity[OF pfc(1)] . 
    with arg_cong[OF pfc(2), of monic] degree_monic_char_poly[OF A]
    have mf: "monic f" using monic_factor monic_prod_root_unity pfc(1) by blast
    with degf have f: "f = 1" using f by auto
    with pfc(3) pfc(2) ks have 
      cpA: "char_poly ?A = prod_root_unity [2,2]" "char_poly A = prod_root_unity [2,2]" by auto
    have spect: "spectrum ?A = {1,-1}" unfolding spectrum_def 
      unfolding eigenvalue_root_char_poly[OF cA] cpA 
      by (auto simp: prod_root_unity_def root_unity_def poly_monom power2_eq_1_iff)
    have sr1: "Spectral_Radius.spectral_radius ?A = 1" unfolding Spectral_Radius.spectral_radius_def
      spect by auto
    {
      assume "irreducible_mat A" 
      from perron_frobenius_irreducible[OF A n0 nonneg this refl sr1[symmetric]]
      have "order 1 (char_poly A) = 1" by auto
      from this[unfolded pfc(2) ks f] have False by code_simp
    }
    hence "\<not> irreducible_mat A" by auto
    from non_irreducible_mat_split[OF A this, unfolded n4]
    obtain n1 n2 B B1 B2 B4 where
      sim: "similar_mat A B" 
      and elem: "elements_mat A = elements_mat B"
      and B: "B = four_block_mat B1 B2 (0\<^sub>m n2 n1) B4"
      and carr: "B1 \<in> carrier_mat n1 n1" "B2 \<in> carrier_mat n1 n2" "B4 \<in> carrier_mat n2 n2" 
      and ns: "0 < n1" "n1 < 4" "0 < n2" "n2 < 4" "n1 + n2 = 4" by auto
    interpret c: field_hom ?c ..
    interpret p: map_poly_inj_idom_divide_hom ?c ..

    from cpA char_poly_four_block_mat_lower_left_zero[OF B carr] char_poly_similar[OF sim] 
    have cpB14: "char_poly B1 * char_poly B4 = prod_root_unity [2,2]" by auto
    note arg_cong[OF this, of ?cp]
    also have "?cp (char_poly B1 * char_poly B4) = (char_poly (?cm B1) * char_poly (?cm B4))" 
      unfolding of_real_hom.char_poly_hom[OF carr(1)] of_real_hom.char_poly_hom[OF carr(3)] 
      by (simp add: p.hom_mult)
    also have "?cp (prod_root_unity [2,2]) = prod_root_unity [2,2]" 
      by (simp add: of_real_hom.hom_prod_root_unity)
    finally have cpB14c: "char_poly (?cm B1) * char_poly (?cm B4) = prod_root_unity [2,2]" by auto
    from carr have B14: "?cm B1 \<in> carrier_mat n1 n1" "?cm B4 \<in> carrier_mat n2 n2" by auto
    from degree_monic_char_poly[OF B14(1)] 
    have B1: "degree (char_poly (?cm B1)) = n1" "char_poly (?cm B1) \<noteq> 0" "monic (char_poly (?cm B1))" 
      by auto
    from degree_monic_char_poly[OF B14(2)] 
    have B4: "degree (char_poly (?cm B4)) = n2" "char_poly (?cm B4) \<noteq> 0" "monic (char_poly (?cm B4))"
      by auto
    {
      fix x
      have "order x (char_poly (?cm B1)) + order x (char_poly (?cm B4)) 
        = order x (prod_root_unity [2,2])" unfolding cpB14c[symmetric]
        by (subst order_mult, insert degree_monic_char_poly[OF B14(1)] 
          degree_monic_char_poly[OF B14(2)], auto)
      also have "\<dots> = (if x = 1 \<or> x = -1 then 2 else 0)"
        by (subst order_prod_root_unity, auto simp: power2_eq_1_iff)
      finally have "order x (char_poly (?cm B1)) + order x (char_poly (?cm B4)) =
        (if x = 1 \<or> x = -1 then 2 else 0)" .
    } note ord_sum = this
    from nonneg elements_mat_four_block_mat_supseteq[OF carr(1,2) _ carr(3), 
      of "0\<^sub>m n2 n1", folded B] elem 
    have nonneg: "nonneg_mat B1" "nonneg_mat B4" "nonneg_mat B2" 
       unfolding nonneg_mat_def by auto
    {
      fix B3
      assume B3: "B3 \<in> {B1,B4}"  
      from B3 carr nonneg ns obtain n3 where *: "B3 \<in> carrier_mat n3 n3" 
        "n3 \<noteq> 0" "nonneg_mat B3" and small: "n3 \<le> 3" by auto
      let ?cp3 = "char_poly (?cm B3)" 
      {
        fix x
        assume "poly ?cp3 x = 0" 
        with B3 have "poly (char_poly (?cm B1) * char_poly (?cm B4)) x = 0" by auto
        from this[unfolded cpB14c] have "x \<in> {1,-1}" unfolding poly_prod_root_unity 
          by (auto simp: power2_eq_1_iff)
      } note choice = this
      {
        fix x
        assume "poly (char_poly B3) x = 0" 
        with B3 have "poly (char_poly B1 * char_poly B4) x = 0" by auto
        from this[unfolded cpB14] have "x \<in> {1,-1}" unfolding poly_prod_root_unity 
          by (auto simp: power2_eq_1_iff)
        hence "x \<le> 1" "x = 1 \<or> x = -1" by auto        
      } note small = this
      from * have B3': "?cm B3 \<in> carrier_mat n3 n3" by auto
      from degree_monic_char_poly[OF B3'] have B30: "?cp3 \<noteq> 0" by auto
      obtain ks3 f3 where dec: "decompose_prod_root_unity (char_poly B3) = (ks3,f3)" (is "?dec = _")
        by (cases ?dec, auto)
      note pcf = perron_frobenius_for_complexity_jnf[OF *(1-3) small(1) dec, simplified]
      from pcf(6)[of 1] have ord1: "order 1 ?cp3 = length ks3" by auto
      from pcf(6)[of "-1"] have ordm1: "order (-1) ?cp3 \<le> length ks3" by auto
      from ord1 ordm1 have ord: "order 1 ?cp3 \<ge> order (-1) ?cp3" by auto
      have set_id: "{a. poly ?cp3 a = 0} = ((if poly ?cp3 1 = 0 then insert 1 else id) 
        (if poly ?cp3 (-1) = 0 then {-1} else {}))" 
        using choice by auto
      have "order (-1) ?cp3 + order 1 ?cp3 \<le> (\<Sum>a | poly ?cp3 a = 0. order a ?cp3)"
        unfolding set_id by (auto intro: order_0I)
      also have "\<dots> \<le> degree ?cp3" using order_sum_degree[OF B30] .
      finally have ord_le: "order (-1) ?cp3 + order 1 ?cp3 \<le> degree ?cp3" .
      {
        assume o1: "order (-1) ?cp3 \<ge> 2" 
        with ord have "order 1 ?cp3 \<ge> 2" by auto
        with o1 have "4 \<le> degree ?cp3" using ord_le by auto
        also have "\<dots> \<le> 3" using degree_monic_char_poly[OF B3'] \<open>n3 \<le> 3\<close> by auto
        finally have False by simp
      }
      hence "order (-1) ?cp3 \<le> 1" by fastforce
      note this ord ord_le
    } note ord = this
    from ord_sum[of "-1"] ord(1)[of B1] ord(1)[of B4] 
    have ord_m1: "order (-1) (char_poly (?cm B1)) = 1" "order (-1) (char_poly (?cm B4)) = 1" by auto
    with ord_sum[of 1] ord(2)[of B1] ord(2)[of B4]
    have ord_1: "order 1 (char_poly (?cm B1)) = 1" "order 1 (char_poly (?cm B4)) = 1" by auto
    from ord(3)[of B1] ord(3)[of B4]
    have n2: "n1 = 2" "n2 = 2" using B1 B4 ns 
      unfolding ord_1 ord_m1 by auto
    from order_root_unity_2[of "char_poly (?cm B1)"] order_root_unity_2[of "char_poly (?cm B4)"] 
      ord_1 ord_m1 B1 B4 n2
    have cp14: "char_poly (?cm B1) = root_unity 2" "char_poly (?cm B4) = root_unity 2" by auto
    note B14 = carr(1,3)[unfolded n2]
    from char_poly_root_unity_2[OF B14(1) cp14(1) nonneg(1)] 
      char_poly_root_unity_2[OF B14(2) cp14(2) nonneg(2)]
    have B1': "B1 $$ (0, 0) = 0" "B1 $$ (1, 1) = 0" "B1 $$ (1, 0) * B1 $$ (0, 1) = 1" 
     and B4': "B4 $$ (0, 0) = 0" "B4 $$ (1, 1) = 0" "B4 $$ (1, 0) * B4 $$ (0, 1) = 1" .
    from a_rt[unfolded cpA] a1 have a1: "a = -1" unfolding poly_prod_root_unity 
      by (auto simp: power2_eq_1_iff)
    obtain a b c d e f g h where 
      a: "a = B1 $$ (0,1)" and
      b: "b = B4 $$ (0,1)" and
      c: "c = B2 $$ (0,0)" and
      d: "d = B2 $$ (0,1)" and
      e: "e = B2 $$ (1,0)" and
      f: "f = B2 $$ (1,1)" and
      g: "g = (b * c - d - a * b * e + a * f) / (2 * b)" and
      h: "h = (b * c + d + a * b * e + a * f) / (2 * a)" by auto
    from B1' B4' have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by (auto simp: a b)
    from B1'(3) have "B1 $$ (0,1) \<noteq> 0" by auto
    with arg_cong[OF B1'(3), of "\<lambda> x. x / B1 $$ (0,1)"] have B1_10: "B1 $$ (1,0) = 1/ a" 
      by (auto simp: a field_simps)
    have B1: "B1 = mat_of_rows_list 2 [[0,a],[1/ a, 0]]" 
      by (rule eq_matI, insert B1' B14(1) B1_10, auto simp: mat_of_rows_list_def, rename_tac i j,
      case_tac i; case_tac j, auto simp: a) 
    from B4'(3) have "B4 $$ (0,1) \<noteq> 0" by auto
    with arg_cong[OF B4'(3), of "\<lambda> x. x / B4 $$ (0,1)"] have B4_10: "B4 $$ (1,0) = 1/ b" 
      by (auto simp: b field_simps)
    have B4: "B4 = mat_of_rows_list 2 [[0,b],[1/ b, 0]]" 
      by (rule eq_matI, insert B4' B14(2) B4_10, auto simp: mat_of_rows_list_def, rename_tac i j,
      case_tac i; case_tac j, auto simp: b) 
    have B2: "B2 = mat_of_rows_list 2 [[c,d],[e,f]]" 
      by (rule eq_matI, insert carr(2)[unfolded n2], auto simp: mat_of_rows_list_def, rename_tac i j,
      case_tac i; case_tac j, auto simp: c d e f) 
    have B: "B = mat_of_rows_list 4 [[0,a,c,d], [1/ a, 0, e, f], [0,0,0,b], [0,0,1/ b,0]]" 
      unfolding B B1 B2 B4 n2
      by (rule eq_mat_dim_4, auto simp: mat_of_rows_list_def)
    from nonneg_matD[OF nonneg(1), of 0 1] have a': "a \<ge> 0" unfolding a unfolding B1 by auto
    from nonneg_matD[OF nonneg(2), of 0 1] have b': "b \<ge> 0" unfolding b unfolding B4 by auto
    from nonneg_matD[OF nonneg(3), of 0 0] have c: "c \<ge> 0" unfolding c unfolding B2 by auto
    from nonneg_matD[OF nonneg(3), of 0 1] have d: "d \<ge> 0" unfolding d unfolding B2 by auto
    from nonneg_matD[OF nonneg(3), of 1 0] have e: "e \<ge> 0" unfolding e unfolding B2 by auto
    from nonneg_matD[OF nonneg(3), of 1 1] have f: "f \<ge> 0" unfolding f unfolding B2 by auto
    let ?C = "mat_of_rows_list 4
      [ [-1, g, 0, 0],
        [ 0, -1, 0 , 0], 
        [ 0, 0, 1, h],
        [ 0, 0, 0, 1] ]"
    let ?D = "mat_of_rows_list 4
      [ [ 1/2, -a/2, (-d - b * (c - a * e) + a * f) / (8 * b), (-d - b * (c - a * e) + a * f) / 8],
        [ 0, 0, 1/2, -b / 2],
        [ 1/a, 1, (c/a + e - (d/a + f) / b) / 2, 0],
        [ 0, 0, 1/b, 1] ]" 
    let ?E = "mat_of_rows_list 4
      [ [ 1, (-c + d/b - a * e + a * f / b) / 4, a/2, (d - a * b * e) / 4],
        [ -1/a, (-c/a + d/a/b - e + f/b)/4, 1/2, (-b * c/a + f) / 4],
        [ 0, 1, 0 , b/2],
        [0, -1/b, 0, 1/2]]" 
    have 1: "?D * ?E = 1\<^sub>m 4" 
      by (rule eq_mat_dim_4, insert a0 b0, auto simp: mat_of_rows_list_def scalar_prod_def
        ring_distribs diff_divide_distrib add_divide_distrib)
    have 11: "?E * ?D = 1\<^sub>m 4" 
      by (rule eq_mat_dim_4, insert a0 b0, auto simp: mat_of_rows_list_def scalar_prod_def
        ring_distribs diff_divide_distrib add_divide_distrib)
    have main: "?D * B * ?E = ?C" unfolding B g h
      by (rule eq_mat_dim_4, insert a0 b0, auto simp: mat_of_rows_list_def scalar_prod_def
        ring_distribs diff_divide_distrib add_divide_distrib)
    have "similar_mat ?C B" 
      by (rule similar_matI[OF _ 1 11 main[symmetric]], auto simp: B)
    from similar_mat_trans[OF sim similar_mat_sym[OF this]]
    have sim: "similar_mat A ?C" .
    hence sim': "similar_mat ?A (?cm ?C)" by (rule of_real_hom.similar_mat_hom)    
    have cC: "?cm ?C \<in> carrier_mat 4 4" by auto
    note cA = cA[unfolded n4]
    from similar_iff_same_jordan_nf[OF cA[unfolded n4] cC] sim'
    have jnf': "jordan_nf (?cm ?C) n_as" using jnf by auto
    let ?comp = "\<lambda> A. compute_nr_of_jordan_blocks (?cm A)" 
    from jordan_nf_block_size_order_bound[OF jnf jb, unfolded cpA a1]
    have "k \<le> 2" by (subst (asm) order_prod_root_unity, auto simp: power2_eq_1_iff)
    with k2 have k2: "k = 2" by simp
    from split_list[OF jb, unfolded a1 k2] obtain nas1 nas2 where 
      n_as: "n_as = nas1 @ (2,-1) # nas2" by auto
    note nonneg = a0 b0 c d e f a' b'
    let ?C1 = "mat_of_rows_list 2 [[-1,?c g],[0,-1]]" 
    let ?C2 = "mat_of_rows_list 2 [[1,?c h],[0,1]]" 
    have C1: "?C1 \<in> carrier_mat 2 2" by auto
    have C2: "?C2 \<in> carrier_mat 2 2" by auto
    have C: "?cm ?C = four_block_mat ?C1 (0\<^sub>m 2 2)
         (0\<^sub>m 2 2) ?C2" 
      by (rule eq_mat_dim_4, auto simp: mat_of_rows_list_def)
    have jnf1: "jordan_nf ?C1 (if g = 0 then [(1,-1),(1,-1)] else [(2,-1)])" (is "jordan_nf _ ?j1")
      using jordan_nf_dim_2[OF refl, of "?c g" "-1"] by auto
    have jnf2: "jordan_nf ?C2 (if h = 0 then [(1,1),(1,1)] else [(2,1)])" (is "jordan_nf _ ?j2")
      using jordan_nf_dim_2[OF refl, of "?c h" 1] by auto
    have jnf12: "jordan_nf (?cm ?C) (?j1 @ ?j2)" unfolding C 
      using jordan_nf_four_block_mat[OF C1 C2 jnf1 jnf2] by auto
    from jnf12[folded sim'[unfolded similar_iff_same_jordan_nf[OF cA cC]]]
    have jnf12: "jordan_nf ?A (?j1 @ ?j2)"  .
    from compute_nr_of_jordan_blocks[OF jnf]
    have comp1: "?comp A x 2 = length (filter (op = (2, x)) n_as)" for x by auto
    from compute_nr_of_jordan_blocks[OF jnf12]
    have comp2: "?comp A x 2 = length (filter (op = (2, x)) (?j1 @ ?j2))" for x by auto
    note comp1[of "-1"]
    also have "length (filter (op = (2, - 1)) n_as) \<ge> 1" unfolding n_as by auto
    finally have 21: "?comp A (-1) 2 \<ge> 1" .
    also have "?comp A (-1) 2 = length (filter (op = (2, - 1)) (?j1 @ ?j2))" 
      unfolding comp2 by auto
    finally have g0: "g \<noteq> 0" by auto
    {
      assume h0: "h = 0"
      hence "sum_list [b * c, d, a * b * e, a * f] = 0" (is "?sum = 0") 
        unfolding h using nonneg by auto
      also have "(?sum = 0) = (\<forall>x\<in>set [b * c, d, a * b * e, a * f]. x = 0)"
        by (rule sum_list_nonneg_eq_0_iff, insert nonneg, auto)
      also have "\<dots> = (\<forall>x\<in>set [c, d, e, f]. x = 0)" using a0 b0 by auto
      finally have "c = 0" "d = 0" "e = 0" "f = 0" by auto
      hence "g = 0" unfolding g by auto
      with g0 have False ..
    }
    hence h0: "h \<noteq> 0" by auto
    from comp2[unfolded comp1, of 1] g0 h0 have "set (filter (op = (2, 1)) n_as) \<noteq> {}" 
      by (cases "filter (op = (2, 1)) n_as", auto)
    hence "(2,1) \<in> set n_as" by auto
    thus ?thesis unfolding k2 by auto
  qed
qed

lemma jnf_perron_frobenius_only_block_1_dim_4:  
  assumes size: "n \<le> 4" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
     order 1 (char_poly A) = length ks \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A 1). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  hence k0: "k \<noteq> 0" by auto
  let ?A = "map_mat complex_of_real A" 
  from A have cA: "?A \<in> carrier_mat n n" by auto
  from arg_cong[OF primitive_root_unityD(2)[OF 1(6)], of cmod, unfolded norm_power] k0 
  have cx: "cmod x = 1" by (smt class_semiring.nat_pow_0 less_one norm_ge_zero norm_one 
    not_less power_decreasing power_inject_exp power_one_right)
  from char_poly_factorized[OF cA] obtain as where cp: "char_poly ?A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by auto
  from jordan_nf_exists[OF cA cp] obtain n_as where jnf: "jordan_nf ?A n_as" ..
  show ?case
  proof 
    fix bsize
    assume "bsize \<in>  fst ` set (compute_set_of_jordan_blocks ?A x)" 
    with compute_set_of_jordan_blocks[OF jnf, of x] 
    have bsize: "(bsize, x) \<in> set n_as" "bsize \<noteq> 0" by force+
    from jordan_block_1_greatest_up_to_4_4[OF size jnf this cx]
    obtain k' where kb: "k' \<ge> bsize" and "(k',1) \<in> set n_as" by auto
    with bsize have "(k',1) \<in> set n_as \<inter> UNIV \<times> {1} - {0} \<times> UNIV" by auto
    from this[folded compute_set_of_jordan_blocks[OF jnf, of 1]] 
      compute_set_of_jordan_blocks_1[OF A]
    have "k' \<in> fst ` set (compute_set_of_jordan_blocks A 1)" by force
    from root_1[OF 1(1,2), rule_format, OF _ this] 1(8)[of 1] kb A show "bsize \<le> d + 1" 
      by (auto simp: order_of_real_char_poly_1)
  qed
qed
end

thm 
  jnf_perron_frobenius_only_blocks_1_and_minus_1
  jnf_perron_frobenius_only_block_1
  jnf_perron_frobenius_only_block_1_dim_4

end
