(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Elementary Column Operations\<close>

text \<open>We define elementary column operations and also combine them with elementary
  row operations. These combined operations are the basis to perform operations which
  preserve similarity of matrices. They are applied later on to convert upper triangular
  matrices into Jordan normal form.\<close>

theory Column_Operations
imports
  Gauss_Jordan
begin

definition mat_multcol :: "nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("multcol") where
  "multcol k a A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
     (\<lambda> (i,j). if k = j then a * A $$ (i,j) else A $$ (i,j))"

definition mat_swapcols :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("swapcols")where
  "swapcols k l A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
    (\<lambda> (i,j). if k = j then A $$ (i,l) else if l = j then A $$ (i,k) else A $$ (i,j))"

definition mat_addcol_vec :: "nat \<Rightarrow> 'a :: plus vec \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mat_addcol_vec k v A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
    (\<lambda> (i,j). if k = j then v $ i + A $$ (i,j) else A $$ (i,j))"

definition mat_addcol :: "'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("addcol") where
  "addcol a k l A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
    (\<lambda> (i,j). if k = j then a * A $$ (i,l) + A $$ (i,j) else A $$ (i,j))"

lemma mat_index_multcol[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> multcol k a A $$ (i,j) = (if k = j then a * A $$ (i,j) else A $$ (i,j))"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> multcol j a A $$ (i,j) = a * A $$ (i,j)"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> k \<noteq> j \<Longrightarrow> multcol k a A $$ (i,j) = A $$ (i,j)"
  "dim\<^sub>r (multcol k a A) = dim\<^sub>r A" "dim\<^sub>c (multcol k a A) = dim\<^sub>c A"
  unfolding mat_multcol_def by auto

lemma mat_index_swapcols[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> swapcols k l A $$ (i,j) = (if k = j then A $$ (i,l) else 
    if l = j then A $$ (i,k) else A $$ (i,j))"
  "dim\<^sub>r (swapcols k l A) = dim\<^sub>r A" "dim\<^sub>c (swapcols k l A) = dim\<^sub>c A"
  unfolding mat_swapcols_def by auto

lemma mat_index_addcol[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> addcol a k l A $$ (i,j) = (if k = j then 
    a * A $$ (i,l) + A $$ (i,j) else A $$ (i,j))"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> addcol a j l A $$ (i,j) = a * A $$(i,l) + A$$(i,j)"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> k \<noteq> j \<Longrightarrow> addcol a k l A $$ (i,j) = A $$(i,j)"
  "dim\<^sub>r (addcol a k l A) = dim\<^sub>r A" "dim\<^sub>c (addcol a k l A) = dim\<^sub>c A"
  unfolding mat_addcol_def by auto

text \<open>Each column-operation can be seen as a multiplication of 
  an elementary matrix from the right\<close>

lemma col_addrow: 
  "l \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> col (addrow_mat n a k l) i = unit\<^sub>v n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> col (addrow_mat n a k l) l = a \<odot>\<^sub>v unit\<^sub>v n k \<oplus>\<^sub>v unit\<^sub>v n l" 
  by (rule vec_eqI, auto)

lemma col_addcol[simp]:
  "k < dim\<^sub>c A \<Longrightarrow> l < dim\<^sub>c A \<Longrightarrow> col (addcol a k l A) k = a \<odot>\<^sub>v col A l \<oplus>\<^sub>v col A k"
  by (rule vec_eqI;simp)

lemma addcol_mat: assumes A: "A \<in> carrier\<^sub>m nr n" 
  and k: "k < n"
  shows "addcol (a :: 'a :: comm_semiring_1) l k A = A \<otimes>\<^sub>m addrow_mat n a k l"
  by (rule mat_eqI, insert A k, auto simp: col_addrow
  scalar_prod_right_distrib[of _ n] scalar_prod_scalar_assoc[of _ n])

lemma col_multrow:  "k \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> col (multrow_mat n k a) i = unit\<^sub>v n i"
  "k < n \<Longrightarrow> col (multrow_mat n k a) k = a \<odot>\<^sub>v unit\<^sub>v n k"
  by (rule vec_eqI, auto)

lemma multcol_mat: assumes A: "(A :: 'a :: comm_ring_1 mat) \<in> carrier\<^sub>m nr n"
  shows "multcol k a A = A \<otimes>\<^sub>m multrow_mat n k a"
  by (rule mat_eqI, insert A, auto simp: col_multrow scalar_scalar_prod_assoc[of _ n])

lemma col_swaprows: 
  "l < n \<Longrightarrow> col (swaprows_mat n l l) l = unit\<^sub>v n l"
  "i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> i < n \<Longrightarrow> col (swaprows_mat n k l) i = unit\<^sub>v n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> col (swaprows_mat n k l) l = unit\<^sub>v n k"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> col (swaprows_mat n k l) k = unit\<^sub>v n l"
  by (rule vec_eqI, auto)

lemma swapcols_mat: assumes A: "A \<in> carrier\<^sub>m nr n" and k: "k < n" "l < n"
  shows "swapcols k l A = A \<otimes>\<^sub>m swaprows_mat n k l"
  by (rule mat_eqI, insert A k, auto simp: col_swaprows)

text \<open>Combining row and column-operations yields similarity transformations.\<close>

definition add_col_sub_row :: "'a :: ring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"  where
  "add_col_sub_row a k l A = addrow (- a) k l (addcol a l k A)"

definition mult_col_div_row :: "'a :: field \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mult_col_div_row a k A = multrow k (inverse a) (multcol k a A)"

definition swap_cols_rows :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "swap_cols_rows k l A = swaprows k l (swapcols k l A)"


lemma add_col_sub_row_dims[simp]: 
  "dim\<^sub>r (add_col_sub_row a k l A) = dim\<^sub>r A"
  "dim\<^sub>c (add_col_sub_row a k l A) = dim\<^sub>c A"
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> add_col_sub_row a k l A \<in> carrier\<^sub>m n n"
  unfolding add_col_sub_row_def mat_carrier_def by auto

lemma add_col_sub_row_index[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> l < dim\<^sub>r A 
    \<Longrightarrow> add_col_sub_row a k l A $$ (i,j) = (if 
      i = k \<and> j = l then A $$ (i, j) + a * A $$ (i, i) - a * a * A $$ (j, i) - a * A $$ (j, j) else if
      i = k \<and> j \<noteq> l then A $$ (i, j) - a * A $$ (l, j) else if
      i \<noteq> k \<and> j = l then A $$ (i, j) + a * A $$ (i, k) else A $$ (i,j))"
  unfolding add_col_sub_row_def by (auto simp: field_simps)

lemma mult_col_div_row_index[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> a \<noteq> 0
    \<Longrightarrow> mult_col_div_row a k A $$ (i,j) = (if 
      i = k \<and> j \<noteq> i then inverse a * A $$ (i, j) else if
      j = k \<and> j \<noteq> i then a * A $$ (i, j) else A $$ (i,j))"
  unfolding mult_col_div_row_def by auto

lemma mult_col_div_row_dims[simp]: 
  "dim\<^sub>r (mult_col_div_row a k A) = dim\<^sub>r A"
  "dim\<^sub>c (mult_col_div_row a k A) = dim\<^sub>c A"
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> mult_col_div_row a k A \<in> carrier\<^sub>m n n"
  unfolding mult_col_div_row_def mat_carrier_def by auto

lemma swap_cols_rows_dims[simp]: 
  "dim\<^sub>r (swap_cols_rows k l A) = dim\<^sub>r A"
  "dim\<^sub>c (swap_cols_rows k l A) = dim\<^sub>c A"
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> swap_cols_rows k l A \<in> carrier\<^sub>m n n"
  unfolding swap_cols_rows_def mat_carrier_def by auto

lemma swap_cols_rows_index[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> a < dim\<^sub>r A \<Longrightarrow> b < dim\<^sub>r A 
    \<Longrightarrow> swap_cols_rows a b A $$ (i,j) = A $$ (if i = a then b else if i = b then a else i,
     if j = a then b else if j = b then a else j)"
  unfolding swap_cols_rows_def 
  by auto 

lemma add_col_sub_row_similar: assumes A: "A \<in> carrier\<^sub>m n n" and kl: "k < n" "l < n" "k \<noteq> l"
  shows "mat_similar (add_col_sub_row a k l A) (A :: 'a :: comm_ring_1 mat)"
proof (rule mat_similarI)
  let ?P = "addrow_mat n (-a) k l"
  let ?Q = "addrow_mat n a k l"
  let ?B = "add_col_sub_row a k l A"
  show carr: "{?B, A, ?P, ?Q} \<subseteq> carrier\<^sub>m n n" using A by auto
  show "?Q \<otimes>\<^sub>m ?P = \<one>\<^sub>m n" by (rule addrow_mat_inv[OF kl])
  show "?P \<otimes>\<^sub>m ?Q = \<one>\<^sub>m n" using addrow_mat_inv[OF kl, of "-a"] by simp
  have col: "addcol a l k A = A \<otimes>\<^sub>m ?Q"
    by (rule addcol_mat[OF A kl(1)])
  have "?B = ?P \<otimes>\<^sub>m (A \<otimes>\<^sub>m ?Q)" unfolding add_col_sub_row_def col
    by (rule addrow_mat[OF _ kl(2), of _ n], insert A, simp)
  thus "?B = ?P \<otimes>\<^sub>m A \<otimes>\<^sub>m ?Q" using carr by (simp add: mat_mult_assoc[of _ n n _ n _ n])
qed

lemma mult_col_div_row_similar: assumes A: "A \<in> carrier\<^sub>m n n" and ak: "k < n" "a \<noteq> 0"
  shows "mat_similar (mult_col_div_row a k A) A"
proof (rule mat_similarI)
  let ?P = "multrow_mat n k (inverse a)"
  let ?Q = "multrow_mat n k a"
  let ?B = "mult_col_div_row a k A"
  show carr: "{?B, A, ?P, ?Q} \<subseteq> carrier\<^sub>m n n" using A by auto
  show "?Q \<otimes>\<^sub>m ?P = \<one>\<^sub>m n" by (rule multrow_mat_inv[OF ak])
  show "?P \<otimes>\<^sub>m ?Q = \<one>\<^sub>m n" using multrow_mat_inv[OF ak(1), of "inverse a"] ak(2) by simp
  have col: "multcol k a A = A \<otimes>\<^sub>m ?Q"
    by (rule multcol_mat[OF A])
  have "?B = ?P \<otimes>\<^sub>m (A \<otimes>\<^sub>m ?Q)" unfolding mult_col_div_row_def col
    by (rule multrow_mat[of _ n n], insert A, simp)
  thus "?B = ?P \<otimes>\<^sub>m A \<otimes>\<^sub>m ?Q" using carr by (simp add: mat_mult_assoc[of _ n n _ n _ n])
qed

lemma swap_cols_rows_similar: assumes A: "A \<in> carrier\<^sub>m n n" and kl: "k < n" "l < n"
  shows "mat_similar (swap_cols_rows k l A) A"
proof (rule mat_similarI)
  let ?P = "swaprows_mat n k l"
  let ?B = "swap_cols_rows k l A"
  show carr: "{?B, A, ?P, ?P} \<subseteq> carrier\<^sub>m n n" using A by auto
  show "?P \<otimes>\<^sub>m ?P = \<one>\<^sub>m n" by (rule swaprows_mat_inv[OF kl])
  show "?P \<otimes>\<^sub>m ?P = \<one>\<^sub>m n" by fact
  have col: "swapcols k l A = A \<otimes>\<^sub>m ?P"
    by (rule swapcols_mat[OF A kl])
  have "?B = ?P \<otimes>\<^sub>m (A \<otimes>\<^sub>m ?P)" unfolding swap_cols_rows_def col
    by (rule swaprows_mat[of _ n n ], insert A kl, auto)
  thus "?B = ?P \<otimes>\<^sub>m A \<otimes>\<^sub>m ?P" using carr by (simp add: mat_mult_assoc[of _ n n _ n _ n])
qed

(* THIS LINE SEPARATES AFP-ENTRY FROM NEWER DEVELOPMENTS *)

lemma swapcols_carrier[simp]: "(swapcols l k A \<in> carrier\<^sub>m n m) = (A \<in> carrier\<^sub>m n m)"
  unfolding mat_swapcols_def mat_carrier_def by auto

fun swap_row_to_front :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "swap_row_to_front A 0 = A"
| "swap_row_to_front A (Suc I) = swap_row_to_front (swaprows I (Suc I) A) I"

fun swap_col_to_front :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "swap_col_to_front A 0 = A"
| "swap_col_to_front A (Suc I) = swap_col_to_front (swapcols I (Suc I) A) I"

lemma swap_row_to_front_result: "A \<in> carrier\<^sub>m n m \<Longrightarrow> I < n \<Longrightarrow> swap_row_to_front A I = 
  mat n m (\<lambda> (i,j). if i = 0 then A $$ (I,j)
  else if i \<le> I then A $$ (i - 1, j) else A $$ (i,j))"
proof (induct I arbitrary: A)
  case 0
  thus ?case
    by (intro mat_eqI, auto)
next
  case (Suc I A)
  from Suc(3) have I: "I < n" by auto
  let ?I = "Suc I"
  let ?A = "swaprows I ?I A"
  have AA: "?A \<in> carrier\<^sub>m n m" using Suc(2) by simp
  have "swap_row_to_front A (Suc I) = swap_row_to_front ?A I" by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if i = 0 then ?A $$ (I, j)
       else if i \<le> I then ?A $$ (i - 1, j) else ?A $$ (i, j))" 
     using Suc(1)[OF AA I] by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if i = 0 then A $$ (?I, j)
       else if i \<le> ?I then A $$ (i - 1, j) else A $$ (i, j))" 
    by (rule mat_eqI, insert I Suc(2), auto)
  finally show ?case .
qed


lemma swap_col_to_front_result: "A \<in> carrier\<^sub>m n m \<Longrightarrow> J < m \<Longrightarrow> swap_col_to_front A J = 
  mat n m (\<lambda> (i,j). if j = 0 then A $$ (i,J)
  else if j \<le> J then A $$ (i, j-1) else A $$ (i,j))"
proof (induct J arbitrary: A)
  case 0
  thus ?case
    by (intro mat_eqI, auto)
next
  case (Suc J A)
  from Suc(3) have J: "J < m" by auto
  let ?J = "Suc J"
  let ?A = "swapcols J ?J A"
  have AA: "?A \<in> carrier\<^sub>m n m" using Suc(2) by simp
  have "swap_col_to_front A (Suc J) = swap_col_to_front ?A J" by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if j = 0 then ?A $$ (i, J)
          else if j \<le> J then ?A $$ (i, j - 1) else ?A $$ (i, j))" 
     using Suc(1)[OF AA J] by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if j = 0 then A $$ (i, ?J)
          else if j \<le> ?J then A $$ (i, j - 1) else A $$ (i, j))" 
    by (rule mat_eqI, insert J Suc(2), auto)
  finally show ?case .
qed

lemma swapcols_is_transp_swap_rows: assumes A: "A \<in> carrier\<^sub>m n m" "k < m" "l < m"
  shows "swapcols k l A = transpose\<^sub>m (swaprows k l (transpose\<^sub>m A))"
  using assms by (intro mat_eqI, auto)



end