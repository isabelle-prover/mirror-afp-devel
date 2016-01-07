(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Jordan Normal Form -- Uniqueness\<close>

text \<open>We prove that the Jordan normal form of a matrix
  is unique up to permutations of the blocks. We do this 
  via generalized eigenspaces, and an algorithm which 
  computes for each potential jordan block (ev,n), how often
  it occurs in any Jordan normal form.\<close>

theory Jordan_Normal_Form_Uniqueness
imports
  Jordan_Normal_Form
  Matrix_Kernel
begin

lemma mat_similar_wit_char_matrix: assumes wit: "mat_similar_wit A B P Q"
  shows "mat_similar_wit (char_matrix A ev) (char_matrix B ev) P Q"
proof -
  def n \<equiv> "dim\<^sub>r A"
  let ?C = "carrier\<^sub>m n n"
  from mat_similar_witD[OF refl wit, folded n_def] have
    A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C"
    and PQ: "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" and QP: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n"
    and AB: "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q"
    by auto
  have "char_matrix A ev = (P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q \<oplus>\<^sub>m (-ev) \<odot>\<^sub>m (P \<otimes>\<^sub>m Q))"
    unfolding char_matrix_def n_def[symmetric] unfolding AB PQ 
    by (intro mat_eqI, insert P B Q, auto)
  also have "(-ev) \<odot>\<^sub>m (P \<otimes>\<^sub>m Q) = P \<otimes>\<^sub>m ((-ev) \<odot>\<^sub>m \<one>\<^sub>m n) \<otimes>\<^sub>m Q" using P Q
    by (metis mat_mult_scalar_assoc mat_mult_scalar_comm mat_one_closed mat_right_mult_one)
  also have "P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q \<oplus>\<^sub>m \<dots> = (P \<otimes>\<^sub>m B \<oplus>\<^sub>m P \<otimes>\<^sub>m ((-ev) \<odot>\<^sub>m \<one>\<^sub>m n)) \<otimes>\<^sub>m Q" using P B
    by (intro mat_mult_left_distrib[symmetric, OF _ _ Q, of _ n], auto)
  also have "P \<otimes>\<^sub>m B \<oplus>\<^sub>m P \<otimes>\<^sub>m ((-ev) \<odot>\<^sub>m \<one>\<^sub>m n) = P \<otimes>\<^sub>m (B  \<oplus>\<^sub>m (-ev) \<odot>\<^sub>m \<one>\<^sub>m n)"
    by (intro mat_mult_right_distrib[symmetric, OF P B], auto)
  also have "(B  \<oplus>\<^sub>m (-ev) \<odot>\<^sub>m \<one>\<^sub>m n) = char_matrix B ev" unfolding char_matrix_def
    by (intro mat_eqI, insert B, auto)
  finally have AB: "char_matrix A ev = P \<otimes>\<^sub>m char_matrix B ev \<otimes>\<^sub>m Q" .
  show "mat_similar_wit (char_matrix A ev) (char_matrix B ev) P Q"
    by (intro mat_similar_witI[OF PQ QP AB _ _ P Q], insert A B, auto)
qed

context fixes ty :: "'a :: field itself"
begin

lemma dim_kernel_non_zero_jordan_block_pow: assumes a: "a \<noteq> 0"
  shows "kernel.dim n (jordan_block n (a :: 'a) ^\<^sub>m k) = 0"
  by (rule kernel_upper_triangular[OF mat_pow_closed[OF jordan_block_carrier]],
  unfold jordan_block_pow, insert a, auto simp: mat_diag_def)

lemma dim_kernel_zero_jordan_block_pow: 
  "kernel.dim n ((jordan_block n (0 :: 'a)) ^\<^sub>m k) = min k n" (is "kernel.dim _ ?A = ?c")
proof - 
  have A: "?A \<in> carrier\<^sub>m n n" by auto
  hence dim: "dim\<^sub>r ?A = n" by simp
  let ?f = "\<lambda> i. min (k + i) n"
  have piv: "pivot_fun ?A ?f n" unfolding jordan_block_zero_pow
    by (intro pivot_funI, auto)
  hence row: "row_echelon_form ?A" unfolding row_echelon_form_def by auto
  from find_base_vectors(5-6)[OF row A]
  have "kernel.dim n ?A = n - length (map fst (pivot_positions ?A))" by auto
  also have "length (map fst (pivot_positions ?A)) = card (fst ` set (pivot_positions ?A))"
    by (subst distinct_card[OF pivot_positions(2)[OF A piv], symmetric], simp)
  also have "fst ` set (pivot_positions ?A) = { 0 ..< (n - ?c)}" unfolding pivot_positions(1)[OF A piv]
    by force
  also have "card \<dots> = n - ?c" by simp
  finally show ?thesis by simp
qed
  
definition dim_gen_eigenspace :: "'a mat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  "dim_gen_eigenspace A ev k = kernel_dim ((char_matrix A ev) ^\<^sub>m k)"

lemma dim_gen_eigenspace_jordan_matrix: 
  "dim_gen_eigenspace (jordan_matrix n_as) ev k
    = (\<Sum> n \<leftarrow> map fst [(n, e)\<leftarrow>n_as . e = ev]. min k n)"
proof -
  let ?JM = "\<lambda> n_as. jordan_matrix n_as"
  let ?CM = "\<lambda> n_as. char_matrix (?JM n_as) ev"
  let ?A = "\<lambda> n_as. (?CM n_as) ^\<^sub>m k"
  let ?n = "\<lambda> n_as. listsum (map fst n_as)"
  let ?C = "\<lambda> n_as. carrier\<^sub>m (?n n_as) (?n n_as)"
  let ?sum = "\<lambda> n_as. \<Sum> n \<leftarrow> map fst [(n, e)\<leftarrow>n_as . e = ev]. min k n"
  let ?dim = "\<lambda> n_as. listsum (map fst n_as)"
  let ?kdim = "\<lambda> n_as. kernel.dim (?dim n_as) (?A n_as)"
  have JM: "\<And> n_as. ?JM n_as \<in> ?C n_as" by auto
  have CM: "\<And> n_as. ?CM n_as \<in> ?C n_as" by auto
  have A: "\<And> n_as. ?A n_as \<in> ?C n_as" by auto  
  have dimc: "dim\<^sub>c (?JM n_as) = ?dim n_as" by simp
  interpret K: kernel "?dim n_as" "?dim n_as" "?A n_as"
    by (unfold_locales, rule A)
  show ?thesis unfolding dim_gen_eigenspace_def K.kernel_dim 
  proof (induct n_as)
    case Nil
    have "?JM Nil = \<one>\<^sub>m 0" unfolding jordan_matrix_def
      by (intro mat_eqI, auto)
    hence id: "?A Nil = \<one>\<^sub>m 0" unfolding char_matrix_def by auto
    show ?case unfolding id using kernel_one_mat[of 0] by auto
  next
    case (Cons ne n_as')
    let ?n_as = "Cons ne n_as'"
    let ?d = "?dim ?n_as"
    let ?d' = "?dim n_as'"
    obtain n e where ne: "ne = (n,e)" by force
    have dim: "?d = n + ?d'" unfolding ne by simp
    let ?jb = "jordan_block n e"
    let ?cm = "char_matrix ?jb ev"
    let ?a = "?cm ^\<^sub>m k"
    have a: "?a \<in> carrier\<^sub>m n n" by simp
    from JM[of n_as'] have dim_rec: "dim\<^sub>r (?JM n_as') = ?d'" "dim\<^sub>c (?JM n_as') = ?d'" by auto
    hence JM_id: "?JM ?n_as = four_block_mat ?jb (\<zero>\<^sub>m n ?d') (\<zero>\<^sub>m ?d' n) (?JM n_as')"
      unfolding ne jordan_matrix_def using JM[of n_as']
      by (simp add: Let_def)
    have CM_id: "?CM ?n_as = four_block_mat ?cm (\<zero>\<^sub>m n ?d') (\<zero>\<^sub>m ?d' n) (?CM n_as')"
      unfolding JM_id
      unfolding char_matrix_def
      by (intro mat_eqI, auto)
    have A_id: "?A ?n_as = four_block_mat ?a (\<zero>\<^sub>m n ?d') (\<zero>\<^sub>m ?d' n) (?A n_as')"
      unfolding CM_id by (rule four_block_mat_pow[OF _ CM], auto)
    have kdim: "?kdim ?n_as = kernel.dim n ?a + ?kdim n_as'"
      unfolding dim A_id
      by (rule kernel_four_block_0_mat[OF refl a A])
    also have "?kdim n_as' = ?sum n_as'" by (rule Cons)
    also have "kernel.dim n ?a = (if e = ev then min k n else 0)"
      using dim_kernel_zero_jordan_block_pow[of n k]
        dim_kernel_non_zero_jordan_block_pow[of "e - ev" n k]
      unfolding char_matrix_jordan_block
      by (cases "e = ev", auto)
    also have "\<dots> + ?sum n_as' = ?sum ?n_as" unfolding ne by auto
    finally show ?case .
  qed
qed

  
lemma dim_gen_eigenspace_similar: assumes sim: "mat_similar A B"
  shows "dim_gen_eigenspace A = dim_gen_eigenspace B"
proof (intro ext)
  fix ev k
  def n \<equiv> "dim\<^sub>r A"
  from sim[unfolded mat_similar_def] obtain P Q where
    wit: "mat_similar_wit A B P Q" by auto
  let ?C = "carrier\<^sub>m n n"
  from mat_similar_witD[OF refl wit, folded n_def]
    have A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C" 
    and PQ: "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" and QP: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n"
    by auto
  from mat_similar_wit_pow[OF mat_similar_wit_char_matrix[OF wit, of ev], of k]
  have wit: "mat_similar_wit (char_matrix A ev ^\<^sub>m k) (char_matrix B ev ^\<^sub>m k) P Q" .
  from A B have cA: "char_matrix A ev ^\<^sub>m k \<in> carrier\<^sub>m n n" 
    and cB: "char_matrix B ev ^\<^sub>m k \<in> carrier\<^sub>m n n" by auto
  hence dim: "dim\<^sub>c (char_matrix A ev ^\<^sub>m k) = n" "dim\<^sub>c (char_matrix B ev ^\<^sub>m k) = n" by auto
  have "dim_gen_eigenspace A ev k = kernel_dim (char_matrix A ev ^\<^sub>m k)"
    unfolding dim_gen_eigenspace_def using A by simp
  also have "\<dots> = kernel_dim (char_matrix B ev ^\<^sub>m k)" unfolding kernel_dim_def dim
    by (rule mat_similar_wit_kernel_dim[OF cA wit])
  also have "\<dots> = dim_gen_eigenspace B ev k" 
    unfolding dim_gen_eigenspace_def using B by simp
  finally show "dim_gen_eigenspace A ev k = dim_gen_eigenspace B ev k" .
qed
  
lemma dim_gen_eigenspace: assumes "jordan_nf A n_as"
  shows "dim_gen_eigenspace A ev k
    = (\<Sum> n \<leftarrow> map fst [(n, e)\<leftarrow>n_as . e = ev]. min k n)"
proof -
  from assms[unfolded jordan_nf_def]
  have sim: "mat_similar A (jordan_matrix n_as)" by auto
  from dim_gen_eigenspace_jordan_matrix[of n_as, folded dim_gen_eigenspace_similar[OF this]]
  show ?thesis .
qed

definition compute_nr_of_jordan_blocks :: "'a mat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  "compute_nr_of_jordan_blocks A ev k = 2 * dim_gen_eigenspace A ev k -
     dim_gen_eigenspace A ev (k - 1) - dim_gen_eigenspace A ev (Suc k)"

text \<open>This lemma finally shows uniqueness of JNFs. Take an arbitrary
  JNF of a matrix $A$, (encoded by the list of Jordan-blocks @{term n_as}),
  then then number of occurrences of each Jordan-Block in @{term n_as} 
  is uniquely determined, namely by @{const compute_nr_of_jordan_blocks}. 
  The condition @{term "k \<noteq> (0 :: nat)"}
  is to ensure that we do not count blocks of dimension 0.\<close>

lemma compute_nr_of_jordan_blocks: assumes jnf: "jordan_nf A n_as"
  and no_0: "k \<noteq> 0"
  shows "compute_nr_of_jordan_blocks A ev k = length (filter (op = (k,ev)) n_as)"
proof -
  from no_0 obtain k1 where k: "k = Suc k1" by (cases k, auto)
  let ?k = "Suc k1" let ?k2 = "Suc ?k"
  let ?dim = "dim_gen_eigenspace A ev"
  let ?sizes = "map fst [(n, e)\<leftarrow>n_as . e = ev]"
  def sizes \<equiv> ?sizes
  let ?two = "length (filter (op = (k, ev)) n_as)"
  have "compute_nr_of_jordan_blocks A ev k = 
    ?dim ?k + ?dim ?k - ?dim k1 - ?dim ?k2" unfolding compute_nr_of_jordan_blocks_def k by simp
  also have "\<dots> = length (filter (op = k) ?sizes)"
    unfolding dim_gen_eigenspace[OF jnf] k sizes_def[symmetric]
  proof (rule sym, induct sizes)
    case (Cons s sizes)
    show ?case
    proof (cases "s = ?k")
      case True
      let ?sum = "\<lambda> k sizes. listsum (map (min k) sizes)"
      let ?len = "\<lambda> sizes. length (filter (op = ?k) sizes)"
      have len: "?len (s # sizes) = Suc (?len sizes)" unfolding True by simp
      have IH: "?len sizes = ?sum ?k sizes + ?sum ?k sizes -
        ?sum k1 sizes - ?sum ?k2 sizes" by (rule Cons)
      have "?sum ?k (s # sizes) + ?sum ?k (s # sizes) -
        ?sum k1 (s # sizes) - ?sum ?k2 (s # sizes)
        = Suc (?sum ?k sizes + ?sum ?k sizes) - 
         (?sum k1 sizes + ?sum ?k2 sizes)"
        using True by simp
      also have "\<dots> = Suc (?sum ?k sizes + ?sum ?k sizes - (?sum k1 sizes + ?sum ?k2 sizes))"
        by (rule Suc_diff_le, induct sizes, auto)
      also have "\<dots> = ?len (s # sizes)" unfolding len IH by simp
      finally show ?thesis by simp
    qed (insert Cons, auto)
  qed simp
  also have "\<dots> = length (filter (op = (k, ev)) n_as)" by (induct n_as, force+)
  finally show ?thesis .
qed

text \<open>One might get more fine-grained and prove the lemma for multisets, 
   so one takes multiplicities into account. For the moment we don't require this for
  complexity analysis, so it remains as future work.\<close>

definition compute_set_of_jordan_blocks :: "'a mat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a)list" where
  "compute_set_of_jordan_blocks A ev \<equiv> let 
     k = Polynomial.order ev (char_poly A);
     as = map (dim_gen_eigenspace A ev) [0 ..< Suc (Suc k)];
     cards = map (\<lambda> k. (k, 2 * as ! k - as ! (k - 1) - as ! Suc k)) [1 ..< Suc k]
     in map (\<lambda> (k,c). (k,ev)) (filter (\<lambda> (k,c). c \<noteq> 0) cards)"

lemma compute_set_of_jordan_blocks: assumes jnf: "jordan_nf A n_as"
  shows "set (compute_set_of_jordan_blocks A ev) = set n_as \<inter> UNIV \<times> {ev} - {0} \<times> UNIV" (is "?C = ?N")
proof -
  note cjb = compute_nr_of_jordan_blocks[OF jnf]
  note d = compute_set_of_jordan_blocks_def Let_def
  def kk \<equiv> "Polynomial.order ev (char_poly A)"
  def as \<equiv> "map (dim_gen_eigenspace A ev) [0 ..< Suc (Suc kk)]"
  def cards \<equiv> "map (\<lambda> k. (k, 2 * as ! k - as ! (k - 1) - as ! Suc k)) [1 ..< Suc kk]"
  have C: "?C = set (map (\<lambda> (k,c). (k,ev)) (filter (\<lambda> (k,c). c \<noteq> 0) cards))"
    unfolding d as_def kk_def cards_def by (rule refl)
  {
    fix i
    assume "i < Suc (Suc kk)"
    hence "as ! i = dim_gen_eigenspace A ev i"
      unfolding as_def by (auto simp del: upt_Suc)
  } note as = this
  (* TODO: perhaps use special code equation, and use inefficient thing in definition *)
  have cards: "cards = map (\<lambda> k. (k, compute_nr_of_jordan_blocks A ev k)) [1 ..< Suc kk]"
    unfolding cards_def
    by (rule map_cong[OF refl], insert as, unfold compute_nr_of_jordan_blocks_def, auto)
  have C: "?C = { (k,ev) | k. compute_nr_of_jordan_blocks A ev k \<noteq> 0 \<and> k \<noteq> 0 \<and> k < Suc kk }"
    unfolding C cards by force
  {
    fix k
    have "(k,ev) \<in> ?C \<longleftrightarrow> (k,ev) \<in> ?N"
    proof (cases "k = 0")
      case True
      thus ?thesis unfolding C by auto
    next
      case False
      show ?thesis
      proof (cases "k < Suc kk")
        case True
        have "length (filter (op = (k, ev)) n_as) \<noteq> 0 \<longleftrightarrow>
          set (filter (op = (k, ev)) n_as) \<noteq> {}" by blast
        have "(k,ev) \<in> ?N \<longleftrightarrow>  set (filter (op = (k, ev)) n_as) \<noteq> {}" using False by auto
        also have "\<dots> \<longleftrightarrow> length (filter (op = (k, ev)) n_as) \<noteq> 0" by blast
        also have "\<dots> \<longleftrightarrow> compute_nr_of_jordan_blocks A ev k \<noteq> 0"
          unfolding compute_nr_of_jordan_blocks[OF jnf False] by simp
        also have "\<dots> \<longleftrightarrow> (k,ev) \<in> ?C" unfolding C using False True by auto
        finally show ?thesis by auto
      next
        case False
        hence "(k,ev) \<notin> ?C" unfolding C by auto
        moreover from False kk_def have k: "k > Polynomial.order ev (char_poly A)" by auto
        with jordan_nf_block_size_order_bound[OF jnf, of k ev]
        have "(k,ev) \<notin> ?N" by auto
        ultimately show ?thesis by simp
      qed
    qed
  }
  thus ?thesis unfolding C by auto
qed
end

end