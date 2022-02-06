section \<open>Auxiliary Properties on Matrices (to be moved)\<close>

text \<open>All of the following theorems should be moved to Matrix-theory.\<close>
theory Move_To_Matrix
  imports Jordan_Normal_Form.Matrix
begin

lemma transpose_vec_mult_scalar: 
  fixes A :: "'a :: comm_semiring_0 mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and x: "x \<in> carrier_vec nc" 
    and y: "y \<in> carrier_vec nr" 
  shows "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)"
proof -
  have "A\<^sup>T *\<^sub>v y = vec nc (\<lambda>i. col A i \<bullet> y)" 
    unfolding mult_mat_vec_def using A by auto
  also have "\<dots> = vec nc (\<lambda>i. y \<bullet> col A i)" 
    by (intro eq_vecI, simp, rule comm_scalar_prod[OF _ y], insert A, auto)
  also have "\<dots> \<bullet> x = y \<bullet> vec nr (\<lambda>i. row A i \<bullet> x)" 
    by (rule assoc_scalar_prod[OF y A x])
  also have "vec nr (\<lambda>i. row A i \<bullet> x) = A *\<^sub>v x"
    unfolding mult_mat_vec_def using A by auto
  finally show ?thesis .
qed

lemma four_block_mat_mult_vec:
  assumes A: "A : carrier_mat nr1 nc1"
      and B: "B : carrier_mat nr1 nc2" 
      and C: "C : carrier_mat nr2 nc1" 
      and D: "D : carrier_mat nr2 nc2"
      and a: "a : carrier_vec nc1"
      and d: "d : carrier_vec nc2"
  shows "four_block_mat A B C D *\<^sub>v (a @\<^sub>v d) = (A *\<^sub>v a + B *\<^sub>v d) @\<^sub>v (C *\<^sub>v a + D *\<^sub>v d)"
    (is "?ABCD *\<^sub>v _ = ?r")
proof
  have ABCD: "?ABCD : carrier_mat (nr1+nr2) (nc1+nc2)" using four_block_carrier_mat[OF A D].
  fix i assume i: "i < dim_vec ?r"
  show "(?ABCD *\<^sub>v (a @\<^sub>v d)) $ i = ?r $ i" (is "?li = _")
  proof (cases "i < nr1")
    case True
      have "?li = (row A i @\<^sub>v row B i) \<bullet> (a @\<^sub>v d)"
        using A row_four_block_mat[OF A B C D] True by simp
      also have "... = row A i \<bullet> a + row B i \<bullet> d"
        apply (rule scalar_prod_append) using A B D a d True by auto
      finally show ?thesis using A B True by auto
    next case False
      let ?i = "i - nr1"
      have "?li = (row C ?i @\<^sub>v row D ?i) \<bullet> (a @\<^sub>v d)"
        using i row_four_block_mat[OF A B C D] False A B C D by simp
      also have "... = row C ?i \<bullet> a + row D ?i \<bullet> d"
        apply (rule scalar_prod_append) using A B C D a d False by auto
      finally show ?thesis using A B C D False i by auto
  qed
qed (insert A B, auto)

lemma mat_of_row_uminus: "mat_of_row (- v) = - mat_of_row v"
  by auto

text \<open>This one already exists, but with a non-required carrier assumption, cf.
  @{thm transpose_uminus}\<close>
lemma transpose_uminus: "(- A)\<^sup>T  = - (A\<^sup>T)"
  by auto

end