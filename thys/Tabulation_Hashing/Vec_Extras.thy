theory Vec_Extras
imports
  "HOL-Analysis.Finite_Cartesian_Product"
  Fixed_Length_Vector.Fixed_Length_Vector
begin

unbundle no Finite_Cartesian_Product.vec_syntax
unbundle Fixed_Length_Vector.vec_syntax

setup_lifting type_definition_vec

text \<open>The most important lemmas to know when working with @{type vec} are
\begin{itemize}
  \item @{thm [source] vec_of_list_inject}: @{thm vec_of_list_inject[no_vars]}
  \item @{thm [source] vec_of_list_inverse}: @{thm vec_of_list_inverse[no_vars]}
  \item @{thm [source] nth_vec.rep_eq}: @{thm nth_vec.rep_eq[no_vars]}
\end{itemize}

Tip:
When using @{const vec_of_list} to create a vector @{term "v :: ('a, 'b) vec"} from
@{term "xs :: 'a list"}, it is essential to separately prove that
@{term "xs \<in> {xs. length xs = CARD('b)}"} for above lemmas to apply\<close>

lift_definition vec_of_fcp :: "('a, 'b::{finite, index1}) Finite_Cartesian_Product.vec \<Rightarrow>
                               ('a, 'b) Fixed_Length_Vector.vec" is
  \<open>\<lambda>x. map (\<lambda>i. Finite_Cartesian_Product.vec_nth x i :: 'a) (indexes :: 'b list)\<close> by simp

definition fcp_of_vec :: "('a, 'b::{finite, index1}) Fixed_Length_Vector.vec \<Rightarrow>
                          ('a, 'b) Finite_Cartesian_Product.vec" where
  \<open>fcp_of_vec \<equiv> \<lambda>x. Finite_Cartesian_Product.vec_lambda (\<lambda>i. x $ i)\<close>
lift_definition (*tag:unused*) enumerate_vec :: "nat \<Rightarrow> ('a,  'b) Fixed_Length_Vector.vec \<Rightarrow>
                                                (nat \<times> 'a, 'b) Fixed_Length_Vector.vec" is
  \<open>List.indexed_from\<close> by simp

lemma infinite_UNIV_vec:
  assumes "infinite (UNIV :: 'a set)" "finite (UNIV :: 'b set)"
  shows "infinite (UNIV :: ('a,'b) Fixed_Length_Vector.vec set)"
proof -
  let ?UNIVA = "UNIV :: 'a set"
  let ?UNIVB = "UNIV :: 'b set"
  let ?UNIVV = "UNIV :: ('a,'b) Fixed_Length_Vector.vec set"

  have "CARD('b) > 0" using assms(2) finite_UNIV_card_ge_0 by blast
  then have "(\<lambda>x. nth_vec' x 0) ` ?UNIVV = ?UNIVA"
    apply (intro surjI[where ?f = "\<lambda>x. replicate_vec x"])
    by (simp add: nth_vec'.rep_eq)
  moreover have "card ((\<lambda>x. nth_vec' x 0) ` ?UNIVV) \<le> card ?UNIVV"
    by (simp add: calculation assms)
  ultimately show ?thesis by (metis assms finite_imageI)
qed

lemma infinite_index_UNIV_vec:
  assumes "infinite (UNIV :: 'b set)"
  shows "(UNIV :: ('a,'b) Fixed_Length_Vector.vec set) = {vec_of_list []}"
  by (metis (mono_tags, lifting) UNIV_eq_I assms card.infinite insertI1 length_0_conv
      list_of_vec_inverse list_of_vec_length)

(* this lemma probably should be added to the Fixed_Length_Vector AFP *)
lemma card_UNIV_vec:
  shows "CARD(('a, 'b) Fixed_Length_Vector.vec) = CARD('a) ^ CARD('b)" (is "?lhs = ?rhs")
proof -
  let ?UNIVA = "UNIV :: 'a set"
  let ?UNIVB = "UNIV :: 'b set"
  let ?UNIVV = "UNIV :: ('a,'b) Fixed_Length_Vector.vec set"

  consider "finite ?UNIVA" | "infinite ?UNIVA" "finite ?UNIVB" | "infinite ?UNIVA" "infinite ?UNIVB"
    by fast
  then show ?thesis
  proof cases
    case 1
    have "?lhs = card ({xs. length xs = CARD('b)} :: 'a list set)"
      using Fixed_Length_Vector.vec.type_definition_vec type_definition.card by blast
    also have "\<dots> = ?rhs" using card_lists_length_eq[of ?UNIVA, OF 1] by simp
    finally show ?thesis .
  next
    case 2
    have "infinite ?UNIVV" using infinite_UNIV_vec[OF 2] .
    then show ?thesis using 2 finite_UNIV_card_ge_0 by (simp add: card_eq_0_iff)
  next
    case 3
    have "card ?UNIVV = Suc 0" unfolding infinite_index_UNIV_vec[OF 3(2)] by simp
    then show ?thesis using 3 by (simp add: card_eq_0_iff)
  qed
qed

lemma (in index1) from_index_neq [simp]:
  assumes "a \<noteq> b"
  shows "from_index a \<noteq> from_index b"
  by (metis assms local.from_to_index)

lemma list_of_vec_not_empty [simp]:
  fixes xs :: "('a, 'b :: index1) Fixed_Length_Vector.vec"
  shows "list_of_vec xs \<noteq> []"
  by (metis from_index_bound gr_implies_not0 list.size(3) list_of_vec_length)

(* for use with the subst tactic *)
lemma (*tag:unused*) id_take_nth_drop_vec:
  fixes xs :: "('a, 'b :: index1) Fixed_Length_Vector.vec"
  assumes "i < CARD('b)"
  shows
    "xs = vec_of_list (
      take i (list_of_vec xs) @
      list_of_vec xs ! i #
      drop (Suc i) (list_of_vec xs))"
  by (simp add: Cons_nth_drop_Suc assms)

(* for use with the subst tactic *)
lemma (*tag:unused*) id_take_nth_drop_vec':
  fixes xs :: "('a, 'b :: index1) Fixed_Length_Vector.vec"
  assumes "i < CARD('b)"
  shows
    "xs = vec_of_list (
      take i (list_of_vec xs) @
      xs $ to_index i #
      drop (Suc i) (list_of_vec xs))"
  by (simp add: Cons_nth_drop_Suc assms nth_vec.rep_eq to_from_index)

(* for nth-based comparison *)
lemma (*tag:unused*) nth_not_mem_enumerate:
  assumes "y ! i \<noteq> x ! i"
  shows "(i, y ! i) \<notin> set (List.indexed_from 0 x)"
  apply (subst in_set_conv_nth, clarsimp)
  using assms nth_indexed_from_eq by fastforce

lemma (*tag:unused*) nth_not_mem_enumerate_take:
  assumes "y ! j \<noteq> x ! j"
  shows "(j, y ! j) \<notin> set (List.indexed_from 0 (take i x))"
  apply (subst in_set_conv_nth, clarsimp)
  by (metis arith_simps(49) assms length_take min_less_iff_conj nth_indexed_from_eq nth_take
      prod.sel(1,2))

lemma (*tag:unused*) nth_not_mem_enumerate_drop:
  assumes "y ! j \<noteq> x ! j"
  shows "(j, y ! j) \<notin> set (List.indexed_from (Suc i) (drop (Suc i) x))"
  apply (subst in_set_conv_nth, clarsimp)
  by (metis assms fst_eqD length_drop linorder_not_le nat_diff_split not_less_zero nth_drop
      nth_indexed_from_eq snd_eqD)

lemma (*tag:unused*) nth_enumerate_eq_vec:
  fixes xs :: "('a, 'b :: index1) Fixed_Length_Vector.vec"
  assumes "m < CARD('b)"
  shows "enumerate_vec n xs $ to_index m = (n + m, xs $ to_index m)"
  by (simp add: nth_vec.rep_eq index.to_from_index index_axioms assms enumerate_vec.rep_eq
  nth_indexed_from_eq)

lemma (*tag:unused*) in_set_enumerate_eq_vec:
  fixes xs :: "('a, 'b :: index1) Fixed_Length_Vector.vec"
  shows "p \<in> set_vec (enumerate_vec n xs) \<longleftrightarrow>
         n \<le> fst p \<and> fst p < CARD('b) + n \<and> xs $ to_index (fst p - n) = snd p"
  apply (simp add:
    in_set_indexed_from_eq nth_vec.rep_eq set_vec.rep_eq index.to_from_index
    index_axioms enumerate_vec.rep_eq nth_indexed_from_eq)
  by (metis less_diff_conv2 to_from_index)

lemma inj_vec_of_fcp:
  shows "inj vec_of_fcp"
  apply (clarsimp
    intro!: injI
    simp: vec_of_fcp_def vec_of_list_inject indexes_def vec_eq_iff Ball_def)
  by (metis from_to_index from_index_bound)

lemma inj_fcp_of_vec:
  shows "inj fcp_of_vec"
  by (auto intro!: injI vec_cong simp: fcp_of_vec_def)

lemma fcp_of_vec_inverse:
  shows "vec_of_fcp (fcp_of_vec x) = x"
  apply (simp add: vec_of_fcp_def fcp_of_vec_def)
  by (metis UNIV_I vec_explode vec_lambda.abs_eq vec_lambda_inverse)

lemma vec_of_fcp_inverse:
  shows "fcp_of_vec (vec_of_fcp x) = x"
  apply (simp add: vec_of_fcp_def fcp_of_vec_def)
  by (metis vec_lambda.abs_eq vec_lambda_nth vec_lambda_unique)

lemma surj_vec_of_fcp:
  shows "surj vec_of_fcp"
  using fcp_of_vec_inverse by (intro surjI)

lemma surj_fcp_of_vec:
  shows "surj fcp_of_vec"
  using vec_of_fcp_inverse by (intro surjI)

lemma bij_vec_of_fcp:
  shows "bij vec_of_fcp"
  by (intro bijI inj_vec_of_fcp surj_vec_of_fcp)

lemma bij_fcp_of_vec:
  shows "bij fcp_of_vec"
  by (intro bijI inj_fcp_of_vec surj_fcp_of_vec)

unbundle no Fixed_Length_Vector.vec_syntax
end (* theory *)
