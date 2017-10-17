(* Author: Thiemann *)
section \<open>Perron-Frobenius Theorem\<close>

subsection \<open>Auxiliary Notions\<close>

text \<open>We define notions like non-negative real-valued matrix, both
  in JNF and in HMA. These notions will be linked via HMA-connect.\<close>

theory Perron_Frobenius_Aux
imports HMA_Connect
begin

definition real_nonneg_mat :: "complex mat \<Rightarrow> bool" where
  "real_nonneg_mat A \<equiv> \<forall> a \<in> elements_mat A. a \<in> \<real> \<and> Re a \<ge> 0"

definition real_nonneg_vec :: "complex Matrix.vec \<Rightarrow> bool" where
  "real_nonneg_vec v \<equiv> \<forall> a \<in> vec_elements v. a \<in> \<real> \<and> Re a \<ge> 0"

definition real_non_neg_vec :: "complex ^ 'n \<Rightarrow> bool" where
  "real_non_neg_vec v \<equiv> (\<forall> a \<in> vec_elements_h v. a \<in> \<real> \<and> Re a \<ge> 0)" 

definition real_non_neg_mat :: "complex ^ 'nr ^ 'nc \<Rightarrow> bool" where
  "real_non_neg_mat A \<equiv> (\<forall> a \<in> elements_mat_h A. a \<in> \<real> \<and> Re a \<ge> 0)" 

lemma real_non_neg_matD: assumes "real_non_neg_mat A"
  shows "A $h i $h j \<in> \<real>" "Re (A $h i $h j) \<ge> 0" 
  using assms unfolding real_non_neg_mat_def elements_mat_h_def by auto

definition nonneg_mat :: "'a :: linordered_idom mat \<Rightarrow> bool" where
  "nonneg_mat A \<equiv> \<forall> a \<in> elements_mat A. a \<ge> 0"

definition non_neg_mat :: "'a :: linordered_idom ^ 'nr ^ 'nc \<Rightarrow> bool" where
  "non_neg_mat A \<equiv> (\<forall> a \<in> elements_mat_h A. a \<ge> 0)" 


context includes lifting_syntax
begin

lemma HMA_real_non_neg_mat [transfer_rule]:
  "((HMA_M :: complex mat \<Rightarrow> complex ^ 'nc ^ 'nr \<Rightarrow> bool) ===> op =) 
  real_nonneg_mat real_non_neg_mat"
  unfolding real_nonneg_mat_def[abs_def] real_non_neg_mat_def[abs_def]
  by transfer_prover

lemma HMA_real_non_neg_vec [transfer_rule]:
  "((HMA_V :: complex Matrix.vec \<Rightarrow> complex ^ 'n \<Rightarrow> bool) ===> op =) 
  real_nonneg_vec real_non_neg_vec"
  unfolding real_nonneg_vec_def[abs_def] real_non_neg_vec_def[abs_def]
  by transfer_prover

lemma HMA_non_neg_mat [transfer_rule]:
  "((HMA_M :: 'a :: linordered_idom mat \<Rightarrow> 'a ^ 'nc ^ 'nr \<Rightarrow> bool) ===> op =) 
  nonneg_mat non_neg_mat"
  unfolding nonneg_mat_def[abs_def] non_neg_mat_def[abs_def]
  by transfer_prover

end

primrec matpow :: "'a::semiring_1^'n^'n \<Rightarrow> nat \<Rightarrow> 'a^'n^'n" where
  matpow_0:   "matpow A 0 = mat 1" |
  matpow_Suc: "matpow A (Suc n) = (matpow A n) ** A"

context includes lifting_syntax
begin  
lemma HMA_pow_mat[transfer_rule]:
  "((HMA_M ::'a::{semiring_1} mat \<Rightarrow> 'a^'n^'n \<Rightarrow> bool) ===> op = ===> HMA_M) pow_mat matpow"
proof -
  {
    fix A :: "'a mat" and A' :: "'a^'n^'n" and n :: nat
    assume [transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim_row A = CARD('n)" unfolding HMA_M_def by simp
    have "HMA_M (pow_mat A n) (matpow A' n)"
    proof (induct n)
      case (Suc n)
      note [transfer_rule] = this
      show ?case by (simp, transfer_prover)
    qed (simp, transfer_prover)
  }
  thus ?thesis by blast
qed
end


end
