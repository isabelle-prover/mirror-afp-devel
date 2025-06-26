theory Test_Embed_Tree
imports
  Lazy_Case.Lazy_Case
  "../Preproc/Embed"
  "../Preproc/Eval_Instances"
  "HOL-Library.Tree"
begin

derive evaluate tree

text \<open>Integers are not supported out of the box, so we have to rewrite some code equations.\<close>

definition nat_diff :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where nat_diff_abs_int: \<open>nat_diff m n = nat \<bar>int m - int n\<bar>\<close>

lemma nat_diff_simps [simp, code]:
  \<open>nat_diff 0 n = n\<close>
  \<open>nat_diff m 0 = m\<close>
  \<open>nat_diff (Suc m) (Suc n) = nat_diff m n\<close>
  by (simp_all add: nat_diff_abs_int)

lemma [code]:
  \<open>wbalanced Leaf \<longleftrightarrow> True\<close>
  \<open>wbalanced (Node l x r) \<longleftrightarrow> nat_diff (size l) (size r) \<le> 1 \<and> wbalanced l \<and> wbalanced r\<close>
  by (auto simp add: nat_diff_abs_int)

text \<open>Sets are also unsupported, so we have to rewrite @{const set_tree} to use @{const inorder}.\<close>

lemma [code_unfold]:
  \<open>(\<forall>x \<in> set_tree l. P x) \<longleftrightarrow> list_all P (inorder l)\<close>
  by (simp add: list_all_iff)

lemma [code]:
  \<open>heap Leaf \<longleftrightarrow> True\<close>
  \<open>heap (Node l m r) \<longleftrightarrow> heap l \<and> heap r \<and> (\<forall>x \<in> set_tree l. m \<le> x) \<and> (\<forall>x \<in> set_tree r. m \<le> x)\<close>
  by auto

text \<open>@{term "(-)"} on @{typ nat} is not pattern compatible\<close>

declassify valid: wbalanced ipl preorder inorder postorder bst_wrt heap
thm valid

experiment begin

code_thms Tree_wbalanced (* FIXME bogus error message when using the non-dict-eliminated constant *)
embed (eval) test1 is Tree_wbalanced .

end

experiment begin

code_thms Tree_ipl Tree_preorder Tree_inorder Tree_postorder
embed (eval) test2 is Tree_ipl Tree_preorder Tree_inorder Tree_postorder .

end

(* FIXME auto-derive these things? *)
derive evaluate
  Orderings_ord__dict
  Orderings_preorder__dict
  Orderings_order__dict
  Orderings_linorder__dict

experiment begin

code_thms Tree_bst__wrt Tree_linorder__class_heap
embed (eval) test3 is Tree_bst__wrt Tree_linorder__class_heap .

end

end
