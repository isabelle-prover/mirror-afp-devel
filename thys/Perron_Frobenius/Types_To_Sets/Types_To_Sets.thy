(*  Title:      From_Types_To_Sets.thy
    Author:     Ondřej Kunčar

    Based on O. Kunčar, A. Popescu: From Types to Sets by Local Type Definitions in Higher-Order Logic;
    Available at: http://www21.in.tum.de/~kuncar/documents/kuncar-popescu-t2s2016-extended.pdf
*)
section \<open>From Types to Sets\<close>

text \<open>This theory allows to simulate local type-definitions within proofs.\<close>

theory Types_To_Sets
imports Main
begin

subsection \<open>Rules\<close>

text\<open>The following file implements the Local Typedef Rule (LT).\<close>
ML_file "local_typedef.ML"

text\<open>The following file implements the Unoverloading Rule (UO).\<close>
ML_file "unoverloading.ML"

text\<open>The following file uses an already existing rule to implement internalization
     of type class annotations.\<close>
ML_file "internalize_sort.ML"


subsection \<open>Auxiliary Lemmas\<close>

definition
  pred_fun :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  [simp]: "pred_fun A B = (\<lambda>f. \<forall>x. A x \<longrightarrow> B (f x))"

lemma Domainp_prod_fun_eq[relator_domain]:
  includes lifting_syntax
  assumes 1: "left_unique T"
  shows "Domainp (T ===> S) = pred_fun (Domainp T) (Domainp S)"
using 1 unfolding rel_fun_def Domainp_iff[abs_def] left_unique_def fun_eq_iff
apply auto
apply blast
apply (subst all_comm)
apply (rule choice)
apply blast
done

context
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
begin
  lemma type_definition_Domainp: "Domainp T = (\<lambda>x. x \<in> A)" 
  proof -
    interpret type_definition Rep Abs A by(rule type)
    show ?thesis
      unfolding Domainp_iff[abs_def] T_def fun_eq_iff
      by (metis Abs_inverse Rep)
  qed
end

lemma list_all_lists: "Collect (list_all (\<lambda>x. x \<in> B)) = lists B"
proof -
  have "(list_all (\<lambda>x. x \<in> B)) l \<longleftrightarrow> l \<in> lists B" for l
  by (induct l) auto
  then show ?thesis by blast
qed

end