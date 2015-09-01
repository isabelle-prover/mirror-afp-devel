(*  
    Title:      Dual_Order.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)


section "Dual Order"

theory Dual_Order
  imports Main
begin

subsection{*Interpretation of dual order based on order*}

text{*Computable Greatest value operator for finite linorder classes. Based on @{thm "Least_def"}*}

interpretation dual_order: order "(op \<ge>)::('a::{order}=>'a=>bool)" "(op >)"
proof 
  fix x y::"'a::{order}" show "(y < x) = (y \<le> x \<and> \<not> x \<le> y)" using less_le_not_le .
  show "x \<le> x" using order_refl .
  fix z show "y \<le> x \<Longrightarrow> z \<le> y \<Longrightarrow> z \<le> x" using order_trans .
next
  fix x y::"'a::{order}" show "y \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> x = y" by (metis eq_iff)
qed

interpretation dual_linorder: linorder "(op \<ge>)::('a::{linorder}=>'a=>bool)" "(op >)" 
proof
  fix x y::'a show "y \<le> x \<or> x \<le> y" using linear .
qed

lemma wf_wellorderI2:
  assumes wf: "wf {(x::'a::ord, y). y < x}"
  assumes lin: "class.linorder (\<lambda>(x::'a) y::'a. y \<le> x) (\<lambda>(x::'a) y::'a. y < x)"
  shows "class.wellorder (\<lambda>(x::'a) y::'a. y \<le> x) (\<lambda>(x::'a) y::'a. y < x)"
  using lin unfolding class.wellorder_def apply (rule conjI)
  apply (rule class.wellorder_axioms.intro) by (blast intro: wf_induct_rule [OF wf])


lemma (in preorder) tranclp_less': "op >\<^sup>+\<^sup>+ = op >"
  by(auto simp add: fun_eq_iff intro: less_trans elim: tranclp.induct)

interpretation dual_wellorder: wellorder "(op \<ge>)::('a::{linorder, finite}=>'a=>bool)" "(op >)" 
proof (rule wf_wellorderI2)
  show "wf {(x :: 'a, y). y < x}"
    by(auto simp add: trancl_def tranclp_less' intro!: finite_acyclic_wf acyclicI)
  show "class.linorder (\<lambda>(x::'a) y::'a. y \<le> x) (\<lambda>(x::'a) y::'a. y < x)"
    unfolding class.linorder_def unfolding class.linorder_axioms_def unfolding class.order_def 
    unfolding class.preorder_def unfolding class.order_axioms_def by auto  
qed

subsection{*Computable greatest operator*}

definition Greatest' :: "('a::order \<Rightarrow> bool) \<Rightarrow> 'a::order" (binder "GREATEST' " 10)
  where "Greatest' P = dual_order.Least P"

text{*The following THE operator will be computable when the underlying type belongs to a suitable 
      class (for example, Enum).*}

lemma [code]: "Greatest' P = (THE x::'a::order. P x \<and> (\<forall>y::'a::order. P y \<longrightarrow> y \<le> x))"
  unfolding Greatest'_def ord.Least_def by fastforce

lemmas Greatest'I2_order = dual_order.LeastI2_order[folded Greatest'_def]
lemmas Greatest'_equality = dual_order.Least_equality[folded Greatest'_def]
lemmas Greatest'I = dual_wellorder.LeastI[folded Greatest'_def]
lemmas Greatest'I2_ex = dual_wellorder.LeastI2_ex[folded Greatest'_def]
lemmas Greatest'I2_wellorder = dual_wellorder.LeastI2_wellorder[folded Greatest'_def]
lemmas Greatest'I_ex = dual_wellorder.LeastI_ex[folded Greatest'_def]
lemmas not_greater_Greatest' = dual_wellorder.not_less_Least[folded Greatest'_def]
lemmas Greatest'I2 = dual_wellorder.LeastI2[folded Greatest'_def]
lemmas Greatest'_ge = dual_wellorder.Least_le[folded Greatest'_def]

end
