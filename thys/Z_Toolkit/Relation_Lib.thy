section \<open> Meta-theory for Relation Library \<close>

theory Relation_Lib
  imports
    Countable_Set_Extra Positive Infinity Enum_Type Record_Default_Instance Def_Const
    Relation_Extra Partial_Fun Partial_Inj Finite_Fun Finite_Inj Total_Fun List_Extra
    Bounded_List Tabulate_Command
begin 

text \<open> This theory marks the boundary between reusable library utilities and the creation of the
  Z notation. We avoid overriding any HOL syntax up until this point, but we do supply some optional 
  bundles. \<close>

lemma if_eqE [elim!]: "\<lbrakk> (if b then e else f) = v; \<lbrakk> b; e = v \<rbrakk> \<Longrightarrow> P; \<lbrakk> \<not> b; f = v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases b, auto)

bundle Z_Type_Syntax
begin

type_notation bool ("\<bool>")
type_notation nat ("\<nat>")
type_notation int ("\<int>")
type_notation rat ("\<rat>")
type_notation real ("\<real>")

type_notation set ("\<bbbP> _" [999] 999)

type_notation tfun (infixr "\<rightarrow>" 0)

notation Pow ("\<bbbP>")
notation Fpow ("\<bbbF>")

end

class refine =
  fixes ref_by :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
  and sref_by :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<sqsubset>" 50)
  assumes ref_by_order: "class.preorder (\<sqsubseteq>) (\<sqsubset>)"

interpretation ref_preorder: preorder "(\<sqsubseteq>)" "(\<sqsubset>)"
  by (fact ref_by_order)

lemma ref_by_trans [trans]: "\<lbrakk> P \<sqsubseteq> Q; Q \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<sqsubseteq> R"
  using ref_preorder.dual_order.trans by auto

abbreviation (input) refines (infix "\<sqsupseteq>" 50) where "Q \<sqsupseteq> P \<equiv> P \<sqsubseteq> Q"
abbreviation (input) srefines (infix "\<sqsupset>" 50) where "Q \<sqsupset> P \<equiv> P \<sqsubset> Q"

instantiation "bool" :: refine
begin

definition "ref_by_bool P Q = (Q \<longrightarrow> P)"
definition "sref_by_bool P Q = (\<not> Q \<and> P)"

instance by (intro_classes, unfold_locales, auto simp add: ref_by_bool_def sref_by_bool_def)

end

instantiation "fun" :: (type, refine) refine
begin

definition ref_by_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where "ref_by_fun f g = (\<forall> x. f(x) \<sqsubseteq> g(x))"
definition sref_by_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where "sref_by_fun f g = (f \<sqsubseteq> g \<and> \<not> (g \<sqsubseteq> f))"

instance 
  by (intro_classes, unfold_locales)
     (auto simp add: ref_by_fun_def sref_by_fun_def ref_preorder.less_le_not_le intro: ref_preorder.order.trans)
end

end