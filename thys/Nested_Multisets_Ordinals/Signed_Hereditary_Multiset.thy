(*  Title:       Signed Hereditar(il)y (Finite) Multisets
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Signed Hereditar(il)y (Finite) Multisets\<close>

theory Signed_Hereditary_Multiset
imports Signed_Multiset Hereditary_Multiset
begin


subsection \<open>Type Definition\<close>

typedef yhmultiset = "UNIV :: hmultiset zmultiset set"
  morphisms zhmsetmset ZHMSet
  by simp

lemmas ZHMSet_inverse[simp] = ZHMSet_inverse[OF UNIV_I]
lemmas ZHMSet_inject[simp] = ZHMSet_inject[OF UNIV_I UNIV_I]

declare
  zhmsetmset_inverse [simp]
  zhmsetmset_inject [simp]

setup_lifting type_definition_yhmultiset

instantiation yhmultiset :: linorder
begin

lift_definition less_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> bool" is "op <" .
lift_definition less_eq_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> bool" is "op \<le>" .

instance
  by (standard; transfer) auto

end

lemma
  zhmsetmset_less[simp]: "zhmsetmset M < zhmsetmset N \<longleftrightarrow> M < N" and
  zhmsetmset_le[simp]: "zhmsetmset M \<le> zhmsetmset N \<longleftrightarrow> M \<le> N"
  by (transfer, rule refl)+

declare
  less_yhmultiset.abs_eq [simp]
  less_eq_yhmultiset.abs_eq [simp]
  less_yhmultiset.rep_eq [symmetric, simp]
  less_eq_yhmultiset.rep_eq [symmetric, simp]

end
