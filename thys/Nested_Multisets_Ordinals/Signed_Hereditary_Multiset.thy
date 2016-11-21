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

typedef zhmultiset = "UNIV :: hmultiset zmultiset set"
  morphisms zhmsetmset ZHMSet
  by simp

lemmas ZHMSet_inverse[simp] = ZHMSet_inverse[OF UNIV_I]
lemmas ZHMSet_inject[simp] = ZHMSet_inject[OF UNIV_I UNIV_I]

declare
  zhmsetmset_inverse [simp]
  zhmsetmset_inject [simp]

setup_lifting type_definition_zhmultiset


subsection \<open>Multiset Order\<close>

instantiation zhmultiset :: linorder
begin

lift_definition less_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> bool" is "op <" .
lift_definition less_eq_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> bool" is "op \<le>" .

instance
  by (intro_classes; transfer) auto

end

lemmas ZHMSet_less[simp] = less_zhmultiset.abs_eq
lemmas ZHMSet_le[simp] = less_eq_zhmultiset.abs_eq
lemmas zhmsetmset_less[simp] = less_zhmultiset.rep_eq[symmetric]
lemmas zhmsetmset_le[simp] = less_eq_zhmultiset.rep_eq[symmetric]


subsection \<open>Embedding and Projections of Syntactic Ordinals\<close>

abbreviation zhmset_of_hmset :: "hmultiset \<Rightarrow> zhmultiset" where
  "zhmset_of_hmset M \<equiv> ZHMSet (zmset_of_mset (hmsetmset M))"

lemma zhmset_of_hmset_inject[simp]: "zhmset_of_hmset M = zhmset_of_hmset N \<longleftrightarrow> M = N"
  by simp

lemma zhmset_of_hmset_less: "zhmset_of_hmset M < zhmset_of_hmset N \<longleftrightarrow> M < N"
  by (simp add: zmset_of_mset_less)

lemma zhmset_of_hmset_le: "zhmset_of_hmset M \<le> zhmset_of_hmset N \<longleftrightarrow> M \<le> N"
  by (simp add: zmset_of_mset_le)

abbreviation hmset_pos :: "zhmultiset \<Rightarrow> hmultiset" where
  "hmset_pos M \<equiv> HMSet (mset_pos (zhmsetmset M))"

abbreviation hmset_neg :: "zhmultiset \<Rightarrow> hmultiset" where
  "hmset_neg M \<equiv> HMSet (mset_neg (zhmsetmset M))"

end
