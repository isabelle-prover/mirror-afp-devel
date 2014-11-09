*** Obsolete ***
section {* Equivalence Relation on Heaps *}

theory Heap_Equivalence
imports Imperative_HOL_Add
begin


text {* We want to apply techniques from separation logic to the total
heap model given through Imperative HOL. Since separation logic
essentially needs an heap model with a possibility to split one heap
into two disjoint parts, we need to introduce partial heaps in
Imperative HOL.  We choose to implement the partial heap by a pair of
an address set and a total heap.  The address set represents the
addresses of the partial heap and the total heap contains their
values.  All values of addresses in the total heap, which are not part
of the address set, should not matter for the partial heap.  For that
reason we build up an equivalence relation on total heaps for a fixed
address set.  The equivalence classes of this relation represent the
possible partial heaps for a fixed address set.  Note that the total
heap in Imperative HOL allows that one address is used for arrays and
references for multiple types, so that our partial heap model may
seems odd.  But the standard monadic combinators given through
Imperative HOL ensure that one address is only used for an array or a
reference of a specific type. *}

text {* Two total heaps are equivalent for a given set of addresses, iff their @{text refs} and @{text arrays} function deliver the same values for all the given addresses. *}

definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" 
  where
  "relH as h h' \<equiv>  
   \<forall>t. \<forall>a \<in> as. refs h t a = refs h' t a \<and> arrays h t a = arrays h' t a"


subsection {* Equivalence Relation*}

text {* As mentioned before, @{text "relH as"} is an equivalence relation on total heaps for every address set @{text as}. *}

-- "Reflexivity"
lemma relH_refl: "relH as h h"
  unfolding relH_def by simp

-- "Symmetry"
lemma relH_sym: "relH as h h' \<Longrightarrow> relH as h' h"
  unfolding relH_def
  by auto

-- "Transitivity"
lemma relH_trans: "\<lbrakk>relH as h1 h2; relH as h2 h3\<rbrakk> \<Longrightarrow> relH as h1 h3"
  unfolding relH_def
  by auto

subsection {* Properties *}

subsubsection {* Subset *}

text {* If two total heaps are equivalent on a given set @{text "bs"} they are also equivalent on every subset of @{text "bs"}. *}
lemma relH_sub:
  assumes "relH bs h h'"
  assumes "as \<subseteq> bs"
  shows "relH as h h'"
using assms unfolding relH_def by auto


subsubsection {* Values *}

text {* If two total heaps form the same partial heap with an address set, than of cause the two total heaps hold for every reference and array in the address set the same value. *}

lemma relH_ref:
  assumes "relH as h h'"
  assumes "addr_of_ref r \<in> as"
  shows "Ref.get h r = Ref.get h' r"
  using assms unfolding relH_def Ref.get_def by auto

lemma relH_array:
  assumes "relH as h h'"
  assumes "addr_of_array r \<in> as"
  shows "Array.get h r = Array.get h' r"
  using assms unfolding relH_def Array.get_def by auto


subsubsection {* Basic Heap Modifications *}

text {* For modifications on a total heap i.e. allocation and updating of a address, we need some lemmas, how the partial heap with a fixed address set is influenced. *}


-- "Changing a value outside the partial heap does not affect the equivalence class."
lemma relH_set_ref: "addr_of_ref r \<notin> as \<Longrightarrow> relH as h (Ref.set r x h)"
  unfolding relH_def Ref.get_def Ref.set_def 
  by auto

-- "Allocation does not affect the equivalence class, if the given address set only contains present addresses of the total heap."
lemma relH_alloc_ref: "as \<subseteq> {a. a < lim h} \<Longrightarrow> relH as h (snd (Ref.alloc x h))"
  unfolding relH_def Ref.alloc_def Ref.set_def
  by (auto simp add: Let_def)


-- "Performing the same changes on equivalent heaps keeps them equivalent."
lemma relH_set_ref_heaps:
  assumes "relH as h h'"
  shows "relH as (Ref.set r x h) (Ref.set r x h')"
  unfolding relH_def apply auto
proof -
  case goal1
  with assms have a: "\<forall>t. refs h t a = refs h' t a" unfolding relH_def by auto
  with goal1 show ?case
    unfolding Ref.set_def by auto  
next
  case goal2
  with assms have a: "\<forall>t. arrays h t a = arrays h' t a" unfolding relH_def by auto
  with goal2 show ?case
    unfolding Ref.set_def by auto
qed 

-- "Changing a value outside the partial heap does not affect the equivalence class."
lemma relH_upd_array: "addr_of_array a \<notin> as \<Longrightarrow> relH as h (Array.update a i x h)"
  unfolding relH_def Array.set_def Array.update_def
  by (auto simp add: Let_def)

-- "Allocation does not affect the equivalence class, if the given address set only contains present addresses of the total heap."
lemma relH_alloc_array: "as \<subseteq> {a. a < lim h} \<Longrightarrow> relH as h (snd (Array.alloc xs h))"
  unfolding relH_def Array.alloc_def Array.set_def
  by (auto simp add: Let_def)

end
