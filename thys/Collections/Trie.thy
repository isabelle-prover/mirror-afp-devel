(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Tries without invariants} *}
theory Trie imports
  Trie_Impl
begin

(*<*)
lemma rev_rev_image: "rev ` rev ` A = A"
by(auto intro: rev_image_eqI[where x="rev y", standard])
(*>*)

subsection {* Abstract type definition *}

typedef (open) ('key, 'val) trie = 
  "{t :: ('key, 'val) Trie_Impl.trie. trie_invar t}"
  morphisms impl_of Trie
proof
  show "Trie_Impl.empty \<in> ?trie" by(simp)
qed

lemma trie_invar_impl_of [simp, intro]: "trie_invar (impl_of t)"
using impl_of[of t] by simp

lemma Trie_impl_of [code abstype]: "Trie (impl_of t) = t"
by(rule impl_of_inverse)

subsection {* Primitive operations *}

definition empty :: "('key, 'val) trie"
where "empty = Trie (Trie_Impl.empty)"

definition update :: "'key list \<Rightarrow> 'val \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where "update ks v t = Trie (Trie_Impl.update (impl_of t) ks v)"

definition delete :: "'key list \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where "delete ks t = Trie (Trie_Impl.delete (impl_of t) ks)"

definition lookup :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> 'val option"
where "lookup t = Trie_Impl.lookup (impl_of t)"

definition isEmpty :: "('key, 'val) trie \<Rightarrow> bool"
where "isEmpty t = Trie_Impl.isEmpty (impl_of t)"

definition iteratei :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('key list \<Rightarrow> 'val \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('key, 'val) trie \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where "iteratei c f t = Trie_Impl.iteratei c (f o rev) (impl_of t)"

lemma impl_of_empty [code abstract]: "impl_of empty = Trie_Impl.empty"
by(simp add: empty_def Trie_inverse)

lemma impl_of_update [code abstract]: "impl_of (update ks v t) = Trie_Impl.update (impl_of t) ks v"
by(simp add: update_def Trie_inverse trie_invar_update)

lemma impl_of_delete [code abstract]: "impl_of (delete ks t) = Trie_Impl.delete (impl_of t) ks"
by(simp add: delete_def Trie_inverse trie_invar_delete)

subsection {* Correctness of primitive operations *}

lemma lookup_empty [simp]: "lookup empty = Map.empty"
by(simp add: lookup_def empty_def Trie_inverse)

lemma lookup_update [simp]: "lookup (update ks v t) = (lookup t)(ks \<mapsto> v)"
by(simp add: lookup_def update_def Trie_inverse trie_invar_update lookup_update')

lemma lookup_delete [simp]: "lookup (delete ks t) = (lookup t)(ks := None)"
by(simp add: lookup_def delete_def Trie_inverse trie_invar_delete lookup_delete')

lemma isEmpty_lookup: "isEmpty t \<longleftrightarrow> lookup t = Map.empty"
by(simp add: isEmpty_def lookup_def isEmpty_lookup_empty)

lemma finite_dom_lookup: "finite (dom (lookup t))"
by(simp add: lookup_def finite_dom_trie_lookup)

lemma iteratei_correct:
  assumes I: "I (dom (lookup m)) \<sigma>0"
  and step: "\<And>k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; lookup m k = Some v; it \<subseteq> dom (lookup m); I it \<sigma> \<rbrakk>
             \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  shows "I {} (iteratei c f m \<sigma>0) \<or>
        (\<exists>it\<subseteq>dom (lookup m). it \<noteq> {} \<and> \<not> c (iteratei c f m \<sigma>0) \<and> I it (iteratei c f m \<sigma>0))"
proof -
  let ?I = "\<lambda>it \<sigma>. I (rev ` it) \<sigma>"
  note trie_invar_impl_of[of m]
  moreover
  from I have "?I (rev ` (dom (lookup m))) \<sigma>0" by(simp add: rev_rev_image)
  moreover {
    fix k v it \<sigma>
    assume "c \<sigma>" "k \<in> it" "lookup m (rev k) = Some v" "it \<subseteq> rev ` dom (lookup m)" "?I it \<sigma>"
    hence "I (rev ` it - {rev k}) (f (rev k) v \<sigma>)"
      by -(rule step, auto)
    hence "?I (it - {k}) ((f o rev) k v \<sigma>)" by(simp add: image_set_diff) }
  ultimately 
  have "?I {} (iteratei c f m \<sigma>0) \<or>
        (\<exists>it\<subseteq>rev ` dom (lookup m). it \<noteq> {} \<and> \<not> c (iteratei c f m \<sigma>0) \<and> ?I it (iteratei c f m \<sigma>0))"
    (is "?terminate \<or> ?interrupt")
    unfolding iteratei_def lookup_def by(rule Trie_Impl.trie_iteratei_correct)
  thus ?thesis
  proof
    assume "?terminate"
    thus ?thesis by simp
  next
    assume "?interrupt" (is "\<exists>it. ?P it")
    then obtain it where "?P it" ..
    hence "rev ` it \<subseteq> dom (lookup m)" "rev ` it \<noteq> {}" "\<not> c (iteratei c f m \<sigma>0)" "I (rev ` it) (iteratei c f m \<sigma>0)"
      by auto
    thus ?thesis by blast
  qed
qed 

subsection {* Type classes *}

instantiation trie :: (equal, equal) equal begin

definition "equal_class.equal (t :: ('a, 'b) trie) t' = (impl_of t = impl_of t')"

instance
proof
qed(simp add: equal_trie_def impl_of_inject)
end

hide_const (open) empty lookup update delete iteratei isEmpty

end