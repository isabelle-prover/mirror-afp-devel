theory MultisetAdd
imports "~~/src/HOL/Library/Multiset"
begin

(* Lemmas for Multisets *)
lemma multiset_insort: 
  "multiset_of (insort_key f x xs) = multiset_of (xs) + {#x#}"
  by (induct xs) (simp_all add: union_ac)

lemma multiset_sort[simp]: "multiset_of (sort_key f xs) = multiset_of xs"
  apply(induct xs arbitrary: f)
  apply(auto simp add: multiset_insort)
done

lemma mset_rev: "multiset_of (rev ls) = multiset_of ls" 
  by (induct ls) simp_all

lemma set_of_diff: "\<forall>m. count C m \<noteq> 0 \<longrightarrow> count A m \<le> count C m \<Longrightarrow> 
  set_of (A - C) = (set_of A) - (set_of C)"
proof -
  case goal1
  hence "\<forall>m. count C m \<noteq> 0 \<longrightarrow> count (A-C) m = 0" by simp
  hence "\<forall>m. count (A-C) m = (if count C m = 0 then count A m else 0)" 
    by simp
  hence "\<forall>m. count (A-C) m \<ge> 1 \<longrightarrow> count C m = 0" by simp
  hence a: "\<forall>m \<in> set_of (A-C). m \<notin> set_of C" by simp
  have "\<forall>m. count (A-C) m \<ge> 1 \<longrightarrow> count A m \<ge> 1" by auto
  hence "\<forall>m \<in> set_of (A-C). m \<in> set_of A" by simp
  with a have "\<forall>m \<in> set_of (A-C). m \<in> set_of A \<and> m \<notin> set_of C" by metis
  hence a: "set_of (A - C) \<subseteq> set_of A - set_of C" by auto
  have "set_of A - set_of C = {x. (x \<in> set_of A \<and> x \<notin> set_of C)}" by blast
  hence "set_of A - set_of C \<subseteq> set_of (A - C)" by auto
  with a show ?case by simp
qed 

lemma set_of_diff_subset: "set_of (A-C) \<subseteq> set_of A"
  by auto
 
lemma subset_diff_inter: "\<lbrakk>A \<subseteq> D; C \<subseteq> D - A\<rbrakk> \<Longrightarrow> A \<inter> C = {}" by auto

lemma count_mset_of: 
  "count (multiset_of ls) t \<le> count (multiset_of (l # ls)) t"
  by (induct ls) simp_all

lemma multiset_of_set_of: "multiset_of ls = m \<Longrightarrow> set ls = set_of m"
  by auto
end