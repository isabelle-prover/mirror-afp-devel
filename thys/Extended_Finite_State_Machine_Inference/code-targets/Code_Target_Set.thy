section\<open>Sets\<close>
text\<open>While the default code generator setup for sets works fine, it does not make for particularly
readable code. The reason for this is that the default setup needs to work with potentially infinite
sets. All of the sets we need to use here are finite so we present an alternative setup for the
basic set operations which generates much cleaner code.\<close>

theory Code_Target_Set
  imports "HOL-Library.Code_Cardinality"
begin

code_datatype set

lemma [code]:
  "Code_Cardinality.finite' = finite"
  "Code_Cardinality.card' = card"
  "Code_Cardinality.eq_set = HOL.equal"
  "Code_Cardinality.subset' = (\<subseteq>)"
  by (simp_all add: equal)

lemma [code]:
  \<open>x \<in> set xs = List.member xs x\<close>
  by simp

lemma [code]:
  \<open>finite (set xs) \<longleftrightarrow> True\<close>
  by simp

lemma [code]:
  \<open>insert x (set xs) = set (List.insert x xs)\<close>
  by (fact insert_code)

lemma [code]:
  \<open>Set.remove x (set xs) = set (removeAll x xs)\<close>
  by (fact remove_code)

lemma [code]:
  \<open>set xs \<union> set ys = set (xs @ ys)\<close>
  by simp

lemma [code]:
  \<open>A - set xs = fold Set.remove xs A\<close>
  by (fact minus_set_fold)

lemma [code]:
  \<open>A \<inter> set xs = set (filter (\<lambda>x. x \<in> A) xs)\<close>
  by (fact inter_set_filter)

lemma [code]:
  \<open>card (set xs) = length (remdups xs)\<close>
  by (fact List.card_set)

lemma [code]:
  \<open>set xs \<subseteq> A \<longleftrightarrow> list_all (\<lambda>x. x \<in> A) xs\<close>
  by (auto simp add: list_all_iff)

lemma [code]:
  \<open>A \<subset> set xs \<longleftrightarrow> A \<subseteq> set xs \<and> list_ex (\<lambda>x. x \<notin> A) xs\<close>
  by (auto simp add: list_ex_iff)

lemma [code]:
  \<open>HOL.equal A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A\<close>
  by (fact equal_set_def)

end
