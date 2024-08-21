theory Worklist_Common
  imports Worklist_Locales
begin

lemma list_ex_foldli:
  "list_ex P xs = foldli xs Not (\<lambda> x y. P x \<or> y) False"
  apply (induction xs)
  subgoal
    by simp
  subgoal for x xs
    by (induction xs) auto
  done

lemma (in Search_Space_finite) finitely_branching:
  assumes "reachable a"
  shows "finite ({a'. E a a' \<and> \<not> empty a'})"
proof -
  have "{a'. E a a' \<and> \<not> empty a'} \<subseteq> {a'. reachable a' \<and> \<not> empty a'}"
    using assms(1) by (auto intro: reachable_step)
  then show ?thesis using finite_reachable
    by (rule finite_subset)
qed

definition (in Search_Space_Key_Defs)
  "map_set_rel =
    {(m, s).
      \<Union>(ran m) = s \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> x. key v = k)) \<and>
      finite (dom m) \<and> (\<forall> k S. m k = Some S \<longrightarrow> finite S)
    }"

end (* Theory *)
