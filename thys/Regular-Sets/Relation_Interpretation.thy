header {* Regular Expressions as Homogeneous Binary Relations *}

theory Relation_Interpretation
imports Regular_Exp
begin

primrec word_rel :: "('a \<Rightarrow> ('b * 'b) set) \<Rightarrow> 'a list \<Rightarrow> ('b * 'b) set"
where
  "word_rel v [] = Id"
| "word_rel v (a#as) = v a O word_rel v as"

definition "rel v r = (\<Union>w\<in>lang r. word_rel v w)"

text {* Soundness: *}

lemma soundness:
 "lang r = lang s \<Longrightarrow> rel v r = rel v s"
unfolding rel_def by auto

text {* Recursive Characterization of rel: *}

lemma rel_Zero: "rel v Zero = {}"
  and rel_One: "rel v One = Id"
  and rel_Atom: "rel v (Atom a) = v a"
  and rel_Plus: "rel v (Plus r s) = rel v r \<union> rel v s"
unfolding rel_def by auto

lemma word_rel_append: 
  "word_rel v w O word_rel v w' = word_rel v (w @ w')"
apply (rule sym)
by (induct w) auto

lemma rel_Times: "rel v (Times r s) = rel v r O rel v s"
by (auto simp: rel_def word_rel_append conc_def rel_comp_UNION_distrib rel_comp_UNION_distrib2)

lemma rel_Pow: "(rel v r) ^^ n = (\<Union>w \<in> lang r ^^ n. word_rel v w)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) thus ?case
  unfolding relpow.simps rel_pow_commute[symmetric]
  by (auto simp add: rel_def conc_def word_rel_append
    rel_comp_UNION_distrib rel_comp_UNION_distrib2)
qed

lemma rel_Star: "rel v (Star r) = (rel v r)^*"
proof
  show "rel v (Star r) \<subseteq> (rel v r)^*"
  proof (rule subsetI)
    fix p
    assume "p \<in> rel v (Star r)"
    then obtain w where "w \<in> star (lang r)"
      and *: "p \<in> word_rel v w" unfolding rel_def by auto
    then obtain n where "w \<in> lang r ^^ n"
      unfolding star_def by auto
    with * have "p \<in> (rel v r) ^^ n"
      unfolding rel_Pow by auto
    thus "p \<in> (rel v r)^*" by (rule rel_pow_imp_rtrancl)
  qed
next
  show "(rel v r)^* \<subseteq> rel v (Star r)"
  proof (rule subsetI)
    fix p
    assume "p \<in> (rel v r)^*"
    then obtain n where "p \<in> (rel v r) ^^ n"
      unfolding rtrancl_power ..
    then obtain w where "w \<in> lang r ^^ n"
      and *: "p \<in> word_rel v w"
      unfolding rel_Pow by auto
    then have "w \<in> star (lang r)" unfolding star_def by auto
    with *
    show "p \<in> rel v (Star r)"
      unfolding rel_def by auto
  qed
qed

lemmas rel_simps[simp] = 
  rel_Zero rel_One rel_Atom rel_Plus rel_Times rel_Star

end