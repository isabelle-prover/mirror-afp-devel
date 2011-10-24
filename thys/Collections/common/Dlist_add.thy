header {* \isaheader{Additions to Distinct Lists} *}
theory Dlist_add imports "~~/src/HOL/Library/Dlist" Misc begin

primrec remove1' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove1' x z [] = z"
| "remove1' x z (y # ys) = (if x = y then z @ ys else remove1' x (y # z) ys)"

definition remove' :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist"
where "remove' a xs = Dlist (remove1' a [] (list_of_dlist xs))"

lemma distinct_remove1': "distinct (xs @ ys) \<Longrightarrow> distinct (remove1' x xs ys)"
by(induct ys arbitrary: xs) simp_all

lemma set_remove1': "distinct ys \<Longrightarrow> set (remove1' x xs ys) = set xs \<union> (set ys - {x})"
by(induct ys arbitrary: xs) auto

lemma list_of_dlist_remove' [simp, code abstract]:
  "list_of_dlist (remove' a xs) = remove1' a [] (list_of_dlist xs)"
by(simp add: remove'_def distinct_remove1')

lemma remove'_correct: "Dlist.member (remove' x xs) y = (if x = y then False else Dlist.member xs y)"
by(simp add: remove'_def Dlist.member_def List.member_def set_remove1')

primrec iteratei_aux :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "iteratei_aux c f [] \<sigma> = \<sigma>"
| "iteratei_aux c f (x # xs) \<sigma> = (if c \<sigma> then iteratei_aux c f xs (f x \<sigma>) else \<sigma>)"

definition iteratei :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b dlist \<Rightarrow> 'a \<Rightarrow> 'a"
where "iteratei c f xs = iteratei_aux c f (list_of_dlist xs)"

lemma iteratei_aux_correct:
  assumes "distinct xs"
  and "I (set xs) \<sigma>0"
  and "\<And>x it \<sigma>. \<lbrakk>c \<sigma>; x \<in> it; it \<subseteq> set xs; I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)"
  shows "I {} (iteratei_aux c f xs \<sigma>0) \<or>
        (\<exists>it\<subseteq>set xs. it \<noteq> {} \<and> \<not> c (iteratei_aux c f xs \<sigma>0) \<and> I it (iteratei_aux c f xs \<sigma>0))"
proof -
  { fix it
    assume "it \<supseteq> set xs" and "I it \<sigma>0" 
      and "\<And>\<sigma> x it'. \<lbrakk> c \<sigma>; x \<in> it'; it' \<subseteq> it; I it' \<sigma> \<rbrakk> \<Longrightarrow> I (it' - {x}) (f x \<sigma>)"
    with `distinct xs`
    have "I (it - set xs) (iteratei_aux c f xs \<sigma>0) 
          \<or> (\<exists>it' \<subseteq> it. it' \<noteq> {} \<and> \<not> c (iteratei_aux c f xs \<sigma>0) \<and> I it' (iteratei_aux c f xs \<sigma>0))"
    proof (induct xs arbitrary: it \<sigma>0)
      case Nil thus ?case by simp
    next
      case (Cons x xs it \<sigma>)
      show ?case
      proof(cases "c \<sigma>")
        case False
        with Cons.prems show ?thesis by simp blast
      next
        case True [simp]
        from Cons have "distinct xs" "x \<notin> set xs" by simp_all
        with `set (x # xs) \<subseteq> it`
        have "distinct xs" "set xs \<subseteq> it - {x}" by auto
        moreover from Cons.prems have "c \<sigma>" "x \<in> it" "it \<subseteq> it" "I it \<sigma>" by simp_all
        hence "I (it - {x}) (f x \<sigma>)" by (rule Cons)
        ultimately have "I (it - {x} - set xs) (iteratei_aux c f xs (f x \<sigma>)) 
                      \<or> (\<exists>it' \<subseteq> it - {x}. it' \<noteq> {} \<and> \<not> c (iteratei_aux c f xs (f x \<sigma>)) \<and>
                               I it' (iteratei_aux c f xs (f x \<sigma>)))"
          (is "?C1 \<or> ?C2")
        proof (rule Cons.hyps [of "it-{x}" "f x \<sigma>"])
          fix \<sigma> x' it'
          assume "c \<sigma>" "x' \<in> it'" "it' \<subseteq> it - {x}" "I it' \<sigma>"
          with Cons.prems show "I (it' - {x'}) (f x' \<sigma>)" by auto
        qed
        thus ?thesis
        proof
          assume ?C1
          thus ?thesis by(auto simp add: True set_diff_diff_left)
        next
          assume ?C2 
          then obtain it' where "it' \<subseteq> it - {x}"
            and "it' \<noteq> {}" and "\<not> c (iteratei_aux c f xs (f x \<sigma>))" 
            and "I it' (iteratei_aux c f xs (f x \<sigma>))" by blast
          thus ?thesis by(auto simp add: exI[where x=it'])
        qed
      qed
    qed }
  from this[OF subset_refl] assms show ?thesis by simp
qed

lemma iteratei_correct:
  assumes "I {y. Dlist.member xs y} \<sigma>0"
  and "\<And>x it \<sigma>. \<lbrakk>c \<sigma>; x \<in> it; it \<subseteq> {y. Dlist.member xs y}; I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)"
  shows "I {} (iteratei c f xs \<sigma>0) \<or>
        (\<exists>it\<subseteq>{y. Dlist.member xs y}. it \<noteq> {} \<and> \<not> c (iteratei c f xs \<sigma>0) \<and> I it (iteratei c f xs \<sigma>0))"
using distinct_list_of_dlist[of xs] assms
unfolding Dlist.member_def List.member_def iteratei_def Collect_mem_eq
by(rule iteratei_aux_correct)

lemma member_empty: "Dlist.member Dlist.empty = (\<lambda>x. False)"
by(simp add: empty_def member_def fun_eq_iff List.member_def)

lemma member_insert [simp]: "Dlist.member (Dlist.insert x xs) = (Dlist.member xs)(x := True)"
by(simp add: Dlist.insert_def Dlist.member_def List.member_def fun_eq_iff)

lemma finite_member [simp, intro!]: "finite {x. Dlist.member xs x}"
by(simp add: member_def List.member_def)

end