theory DistinctVars
imports Main "~~/src/HOL/Library/AList"
begin

abbreviation delete where "delete \<equiv> AList.delete"
abbreviation update where "update \<equiv> AList.update"

subsubsection {* The domain of a associative list *}

definition heapVars
  where "heapVars h = fst ` set h"

lemma heapVarsAppend[simp]:"heapVars (a @ b) = heapVars a \<union> heapVars b"
  and [simp]:"heapVars ((v,e) # h) = insert v (heapVars h)"
  and [simp]:"heapVars (p # h) = insert (fst p) (heapVars h)"
  and [simp]:"heapVars [] = {}"
  by (auto simp add: heapVars_def)

lemma heapVars_from_set:
  "(x, e) \<in> set h \<Longrightarrow> x \<in> heapVars h"
by (induct h, auto)

lemma finite_heapVars[simp]:
  "finite (heapVars \<Gamma>)"
  by (auto simp add: heapVars_def)

lemma delete_no_there:
  "x \<notin> heapVars \<Gamma> \<Longrightarrow> delete x \<Gamma> = \<Gamma>"
  by (induct \<Gamma>, auto)

lemma heapVars_delete[simp]:
  "heapVars (delete x \<Gamma>) = heapVars \<Gamma> - {x}"
  by (induct \<Gamma>, auto)

subsubsection {* Junk-free associative lists *}

inductive distinctVars  where
  [simp]: "distinctVars []" |
  [intro]:"x \<notin> heapVars \<Gamma> \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinctVars ((x, e)  # \<Gamma>)"

lemma [simp]: "distinctVars [x]"
  by (cases x, auto)

lemma distinctVars_appendI:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars \<Delta> \<Longrightarrow> heapVars \<Gamma> \<inter> heapVars \<Delta> = {} \<Longrightarrow> distinctVars (\<Gamma> @ \<Delta>)"
  by (induct \<Gamma> rule:distinctVars.induct, auto)

lemma distinctVars_ConsD:
  assumes "distinctVars ((x,e) # \<Gamma>)"
  shows "x \<notin> heapVars \<Gamma>" and "distinctVars \<Gamma>"
  by (rule distinctVars.cases[OF assms], simp_all)+

lemma distinctVars_appendD:
  assumes "distinctVars (\<Gamma> @ \<Delta>)"
  shows distinctVars_appendD1: "distinctVars \<Gamma>"
  and distinctVars_appendD2: "distinctVars \<Delta>"
  and distinctVars_appendD3: "heapVars \<Gamma> \<inter> heapVars \<Delta> = {}"
proof-
  from assms
  have "distinctVars \<Gamma> \<and> distinctVars \<Delta> \<and> heapVars \<Gamma> \<inter> heapVars \<Delta> = {}"
  proof (induct \<Gamma> )
  case Nil thus ?case by simp
  next
  case (Cons p \<Gamma>)
    obtain x e where "p = (x,e)" by (metis PairE)
    with Cons have "distinctVars ((x,e) # (\<Gamma>@ \<Delta>))" by simp
    hence "x \<notin> heapVars (\<Gamma>@ \<Delta>)" and "distinctVars (\<Gamma> @ \<Delta>)" by (rule distinctVars_ConsD)+

    from `x \<notin> heapVars (\<Gamma>@ \<Delta>)` have  "x \<notin> heapVars \<Gamma>"  and "x \<notin> heapVars \<Delta>" by auto

    from Cons(1)[OF `distinctVars (\<Gamma> @ \<Delta>)`]
    have "distinctVars \<Gamma>" and "distinctVars \<Delta>" and "heapVars \<Gamma> \<inter> heapVars \<Delta> = {}" by auto
    have "distinctVars (p # \<Gamma>)"
      using `p = _` `x \<notin> heapVars \<Gamma>` `distinctVars \<Gamma>` by auto
    moreover
    have "heapVars (p # \<Gamma>) \<inter> heapVars \<Delta> = {}" 
      using `p = _` `x \<notin> heapVars \<Delta>` `heapVars \<Gamma> \<inter> heapVars \<Delta> = {}` by auto
    ultimately
    show ?case using `distinctVars \<Delta>` by auto
  qed
  thus "distinctVars \<Gamma>" and "distinctVars \<Delta>" and "heapVars \<Gamma> \<inter> heapVars \<Delta> = {}" by auto
qed

lemma distinctVars_Cons:
  "distinctVars (x # \<Gamma>) \<longleftrightarrow> (fst x \<notin> heapVars \<Gamma> \<and> distinctVars \<Gamma>)"
  by (metis PairE distinctVars.intros(2) distinctVars_ConsD fst_conv)

lemma distinctVars_append:
  "distinctVars (\<Gamma> @ \<Delta>) \<longleftrightarrow> (distinctVars \<Gamma> \<and> distinctVars \<Delta> \<and> heapVars \<Gamma> \<inter> heapVars \<Delta> = {})"
  by (metis distinctVars_appendD distinctVars_appendI)

lemma distinctVars_Cons_subset:
  assumes "heapVars ((x,e)#\<Gamma>) \<subseteq> heapVars ((x,e')#\<Delta>)"
  assumes "distinctVars ((x,e)#\<Gamma>)"
  assumes "distinctVars ((x,e')#\<Delta>)"
  shows "heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
proof-
  have "x \<notin> heapVars \<Gamma>" and "x \<notin> heapVars \<Delta>"
    using assms(2,3) by (metis distinctVars_ConsD(1))+
  thus ?thesis using assms(1)
    by auto
qed

lemma distinctVars_delete:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars (delete x \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply (auto simp add: distinctVars_Cons)
  done

lemma dom_map_of_conv_heapVars[simp]:
  "dom (map_of xys) = heapVars xys"
  by (induct xys) (auto simp add: dom_if)

lemma distinctVars_set_delete_insert:
  assumes "distinctVars \<Gamma>"
  assumes "(x,e) \<in> set \<Gamma>"
  shows "set ((x,e) # delete x \<Gamma>) = set \<Gamma>"
  using assms
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply auto[1]
  apply (case_tac "xa = x")
  apply (auto simp add: heapVars_def)[1]
    apply (metis fst_conv imageI)
  apply auto
  done

lemma the_map_of_snd:
  "x\<in> heapVars \<Gamma> \<Longrightarrow> the (map_of \<Gamma> x) \<in> snd ` set \<Gamma>"
by (induct \<Gamma>, auto)
end
