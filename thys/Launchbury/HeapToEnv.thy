theory "HeapToEnv"
  imports "DistinctVars" "Nominal-Utils" "FMap-Nominal-HOLCF"
begin

default_sort type

subsubsection {* Conversion from heaps to environments *} 

function heapToEnv :: "('var \<times> 'exp) list \<Rightarrow> ('exp \<Rightarrow> 'value) \<Rightarrow> 'var f\<rightharpoonup> 'value"
where
  "heapToEnv [] _ = fempty"
| "heapToEnv ((x,e)#h) eval = (heapToEnv h eval) (x f\<mapsto> eval e)"
by (pat_completeness, auto)
termination by lexicographic_order

lemma cont2cont_heapToEnv[simp, cont2cont]:
  "(\<And> e . e \<in> snd ` set h \<Longrightarrow> cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. heapToEnv h (eval \<rho>))"
  by(induct h, auto)

lemma heapToEnv_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv h eval = heapToEnv (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv.induct, auto simp add: fmap_upd_eqvt)

lemma heapToEnv_fdom[simp]:"fdom (heapToEnv h eval) = heapVars h"
  by (induct h eval rule:heapToEnv.induct, auto)

lemma heapToEnv_cong[fundef_cong]:
  "\<lbrakk> heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
    \<Longrightarrow>  heapToEnv heap1 eval1 = heapToEnv heap2 eval2"
 by (induct heap2 eval2 arbitrary:heap1 rule:heapToEnv.induct, auto)

lemma lookupHeapToEnv:
  assumes "v \<in> heapVars h"
  shows "(heapToEnv h f) f! v = f (the (map_of h v))"
  using assms
  apply (induct h)
  apply simp
  apply (case_tac a)
  apply auto
  done

lemma lookupHeapToEnvNotAppend[simp]:
  assumes "x \<notin> heapVars \<Gamma>"
  shows "heapToEnv (\<Gamma>@h) f f! x = heapToEnv h f f! x"
  using assms by (induct \<Gamma>, auto)

lemma heapToEnv_remove_Cons_fmap_expand:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> heapToEnv ((x, e) # \<Gamma>) eval\<^bsub>[S]\<^esub> = heapToEnv \<Gamma> eval\<^bsub>[S]\<^esub>"
  apply (rule fmap_eqI)
  apply simp
  apply (subgoal_tac "xa \<noteq> x")
  apply (case_tac "xa \<in> heapVars \<Gamma>")
  apply simp
  apply simp
  apply auto
  done

lemma heapToEnv_mono:
  "finite d1 \<Longrightarrow>
   d1 = d2 \<Longrightarrow>
   x \<notin> heapVars \<Gamma> \<Longrightarrow>
  heapToEnv \<Gamma> eval\<^bsub>[d1]\<^esub> \<sqsubseteq> heapToEnv ((x, e) # \<Gamma>) eval\<^bsub>[d2]\<^esub>"
   apply (erule subst)
   apply (rule fmap_expand_belowI)
   apply simp
   apply (rule eq_imp_below)
   apply simp
   apply (metis the_lookup_fmap_upd_other[symmetric])
   done

subsubsection {* Reordering lemmas *}

lemma heapToEnv_reorder_head:
  assumes "x \<noteq> y"
  shows "heapToEnv ((x,e1)#(y,e2)#\<Gamma>) eval = heapToEnv ((y,e2)#(x,e1)#\<Gamma>) eval"
  by (simp add: fmap_upd_twist[OF assms])

lemma heapToEnv_reorder_head_append:
  assumes "x \<notin> heapVars \<Gamma>"
  shows "heapToEnv ((x,e)#\<Gamma>@\<Delta>) eval = heapToEnv (\<Gamma> @ ((x,e)#\<Delta>)) eval"
  using assms
  apply (induct \<Gamma>)
  apply simp
  apply (case_tac a)
  apply (auto simp del: heapToEnv.simps simp add: heapToEnv_reorder_head)
  apply simp
  done

lemma heapToEnv_delete_insert:
  assumes "distinctVars \<Gamma>"
  assumes "(x,e) \<in> set \<Gamma>"
  shows "heapToEnv \<Gamma> eval = heapToEnv ((x,e) # delete x \<Gamma>) eval"
using assms
proof (induct \<Gamma> rule:distinctVars.induct)
  case goal1 thus ?case by simp
next
  case (goal2 y \<Gamma> e2)
  show ?case
  proof(cases "(x,e) = (y,e2)")
  case True
    from `y \<notin> heapVars \<Gamma>`
    have "x \<notin> heapVars \<Gamma>" using True by simp
    hence "delete x \<Gamma> = \<Gamma>" by (rule delete_no_there)
    with True show ?thesis by simp
  next
  case False
    hence "x \<noteq> y" by (metis goal2(1) goal2(4) heapVars_from_set set_ConsD)
    hence "(x, e) \<in> set \<Gamma>" by (metis False goal2(4) set_ConsD)
    note hyp = goal2(3)[OF this]

    have "heapToEnv ((x, e) # delete x ((y, e2) # \<Gamma>)) eval 
      = heapToEnv ((x, e) # ((y, e2) # delete x \<Gamma>)) eval"
      using False by simp
    also have "... = heapToEnv ((y, e2) # ((x, e) # delete x \<Gamma>)) eval"
      by (rule heapToEnv_reorder_head[OF `x \<noteq> y`])
    also have "... = heapToEnv ((y, e2) # \<Gamma>) eval"
      using hyp
      by simp
    finally
    show ?thesis by (rule sym)
  qed
qed

lemma heapToEnv_reorder:
  assumes "distinctVars \<Gamma>"
  assumes "distinctVars \<Delta>"
  assumes "set \<Gamma> = set \<Delta>"
  shows "heapToEnv \<Gamma> eval = heapToEnv \<Delta> eval"
using assms
proof (induct \<Gamma> arbitrary: \<Delta> rule:distinctVars.induct)
case goal1 thus ?case by simp
next
case (goal2 x \<Gamma> e \<Delta>)
  hence "(x,e) \<in> set \<Delta>"
    by (metis ListMem_iff elem)
  note Delta' = heapToEnv_delete_insert[OF `distinctVars \<Delta>` this]

  have "distinctVars (delete x \<Delta>)" 
    by (rule distinctVars_delete[OF goal2(4)])
  moreover
  from `set ((x, e) # \<Gamma>) = set \<Delta>`
  have "set (delete x ((x, e) # \<Gamma>)) = set (delete x \<Delta>)"
    by (metis filter_set delete_eq)
  hence "set \<Gamma> = set (delete x \<Delta>)"
    by (simp add: delete_no_there[OF `x \<notin> heapVars \<Gamma>`])
  ultimately
  have "heapToEnv \<Gamma> eval = heapToEnv (delete x \<Delta>) eval"
    by (rule goal2(3))
  thus ?case
    by (simp add: Delta')
qed

lemma heapToEnv_subst_exp:
  assumes "eval e = eval e'"
  shows "heapToEnv ((x,e)#\<Gamma>) eval = heapToEnv ((x,e')#\<Gamma>) eval"
  by (simp add: assms)
end
