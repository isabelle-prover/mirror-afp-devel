header {* A While-Combinator With Optional Result *}

(* Should become part of Library *)

theory While_Option
imports Main
begin

consts while_aux :: "('a => bool) \<times> ('a => 'a) \<times> 'a => 'a option"
recdef (permissive) while_aux
"same_fst (\<lambda>b. True) (\<lambda>b. same_fst (\<lambda>c. True) (\<lambda>c. {(t, s).  b s \<and> c s = t \<and> (EX k. ~b((c^^k) s))}))"

"while_aux (b, c, s) =
 (if (ALL k. b ((c^^k) s))
  then None
  else if b s then while_aux (b, c, c s)
       else Some s)"

recdef_tc while_aux_tc: while_aux
apply (rule wf_same_fst)
apply (rule wf_same_fst)
apply(rename_tac b c)
apply(rule ccontr)
apply (simp add: wf_iff_no_infinite_down_chain)
apply auto
apply(subgoal_tac "ALL i. f i = (c^^i)(f 0)")
apply metis
apply rule
apply(induct_tac i)
apply simp
apply(simp)
by metis


definition while :: "('a => bool) => ('a => 'a) => 'a => 'a option" where
"while b c s = while_aux (b, c, s)"

lemma while_aux_unfold:
"while_aux (b, c, s) =
 (if (ALL k. b((c^^k)s))
  then None
  else if b s then while_aux (b, c, c s)
      else Some s)"
apply (rule while_aux_tc [THEN while_aux.simps [THEN trans]])
apply (rule refl)
done

theorem while_unfold [code]:
"while b c s = (if b s then while b c (c s) else Some s)"
apply (unfold while_def)
apply (rule while_aux_unfold [THEN trans])
apply auto
apply (subst while_aux_unfold)
apply(subgoal_tac "ALL k. b ((c ^^ k) (c s))")
apply simp
apply rule
apply (erule_tac x = "Suc k" in allE)
apply (simp add: funpow_swap1)
apply (erule_tac x = "0" in allE)
apply simp
done

hide_const while_aux

lemma def_while_unfold:
assumes fdef: "f == while test do"
shows "f x = (if test x then f(do x) else Some x)"
proof -
  have "f x = while test do x" using fdef by simp
  also have "\<dots> = (if test x then while test do (do x) else Some x)"
    by(rule while_unfold)
  also have "\<dots> = (if test x then f(do x) else Some x)" by(simp add:fdef[symmetric])
  finally show ?thesis .
qed

lemma All_less_Suc: "(ALL i<Suc n. P i) \<longleftrightarrow> P 0 & (ALL i < n. P(Suc i))"
by (metis less_Suc_eq_0_disj)

lemma while_Some: assumes "while b c s = Some t"
shows "EX k. t = (c^^k) s & ~ b t & (ALL i<k. b((c^^i) s))"
proof -
  from assms obtain kk where 0: "~b((c^^kk) s)"
    using while_aux_unfold[of b c s] by(simp add: while_def split:if_splits)
  def k == "(LEAST k. ~ b((c^^k) s))"
  have 1: "~ b((c^^k) s)" unfolding k_def using 0 by(rule LeastI)
  have 2: "ALL i<k. b((c^^i) s)" unfolding k_def by(blast dest: not_less_Least)
  from 1 2 assms have "t = (c^^k) s"
  proof(induct k arbitrary: s)
    case 0 with while_unfold[of b c s]
    show ?case by simp
  next
    case (Suc k) with while_unfold[of b c s]
    show ?case by (simp add: funpow_swap1 All_less_Suc)
  qed
  with 1 2 show ?thesis by blast
qed

theorem while_rule:
assumes "!!s. P s ==> b s ==> P (c s)"
and "while b c s = Some t"
and "P s"
shows "P t & ~ b t"
proof -
  from while_Some[OF assms(2)] obtain k where
    1: "t = (c^^k) s" and "~b t" and 2: "ALL i<k. b((c^^i)s)" by blast
  from 1 2 have "P(s) \<Longrightarrow> P(t)"
  proof(induct k arbitrary: s)
    case 0 thus ?case by simp
  next
    case (Suc k)
    thus ?case using assms(1)[of s] by(auto simp: funpow_swap1 All_less_Suc)
  qed
  from this[OF `P s`] `~b t` show "P t & ~b t" ..
qed

end
