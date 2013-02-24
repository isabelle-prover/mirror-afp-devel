theory LaunchburyUnBH
imports LaunchburyStacked LaunchburyNoBH
begin


lemma delete_append[simp]: "delete x (al1@al2) = delete x al1 @ delete x al2"
  by (simp add: AList.delete_eq)

lemma forgetBH:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  assumes "distinctVars (\<Gamma>' @ \<Gamma>)"
  shows "\<Gamma>' @ \<Gamma> [\<Down>] \<Delta>' @ \<Delta>"
using assms
proof (induct rule: reds_distinct_ind)
case (Lambda \<Gamma> x y e \<Gamma>')
  show ?case
    unfolding append_Cons
    apply (rule LaunchburyNoBH.Lambda)
    done
next
case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z e')
  show ?case
  unfolding append_Cons
  proof(rule LaunchburyNoBH.Application)
    show "atom n \<sharp> (\<Gamma>' @ \<Gamma>, delete x ((x, App (Var n) y) # \<Delta>' @ \<Delta>), x, e, y, \<Theta>' @ \<Theta>, z)"
      and "atom z \<sharp> (\<Gamma>' @ \<Gamma>, delete x ((x, App (Var n) y) # \<Delta>' @ \<Delta>), x, e, y, \<Theta>' @ \<Theta>)"
      using Application
      by (auto simp add: fresh_Pair fresh_Cons fresh_append eqvt_fresh_cong2[where f = delete, OF delete_eqvt])
    show "(n, e) # (x, App (Var n) y) # \<Gamma>' @ \<Gamma> [\<Down>] (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' @ \<Delta>"
      by (rule Application(9)[unfolded append_Cons])

    have "x \<notin> heapVars (\<Delta>' @ \<Delta>)"
      using Application(6)
      by (simp add: distinctVars_Cons)
    hence [simp]:"delete x \<Delta>' = \<Delta>'"  "delete x \<Delta> = \<Delta>"
      by (auto intro: delete_no_there)

    show "(x, e'[z::=y]) # delete x ((x, App (Var n) y) # \<Delta>' @ \<Delta>) [\<Down>] \<Theta>' @ \<Theta>"
      using Application(11)
      by simp
  qed
next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have [simp]:"x \<noteq> y"
    using Variable(3)
    by (auto simp add: distinctVars_Cons)
  note this[symmetric,simp]

  have "y \<notin> heapVars \<Gamma>'"
    using Variable(3)
    by (auto simp add: distinctVars_Cons)
  hence [simp]: "delete y \<Gamma>' = \<Gamma>'"
    by (rule delete_no_there)

  have "x \<notin> heapVars \<Delta>'"
    using Variable(4)
    by (auto simp add: distinctVars_Cons)
  hence [simp]: "delete x \<Delta>' = \<Delta>'"
    by (rule delete_no_there)

  have "x \<notin> heapVars \<Delta>"
    using Variable(4)
    by (auto simp add: distinctVars_Cons)
  hence [simp]: "delete x \<Delta> = \<Delta>"
    by (rule delete_no_there)

  have "((x, Var y) # \<Gamma>') @ \<Gamma> [\<Down>] (x, z) # delete x (((x, Var y) # \<Delta>') @ (y, z) # \<Delta>)"
  unfolding append_Cons 
  proof (rule LaunchburyNoBH.Variable)
    show "(y, e) \<in> set ((x, Var y) # \<Gamma>' @ \<Gamma>)"
      using Variable(1) by simp
    show "(y, e) # delete y ((x, Var y) # \<Gamma>' @ \<Gamma>) [\<Down>] (y, z) # (((x, Var y) # \<Delta>') @ \<Delta>)"
      using Variable(7) by simp
   
    show "set ((x, Var y) # \<Delta>' @ (y, z) # \<Delta>) = set ((y, z) # ((x, Var y) # \<Delta>') @ \<Delta>)"
      by auto
  qed
  thus ?case
    unfolding append_Cons
    by simp
next
case (Let as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
  show ?case
  unfolding append_Cons
  proof (rule LaunchburyNoBH.Let)
    show "set (bn as) \<sharp>* (\<Gamma>' @ \<Gamma>, x, Terms.Let as body)"
      using Let(1) by (simp add: fresh_star_Pair fresh_star_append)
    show "distinctVars (asToHeap as)" by fact
    show " (x, body) # \<Gamma>' @ asToHeap as  @ \<Gamma> [\<Down>] \<Delta>' @ \<Delta>"
      using Let(7) by simp
    show "set (\<Gamma>' @ asToHeap as @ \<Gamma>) = set (asToHeap as @ \<Gamma>' @ \<Gamma>)"
      by auto
qed


qed
