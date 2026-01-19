(*  Title:       Tools for executable specifications
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section "Tools for executable specifications"

theory ImplHelper
imports Main
begin

subsection "Searching in Lists"
  
text \<open> Given a function @{term "f :: 's \<Rightarrow> 'a option"} and a list @{term "l :: 's list"}, return the result of the first element @{term "e\<in>set l"} with @{term "f e \<noteq> None"}.
  The functional code snippet @{term "first_that f l"} corresponds to the imperative code snippet: {\em for e in l do \{ if f e $\neq$ None then return Some (f e) \}; return None }
\<close>
  
primrec first_that :: "('s \<Rightarrow> 'a option) \<Rightarrow> 's list \<Rightarrow> 'a option" where
  "first_that f [] = None"
| "first_that f (e#w) = (case f e of None \<Rightarrow> first_that f w | Some a \<Rightarrow> Some a)"

lemma first_thatE1: "first_that f l = Some a \<Longrightarrow> \<exists>e\<in>set l. f e = Some a"
  apply (induct l)
  subgoal by simp
  subgoal for aa l by (cases "f aa") auto
  done

lemma first_thatE2: "first_that f l = None \<Longrightarrow> \<forall>e\<in>set l. f e = None"
  apply (induct l)
  subgoal by simp
  subgoal for aa l by (cases "f aa") auto
  done
 
lemmas first_thatE = first_thatE1 first_thatE2

lemma first_thatI1: "e\<in>set l \<and> f e = Some a \<Longrightarrow> \<exists>a'. first_that f l = Some a'"
  by (cases "first_that f l") (auto dest: first_thatE2)
  
lemma first_thatI2: "\<forall>e\<in>set l. f e = None \<Longrightarrow> first_that f l = None"
  by (cases "first_that f l") (auto dest: first_thatE1)

lemmas first_thatI = first_thatI1 first_thatI2

end
