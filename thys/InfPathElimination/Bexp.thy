theory Bexp
imports Aexp
begin

section {* Boolean Expressions *}

text {* We proceed as in \verb?Aexp.thy?. *}

subsection{* Basic definitions *}

subsubsection {* The $\mathit{bexp}$ type-synonym *}

text {* We represent boolean expressions, their set of variables and the notion of freshness of a 
variable in the same way than for arithmetic expressions. *}

type_synonym ('v,'d) bexp = "('v,'d) state \<Rightarrow> bool"


definition vars ::
  "('v,'d) bexp \<Rightarrow> 'v set"
where
  "vars e = {v. \<exists> \<sigma> val. e (\<sigma>(v := val)) \<noteq> e \<sigma>}"


abbreviation fresh ::
  "'v \<Rightarrow> ('v,'d) bexp \<Rightarrow> bool"
where
  "fresh v e \<equiv> v \<notin> vars e"


subsubsection{* Satisfiability of an expression *}

text {* A boolean expression @{term "e"} is satisfiable if there exists a state @{term "\<sigma>"} such 
that @{term "e \<sigma>"} is \emph{true}. *}


definition sat ::
  "('v,'d) bexp \<Rightarrow> bool"
where
  "sat e = (\<exists> \<sigma>. e \<sigma>)"


subsubsection {* Entailment *}

text {* A boolean expression @{term "\<phi>"} entails another boolean expression @{term "\<psi>"} if all 
states making @{term "\<phi>"} true also make @{term "\<psi>"} true. *}

definition entails ::
  "('v,'d) bexp \<Rightarrow> ('v,'d) bexp \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>B" 55) 
where
  "\<phi> \<Turnstile>\<^sub>B \<psi> \<equiv> (\<forall> \<sigma>. \<phi> \<sigma> \<longrightarrow> \<psi> \<sigma>)"


subsubsection {* Conjunction *}

text {* In the following, path predicates are represented by sets of boolean expressions. We define 
the conjunction of a set of boolean expressions @{term "E"} as the expression that 
associates \emph{true} to a state @{term "\<sigma>"} if, for all elements @{text "e"} of 
@{term "E"}, @{term "e"} associates \emph{true} to @{term "\<sigma>"}. *}


definition conjunct :: 
  "('v,'d) bexp set \<Rightarrow> ('v,'d) bexp"
where
  "conjunct E \<equiv> (\<lambda> \<sigma>. \<forall> e \<in> E. e \<sigma>)"



subsection{* Properties about the variables of an expression *}

text {* As said earlier, our definition of symbolic execution requires the existence of a fresh 
symbolic variable in the case of an assignment. In the following, a number of proof relies on this 
fact. We will show the existence of such variables assuming the set of symbolic variables already in 
use is finite and show that symbolic execution preserves the finiteness of this set, under certain 
conditions. This in turn 
requires a number of lemmas about the finiteness of boolean expressions.
More precisely, when symbolic execution goes through a guard or an assignment, it conjuncts a new 
expression to the path predicate. In the case of an assignment, this new expression is an equality 
linking the new symbolic variable associated to the defined program variable to its symbolic value. 
In the following, we prove that:
\begin{enumerate}
  \item the conjunction of a finite set of expressions whose sets of variables are finite has a 
finite set of variables,
  \item the equality of two arithmetic expressions whose sets of variables are finite has a finite 
set of variables.
\end{enumerate} *}

subsubsection {* Variables of a conjunction *}

text {* The set of variables of the conjunction of two expressions is a subset of the union of the 
sets of variables of the two sub-expressions. As a consequence, the set of variables of the conjunction 
of a finite set of expressions whose sets of variables are finite is also finite. *} 


lemma vars_of_conj :
  "vars (\<lambda> \<sigma>. e1 \<sigma> \<and> e2 \<sigma>) \<subseteq> vars e1 \<union> vars e2" 
(is "vars ?e \<subseteq> vars e1 \<union> vars e2")
unfolding subset_iff
proof (intro allI impI)
  fix v assume "v \<in> vars ?e"

  then obtain \<sigma> val 
  where "?e (\<sigma> (v := val)) \<noteq> ?e \<sigma>" 
  unfolding vars_def by blast

  hence "e1 (\<sigma> (v := val)) \<noteq> e1 \<sigma> \<or> e2 (\<sigma> (v := val)) \<noteq> e2 \<sigma>" 
  by auto

  thus "v \<in> vars e1 \<union> vars e2" unfolding vars_def by blast
qed


lemma finite_conj :
  assumes "finite E"
  assumes "\<forall> e \<in> E. finite (vars e)"
  shows   "finite (vars (conjunct E))"
using assms
proof (induct rule : finite_induct, goal_cases)
  case 1 thus ?case by (simp add : vars_def conjunct_def)
next
  case (2 e E) 

  thus ?case 
  using vars_of_conj[of e "conjunct E"]
  by (rule_tac rev_finite_subset, auto simp add : conjunct_def)
qed


subsubsection {* Variables of an equality *}

text {* We proceed analogously for the equality of two arithmetic expressions. *}


lemma vars_of_eq_a :
  shows  "vars (\<lambda> \<sigma>. e1 \<sigma> = e2 \<sigma>) \<subseteq> Aexp.vars e1 \<union> Aexp.vars e2"
(is "vars ?e \<subseteq> Aexp.vars e1 \<union> Aexp.vars e2")
unfolding subset_iff
proof (intro allI impI)

  fix v assume "v \<in> vars ?e"

  then obtain \<sigma> val where "?e (\<sigma> (v := val)) \<noteq> ?e \<sigma>" 
  unfolding vars_def by blast

  hence "e1 (\<sigma> (v := val)) \<noteq> e1 \<sigma> \<or> e2 (\<sigma> (v := val)) \<noteq> e2 \<sigma>"
  by auto

  thus "v \<in> Aexp.vars e1 \<union> Aexp.vars e2" 
  unfolding Aexp.vars_def by blast
qed


lemma finite_vars_of_a_eq :
  assumes "finite (Aexp.vars e1)"
  assumes "finite (Aexp.vars e2)"
  shows   "finite (vars (\<lambda> \<sigma>. e1 \<sigma> = e2 \<sigma>))"
using assms vars_of_eq_a[of e1 e2] by (rule_tac rev_finite_subset, auto)

end
