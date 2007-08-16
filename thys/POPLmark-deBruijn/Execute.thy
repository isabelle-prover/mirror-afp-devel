(*  Title:      Poplmark/Execute.thy
    ID:         $Id: Execute.thy,v 1.1 2007-08-16 13:04:18 nipkow Exp $
    Author:     Stefan Berghofer, TU Muenchen, 2005
*)
(*<*)
theory Execute
imports PoplmarkRecord Executable_Set Efficient_Nat
begin
(*>*)

section {* Executing the specification *}

text {*
\label{sec:exec}
An important criterion that a solution to the {\sc PoplMark} Challenge should
fulfill is the possibility to {\it animate} the specification. For example,
it should be possible to apply the reduction relation for the calculus to
example terms. Since the reduction relations are defined inductively, they can
be interpreted as a logic program in the style of {\sc Prolog}.
The definition of the single-step evaluation relation presented in \secref{sec:evaluation}
and \secref{sec:evaluation-rcd} is directly executable.

In order to compute the normal form of a term using the one-step evaluation
relation @{text "\<longmapsto>"}, we introduce the inductive predicate @{text "t \<Down> u"},
denoting that @{text u} is a normal form of @{text t}.
*}

inductive norm :: "trm \<Rightarrow> trm \<Rightarrow> bool"  (infixl "\<Down>" 50)
where
  "t \<in> value \<Longrightarrow> t \<Down> t"
| "t \<longmapsto> s \<Longrightarrow> s \<Down> u \<Longrightarrow> t \<Down> u"

definition normal_forms where
  "normal_forms t \<equiv> {u. t \<Down> u}"

lemma [code ind_set]: "Rcd [] \<in> value"
  by (rule value.Rcd) simp

lemma [code ind_set]: "t \<in> value \<Longrightarrow> Rcd fs \<in> value \<Longrightarrow> Rcd ((l, t) # fs) \<in> value"
  apply (rule value.Rcd)
  apply (ind_cases "Rcd fs \<in> value")
  apply simp
  done

lemmas [code ind_set] = value.Abs value.TAbs

constdefs
  natT :: type
  "natT \<equiv> \<forall><:Top. (\<forall><:TVar 0. (\<forall><:TVar 1. (TVar 2 \<rightarrow> TVar 1) \<rightarrow> TVar 0 \<rightarrow> TVar 1))"
  fact2 :: trm
  "fact2 \<equiv>
   LET PVar natT =
     (\<lambda><:Top. \<lambda><:TVar 0. \<lambda><:TVar 1. \<lambda>:TVar 2 \<rightarrow> TVar 1. \<lambda>: TVar 1. Var 1 \<bullet> Var 0)
   IN
   LET PRcd
     [(''pluspp'', PVar (natT \<rightarrow> natT \<rightarrow> natT)),
      (''multpp'', PVar (natT \<rightarrow> natT \<rightarrow> natT))] = Rcd
     [(''multpp'', \<lambda>:natT. \<lambda>:natT. \<lambda><:Top. \<lambda><:TVar 0. \<lambda><:TVar 1. \<lambda>:TVar 2 \<rightarrow> TVar 1.
        Var 5 \<bullet>\<^isub>\<tau> TVar 3 \<bullet>\<^isub>\<tau> TVar 2 \<bullet>\<^isub>\<tau> TVar 1 \<bullet> (Var 4 \<bullet>\<^isub>\<tau> TVar 3 \<bullet>\<^isub>\<tau> TVar 2 \<bullet>\<^isub>\<tau> TVar 1) \<bullet> Var 0),
      (''pluspp'', \<lambda>:natT. \<lambda>:natT. \<lambda><:Top. \<lambda><:TVar 0. \<lambda><:TVar 1. \<lambda>:TVar 2 \<rightarrow> TVar 1. \<lambda>:TVar 1.
        Var 6 \<bullet>\<^isub>\<tau> TVar 4 \<bullet>\<^isub>\<tau> TVar 3 \<bullet>\<^isub>\<tau> TVar 3 \<bullet> Var 1 \<bullet>
          (Var 5 \<bullet>\<^isub>\<tau> TVar 4 \<bullet>\<^isub>\<tau> TVar 3 \<bullet>\<^isub>\<tau> TVar 2 \<bullet> Var 1 \<bullet> Var 0))]
   IN
     Var 0 \<bullet> (Var 1 \<bullet> Var 2 \<bullet> Var 2) \<bullet> Var 2"

value "normal_forms fact2"

code_module EvalF
contains normal_forms

code_module Test
imports EvalF
contains "fact2"

ML "EvalF.normal_forms Test.fact2"

text {*
Unfortunately, the definition based
on evaluation contexts from \secref{sec:evaluation-ctxt} is not directly executable.
The reason is that from the definition of evaluation contexts, the code generator
cannot immediately read off an algorithm that, given a term @{text t}, computes a context
@{text E} and a term @{text "t\<^isub>0"} such that @{text "t = E t\<^isub>0"}. In order to do this, one
would have to extract the algorithm contained in the proof of the {\it decomposition lemma}
from \secref{sec:evaluation-ctxt}.
*}

(*<*)
end
(*>*)