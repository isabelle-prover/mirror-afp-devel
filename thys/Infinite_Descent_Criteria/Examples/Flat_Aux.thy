(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

section "Instantiating the Abstract Framework"

text "We now provide concrete examples of this framework in action applying a range of the criterion shown "

subsection "Infinite Descent Examples"
subsubsection "Flat Aux Example"
theory Flat_Aux
  imports "../Criterion/All"
begin


(*we encode only the recursive cases, others trivially terminate*)
fun flat and aux where
  "flat [] = []"
 |"flat (l#ls) = aux l ls"
 |"aux [] ls = flat ls"
 |"aux (x#xs) ls = x # aux xs ls"

(*the following are the agda call matrices generated*)
(*I will use these for the example, note that agda adds hidden "meta" arguements, which is why 
  Flat has 2 arguments, and Aux has 3, as opposed to the above function....*)
(*
 Flat \<rightarrow> Aux        
           -1
           -1
 Aux \<rightarrow> Flat
           ?     =
 Aux \<rightarrow> Aux
           -1    ?
           ?     = 
*)

(*types*)
datatype node = Flat | Aux
type_synonym pos = nat

(*Nodes, Edges, Positions and Relations between them*)
definition "Node \<equiv> {Flat, Aux}"

lemma nd_aux[simp]:"nd \<noteq> Aux \<longleftrightarrow> nd = Flat" by(cases nd, auto)
lemma nd_flat[simp]:"nd \<noteq> Flat \<longleftrightarrow> nd = Aux" by(cases nd, auto)

lemma alw_nodes:"alw (holdsS Node) nds" 
  unfolding alw_holdsS_iff_snth Node_def apply(rule allI)
  subgoal for i by(induct i, auto) .

fun edge::"node \<Rightarrow> node \<Rightarrow> bool" where
"edge Flat Aux = HOL.True"|
"edge Aux _ = HOL.True"|
"edge Flat Flat = HOL.False"

lemma edge_Flat[simp]:"edge Flat x \<longleftrightarrow> x = Aux" by(cases x, auto)

lemma edge_Flat'[simp]:"edge nd Flat \<longleftrightarrow> nd = Aux" by(cases nd, auto)

fun PosOf::"node \<Rightarrow> pos set" where 
"PosOf Flat = {0}"|
"PosOf Aux = {0,1}"

(*sets relating positions together*)
definition RR_set :: "((node \<times> pos) \<times> (node \<times> pos) \<times> slope) set" where
  "RR_set = {
     ((Flat, 0), (Aux, 0), Decr),
     ((Flat, 0), (Aux, 1), Decr),
     ((Aux, 1), (Flat, 0), Main),
     ((Aux, 0), (Aux, 0), Decr),
     ((Aux, 1), (Aux, 1), Main)
   }"


definition RR :: "node \<times> pos \<Rightarrow> node \<times> pos \<Rightarrow> slope \<Rightarrow> bool" where
  "RR np1 np2 s \<equiv> ((np1, np2, s) \<in> RR_set)"

definition RRs :: "node \<Rightarrow> node \<Rightarrow> (pos \<Rightarrow> pos \<Rightarrow> slope \<Rightarrow> bool)" where
  "RRs n n' \<equiv> (\<lambda>p p' s. (((n, p), (n, p'), s) \<in> RR_set))"

lemmas RRs_defs = RRs_def RR_set_def

lemmas RR_defs = RR_def RR_set_def
lemma RR_aux_aux_1[simp]:"RR (Aux, 0) (Aux, 0) Decr" unfolding RR_defs by auto


(*RR sound*)
lemma P_inPosOf:"RR (nd, P) (nd', P') sl \<Longrightarrow> P \<in> PosOf nd"
                 "RR (nd, P) (nd', P') sl \<Longrightarrow> P' \<in> PosOf nd'" by(auto simp: RR_defs)

interpretation Sloped_Graph where 
  Node = Node and edge = edge and PosOf = PosOf and RR = RR 
  apply unfold_locales
  by(auto simp: RR_defs SlopedRels_def Node_def elim: PosOf.cases)

lemma lang_run_inj:"x \<in> NBA.language Paut\<^sub>V \<Longrightarrow> \<exists>r. NBA.run Paut\<^sub>V (x ||| r) None"
  by(erule nba.language_elim, auto)

end
