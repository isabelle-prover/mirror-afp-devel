theory Program_Graph imports Labeled_Transition_Systems.LTS Datalog begin


section \<open>Actions\<close>

datatype (fv_arith: 'v) arith =
  Integer int
  | Arith_Var 'v
  | Arith_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> int" "'v arith"
  | Minus "'v arith"

datatype (fv_boolean: 'v) boolean =
  true
  | false
  | Rel_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> bool" "'v arith"
  | Bool_Op "'v boolean" "bool \<Rightarrow> bool \<Rightarrow> bool" "'v boolean"
  | Neg "'v boolean"

datatype 'v action =
  Asg 'v "'v arith" ("_ ::= _" [1000, 61] 61)
  | Bool "'v boolean"
  | Skip


section \<open>Memories\<close>

type_synonym 'v memory = "'v \<Rightarrow> int"


section \<open>Semantics\<close>

fun sem_arith :: "'v arith \<Rightarrow> 'v memory \<Rightarrow> int" where
  "sem_arith (Integer n) \<sigma> = n"
| "sem_arith (Arith_Var x) \<sigma> = \<sigma> x"
| "sem_arith (Arith_Op a1 op a2) \<sigma> = op (sem_arith a1 \<sigma>) (sem_arith a2 \<sigma>)"
| "sem_arith (Minus a) \<sigma> = - (sem_arith a \<sigma>)"

fun sem_bool :: "'v boolean \<Rightarrow> 'v memory \<Rightarrow> bool" where
  "sem_bool true \<sigma> = True"
| "sem_bool false \<sigma> = False"
| "sem_bool (Rel_Op a1 op a2) \<sigma> = op (sem_arith a1 \<sigma>) (sem_arith a2 \<sigma>)"
| "sem_bool (Bool_Op b1 op b2) \<sigma> = op (sem_bool b1 \<sigma>) (sem_bool b2 \<sigma>)"
| "sem_bool (Neg b) \<sigma> = (\<not>(sem_bool b \<sigma>))"

fun sem_action :: "'v action \<Rightarrow> 'v memory \<rightharpoonup> 'v memory" where
  "sem_action (x ::= a) \<sigma> = Some (\<sigma>(x := sem_arith a \<sigma>))"
| "sem_action (Bool b) \<sigma> = (if sem_bool b \<sigma> then Some \<sigma> else None)"
| "sem_action Skip \<sigma> = Some \<sigma>"


section \<open>Program Graphs\<close>


subsection \<open>Types\<close>

type_synonym ('n,'a) edge = "'n \<times> 'a \<times> 'n"

type_synonym ('n,'a) program_graph = "('n,'a) edge set \<times> 'n \<times> 'n"

type_synonym ('n,'v) config = "'n * 'v memory"


subsection \<open>Program Graph Locale\<close>

locale program_graph = 
  fixes pg :: "('n,'a) program_graph"
begin

definition edges where 
  "edges = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition pg_rev :: "('n,'a) program_graph" where
  "pg_rev = (rev_edge ` edges, end, start)"

end

subsection \<open>Finite Program Graph Locale\<close>

locale finite_program_graph = program_graph pg
  for pg :: "('n::finite,'v) program_graph" +
  assumes "finite edges"
begin

lemma finite_pg_rev: "finite (fst pg_rev)"
  by (metis finite_program_graph_axioms finite_program_graph_def finite_imageI fst_conv pg_rev_def)

end

locale finite_action_program_graph = 
  fixes pg :: "('n,'v action) program_graph"
begin

interpretation program_graph pg .

\<comment> \<open>Execution Sequences:\<close>

fun initial_config_of :: "('n,'v) config \<Rightarrow> bool" where
  "initial_config_of (q,\<sigma>) \<longleftrightarrow> q = start"

fun final_config_of :: "('n,'v) config \<Rightarrow> bool" where
  "final_config_of (q,\<sigma>) \<longleftrightarrow> q = end"

inductive exe_step :: "('n,'v) config \<Rightarrow> 'v action \<Rightarrow> ('n,'v) config \<Rightarrow> bool" where
  "(q1, \<alpha>, q2) \<in> edges \<Longrightarrow> sem_action \<alpha> \<sigma> = Some \<sigma>' \<Longrightarrow> exe_step (q1,\<sigma>) \<alpha> (q2,\<sigma>')"

end


end
