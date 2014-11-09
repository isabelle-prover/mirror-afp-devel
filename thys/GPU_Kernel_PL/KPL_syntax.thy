section {* Syntax of KPL *}

theory KPL_syntax imports 
  Misc
begin

text{* Locations of local variables *}
typedecl V 

text {* C strings *}
typedecl name

text {* Procedure names *}
typedecl proc_name

text {* Local-id, group-id *}
type_synonym lid = nat
type_synonym gid = nat

text {* Fully-qualified thread-id *}
type_synonym tid = "gid \<times> lid"

text {* Let @{term "(G,T)"} range over threadsets *}
type_synonym threadset = "gid set \<times> (gid \<rightharpoonup> lid set)"

text {* Returns the set of tids in a threadset *}
fun tids :: "threadset \<Rightarrow> tid set"
where
  "tids (G,T) = {(i,j) | i j. i \<in> G \<and> j \<in> the (T i)}"

type_synonym word = nat  (* should really be machine words *)

datatype loc =
  Name name
| Var V

text {* Local expressions *}
datatype local_expr =
  Loc loc
| Gid
| Lid
| eTrue
| eConj local_expr local_expr  (infixl "\<and>*" 50)
| eNot local_expr              ("\<not>*")

text {* Basic statements *}
datatype basic_stmt =
  Assign loc local_expr
| Read loc local_expr
| Write local_expr local_expr

text {* Statements *}
datatype stmt =
  Basic basic_stmt
| Seq stmt stmt (infixl ";;" 50)
| Local name stmt
| If local_expr stmt stmt
| While local_expr stmt
| WhileDyn local_expr stmt
| Call proc_name local_expr
| Barrier
| Break
| Continue
| Return

text {* Procedures comprise a procedure name, parameter name, and a body statement *}
record proc = 
  proc_name :: proc_name
  param :: name
  body :: stmt

text {* Kernels *}
record kernel = 
  groups :: nat
  threads :: nat
  procs :: "proc list"
  main :: stmt

end
