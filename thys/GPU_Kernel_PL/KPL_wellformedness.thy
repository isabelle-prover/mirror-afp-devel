section {* Well-formedness of KPL kernels *}

theory KPL_wellformedness imports 
  KPL_syntax
begin

text {* 
  Well-formed local expressions. @{term "wf_local_expr ns e"} 
  means that 
  \begin{itemize} 
  \item @{term e} does not mention any internal locations, and
  \item any name mentioned by @{term e} is in the set @{term ns}.
  \end{itemize}
*}
fun wf_local_expr :: "name set \<Rightarrow> local_expr \<Rightarrow> bool"
where
  "wf_local_expr ns (Loc (Var j)) = False"
| "wf_local_expr ns (Loc (Name n)) = (n \<in> ns)"
| "wf_local_expr ns (e1 \<and>* e2) =
  (wf_local_expr ns e1 \<and> wf_local_expr ns e2)"
| "wf_local_expr ns (\<not>* e) = wf_local_expr ns e"
| "wf_local_expr ns _ = True"

text {* 
  Well-formed basic statements. @{term "wf_basic_stmt ns b"} 
  means that 
  \begin{itemize}
  \item @{term b} does not mention any internal locations, and
  \item any name mentioned by @{term b} is in the set @{term ns}.
  \end{itemize}
*}
fun wf_basic_stmt :: "name set \<Rightarrow> basic_stmt \<Rightarrow> bool"
where
  "wf_basic_stmt ns (Assign x e) = wf_local_expr ns e"
| "wf_basic_stmt ns (Read x e) = wf_local_expr ns e"
| "wf_basic_stmt ns (Write e1 e2) = 
  (wf_local_expr ns e1 \<and> wf_local_expr ns e2)"

text {* 
  Well-formed statements. @{term "wf_stmt ns F S"} means:
  \begin{itemize}
  \item @{term S} only calls procedures whose name is in @{term F},
  \item @{term S} does not contain @{term WhileDyn}, 
  \item @{term S} does not mention internal variables, 
  \item @{term S} only mentions names in @{term ns}, and
  \item @{term S} does not declare the same name twice, e.g. @{term "Local x (Local x foo)"}.
  \end{itemize}
*}
fun wf_stmt :: "name set \<Rightarrow> proc_name set \<Rightarrow> stmt \<Rightarrow> bool"
where
  "wf_stmt ns F (Basic b) = wf_basic_stmt ns b"
| "wf_stmt ns F (S1 ;; S2) = (wf_stmt ns F S1 \<and> wf_stmt ns F S2)"
| "wf_stmt ns F (Local n S) = (n \<notin> ns \<and> wf_stmt ({n} \<union> ns) F S)"
| "wf_stmt ns F (If e S1 S2) = 
  (wf_local_expr ns e \<and> wf_stmt ns F S1 \<and> wf_stmt ns F S2)"
| "wf_stmt ns F (While e S) = 
  (wf_local_expr ns e \<and> wf_stmt ns F S)"
| "wf_stmt ns F (WhileDyn _ _) = False"
| "wf_stmt ns F (Call f e) = (f \<in> F \<and> wf_local_expr ns e)"
| "wf_stmt _ _ _ = True"

text {* @{term "no_return S"} holds if @{term S} does not contain a @{term Return} statement *}
fun no_return :: "stmt \<Rightarrow> bool"
where
  "no_return (S1 ;; S2) = (no_return S1 \<and> no_return S2)"
| "no_return (Local n S) = no_return S"
| "no_return (If e S1 S2) = (no_return S1 \<and> no_return S2)"
| "no_return (While e S) = (no_return S)"
| "no_return Return = False"
| "no_return _ = True"

text {* Well-formed kernel *}
definition wf_kernel :: "kernel \<Rightarrow> bool"
where
  "wf_kernel P \<equiv>
  let F = set (map proc_name (procs P)) in
 
  (* The main statement must not refer to *any*
     variable, except those it locally defines. *)
  wf_stmt {} F (main P)

  (* The main statement contains no return statement. *)
\<and> no_return (main P)
 
  (* A procedure body may refer only to its argument. *)
\<and> list_all (\<lambda>f. wf_stmt {param f} F (body f)) (procs P)"


end
