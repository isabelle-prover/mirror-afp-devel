theory Preprocessor 
imports 
  PCompiler
  "../J/Annotate"
begin

primrec annotate_Mb :: "J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> (vname list \<times> expr) \<Rightarrow> (vname list \<times> expr)"
where "annotate_Mb P C M Ts T (pns, e) = (pns, annotate P [this # pns [\<mapsto>] Class C # Ts] e)"

declare annotate_Mb.simps [simp del]

definition annotate_prog :: "J_prog \<Rightarrow> J_prog"
where "annotate_prog P = compP (annotate_Mb P) P"

end

