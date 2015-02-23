theory CoCallAnalysisSig
imports Terms Arity CoCallGraph
begin

locale CoCallAnalysis =
  fixes ccExp :: "exp \<Rightarrow> Arity \<rightarrow> CoCalls"

locale CoCallAnalyisHeap = 
  fixes ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"

end
