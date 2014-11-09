section {* Miscellaneous Lemmas *}
theory Sep_Misc
imports Main "../../Automatic_Refinement/Lib/Misc"
begin
  text {* These lemmas are candidates to be pushed into the Isabelle/HOL 
    standard libraries *}

lemma imp_mp_iff[simp]: "a \<and> (a \<longrightarrow> b) \<longleftrightarrow> a \<and> b" 
  by metis

lemma Un_empty'[simp]: 
  "{} = a\<union>b \<longleftrightarrow> a={} \<and> b={}" 
  by auto

text {* The following lemma is useful to split non-empty lists. *}  
lemma list_not_emptyE: 
  assumes "l\<noteq>[]"
  obtains x xs where "l=x#xs" 
  using assms by (metis list.exhaust)

lemma map_of_eq_empty_iff [simp]:
  "map_of xs = Map.empty \<longleftrightarrow> xs=[]"
proof 
  assume "map_of xs = Map.empty"
  thus "xs = []" by (induct xs) simp_all
qed auto

end
