chapter \<open>Derive\<close>
text \<open>
This theory includes the Isabelle/ML code needed for the derivation and exports the two keywords
\texttt{derive\_generic} and \texttt{derive\_generic\_setup}.
\<close>

theory Derive
  imports Main Tagged_Prod_Sum
  keywords "derive_generic" :: thy_decl
       and "derive_generic_setup" :: thy_decl
begin

context begin

qualified definition iso :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
"iso from to = ((\<forall> a. to (from a) = a) \<and> (\<forall> b . from (to b) = b))"

lemma iso_intro: "(\<And>a. to (from a) = a) \<Longrightarrow> (\<And>b. from (to b) = b) \<Longrightarrow> iso from to"
  unfolding iso_def by simp

end

ML_file "derive_util.ML"
ML_file "derive_laws.ML"
ML_file "derive_setup.ML"
ML_file "derive.ML"

end