theory logics_quantifiers_example
  imports logics_quantifiers conditions_positive_infinitary
begin

subsection \<open>Examples on Quantifiers\<close>

text\<open>First-order quantification example.\<close>
lemma "(\<forall>x. A x \<longrightarrow> (\<exists>y. B x y)) \<longleftrightarrow> (\<forall>x. \<exists>y. A x \<longrightarrow> B x y)" by simp
lemma "(\<^bold>\<forall>x. A x  \<^bold>\<rightarrow> (\<^bold>\<exists>y. B x y))  \<^bold>= (\<^bold>\<forall>x. \<^bold>\<exists>y. A x  \<^bold>\<rightarrow>  B x y)" by (simp add: impl_def mexists_def setequ_def)

text\<open>Propositional quantification example.\<close>
lemma "\<forall>A. (\<exists>B. (A \<longleftrightarrow> \<not>B))" by blast
lemma "(\<^bold>\<forall>A. (\<^bold>\<exists>B. A  \<^bold>\<leftrightarrow> \<^bold>\<midarrow>B)) \<^bold>= \<^bold>\<top>" unfolding mforall_def mexists_def by (smt (verit) compl_def dimpl_def setequ_def top_def)

text\<open>Drinker's principle.\<close>
lemma "\<^bold>\<exists>x. Drunk x \<^bold>\<rightarrow> (\<^bold>\<forall>y. Drunk y) \<^bold>= \<^bold>\<top>"
  by (simp add: impl_def mexists_def mforall_def setequ_def top_def)

text\<open>Example in non-classical logics.\<close>
typedecl w 
type_synonym \<sigma> = "(w \<sigma>)"

consts \<C>::"\<sigma> \<Rightarrow> \<sigma>"
abbreviation "\<I> \<equiv> \<C>\<^sup>d"
abbreviation "CLOSURE \<phi> \<equiv> ADDI \<phi> \<and> EXPN \<phi> \<and> NORM \<phi> \<and> IDEM \<phi>"
abbreviation "INTERIOR \<phi> \<equiv> MULT \<phi> \<and> CNTR \<phi> \<and> DNRM \<phi> \<and> IDEM \<phi>"

definition mforallInt::"(\<sigma> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<Pi>\<^sup>I_") 
  where "\<^bold>\<Pi>\<^sup>I\<phi> \<equiv> \<^bold>\<Pi>[fp \<I>]\<phi>"
definition mexistsInt::"(\<sigma> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<Sigma>\<^sup>I_") 
  where "\<^bold>\<Sigma>\<^sup>I\<phi> \<equiv> \<^bold>\<Sigma>[fp \<I>]\<phi>"

(*To improve readability, we introduce for them standard binder notation.*)
notation mforallInt (binder "\<^bold>\<forall>\<^sup>I" [48]49) 
notation mexistsInt (binder "\<^bold>\<exists>\<^sup>I" [48]49) 

abbreviation intneg ("\<^bold>\<not>\<^sup>I_") where "\<^bold>\<not>\<^sup>IA \<equiv> \<I>\<^sup>d\<^sup>- A"
abbreviation parneg ("\<^bold>\<not>\<^sup>C_") where "\<^bold>\<not>\<^sup>CA \<equiv> \<C>\<^sup>d\<^sup>- A"

lemma "(\<^bold>\<forall>X. (\<^bold>\<exists>B. (X  \<^bold>\<leftrightarrow> \<^bold>\<midarrow>B))) \<^bold>= \<^bold>\<top>" by (smt (verit, del_insts) compl_def dimpl_def mexists_def mforall_def setequ_def top_def)
lemma "(\<^bold>\<forall>\<^sup>IX. (\<^bold>\<exists>\<^sup>IB. (X  \<^bold>\<leftrightarrow> \<^bold>\<not>\<^sup>IB))) \<^bold>= \<^bold>\<top>" nitpick oops \<comment>\<open> counterexample \<close>


subsection \<open>Barcan formula and its converse\<close>

text\<open>The converse Barcan formula follows readily from monotonicity.\<close>
lemma CBarcan1: "MONO \<phi> \<Longrightarrow> \<forall>\<pi>.  \<phi>(\<^bold>\<forall>x. \<pi> x)  \<^bold>\<le> (\<^bold>\<forall>x. \<phi>(\<pi> x))" by (smt (verit, ccfv_SIG) MONO_def mforall_def subset_def)
lemma CBarcan2: "MONO \<phi> \<Longrightarrow> \<forall>\<pi>. (\<^bold>\<exists>x. \<phi>(\<pi> x)) \<^bold>\<le> \<phi>(\<^bold>\<exists>x. \<pi> x)" by (smt (verit) MONO_def mexists_def subset_def)

text\<open>However, the Barcan formula requires a stronger assumption (of an infinitary character).\<close>
lemma Barcan1: "iMULT\<^sup>b \<phi> \<Longrightarrow> \<forall>\<pi>. (\<^bold>\<forall>x. \<phi>(\<pi> x)) \<^bold>\<le> \<phi>(\<^bold>\<forall>x. \<pi> x)" unfolding iMULT_b_def by (smt (verit) infimum_def mforall_char image_def range_char1 subset_def)
lemma Barcan2: "iADDI\<^sup>a \<phi> \<Longrightarrow> \<forall>\<pi>. \<phi>(\<^bold>\<exists>x. \<pi> x) \<^bold>\<le> (\<^bold>\<exists>x. \<phi>(\<pi> x))" unfolding iADDI_a_def by (smt (verit, ccfv_threshold) mexists_char image_def range_char1 subset_def supremum_def)

text\<open>Converse Barcan Formula and composition.\<close>
lemma "MONO \<phi> \<Longrightarrow> \<forall>\<pi>.  \<phi>(\<^bold>\<Pi> \<pi>) \<^bold>\<le> \<^bold>\<Pi>(\<phi> \<circ> \<pi>)" by (metis MONO_iMULTa iMULT_a_def mforall_char mforall_comp mforall_const_char)
lemma "MONO \<phi> \<Longrightarrow> \<forall>\<pi>.  \<phi>(\<^bold>\<Pi>[D] \<pi>) \<^bold>\<le> \<^bold>\<Pi>[D](\<phi> \<circ> \<pi>)"  by (smt (verit) MONO_iMULTa fun_comp_def iMULT_a_def mforall_const_char mforall_const_def image_def subset_def)
lemma "CNTR \<phi> \<Longrightarrow> iMULT \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow>  \<forall>\<pi>.  \<phi>(\<^bold>\<Pi>{\<psi>} \<pi>) \<^bold>\<le> \<^bold>\<Pi>{\<psi>}(\<phi> \<circ> \<pi>)" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>Barcan Formula and composition.\<close>
lemma "iMULT\<^sup>b \<phi> \<Longrightarrow> \<forall>\<pi>. \<^bold>\<Pi>(\<phi> \<circ> \<pi>) \<^bold>\<le> \<phi>(\<^bold>\<Pi> \<pi>)" by (metis iMULT_b_def mforall_char mforall_comp mforall_const_char)
lemma "iMULT\<^sup>b \<phi> \<Longrightarrow> \<forall>\<pi>. \<^bold>\<Pi>[D](\<phi> \<circ> \<pi>) \<^bold>\<le> \<phi>(\<^bold>\<Pi>[D] \<pi>)" by (smt (verit) fun_comp_def iMULT_b_def infimum_def mforall_const_char image_def subset_def)
lemma "iADDI \<phi> \<Longrightarrow> iMULT \<phi> \<Longrightarrow> \<forall>\<pi>. \<^bold>\<Pi>{\<psi>}(\<phi> \<circ> \<pi>) \<^bold>\<le> \<phi>(\<^bold>\<Pi>{\<psi>} \<pi>)" nitpick oops \<comment>\<open> counterexample \<close>

end
