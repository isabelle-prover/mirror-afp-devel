theory logics_operators
  imports conditions_positive
begin

subsection \<open>Converting between topological operators\<close>

text\<open>We verify minimal conditions under which operators resulting from conversion functions coincide.\<close>

text\<open>Conversions between interior, closure and exterior are straightforward and hold without restrictions: 
  Interior and closure are each other duals. Exterior is the complement of closure.
  We focus here on conversions involving the border and frontier operators.\<close>

text\<open>Interior operator as derived from border.\<close>
definition Int_br::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<I>\<^sub>B") 
  where "\<I>\<^sub>B \<B> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<B> A)"
text\<open>Interior operator as derived from frontier.\<close>
definition Int_fr::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<I>\<^sub>F") 
  where "\<I>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<F> A)"
text\<open>Closure operator as derived from border.\<close>
definition Cl_br::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<C>\<^sub>B") 
  where "\<C>\<^sub>B \<B> \<equiv> \<lambda>A. A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"
text\<open>Closure operator as derived from frontier.\<close>
definition Cl_fr::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<C>\<^sub>F") 
  where "\<C>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<or> (\<F> A)"
text\<open>Frontier operator as derived from interior.\<close>
definition Fr_int::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<F>\<^sub>I") 
  where "\<F>\<^sub>I \<I> \<equiv> \<lambda>A. \<^bold>\<midarrow>(\<I> A \<^bold>\<or> \<I>(\<^bold>\<midarrow>A))"
text\<open>Frontier operator as derived from closure.\<close>
definition Fr_cl::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<F>\<^sub>C") 
  where "\<F>\<^sub>C \<C> \<equiv> \<lambda>A. (\<C> A) \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)"
text\<open>Frontier operator as derived from border.\<close>
definition Fr_br::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<F>\<^sub>B") 
  where "\<F>\<^sub>B \<B> \<equiv> \<lambda>A. \<B> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"
text\<open>Border operator as derived from interior.\<close>
definition Br_int::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<B>\<^sub>I") 
  where "\<B>\<^sub>I \<I> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<I> A)"
text\<open>Border operator as derived from closure.\<close>
definition Br_cl::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<B>\<^sub>C")  
  where "\<B>\<^sub>C \<C> \<equiv> \<lambda>A. A \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)"
text\<open>Border operator as derived from frontier.\<close>
definition Br_fr::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<B>\<^sub>F") 
  where "\<B>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<and> (\<F> A)"

text\<open>Inter-definitions involving border or frontier do not hold without restrictions.\<close>
lemma "\<B> = \<B>\<^sub>C (\<C>\<^sub>B \<B>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<B> = \<B>\<^sub>I (\<I>\<^sub>B \<B>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<B> = \<B>\<^sub>F (\<F>\<^sub>B \<B>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<F> = \<F>\<^sub>C (\<C>\<^sub>F \<F>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<F> = \<F>\<^sub>I (\<I>\<^sub>F \<F>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<F> = \<F>\<^sub>B (\<B>\<^sub>F \<F>)" nitpick oops \<comment>\<open> countermodel \<close>

lemma "\<C> = \<C>\<^sub>B (\<B>\<^sub>C \<C>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<C> = \<C>\<^sub>F (\<F>\<^sub>C \<C>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<I> = \<I>\<^sub>B (\<B>\<^sub>C \<I>)" nitpick oops \<comment>\<open> countermodel \<close>
lemma "\<I> = \<I>\<^sub>F (\<F>\<^sub>C \<I>)" nitpick oops \<comment>\<open> countermodel \<close>


text\<open>Inter-definitions involving border or frontier always assume the second Kuratowski condition 
  (or its respective counterpart: C2, I2, B2 or F2).\<close>
abbreviation "C2 \<phi> \<equiv> EXPN \<phi>"
abbreviation "I2 \<phi> \<equiv> CNTR \<phi>"
abbreviation "B2 \<phi> \<equiv> CNTR \<phi>"
abbreviation "F2 \<phi> \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>A) \<^bold>= \<phi> A"

lemma "B2 \<B> \<Longrightarrow> \<B> = \<B>\<^sub>C (\<C>\<^sub>B \<B>)" unfolding CNTR_def Br_cl_def Cl_br_def conn order by metis
lemma "B2 \<B> \<Longrightarrow> \<B> = \<B>\<^sub>I (\<I>\<^sub>B \<B>)" unfolding CNTR_def Br_int_def Int_br_def conn order by metis
lemma "B2 \<B> \<Longrightarrow> \<B> = \<B>\<^sub>F (\<F>\<^sub>B \<B>)" unfolding CNTR_def Br_fr_def Fr_br_def conn order by metis
lemma "F2 \<F> \<Longrightarrow> \<F> = \<F>\<^sub>C (\<C>\<^sub>F \<F>)" unfolding Cl_fr_def Fr_cl_def conn order by metis
lemma "F2 \<F> \<Longrightarrow> \<F> = \<F>\<^sub>I (\<I>\<^sub>F \<F>)" unfolding Int_fr_def Fr_int_def conn order by metis
lemma "F2 \<F> \<Longrightarrow> \<F> = \<F>\<^sub>B (\<B>\<^sub>F \<F>)" unfolding Br_fr_def Fr_br_def conn order by metis

lemma "C2 \<C> \<Longrightarrow> \<C> = \<C>\<^sub>B (\<B>\<^sub>C \<C>)" unfolding EXPN_def Br_cl_def Cl_br_def conn order by metis
lemma "C2 \<C> \<Longrightarrow> \<C> = \<C>\<^sub>F (\<F>\<^sub>C \<C>)" unfolding EXPN_def Fr_cl_def Cl_fr_def conn order by metis
lemma "I2 \<I> \<Longrightarrow> \<I> = \<I>\<^sub>B (\<B>\<^sub>I \<I>)" unfolding CNTR_def Int_br_def Br_int_def conn order by metis
lemma "I2 \<I> \<Longrightarrow> \<I> = \<I>\<^sub>F (\<F>\<^sub>I \<I>)" unfolding CNTR_def Int_fr_def Fr_int_def conn order by metis

end
