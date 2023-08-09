theory conditions_relativized
  imports conditions_negative
begin

subsection \<open>Relativized Conditions\<close>

text\<open>We continue defining and interrelating axiomatic conditions on unary operations (operators). 
 This time we consider their 'relativized' variants.\<close>

text\<open>Relativized order and equality relations.\<close>
definition subset_in::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<^bold>\<le>\<^sub>__") 
  where \<open>A \<^bold>\<le>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>
definition subset_out::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<^bold>\<le>\<^sup>__") 
  where \<open>A \<^bold>\<le>\<^sup>U B \<equiv> \<forall>x. \<not>U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>
definition setequ_in::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<^bold>=\<^sub>__") 
  where \<open>A \<^bold>=\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>
definition setequ_out::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<^bold>=\<^sup>__") 
  where \<open>A \<^bold>=\<^sup>U B \<equiv> \<forall>x. \<not>U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>

declare subset_in_def[order] subset_out_def[order] setequ_in_def[order] setequ_out_def[order]

lemma subset_in_out: "(let U=C in (A \<^bold>\<le>\<^sub>U B)) = (let U=\<^bold>\<midarrow>C in (A \<^bold>\<le>\<^sup>U B))" by (simp add: compl_def subset_in_def subset_out_def)
lemma setequ_in_out: "(let U=C in (A \<^bold>=\<^sub>U B)) = (let U=\<^bold>\<midarrow>C in (A \<^bold>=\<^sup>U B))" by (simp add: compl_def setequ_in_def setequ_out_def)

lemma subset_in_char: "(A \<^bold>\<le>\<^sub>U B) = (U \<^bold>\<and> A \<^bold>\<le> U \<^bold>\<and> B)" unfolding order conn by blast
lemma subset_out_char: "(A \<^bold>\<le>\<^sup>U B) = (U \<^bold>\<or> A \<^bold>\<le> U \<^bold>\<or> B)" unfolding order conn by blast
lemma setequ_in_char: "(A \<^bold>=\<^sub>U B) = (U \<^bold>\<and> A \<^bold>= U \<^bold>\<and> B)" unfolding order conn by blast
lemma setequ_out_char: "(A \<^bold>=\<^sup>U B) = (U \<^bold>\<or> A \<^bold>= U \<^bold>\<or> B)" unfolding order conn by blast

text\<open>Relativization cannot be meaningfully applied to conditions (n)NORM or (n)DNRM.\<close>
lemma "NORM \<phi>  = (let U = \<^bold>\<top> in ((\<phi> \<^bold>\<bottom>) \<^bold>=\<^sub>U \<^bold>\<bottom>))" by (simp add: NORM_def setequ_def setequ_in_def top_def)
lemma "(let U = \<^bold>\<bottom> in ((\<phi> \<^bold>\<bottom>) \<^bold>=\<^sub>U \<^bold>\<bottom>))" by (simp add: bottom_def setequ_in_def)

text\<open>Relativization ('in' resp. 'out') leaves (n)EXPN/(n)CNTR unchanged or trivializes them.\<close>
lemma "EXPN \<phi>  = (\<forall>A. A \<^bold>\<le>\<^sub>A \<phi> A)" by (simp add: EXPN_def subset_def subset_in_def)
lemma "CNTR \<phi>  = (\<forall>A. (\<phi> A) \<^bold>\<le>\<^sup>A A)" by (metis (mono_tags, lifting) CNTR_def subset_def subset_out_def)
lemma "\<forall>A. A \<^bold>\<le>\<^sup>A \<phi> A" by (simp add: subset_out_def)
lemma "\<forall>A. (\<phi> A) \<^bold>\<le>\<^sub>A A" by (simp add: subset_in_def)


text\<open>Relativized ADDI variants.\<close>
definition ADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr")
  where "ADDIr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<^bold>=\<^sup>U (\<phi> A) \<^bold>\<or> (\<phi> B))"
definition ADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr\<^sup>a")
  where "ADDIr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<^bold>\<le>\<^sup>U (\<phi> A) \<^bold>\<or> (\<phi> B))" 
definition ADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr\<^sup>b")
  where "ADDIr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ((\<phi> A) \<^bold>\<or> (\<phi> B) \<^bold>\<le>\<^sup>U \<phi>(A \<^bold>\<or> B))"
 
declare ADDIr_def[cond] ADDIr_a_def[cond] ADDIr_b_def[cond]

lemma ADDIr_char: "ADDIr \<phi> = (ADDIr\<^sup>a \<phi> \<and> ADDIr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_out_char subset_out_char)

lemma ADDIr_a_impl: "ADDI\<^sup>a \<phi> \<longrightarrow> ADDIr\<^sup>a \<phi>" by (simp add: ADDI_a_def ADDIr_a_def subset_def subset_out_def)
lemma ADDIr_a_equ:  "EXPN \<phi> \<Longrightarrow> ADDIr\<^sup>a \<phi> = ADDI\<^sup>a \<phi>" unfolding cond by (smt (verit, del_insts) join_def subset_def subset_out_def)
lemma ADDIr_a_equ':"nEXPN \<phi> \<Longrightarrow> ADDIr\<^sup>a \<phi> = ADDI\<^sup>a \<phi>" unfolding cond by (smt (verit, ccfv_threshold) compl_def subset_def subset_out_def)

lemma ADDIr_b_impl: "ADDI\<^sup>b \<phi> \<longrightarrow> ADDIr\<^sup>b \<phi>" by (simp add: ADDI_b_def ADDIr_b_def subset_def subset_out_def)
lemma "nEXPN \<phi> \<Longrightarrow> ADDIr\<^sup>b \<phi> \<longrightarrow> ADDI\<^sup>b \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma ADDIr_b_equ: "EXPN \<phi> \<Longrightarrow> ADDIr\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" unfolding cond by (smt (z3) subset_def subset_out_def)


text\<open>Relativized MULT variants.\<close>
definition MULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr")
  where "MULTr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<^bold>=\<^sub>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition MULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr\<^sup>a")
  where "MULTr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<^bold>\<le>\<^sub>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition MULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr\<^sup>b")
  where "MULTr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ((\<phi> A) \<^bold>\<and> (\<phi> B) \<^bold>\<le>\<^sub>U \<phi>(A \<^bold>\<and> B))"

declare MULTr_def[cond] MULTr_a_def[cond] MULTr_b_def[cond]

lemma MULTr_char: "MULTr \<phi> = (MULTr\<^sup>a \<phi> \<and> MULTr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_in_char subset_in_char)

lemma MULTr_a_impl: "MULT\<^sup>a \<phi> \<longrightarrow> MULTr\<^sup>a \<phi>" by (simp add: MULT_a_def MULTr_a_def subset_def subset_in_def)
lemma "nCNTR \<phi> \<Longrightarrow> MULTr\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>a \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma MULTr_a_equ: "CNTR \<phi> \<Longrightarrow> MULTr\<^sup>a \<phi> = MULT\<^sup>a \<phi>" unfolding cond by (smt (verit, del_insts) subset_def subset_in_def)

lemma MULTr_b_impl: "MULT\<^sup>b \<phi> \<longrightarrow> MULTr\<^sup>b \<phi>" by (simp add: MULT_b_def MULTr_b_def subset_def subset_in_def)
lemma "MULTr\<^sup>b \<phi> \<longrightarrow> MULT\<^sup>b \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma MULTr_b_equ:  "CNTR \<phi> \<Longrightarrow> MULTr\<^sup>b \<phi> = MULT\<^sup>b \<phi>" unfolding cond by (smt (verit, del_insts) meet_def subset_def subset_in_def)
lemma MULTr_b_equ':"nCNTR \<phi> \<Longrightarrow> MULTr\<^sup>b \<phi> = MULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_in_def)

text\<open>Weak variants of monotonicity.\<close>
definition MONOw1::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MONOw\<^sup>1") 
  where "MONOw\<^sup>1 \<phi> \<equiv> \<forall>A B. A \<^bold>\<le> B \<longrightarrow> (\<phi> A) \<^bold>\<le> B \<^bold>\<or> (\<phi> B)"
definition MONOw2::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MONOw\<^sup>2")
  where "MONOw\<^sup>2 \<phi> \<equiv> \<forall>A B. A \<^bold>\<le> B \<longrightarrow> A \<^bold>\<and> (\<phi> A) \<^bold>\<le> (\<phi> B)"

declare MONOw1_def[cond] MONOw2_def[cond]

lemma MONOw1_ADDIr_b: "MONOw\<^sup>1 \<phi> = ADDIr\<^sup>b \<phi>" proof -
  have l2r: "MONOw\<^sup>1 \<phi> \<longrightarrow> ADDIr\<^sup>b \<phi>"  unfolding cond subset_out_char by (metis (mono_tags, opaque_lifting) L7 join_def subset_def) 
  have r2l: "ADDIr\<^sup>b \<phi> \<longrightarrow> MONOw\<^sup>1 \<phi>" unfolding cond subset_out_char by (metis (full_types) L9 join_def setequ_ext subset_def)
  show ?thesis using l2r r2l by blast
qed
lemma MONOw2_MULTr_a: "MONOw\<^sup>2 \<phi> = MULTr\<^sup>a \<phi>" proof -
  have l2r: "MONOw\<^sup>2 \<phi> \<longrightarrow> MULTr\<^sup>a \<phi>" unfolding cond subset_in_char by (meson L4 L5 L8 L9)
  have r2l:"MULTr\<^sup>a \<phi> \<longrightarrow> MONOw\<^sup>2 \<phi>" unfolding cond subset_in_char by (metis BA_distr1 L2 L5 L6 L9 setequ_ext)
  show ?thesis using l2r r2l by blast
qed

lemma MONOw1_impl: "MONO \<phi> \<longrightarrow> MONOw\<^sup>1 \<phi>" by (simp add: ADDIr_b_impl MONO_ADDIb MONOw1_ADDIr_b)
lemma "MONOw\<^sup>1 \<phi> \<longrightarrow> MONO \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma MONOw2_impl: "MONO \<phi> \<longrightarrow> MONOw\<^sup>2 \<phi>" by (simp add: MONO_MULTa MONOw2_MULTr_a MULTr_a_impl)
lemma "MONOw\<^sup>2 \<phi> \<longrightarrow> MONO \<phi>" nitpick oops \<comment>\<open> countermodel \<close>


text\<open>We have in fact that (n)CNTR (resp. (n)EXPN) implies MONOw-1/ADDIr-b (resp. MONOw-2/MULTr-a).\<close>
lemma CNTR_MONOw1_impl: "CNTR \<phi> \<longrightarrow> MONOw\<^sup>1 \<phi>" by (metis CNTR_def L3 MONOw1_def subset_char1)
lemma nCNTR_MONOw1_impl: "nCNTR \<phi> \<longrightarrow> MONOw\<^sup>1 \<phi>" by (smt (verit, ccfv_threshold) MONOw1_def compl_def join_def nCNTR_def subset_def)
lemma EXPN_MONOw2_impl: "EXPN \<phi> \<longrightarrow> MONOw\<^sup>2 \<phi>" by (metis EXPN_def L4 MONOw2_def subset_char1)
lemma nEXPN_MONOw2_impl: "nEXPN \<phi> \<longrightarrow> MONOw\<^sup>2 \<phi>" by (smt (verit) MONOw2_def compl_def meet_def nEXPN_def subset_def)

text\<open>Relativized nADDI variants.\<close>
definition nADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr")
  where "nADDIr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<^bold>=\<^sup>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition nADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr\<^sup>a")
  where "nADDIr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ((\<phi> A) \<^bold>\<and> (\<phi> B) \<^bold>\<le>\<^sup>U \<phi>(A \<^bold>\<or> B))" 
definition nADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr\<^sup>b")
  where "nADDIr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<^bold>\<le>\<^sup>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
 
declare nADDIr_def[cond] nADDIr_a_def[cond] nADDIr_b_def[cond]

lemma nADDIr_char: "nADDIr \<phi> = (nADDIr\<^sup>a \<phi> \<and> nADDIr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_out_char subset_out_char)

lemma nADDIr_a_impl: "nADDI\<^sup>a \<phi> \<longrightarrow> nADDIr\<^sup>a \<phi>" unfolding cond by (simp add: subset_def subset_out_def)
lemma "nADDIr\<^sup>a \<phi> \<longrightarrow> nADDI\<^sup>a \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma nADDIr_a_equ:  "EXPN \<phi> \<Longrightarrow> nADDIr\<^sup>a \<phi> = nADDI\<^sup>a \<phi>" unfolding cond by (smt (z3) subset_def subset_out_def)
lemma nADDIr_a_equ':"nEXPN \<phi> \<Longrightarrow> nADDIr\<^sup>a \<phi> = nADDI\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_out_def)

lemma nADDIr_b_impl: "nADDI\<^sup>b \<phi> \<longrightarrow> nADDIr\<^sup>b \<phi>" by (simp add: nADDI_b_def nADDIr_b_def subset_def subset_out_def)
lemma "EXPN \<phi> \<Longrightarrow> nADDIr\<^sup>b \<phi> \<longrightarrow> nADDI\<^sup>b \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma nADDIr_b_equ: "nEXPN \<phi> \<Longrightarrow> nADDIr\<^sup>b \<phi> = nADDI\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_out_def)


text\<open>Relativized nMULT variants.\<close>
definition nMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr")
  where "nMULTr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<^bold>=\<^sub>U (\<phi> A) \<^bold>\<or> (\<phi> B))"
definition nMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr\<^sup>a")
  where "nMULTr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ((\<phi> A) \<^bold>\<or> (\<phi> B) \<^bold>\<le>\<^sub>U \<phi>(A \<^bold>\<and> B))"
definition nMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr\<^sup>b")
  where "nMULTr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<^bold>\<le>\<^sub>U (\<phi> A) \<^bold>\<or> (\<phi> B))"

declare nMULTr_def[cond] nMULTr_a_def[cond] nMULTr_b_def[cond]

lemma nMULTr_char: "nMULTr \<phi> = (nMULTr\<^sup>a \<phi> \<and> nMULTr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_in_char subset_in_char)

lemma nMULTr_a_impl: "nMULT\<^sup>a \<phi> \<longrightarrow> nMULTr\<^sup>a \<phi>" by (simp add: nMULT_a_def nMULTr_a_def subset_def subset_in_def)
lemma "CNTR \<phi> \<Longrightarrow> nMULTr\<^sup>a \<phi> \<longrightarrow> nMULT\<^sup>a \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma nMULTr_a_equ: "nCNTR \<phi> \<Longrightarrow> nMULTr\<^sup>a \<phi> = nMULT\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_in_def)

lemma nMULTr_b_impl: "nMULT\<^sup>b \<phi> \<longrightarrow> nMULTr\<^sup>b \<phi>" by (simp add: nMULT_b_def nMULTr_b_def subset_def subset_in_def)
lemma "nMULTr\<^sup>b \<phi> \<longrightarrow> nMULT\<^sup>b \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma nMULTr_b_equ:  "CNTR \<phi> \<Longrightarrow> nMULTr\<^sup>b \<phi> = nMULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_in_def)
lemma nMULTr_b_equ':"nCNTR \<phi> \<Longrightarrow> nMULTr\<^sup>b \<phi> = nMULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_in_def)


text\<open>Weak variants of antitonicity.\<close>
definition ANTIw1::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ANTIw\<^sup>1") 
  where "ANTIw\<^sup>1 \<phi> \<equiv> \<forall>A B. A \<^bold>\<le> B \<longrightarrow> (\<phi> B) \<^bold>\<le> B \<^bold>\<or> (\<phi> A)"
definition ANTIw2::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ANTIw\<^sup>2")
  where "ANTIw\<^sup>2 \<phi> \<equiv> \<forall>A B. A \<^bold>\<le> B \<longrightarrow> A \<^bold>\<and> (\<phi> B) \<^bold>\<le> (\<phi> A)"

declare ANTIw1_def[cond] ANTIw2_def[cond]

lemma ANTIw1_nADDIr_b: "ANTIw\<^sup>1 \<phi> = nADDIr\<^sup>b \<phi>" proof -
  have l2r: "ANTIw\<^sup>1 \<phi> \<longrightarrow> nADDIr\<^sup>b \<phi>" unfolding cond subset_out_char by (smt (verit, ccfv_SIG) BA_distr2 L8 join_def setequ_ext subset_def)
  have r2l: "nADDIr\<^sup>b \<phi> \<longrightarrow> ANTIw\<^sup>1 \<phi>" unfolding cond subset_out_def by (metis (full_types) L9 join_def meet_def setequ_ext subset_def)
  show ?thesis using l2r r2l by blast
qed
lemma ANTIw2_nMULTr_a: "ANTIw\<^sup>2 \<phi> = nMULTr\<^sup>a \<phi>" proof -
  have l2r: "ANTIw\<^sup>2 \<phi> \<longrightarrow> nMULTr\<^sup>a \<phi>" unfolding cond subset_in_char by (metis BA_distr1 L3 L4 L5 L7 L8 setequ_ext)
  have r2l: "nMULTr\<^sup>a \<phi> \<longrightarrow> ANTIw\<^sup>2 \<phi>" unfolding cond subset_in_def by (metis (full_types) L10 join_def meet_def setequ_ext subset_def)
  show ?thesis using l2r r2l by blast
qed

lemma "ANTI \<phi> \<longrightarrow> ANTIw\<^sup>1 \<phi>" by (simp add: ANTI_nADDIb ANTIw1_nADDIr_b nADDIr_b_impl)
lemma "ANTIw\<^sup>1 \<phi> \<longrightarrow> ANTI \<phi>" nitpick oops \<comment>\<open> countermodel \<close>
lemma "ANTI \<phi> \<longrightarrow> ANTIw\<^sup>2 \<phi>" by (simp add: ANTI_nMULTa ANTIw2_nMULTr_a nMULTr_a_impl)
lemma "ANTIw\<^sup>2 \<phi> \<longrightarrow> ANTI \<phi>" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>We have in fact that (n)CNTR (resp. (n)EXPN) implies ANTIw-1/nADDIr-b (resp. ANTIw-2/nMULTr-a).\<close>
lemma CNTR_ANTIw1_impl: "CNTR \<phi> \<longrightarrow> ANTIw\<^sup>1 \<phi>" unfolding cond using L3 subset_char1 by blast
lemma nCNTR_ANTIw1_impl: "nCNTR \<phi> \<longrightarrow> ANTIw\<^sup>1 \<phi>" unfolding cond by (metis (full_types) compl_def join_def subset_def)
lemma EXPN_ANTIw2_impl: "EXPN \<phi> \<longrightarrow> ANTIw\<^sup>2 \<phi>" unfolding cond using L4 subset_char1 by blast
lemma nEXPN_ANTIw2_impl: "nEXPN \<phi> \<longrightarrow> ANTIw\<^sup>2 \<phi>" unfolding cond by (metis (full_types) compl_def meet_def subset_def)

text\<open>Dual interrelations.\<close>
lemma ADDIr_dual1: "ADDIr\<^sup>a \<phi> = MULTr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (z3) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma ADDIr_dual2: "ADDIr\<^sup>b \<phi> = MULTr\<^sup>a \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_threshold) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma ADDIr_dual:  "ADDIr \<phi> = MULTr \<phi>\<^sup>d" using ADDIr_char ADDIr_dual1 ADDIr_dual2 MULTr_char by blast

lemma nADDIr_dual1: "nADDIr\<^sup>a \<phi> = nMULTr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (verit, del_insts) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma nADDIr_dual2: "nADDIr\<^sup>b \<phi> = nMULTr\<^sup>a \<phi>\<^sup>d" by (smt (z3) BA_deMorgan1 BA_dn compl_def nADDIr_b_def nMULTr_a_def op_dual_def setequ_ext subset_in_def subset_out_def)
lemma nADDIr_dual: "nADDIr \<phi> = nMULTr \<phi>\<^sup>d" using nADDIr_char nADDIr_dual1 nADDIr_dual2 nMULTr_char by blast


text\<open>Complement interrelations.\<close>
lemma ADDIr_a_cmpl: "ADDIr\<^sup>a \<phi> = nADDIr\<^sup>a \<phi>\<^sup>-" unfolding cond by (smt (verit, del_insts) BA_deMorgan1 compl_def setequ_ext subset_out_def svfun_compl_def)
lemma ADDIr_b_cmpl: "ADDIr\<^sup>b \<phi> = nADDIr\<^sup>b \<phi>\<^sup>-" unfolding cond by (smt (verit, del_insts) BA_deMorgan1 compl_def setequ_ext subset_out_def svfun_compl_def)
lemma ADDIr_cmpl: "ADDIr \<phi> = nADDIr \<phi>\<^sup>-" by (simp add: ADDIr_a_cmpl ADDIr_b_cmpl ADDIr_char nADDIr_char)
lemma MULTr_a_cmpl: "MULTr\<^sup>a \<phi> = nMULTr\<^sup>a \<phi>\<^sup>-" unfolding cond by (smt (verit, del_insts) BA_deMorgan2 compl_def setequ_ext subset_in_def svfun_compl_def)
lemma MULTr_b_cmpl: "MULTr\<^sup>b \<phi> = nMULTr\<^sup>b \<phi>\<^sup>-" unfolding cond by (smt (verit, ccfv_threshold) BA_deMorgan2 compl_def setequ_ext subset_in_def svfun_compl_def)
lemma MULTr_cmpl: "MULTr \<phi> = nMULTr \<phi>\<^sup>-" by (simp add: MULTr_a_cmpl MULTr_b_cmpl MULTr_char nMULTr_char)


text\<open>Fixed-point interrelations.\<close>
lemma EXPN_fp:  "EXPN \<phi> = EXPN \<phi>\<^sup>f\<^sup>p" by (simp add: EXPN_def dimpl_def op_fixpoint_def subset_def)
lemma EXPN_fpc: "EXPN \<phi> = nEXPN \<phi>\<^sup>f\<^sup>p\<^sup>-" using EXPN_fp nEXPN_CNTR_compl by blast
lemma CNTR_fp:  "CNTR \<phi> = nCNTR \<phi>\<^sup>f\<^sup>p" by (metis EXPN_CNTR_dual1 EXPN_fp dual_compl_char2 dual_invol nCNTR_EXPN_compl ofp_comm_dc1 sfun_compl_invol)
lemma CNTR_fpc: "CNTR \<phi> = CNTR \<phi>\<^sup>f\<^sup>p\<^sup>-" by (metis CNTR_fp nCNTR_EXPN_compl ofp_comm_compl ofp_invol)

lemma nNORM_fp: "NORM \<phi> = nNORM \<phi>\<^sup>f\<^sup>p" by (metis NORM_def fixpoints_def fp_rel nNORM_def)
lemma NORM_fpc: "NORM \<phi> = NORM \<phi>\<^sup>f\<^sup>p\<^sup>-" by (simp add: NORM_def bottom_def ofp_fixpoint_compl_def sdiff_def)
lemma DNRM_fp:  "DNRM \<phi> = DNRM \<phi>\<^sup>f\<^sup>p" by (simp add: DNRM_def dimpl_def op_fixpoint_def top_def)
lemma DNRM_fpc: "DNRM \<phi> = nDNRM \<phi>\<^sup>f\<^sup>p\<^sup>-" using DNRM_fp nDNRM_DNRM_compl by blast

lemma ADDIr_a_fpc: "ADDIr\<^sup>a \<phi> = ADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>-" unfolding cond subset_out_def by (simp add: join_def ofp_fixpoint_compl_def sdiff_def)
lemma ADDIr_a_fp: "ADDIr\<^sup>a \<phi> = nADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p" by (metis ADDIr_a_cmpl ADDIr_a_fpc sfun_compl_invol)
lemma ADDIr_b_fpc: "ADDIr\<^sup>b \<phi> = ADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>-" unfolding cond subset_out_def by (simp add: join_def ofp_fixpoint_compl_def sdiff_def)
lemma ADDIr_b_fp: "ADDIr\<^sup>b \<phi> = nADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p" by (metis ADDIr_b_cmpl ADDIr_b_fpc sfun_compl_invol)

lemma MULTr_a_fp: "MULTr\<^sup>a \<phi> = MULTr\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_def by (simp add: dimpl_def meet_def op_fixpoint_def)
lemma MULTr_a_fpc: "MULTr\<^sup>a \<phi> = nMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>-" using MULTr_a_cmpl MULTr_a_fp by blast
lemma MULTr_b_fp: "MULTr\<^sup>b \<phi> = MULTr\<^sup>b \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_def by (simp add: dimpl_def meet_def op_fixpoint_def)
lemma MULTr_b_fpc: "MULTr\<^sup>b \<phi> = nMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>-" using MULTr_b_cmpl MULTr_b_fp by blast


text\<open>Relativized IDEM variants.\<close>
definition IDEMr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEMr\<^sup>a")
  where "IDEMr\<^sup>a \<phi> \<equiv> \<forall>A. \<phi>(A \<^bold>\<or> \<phi> A) \<^bold>\<le>\<^sup>A (\<phi> A)"
definition IDEMr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEMr\<^sup>b") 
  where "IDEMr\<^sup>b \<phi> \<equiv> \<forall>A. (\<phi> A) \<^bold>\<le>\<^sub>A \<phi>(A \<^bold>\<and> \<phi> A)"
declare IDEMr_a_def[cond] IDEMr_b_def[cond]

text\<open>Relativized nIDEM variants.\<close>
definition nIDEMr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEMr\<^sup>a") 
  where "nIDEMr\<^sup>a \<phi> \<equiv> \<forall>A. (\<phi> A) \<^bold>\<le>\<^sup>A \<phi>(A \<^bold>\<or> \<^bold>\<midarrow>(\<phi> A))"
definition nIDEMr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEMr\<^sup>b") 
  where "nIDEMr\<^sup>b \<phi> \<equiv> \<forall>A. \<phi>(A \<^bold>\<and> \<^bold>\<midarrow>(\<phi> A)) \<^bold>\<le>\<^sub>A (\<phi> A)"

declare nIDEMr_a_def[cond] nIDEMr_b_def[cond]


text\<open>Complement interrelations.\<close>
lemma IDEMr_a_cmpl: "IDEMr\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>-" unfolding cond subset_in_def subset_out_def by (metis compl_def sfun_compl_invol svfun_compl_def)
lemma IDEMr_b_cmpl: "IDEMr\<^sup>b \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>-" unfolding cond subset_in_def subset_out_def by (metis compl_def sfun_compl_invol svfun_compl_def)

text\<open>Dual interrelation.\<close>
lemma IDEMr_dual: "IDEMr\<^sup>a \<phi> = IDEMr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_def subset_out_def op_dual_def by (metis (mono_tags, opaque_lifting) BA_dn compl_def diff_char1 diff_char2 impl_char setequ_ext)
lemma nIDEMr_dual: "nIDEMr\<^sup>a \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>d" by (metis IDEMr_dual IDEMr_a_cmpl IDEMr_b_cmpl dual_compl_char1 dual_compl_char2 sfun_compl_invol)

text\<open>Fixed-point interrelations.\<close>
lemma nIDEMr_a_fpc: "nIDEMr\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>-" proof -
  have "\<forall>A. (\<lambda>p. A p \<or> \<not>\<phi> A p) = (\<lambda>p. A p \<or> \<phi> A p = A p)" by blast
  thus ?thesis unfolding cond subset_out_def ofp_fixpoint_compl_def conn order by simp
qed
lemma IDEMr_a_fp: "IDEMr\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p" by (metis IDEMr_a_cmpl nIDEMr_a_fpc ofp_invol)
lemma IDEMr_a_fpc: "IDEMr\<^sup>a \<phi> = IDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>-" by (metis IDEMr_a_cmpl nIDEMr_a_fpc ofp_comm_compl)
lemma IDEMr_b_fp: "IDEMr\<^sup>b \<phi> = IDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p" by (metis IDEMr_a_fpc IDEMr_dual dual_compl_char1 dual_invol ofp_comm_compl ofp_comm_dc2)
lemma IDEMr_b_fpc: "IDEMr\<^sup>b \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>-" using IDEMr_b_fp IDEMr_b_cmpl by blast


text\<open>The original border condition B1' (by Zarycki) is equivalent to the conjuntion of nMULTr and CNTR.\<close>
abbreviation "B1' \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>= (A \<^bold>\<and> \<phi> B) \<^bold>\<or> (\<phi> A \<^bold>\<and> B)" 

lemma "B1' \<phi> = (nMULTr \<phi> \<and> CNTR \<phi>)" proof -
  have l2ra: "B1' \<phi> \<longrightarrow> nMULTr \<phi>" unfolding cond by (smt (z3) join_def meet_def setequ_ext setequ_in_def)
  have l2rb: "B1' \<phi> \<longrightarrow> CNTR \<phi>" unfolding cond by (metis L2 L4 L5 L7 L9 setequ_ext)
  have r2l: "(nMULTr \<phi> \<and> CNTR \<phi>) \<longrightarrow> B1' \<phi>" unfolding cond by (smt (z3) L10 join_def meet_def setequ_def setequ_in_char)
  from l2ra l2rb r2l show ?thesis by blast
qed

text\<open>Modulo conditions nMULTr and CNTR the border condition B4 is equivalent to nIDEMr-b.\<close>
abbreviation "B4 \<phi> \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A)) \<^bold>\<le> A"

lemma "nMULTr \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> B4 \<phi> = nIDEMr\<^sup>b \<phi>" proof -
  assume a1: "nMULTr \<phi>" and a2: "CNTR \<phi>"
  have l2r: "nMULTr\<^sup>b \<phi> \<Longrightarrow> B4 \<phi> \<longrightarrow> nIDEMr\<^sup>b \<phi>" unfolding cond subset_in_char subset_def by (metis BA_deMorgan1 BA_dn compl_def meet_def setequ_ext)
  have r2l: "nMULTr\<^sup>a \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> nIDEMr\<^sup>b \<phi> \<longrightarrow> B4 \<phi>" unfolding cond by (smt (verit) compl_def join_def meet_def subset_def subset_in_def)
  from l2r r2l show ?thesis using a1 a2 nMULTr_char by blast
qed

end
