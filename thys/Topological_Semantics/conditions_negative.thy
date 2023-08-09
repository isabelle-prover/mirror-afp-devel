theory conditions_negative
  imports conditions_positive
begin

subsection \<open>Negative Conditions\<close>

text\<open>We continue defining and interrelating axiomatic conditions on unary operations (operators). 
  We now move to conditions commonly satisfied by negation-like logical operations.\<close>

text\<open>Anti-tonicity (ANTI).\<close>
definition ANTI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ANTI")
  where "ANTI \<phi> \<equiv> \<forall>A B. A \<^bold>\<le> B \<longrightarrow> \<phi> B \<^bold>\<le> \<phi> A"

declare ANTI_def[cond]

text\<open>ANTI is self-dual.\<close>
lemma ANTI_dual: "ANTI \<phi> = ANTI \<phi>\<^sup>d" by (smt (verit) BA_cp ANTI_def dual_invol op_dual_def)
text\<open>ANTI is the 'complement' of MONO.\<close>
lemma ANTI_MONO: "MONO \<phi> = ANTI \<phi>\<^sup>-" by (metis ANTI_def BA_cp MONO_def svfun_compl_def)


text\<open>Anti-expansive/extensive (nEXPN) and its dual anti-contractive (nCNTR).\<close>
definition nEXPN::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nEXPN")
  where "nEXPN \<phi>  \<equiv> \<forall>A. \<phi> A \<^bold>\<le> \<^bold>\<midarrow>A"
definition nCNTR::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nCNTR")
  where "nCNTR \<phi> \<equiv> \<forall>A. \<^bold>\<midarrow>A \<^bold>\<le> \<phi> A"

declare nEXPN_def[cond] nCNTR_def[cond]

text\<open>nEXPN and nCNTR are dual to each other.\<close>
lemma nEXPN_nCNTR_dual1: "nEXPN \<phi> = nCNTR \<phi>\<^sup>d" unfolding cond by (metis BA_cp BA_dn op_dual_def setequ_ext)
lemma nEXPN_nCNTR_dual2: "nCNTR \<phi> = nEXPN \<phi>\<^sup>d" by (simp add: dual_invol nEXPN_nCNTR_dual1)

text\<open>nEXPN and nCNTR are the 'complements' of EXPN and CNTR respectively.\<close>
lemma nEXPN_CNTR_compl: "EXPN \<phi> = nEXPN \<phi>\<^sup>-" by (metis BA_cp EXPN_def nEXPN_def svfun_compl_def)
lemma nCNTR_EXPN_compl: "CNTR \<phi> = nCNTR \<phi>\<^sup>-" by (metis EXPN_CNTR_dual2 dual_compl_char1 dual_compl_char2 nEXPN_CNTR_compl nEXPN_nCNTR_dual2)

text\<open>Anti-Normality (nNORM) and its dual (nDNRM).\<close>
definition nNORM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nNORM")
  where "nNORM \<phi>  \<equiv> (\<phi> \<^bold>\<bottom>) \<^bold>= \<^bold>\<top>"
definition nDNRM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nDNRM")
  where "nDNRM \<phi> \<equiv> (\<phi> \<^bold>\<top>) \<^bold>= \<^bold>\<bottom>" 

declare nNORM_def[cond] nDNRM_def[cond]

text\<open>nNORM and nDNRM are dual to each other.\<close>
lemma nNOR_dual1: "nNORM \<phi> = nDNRM \<phi>\<^sup>d" unfolding cond by (simp add: bottom_def compl_def op_dual_def setequ_def top_def)
lemma nNOR_dual2: "nDNRM \<phi> = nNORM \<phi>\<^sup>d" by (simp add: dual_invol nNOR_dual1) 

text\<open>nNORM and nDNRM are the 'complements' of NORM and DNRM respectively.\<close>
lemma nNORM_NORM_compl: "NORM \<phi> = nNORM \<phi>\<^sup>-" by (simp add: NORM_def bottom_def compl_def nNORM_def setequ_def svfun_compl_def top_def)
lemma nDNRM_DNRM_compl: "DNRM \<phi> = nDNRM \<phi>\<^sup>-" by (simp add: DNRM_def bottom_def compl_def nDNRM_def setequ_def svfun_compl_def top_def)

text\<open>nEXPN (nCNTR) entail nDNRM (nNORM).\<close>
lemma nEXPN_impl_nDNRM: "nEXPN \<phi> \<longrightarrow> nDNRM \<phi>" unfolding cond by (metis bottom_def compl_def setequ_def subset_def top_def)
lemma nCNTR_impl_nNORM: "nCNTR \<phi> \<longrightarrow> nNORM \<phi>" by (simp add: nEXPN_impl_nDNRM nEXPN_nCNTR_dual2 nNOR_dual1)


text\<open>Anti-Idempotence (nIDEM).\<close>
definition nIDEM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEM") 
  where "nIDEM \<phi>  \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>(\<phi> A)) \<^bold>= (\<phi> A)"
definition nIDEM_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEM\<^sup>a") 
  where "nIDEM_a \<phi> \<equiv> \<forall>A. (\<phi> A) \<^bold>\<le> \<phi>(\<^bold>\<midarrow>(\<phi> A))"
definition nIDEM_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEM\<^sup>b") 
  where "nIDEM_b \<phi> \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>(\<phi> A)) \<^bold>\<le> (\<phi> A)"

declare nIDEM_def[cond] nIDEM_a_def[cond] nIDEM_b_def[cond]

text\<open>nIDEM-a and nIDEM-b are dual to each other.\<close>
lemma nIDEM_dual1: "nIDEM\<^sup>a \<phi> = nIDEM\<^sup>b \<phi>\<^sup>d" unfolding cond by (metis BA_cp BA_dn op_dual_def setequ_ext)
lemma nIDEM_dual2: "nIDEM\<^sup>b \<phi> = nIDEM\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol nIDEM_dual1)

lemma nIDEM_char: "nIDEM \<phi> = (nIDEM\<^sup>a \<phi> \<and> nIDEM\<^sup>b \<phi>)" unfolding cond setequ_char by blast
lemma nIDEM_dual: "nIDEM \<phi> = nIDEM \<phi>\<^sup>d" using nIDEM_char nIDEM_dual1 nIDEM_dual2 by blast

text\<open>nIDEM(a/b) and IDEM(a/b) are the 'complements' each other.\<close>
lemma nIDEM_a_compl: "IDEM\<^sup>a \<phi> = nIDEM\<^sup>a \<phi>\<^sup>-" by (metis (no_types, lifting) BA_cp IDEM_a_def nIDEM_a_def sfun_compl_invol svfun_compl_def)
lemma nIDEM_b_compl: "IDEM\<^sup>b \<phi> = nIDEM\<^sup>b \<phi>\<^sup>-" by (metis IDEM_dual2 dual_compl_char1 dual_compl_char2 nIDEM_a_compl nIDEM_dual2)
lemma nIDEM_compl: "nIDEM \<phi> = IDEM \<phi>\<^sup>-" by (simp add: IDEM_char nIDEM_a_compl nIDEM_b_compl nIDEM_char sfun_compl_invol)

text\<open>nEXPN (nCNTR) entail nIDEM-a (nIDEM-b).\<close>
lemma nEXPN_impl_nIDEM_a: "nEXPN \<phi> \<longrightarrow> nIDEM\<^sup>b \<phi>" by (metis nEXPN_def nIDEM_b_def sfun_compl_invol svfun_compl_def)
lemma nCNTR_impl_nIDEM_b: "nCNTR \<phi> \<longrightarrow> nIDEM\<^sup>a \<phi>" by (simp add: nEXPN_impl_nIDEM_a nEXPN_nCNTR_dual2 nIDEM_dual1)


text\<open>Anti-distribution over joins or anti-additivity (nADDI) and its dual.\<close>
definition nADDI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDI")
  where "nADDI \<phi>  \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<^bold>= (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition nADDI_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDI\<^sup>a")
  where "nADDI\<^sup>a \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<and> (\<phi> B) \<^bold>\<le> \<phi>(A \<^bold>\<or> B)" 
definition nADDI_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDI\<^sup>b")
  where "nADDI\<^sup>b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<^bold>\<le> (\<phi> A) \<^bold>\<and> (\<phi> B)"

text\<open>Anti-distribution over meets or anti-multiplicativity (nMULT).\<close>
definition nMULT::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULT") 
  where "nMULT \<phi>  \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>= (\<phi> A) \<^bold>\<or> (\<phi> B)" 
definition nMULT_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULT\<^sup>a")
  where "nMULT\<^sup>a \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<or> (\<phi> B) \<^bold>\<le> \<phi>(A \<^bold>\<and> B)"
definition nMULT_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULT\<^sup>b")
  where "nMULT\<^sup>b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<le> (\<phi> A) \<^bold>\<or> (\<phi> B)" 

declare nADDI_def[cond] nADDI_a_def[cond] nADDI_b_def[cond]
        nMULT_def[cond] nMULT_a_def[cond] nMULT_b_def[cond]

lemma nADDI_char: "nADDI \<phi> = (nADDI\<^sup>a \<phi> \<and> nADDI\<^sup>b \<phi>)" unfolding cond using setequ_char by blast
lemma nMULT_char: "nMULT \<phi> = (nMULT\<^sup>a \<phi> \<and> nMULT\<^sup>b \<phi>)" unfolding cond using setequ_char by blast

text\<open>ANTI, nMULT-a and nADDI-b are equivalent.\<close>
lemma ANTI_nMULTa: "nMULT\<^sup>a \<phi> = ANTI \<phi>" unfolding cond by (smt (z3) L10 L7 join_def meet_def setequ_ext subset_def)
lemma ANTI_nADDIb: "nADDI\<^sup>b \<phi> = ANTI \<phi>" unfolding cond by (smt (verit) BA_cp BA_deMorgan1 L10 L3 L5 L8 L9 setequ_char setequ_ext)

text\<open>Below we prove several duality relationships between nADDI(a/b) and nMULT(a/b).\<close>

text\<open>Duality between nMULT-a and nADDI-b (an easy corollary from the self-duality of ANTI).\<close>
lemma nMULTa_nADDIb_dual1: "nMULT\<^sup>a \<phi> = nADDI\<^sup>b \<phi>\<^sup>d" using ANTI_nADDIb ANTI_nMULTa ANTI_dual by blast
lemma nMULTa_nADDIb_dual2: "nADDI\<^sup>b \<phi> = nMULT\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol nMULTa_nADDIb_dual1)
text\<open>Duality between nADDI-a and nMULT-b.\<close>
lemma nADDIa_nMULTb_dual1: "nADDI\<^sup>a \<phi> = nMULT\<^sup>b \<phi>\<^sup>d" unfolding cond by (metis (no_types, lifting) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma nADDIa_nMULTb_dual2: "nMULT\<^sup>b \<phi> = nADDI\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol nADDIa_nMULTb_dual1)
text\<open>Duality between ADDI and MULT.\<close>
lemma nADDI_nMULT_dual1: "nADDI \<phi> = nMULT \<phi>\<^sup>d" using nADDI_char nADDIa_nMULTb_dual1 nMULT_char nMULTa_nADDIb_dual2 by blast
lemma nADDI_nMULT_dual2: "nMULT \<phi> = nADDI \<phi>\<^sup>d" by (simp add: dual_invol nADDI_nMULT_dual1)

text\<open>nADDI and nMULT are the 'complements' of ADDI and MULT respectively.\<close>
lemma nADDIa_compl: "ADDI\<^sup>a \<phi> = nADDI\<^sup>a \<phi>\<^sup>-" by (metis ADDI_a_def BA_cp BA_deMorgan1 nADDI_a_def setequ_ext svfun_compl_def)
lemma nADDIb_compl: "ADDI\<^sup>b \<phi> = nADDI\<^sup>b \<phi>\<^sup>-" by (simp add: ANTI_nADDIb ANTI_MONO MONO_ADDIb sfun_compl_invol)
lemma nADDI_compl: "ADDI \<phi> = nADDI \<phi>\<^sup>-" by (simp add: ADDI_char nADDI_char nADDIa_compl nADDIb_compl)
lemma nMULTa_compl: "MULT\<^sup>a \<phi> = nMULT\<^sup>a \<phi>\<^sup>-" by (simp add: ANTI_MONO ANTI_nMULTa MONO_MULTa sfun_compl_invol)
lemma nMULTb_compl: "MULT\<^sup>b \<phi> = nMULT\<^sup>b \<phi>\<^sup>-" by (metis BA_cp BA_deMorgan2 MULT_b_def nMULT_b_def setequ_ext svfun_compl_def)
lemma nMULT_compl: "MULT \<phi> = nMULT \<phi>\<^sup>-" by (simp add: MULT_char nMULT_char nMULTa_compl nMULTb_compl)


text\<open>We verify properties regarding closure over meets/joins for fixed-points.\<close>

text\<open>nMULT for an operator implies join-closedness of the set of fixed-points of its dual-complement.\<close>
lemma nMULT_joinclosed: "nMULT \<phi> \<Longrightarrow> join_closed (fp (\<phi>\<^sup>d\<^sup>-))" by (smt (verit, del_insts) ADDI_MULT_dual2 ADDI_joinclosed BA_deMorgan1 MULT_def dual_compl_char2 nMULT_def setequ_ext svfun_compl_def)
lemma "join_closed (fp (\<phi>\<^sup>d\<^sup>-)) \<Longrightarrow> nMULT \<phi>" nitpick oops \<comment>\<open> countermodel found: needs further assumptions \<close>
lemma joinclosed_nMULT: "ANTI \<phi> \<Longrightarrow> nCNTR \<phi> \<Longrightarrow> nIDEM\<^sup>b \<phi> \<Longrightarrow> join_closed (fp (\<phi>\<^sup>d\<^sup>-)) \<Longrightarrow> nMULT \<phi>" by (metis ANTI_MONO ANTI_dual IDEM_char IDEM_dual dual_compl_char1 dual_compl_char2 joinclosed_ADDI nADDI_compl nADDI_nMULT_dual2 nCNTR_impl_nIDEM_b nEXPN_CNTR_compl nEXPN_nCNTR_dual2 nIDEM_char nIDEM_compl sfun_compl_invol)

text\<open>nADDI for an operator implies meet-closedness of the set of fixed-points of its dual-complement.\<close>
lemma nADDI_meetclosed: "nADDI \<phi> \<Longrightarrow> meet_closed (fp (\<phi>\<^sup>d\<^sup>-))" by (smt (verit, ccfv_threshold) ADDI_MULT_dual1 ADDI_def BA_deMorgan2 MULT_meetclosed dual_compl_char2 nADDI_def setequ_ext svfun_compl_def)
lemma "meet_closed (fp (\<phi>\<^sup>d\<^sup>-)) \<Longrightarrow> nADDI \<phi>" nitpick oops \<comment>\<open> countermodel found: needs further assumptions \<close>
lemma meetclosed_nADDI: "ANTI \<phi> \<Longrightarrow> nEXPN \<phi> \<Longrightarrow> nIDEM\<^sup>a \<phi> \<Longrightarrow> meet_closed (fp (\<phi>\<^sup>d\<^sup>-)) \<Longrightarrow> nADDI \<phi>" by (metis ADDI_MULT_dual2 ADDI_joinclosed ANTI_MONO ANTI_dual dual_compl_char1 dual_compl_char2 joinclosed_nMULT meetclosed_MULT nADDI_nMULT_dual1 nCNTR_EXPN_compl nEXPN_nCNTR_dual1 nIDEM_b_compl nIDEM_dual1 sfun_compl_invol)

text\<open>Assuming ANTI, we have that nEXPN (nCNTR) implies meet-closed (join-closed) for the set of fixed-points.\<close>
lemma nEXPN_meetclosed: "ANTI \<phi> \<Longrightarrow> nEXPN \<phi> \<Longrightarrow> meet_closed (fp \<phi>)" by (metis (full_types) L10 compl_def fixpoints_def meet_closed_def nEXPN_def setequ_ext subset_def)
lemma nCNTR_joinclosed: "ANTI \<phi> \<Longrightarrow> nCNTR \<phi> \<Longrightarrow> join_closed (fp \<phi>)" by (smt (verit, ccfv_threshold) BA_impl L9 fixpoints_def impl_char join_closed_def nCNTR_def setequ_char setequ_ext)

end
