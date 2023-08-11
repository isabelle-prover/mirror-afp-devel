theory logics_negation
  imports logics_consequence conditions_relativized
begin

subsection \<open>Properties of negation(-like) operators\<close>

text\<open>To avoid visual clutter we introduce convenient notation for type for properties of operators.\<close>
type_synonym 'w \<Omega> = "('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool"

named_theorems neg (*to group together definitions for properties of negations*)


subsubsection \<open>Principles of excluded middle, contradiction and explosion\<close>

text\<open>TND: tertium non datur, aka. law of excluded middle (resp. strong, weak, minimal).\<close>
abbreviation pTND  ("TND\<^sup>_  _") where "TND\<^sup>a  \<eta> \<equiv>         [\<turnstile> a \<^bold>\<or> \<eta> a]"
abbreviation pTNDw ("TNDw\<^sup>_ _") where "TNDw\<^sup>a \<eta> \<equiv> \<forall>b. [\<eta> b \<turnstile> a, \<eta> a]"
abbreviation pTNDm ("TNDm\<^sup>_ _") where "TNDm\<^sup>a \<eta> \<equiv>     [\<eta> \<^bold>\<bottom> \<turnstile> a, \<eta> a]"
definition TND ::"'w \<Omega>" where "TND  \<eta> \<equiv> \<forall>\<phi>. TND\<^sup>\<phi>  \<eta>"
definition TNDw::"'w \<Omega>" where "TNDw \<eta> \<equiv> \<forall>\<phi>. TNDw\<^sup>\<phi> \<eta>"
definition TNDm::"'w \<Omega>" where "TNDm \<eta> \<equiv> \<forall>\<phi>. TNDm\<^sup>\<phi> \<eta>"
declare TND_def[neg] TNDw_def[neg] TNDm_def[neg]

text\<open>Explore some (non)entailment relations.\<close>
lemma "TND  \<eta> \<Longrightarrow> TNDw \<eta>" unfolding neg conn order by simp
lemma "TNDw \<eta> \<Longrightarrow> TND  \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "TNDw \<eta> \<Longrightarrow> TNDm \<eta>" unfolding neg by simp
lemma "TNDm \<eta> \<Longrightarrow> TNDw \<eta>" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>ECQ: ex contradictione (sequitur) quodlibet (variants: strong, weak, minimal).\<close>
abbreviation pECQ  ("ECQ\<^sup>_ _")  where "ECQ\<^sup>a  \<eta> \<equiv>     [a, \<eta> a \<turnstile> \<^bold>\<bottom>]"
abbreviation pECQw ("ECQw\<^sup>_ _") where "ECQw\<^sup>a \<eta> \<equiv> \<forall>b. [a, \<eta> a \<turnstile> \<eta> b]"
abbreviation pECQm ("ECQm\<^sup>_ _") where "ECQm\<^sup>a \<eta> \<equiv>     [a, \<eta> a \<turnstile> \<eta> \<^bold>\<top>]"
definition ECQ ::"'w \<Omega>" where  "ECQ \<eta> \<equiv> \<forall>a. ECQ\<^sup>a  \<eta>"
definition ECQw::"'w \<Omega>" where "ECQw \<eta> \<equiv> \<forall>a. ECQw\<^sup>a \<eta>"
definition ECQm::"'w \<Omega>" where "ECQm \<eta> \<equiv> \<forall>a. ECQm\<^sup>a \<eta>"
declare ECQ_def[neg] ECQw_def[neg] ECQm_def[neg]

text\<open>Explore some (non)entailment relations.\<close>
lemma "ECQ  \<eta> \<Longrightarrow> ECQw \<eta>" unfolding neg conn order by blast
lemma "ECQw \<eta> \<Longrightarrow> ECQ  \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "ECQw \<eta> \<Longrightarrow> ECQm \<eta>" unfolding neg by simp
lemma "ECQm \<eta> \<Longrightarrow> ECQw \<eta>" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>LNC: law of non-contradiction.\<close>
abbreviation pLNC  ("LNC\<^sup>_ _")  where "LNC\<^sup>a \<eta> \<equiv> [\<turnstile> \<eta>(a \<^bold>\<and> \<eta> a)]"
definition LNC::"'w \<Omega>" where "LNC \<eta> \<equiv> \<forall>a. LNC\<^sup>a \<eta>"
declare LNC_def[neg]

text\<open>ECQ and LNC are in general independent.\<close>
lemma "ECQ \<eta> \<Longrightarrow> LNC \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "LNC \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops \<comment>\<open> counterexample \<close>


subsubsection \<open>Contraposition rules\<close>

text\<open>CoP: contraposition (weak 'rule-like' variants).
Variant 0 is antitonicity (ANTI). Variants 1-3 are stronger.\<close>
abbreviation pCoP1 ("CoP1\<^sup>_\<^sup>_ _") where "CoP1\<^sup>a\<^sup>b \<eta> \<equiv> [a \<turnstile> \<eta> b] \<longrightarrow> [b \<turnstile> \<eta> a]"
abbreviation pCoP2 ("CoP2\<^sup>_\<^sup>_ _") where "CoP2\<^sup>a\<^sup>b \<eta> \<equiv> [\<eta> a \<turnstile> b] \<longrightarrow> [\<eta> b \<turnstile> a]"
abbreviation pCoP3 ("CoP3\<^sup>_\<^sup>_ _") where "CoP3\<^sup>a\<^sup>b \<eta> \<equiv> [\<eta> a \<turnstile> \<eta> b] \<longrightarrow> [b \<turnstile> a]"

abbreviation CoP0 ::"'w \<Omega>" where "CoP0  \<eta> \<equiv> ANTI \<eta>"
definition   CoP1 ::"'w \<Omega>" where "CoP1  \<eta> \<equiv> \<forall>a b. CoP1\<^sup>a\<^sup>b \<eta>"
definition   CoP2 ::"'w \<Omega>" where "CoP2  \<eta> \<equiv> \<forall>a b. CoP2\<^sup>a\<^sup>b \<eta>"
definition   CoP3 ::"'w \<Omega>" where "CoP3  \<eta> \<equiv> \<forall>a b. CoP3\<^sup>a\<^sup>b \<eta>"

declare CoP1_def[neg] CoP2_def[neg] CoP3_def[neg]

text\<open>Explore some (non)entailment relations.\<close>
lemma "CoP1 \<eta> \<Longrightarrow> CoP0 \<eta>" unfolding ANTI_def CoP1_def using subset_char1 by blast
lemma "CoP0 \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "CoP2 \<eta> \<Longrightarrow> CoP0 \<eta>" unfolding ANTI_def CoP2_def using subset_char1 by blast
lemma "CoP0 \<eta> \<Longrightarrow> CoP2 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "CoP3 \<eta> \<Longrightarrow> CoP0 \<eta>" oops (*TODO*)
lemma "CoP0 \<eta> \<Longrightarrow> CoP3 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>All three strong variants are pairwise independent. However, CoP3 follows from CoP1 plus CoP2.\<close>
lemma CoP123: "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> CoP3 \<eta>" unfolding neg order by smt
text\<open>Taking all CoP together still leaves room for a boldly paraconsistent resp. paracomplete logic.\<close>
lemma "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops \<comment>\<open> counterexample \<close> 
lemma "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops \<comment>\<open> counterexample \<close> 


subsubsection \<open>Modus tollens rules\<close>

text\<open>MT: modus (tollendo) tollens (weak 'rule-like' variants).\<close>
abbreviation pMT0 ("MT0\<^sup>_\<^sup>_ _") where "MT0\<^sup>a\<^sup>b \<eta> \<equiv> [a \<turnstile> b] \<and> [\<turnstile> \<eta> b] \<longrightarrow> [\<turnstile> \<eta> a]"
abbreviation pMT1 ("MT1\<^sup>_\<^sup>_ _") where "MT1\<^sup>a\<^sup>b \<eta> \<equiv> [a \<turnstile> \<eta> b] \<and> [\<turnstile> b] \<longrightarrow> [\<turnstile> \<eta> a]"
abbreviation pMT2 ("MT2\<^sup>_\<^sup>_ _") where "MT2\<^sup>a\<^sup>b \<eta> \<equiv> [\<eta> a \<turnstile> b] \<and> [\<turnstile> \<eta> b] \<longrightarrow> [\<turnstile> a]"
abbreviation pMT3 ("MT3\<^sup>_\<^sup>_ _") where "MT3\<^sup>a\<^sup>b \<eta> \<equiv> [\<eta> a \<turnstile> \<eta> b] \<and> [\<turnstile> b] \<longrightarrow> [\<turnstile> a]"
definition MT0::"'w \<Omega>" where "MT0 \<eta> \<equiv> \<forall>a b. MT0\<^sup>a\<^sup>b \<eta>"
definition MT1::"'w \<Omega>" where "MT1 \<eta> \<equiv> \<forall>a b. MT1\<^sup>a\<^sup>b \<eta>"
definition MT2::"'w \<Omega>" where "MT2 \<eta> \<equiv> \<forall>a b. MT2\<^sup>a\<^sup>b \<eta>"
definition MT3::"'w \<Omega>" where "MT3 \<eta> \<equiv> \<forall>a b. MT3\<^sup>a\<^sup>b \<eta>"

declare MT0_def[neg] MT1_def[neg] MT2_def[neg] MT3_def[neg]

text\<open>Again, all MT variants are pairwise independent. We explore some (non)entailment relations.\<close>
lemma "CoP0 \<eta> \<Longrightarrow> MT0 \<eta>" unfolding neg order cond conn by blast
lemma "CoP1 \<eta> \<Longrightarrow> MT1 \<eta>" unfolding neg order conn by blast
lemma "CoP2 \<eta> \<Longrightarrow> MT2 \<eta>" unfolding neg order conn by blast
lemma "CoP3 \<eta> \<Longrightarrow> MT3 \<eta>" unfolding neg order conn by blast
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> CoP0 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma MT123: "MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta>"  unfolding neg order conn by metis


subsubsection \<open>Double negation introduction and elimination\<close>

text\<open>DNI/DNE: double negation introduction/elimination (strong 'axiom-like' variants).\<close>
abbreviation pDNI ("DNI\<^sup>_ _") where "DNI\<^sup>a \<eta> \<equiv> [a \<turnstile> \<eta>(\<eta> a)]"
abbreviation pDNE ("DNE\<^sup>_ _") where "DNE\<^sup>a \<eta> \<equiv> [\<eta>(\<eta> a) \<turnstile> a]"
definition DNI::"'w \<Omega>" where "DNI \<eta> \<equiv> \<forall>a. DNI\<^sup>a \<eta>"
definition DNE::"'w \<Omega>" where "DNE \<eta> \<equiv> \<forall>a. DNE\<^sup>a \<eta>"
declare DNI_def[neg] DNE_def[neg]

text\<open>CoP1 (resp. CoP2) can alternatively be defined as CoPw plus DNI (resp. DNE).\<close>
lemma "DNI \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma CoP1_def2: "CoP1 \<eta> = (CoP0 \<eta> \<and> DNI \<eta>)" unfolding neg cond using subset_char2 by blast
lemma "DNE \<eta> \<Longrightarrow>  CoP2 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma CoP2_def2: "CoP2 \<eta> = (CoP0 \<eta> \<and> DNE \<eta>)" unfolding neg cond using subset_char1 by blast

text\<open>Explore some non-entailment relations:\<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> CoP0 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT0 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT1 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT2 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT3 \<eta>" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>DNI/DNE: double negation introduction/elimination (weak 'rule-like' variants).\<close>
abbreviation prDNI ("rDNI\<^sup>_ _") where "rDNI\<^sup>a \<eta> \<equiv> [\<turnstile> a] \<longrightarrow> [\<turnstile> \<eta>(\<eta> a)]"
abbreviation prDNE ("rDNE\<^sup>_ _") where "rDNE\<^sup>a \<eta> \<equiv> [\<turnstile> \<eta>(\<eta> a)] \<longrightarrow> [\<turnstile> a]"
definition rDNI::"'w \<Omega>" where "rDNI \<eta> \<equiv> \<forall>a. rDNI\<^sup>a \<eta>"
definition rDNE::"'w \<Omega>" where "rDNE \<eta> \<equiv> \<forall>a. rDNE\<^sup>a \<eta>"
declare rDNI_def[neg] rDNE_def[neg]

text\<open>The 'rule-like' variants for DNI/DNE are strictly weaker than the 'axiom-like' ones.\<close>
lemma "DNI \<eta> \<Longrightarrow> rDNI \<eta>" unfolding neg order conn by simp
lemma "rDNI \<eta> \<Longrightarrow> DNI \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "DNE \<eta> \<Longrightarrow> rDNE \<eta>" unfolding neg order conn by blast
lemma "rDNE \<eta> \<Longrightarrow> DNE \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
text\<open>The 'rule-like' variants for DNI/DNE follow already from modus tollens.\<close>
lemma MT1_rDNI: "MT1 \<eta> \<Longrightarrow> rDNI \<eta>" unfolding neg order by blast
lemma MT2_rDNE: "MT2 \<eta> \<Longrightarrow> rDNE \<eta>" unfolding neg order by blast


subsubsection \<open>(Anti)Normality and its dual\<close>

text\<open>nNORM (resp. nDNRM) is entailed by CoP1 (resp. CoP2). \<close>
lemma CoP1_NORM: "CoP1 \<eta> \<Longrightarrow> nNORM \<eta>" unfolding neg cond conn order by simp
lemma CoP2_DNRM: "CoP2 \<eta> \<Longrightarrow> nDNRM \<eta>" unfolding neg cond conn by (smt (verit) setequ_char subset_def)
lemma "DNI \<eta> \<Longrightarrow> nNORM \<eta>" nitpick oops \<comment>\<open> counterexample \<close> 
lemma "DNE \<eta> \<Longrightarrow> nDNRM \<eta>" nitpick oops \<comment>\<open> counterexample \<close> 
text\<open>nNORM and nDNRM together entail the rule variant of DNI (rDNI).\<close>
lemma nDNRM_rDNI: "nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> rDNI \<eta>" unfolding neg cond by (simp add: gtrue_def setequ_ext)
lemma "nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> rDNE \<eta>" nitpick oops \<comment>\<open> counterexample \<close>


subsubsection \<open>De Morgan laws\<close>

text\<open>De Morgan laws correspond to anti-additivity and anti-multiplicativity).\<close>

text\<open>DM3 (resp. DM4) are entailed by CoP0/ANTI together with DNE (resp. DNI).\<close>
lemma CoP0_DNE_nMULTb: "CoP0 \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta>" unfolding neg cond by (metis ANTI_def ANTI_nADDIb L12 nADDI_b_def subset_char1)
lemma CoP0_DNI_nADDIa: "CoP0 \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta>" unfolding neg cond by (metis ANTI_def ANTI_nMULTa L11 nMULT_a_def subset_char2)

text\<open>From this follows that DM3 (resp. DM4) is entailed by CoP2 (resp. CoP1).\<close>
lemma CoP2_nMULTb: "CoP2 \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta>" by (simp add: CoP0_DNE_nMULTb CoP2_def2)
lemma CoP1_nADDIa: "CoP1 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta>" by (simp add: CoP0_DNI_nADDIa CoP1_def2)
   
text\<open>Explore some non-entailment relations:\<close>
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> DNI \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> DNE \<eta>" nitpick oops \<comment>\<open> counterexample \<close> 
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops \<comment>\<open> counterexample \<close> 

subsubsection \<open>Strong contraposition (axiom-like)\<close>
text\<open>Observe that the definitions below take implication as an additional parameter: @{text "\<iota>"}.\<close>

text\<open>lCoP: (local) contraposition (strong 'axiom-like' variants, using local consequence).\<close>
abbreviation plCoP0 ("lCoP0\<^sup>_\<^sup>_ _ _") where "lCoP0\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> a b \<turnstile> \<iota> (\<eta> b) (\<eta> a)]"
abbreviation plCoP1 ("lCoP1\<^sup>_\<^sup>_ _ _") where "lCoP1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> a (\<eta> b) \<turnstile> \<iota> b (\<eta> a)]"
abbreviation plCoP2 ("lCoP2\<^sup>_\<^sup>_ _ _") where "lCoP2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> (\<eta> a) b \<turnstile> \<iota> (\<eta> b) a]"
abbreviation plCoP3 ("lCoP3\<^sup>_\<^sup>_ _ _") where "lCoP3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> (\<eta> a) (\<eta> b) \<turnstile> \<iota> b a]"
definition lCoP0::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>"  where "lCoP0  \<iota> \<eta> \<equiv> \<forall>a b. lCoP0\<^sup>a\<^sup>b \<iota> \<eta>"
definition lCoP1::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>"  where "lCoP1  \<iota> \<eta> \<equiv> \<forall>a b. lCoP1\<^sup>a\<^sup>b \<iota> \<eta>"
definition lCoP2::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>"  where "lCoP2  \<iota> \<eta> \<equiv> \<forall>a b. lCoP2\<^sup>a\<^sup>b \<iota> \<eta>"
definition lCoP3::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>"  where "lCoP3  \<iota> \<eta> \<equiv> \<forall>a b. lCoP3\<^sup>a\<^sup>b \<iota> \<eta>"

declare lCoP0_def[neg] lCoP1_def[neg] lCoP2_def[neg] lCoP3_def[neg]

text\<open>All these contraposition variants are in general independent from each other.
However if we employ classical implication we can verify some relationships.\<close>

lemma lCoP1_def2: "lCoP1(\<^bold>\<rightarrow>) \<eta> = (lCoP0(\<^bold>\<rightarrow>) \<eta> \<and> DNI \<eta>)" unfolding neg conn order by metis
lemma lCoP2_def2: "lCoP2(\<^bold>\<rightarrow>) \<eta> = (lCoP0(\<^bold>\<rightarrow>) \<eta> \<and> DNE \<eta>)" unfolding neg conn order by blast
lemma "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "lCoP3(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma lCoP123: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<and> lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by metis

text\<open>Strong/axiom-like variants imply weak/rule-like ones as expected.\<close>
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP0 \<eta>" unfolding neg cond conn order by blast
lemma "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP1 \<eta>" unfolding neg conn order by blast
lemma "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP2 \<eta>" unfolding neg conn order by blast
lemma "lCoP3(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP3 \<eta>" unfolding neg conn order by blast

text\<open>Explore some (non)entailment relations.\<close>
lemma lCoP1_TND: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> TND \<eta>" unfolding neg conn by (smt (verit, best) setequ_char subset_def)
lemma "TND \<eta> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma lCoP2_ECQ: "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> ECQ \<eta>" unfolding neg conn by (smt (verit) setequ_def subset_def)
lemma "ECQ \<eta> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>


subsubsection \<open>Local modus tollens axioms\<close>

text\<open>lMT: (local) Modus tollens (strong, 'axiom-like' variants, using local consequence).\<close>
abbreviation plMT0 ("lMT0\<^sup>_\<^sup>_ _ _") where "lMT0\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> a b, \<eta> b \<turnstile> \<eta> a]"
abbreviation plMT1 ("lMT1\<^sup>_\<^sup>_ _ _") where "lMT1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> a (\<eta> b), b \<turnstile> \<eta> a]"
abbreviation plMT2 ("lMT2\<^sup>_\<^sup>_ _ _") where "lMT2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> (\<eta> a) b, \<eta> b \<turnstile> a]"
abbreviation plMT3 ("lMT3\<^sup>_\<^sup>_ _ _") where "lMT3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> (\<eta> a) (\<eta> b), b \<turnstile> a]"
definition lMT0::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "lMT0 \<iota> \<eta> \<equiv> \<forall>a b. lMT0\<^sup>a\<^sup>b \<iota> \<eta>"
definition lMT1::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "lMT1 \<iota> \<eta> \<equiv> \<forall>a b. lMT1\<^sup>a\<^sup>b \<iota> \<eta>"
definition lMT2::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "lMT2 \<iota> \<eta> \<equiv> \<forall>a b. lMT2\<^sup>a\<^sup>b \<iota> \<eta>"
definition lMT3::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "lMT3 \<iota> \<eta> \<equiv> \<forall>a b. lMT3\<^sup>a\<^sup>b \<iota> \<eta>"
  
declare lMT0_def[neg] lMT1_def[neg] lMT2_def[neg] lMT3_def[neg]

text\<open>All these MT variants are in general independent from each other and also from (strong) CoP instances.
However if we take classical implication we can verify that local MT and CoP are indeed equivalent.\<close>
lemma "lMT0(\<^bold>\<rightarrow>) \<eta> = lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lMT1(\<^bold>\<rightarrow>) \<eta> = lCoP1(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lMT2(\<^bold>\<rightarrow>) \<eta> = lCoP2(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lMT3(\<^bold>\<rightarrow>) \<eta> = lCoP3(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast


subsubsection \<open>Disjunctive syllogism\<close>

text\<open>DS: disjunctive syllogism.\<close>
abbreviation pDS1 ("DS1\<^sup>_\<^sup>_ _ _") where "DS1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [a \<^bold>\<or> b \<turnstile> \<iota> (\<eta> a) b]"
abbreviation pDS2 ("DS2\<^sup>_\<^sup>_ _ _") where "DS2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> (\<eta> a) b \<turnstile> a \<^bold>\<or> b]"
abbreviation pDS3 ("DS3\<^sup>_\<^sup>_ _ _") where "DS3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<eta> a \<^bold>\<or> b \<turnstile> \<iota> a b]"
abbreviation pDS4 ("DS4\<^sup>_\<^sup>_ _ _") where "DS4\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> [\<iota> a b \<turnstile> \<eta> a \<^bold>\<or> b]"
definition DS1::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "DS1 \<iota> \<eta> \<equiv> \<forall>a b. DS1\<^sup>a\<^sup>b \<iota> \<eta>"
definition DS2::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "DS2 \<iota> \<eta> \<equiv> \<forall>a b. DS2\<^sup>a\<^sup>b \<iota> \<eta>"
definition DS3::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "DS3 \<iota> \<eta> \<equiv> \<forall>a b. DS3\<^sup>a\<^sup>b \<iota> \<eta>"
definition DS4::"('w \<sigma>\<Rightarrow>'w \<sigma>\<Rightarrow>'w \<sigma>) \<Rightarrow> 'w \<Omega>" where "DS4 \<iota> \<eta> \<equiv> \<forall>a b. DS4\<^sup>a\<^sup>b \<iota> \<eta>"

declare DS1_def[neg] DS2_def[neg] DS3_def[neg] DS4_def[neg]

text\<open>All DS variants are in general independent from each other. However if we take classical implication
we can verify that the pairs DS1-DS3 and DS2-DS4 are indeed equivalent. \<close>
lemma "DS1(\<^bold>\<rightarrow>) \<eta> = DS3(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "DS2(\<^bold>\<rightarrow>) \<eta> = DS4(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast

text\<open>Explore some (non)entailment relations.\<close>
lemma DS1_nDNor: "DS1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> nDNRM \<eta>" unfolding neg cond conn order by metis
lemma DS2_nNor:  "DS2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> nNORM \<eta>" unfolding neg cond conn order by metis
lemma lCoP2_DS1: "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma lCoP1_DS2: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "CoP2 \<eta> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "CoP1 \<eta> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<eta>" nitpick oops \<comment>\<open> counterexample \<close>

end
