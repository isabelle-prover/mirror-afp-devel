theory conditions_positive_infinitary
  imports conditions_positive boolean_algebra_infinitary
begin

subsection \<open>Infinitary Positive Conditions\<close>

text\<open>We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.\<close>

text\<open>Distribution over infinite joins (suprema) or infinite additivity (iADDI).\<close>
definition iADDI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI")
  where "iADDI \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>= \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI\<^sup>a")
  where "iADDI\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<le> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI\<^sup>b")
  where "iADDI\<^sup>b \<phi> \<equiv> \<forall>S. \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le> \<phi>(\<^bold>\<Or>S)"
text\<open>Distribution over infinite meets (infima) or infinite multiplicativity (iMULT).\<close>
definition iMULT::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT")
  where "iMULT \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>= \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>" 
definition iMULT_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT\<^sup>a")
  where "iMULT\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<le> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"
definition iMULT_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT\<^sup>b")
  where "iMULT\<^sup>b \<phi> \<equiv> \<forall>S. \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le> \<phi>(\<^bold>\<And>S)"

declare iADDI_def[cond] iADDI_a_def[cond] iADDI_b_def[cond]
        iMULT_def[cond] iMULT_a_def[cond] iMULT_b_def[cond]

lemma iADDI_char: "iADDI \<phi> = (iADDI\<^sup>a \<phi> \<and> iADDI\<^sup>b \<phi>)" unfolding cond using setequ_char by blast
lemma iMULT_char: "iMULT \<phi> = (iMULT\<^sup>a \<phi> \<and> iMULT\<^sup>b \<phi>)" unfolding cond using setequ_char by blast

text\<open>ADDI-b and iADDI-b are in fact equivalent.\<close>
lemma iADDIb_equ: "iADDI\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" proof -
  have lr: "iADDI\<^sup>b \<phi> \<Longrightarrow> ADDI\<^sup>b \<phi>" proof -
  assume iaddib: "iADDI\<^sup>b \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>" (*Isabelle forces us to use 'a as type variable name*)
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<Or>?S = A \<^bold>\<or> B" unfolding supremum_def join_def by blast
    hence p1: "\<phi>(\<^bold>\<Or>?S) = \<phi>(A \<^bold>\<or> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding image_def by metis
    hence p2: "\<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<or> (\<phi> B)" unfolding supremum_def join_def by auto
    have " \<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> \<^bold>\<le> \<phi>(\<^bold>\<Or>?S)" using iaddib iADDI_b_def by blast    
    hence "(\<phi> A) \<^bold>\<or> (\<phi> B) \<^bold>\<le> \<phi>(A \<^bold>\<or> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: ADDI_b_def) qed
  have rl: "ADDI\<^sup>b \<phi> \<Longrightarrow> iADDI\<^sup>b \<phi>" unfolding iADDI_b_def by (smt (verit) MONO_ADDIb MONO_def lub_def image_def sup_lub upper_bounds_def) 
  from lr rl show ?thesis by auto
qed
text\<open>MULT-a and iMULT-a are also equivalent.\<close>
lemma iMULTa_equ: "iMULT\<^sup>a \<phi> = MULT\<^sup>a \<phi>" proof -
  have lr: "iMULT\<^sup>a \<phi> \<Longrightarrow> MULT\<^sup>a \<phi>" proof -
  assume imulta: "iMULT\<^sup>a \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>" (*Isabelle forces us to use 'a as type variable name*)
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<And>?S = A \<^bold>\<and> B" unfolding infimum_def meet_def by blast
    hence p1: "\<phi>(\<^bold>\<And>?S) = \<phi>(A \<^bold>\<and> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding image_def by metis
    hence p2: "\<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<and> (\<phi> B)" unfolding infimum_def meet_def by auto
    have "\<phi>(\<^bold>\<And>?S) \<^bold>\<le> \<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk>" using imulta iMULT_a_def by blast    
    hence "\<phi>(A \<^bold>\<and> B) \<^bold>\<le> (\<phi> A) \<^bold>\<and> (\<phi> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: MULT_a_def) qed
  have rl: "MULT\<^sup>a \<phi> \<Longrightarrow> iMULT\<^sup>a \<phi>" by (smt (verit) MONO_MULTa MONO_def glb_def iMULT_a_def inf_glb lower_bounds_def image_def)
  from lr rl show ?thesis by blast
qed

text\<open>Thus we have that MONO, ADDI-b/iADDI-b and MULT-a/iMULT-a are all equivalent.\<close>
lemma MONO_iADDIb: "iADDI\<^sup>b \<phi> = MONO \<phi>" unfolding MONO_ADDIb iADDIb_equ by simp
lemma MONO_iMULTa: "iMULT\<^sup>a \<phi> = MONO \<phi>" unfolding MONO_MULTa iMULTa_equ by simp


text\<open>Below we prove several duality relationships between iADDI(a/b) and iMULT(a/b).\<close>

text\<open>Duality between iMULT-a and iADDI-b (an easy corollary from the previous equivalence).\<close>
lemma iMULTa_iADDIb_dual1: "iMULT\<^sup>a \<phi> = iADDI\<^sup>b \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual1 iADDIb_equ iMULTa_equ)
lemma iMULTa_iADDIb_dual2: "iADDI\<^sup>b \<phi> = iMULT\<^sup>a \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual2 iADDIb_equ iMULTa_equ)
text\<open>Duality between iADDI-a and iMULT-b.\<close>
lemma iADDIa_iMULTb_dual1: "iADDI\<^sup>a \<phi> = iMULT\<^sup>b \<phi>\<^sup>d" by (smt (z3) BA_cmpl_equ BA_cp dualcompl_invol iADDI_a_def iDM_a iMULT_b_def im_prop1 op_dual_def setequ_ext)
lemma iADDIa_iMULTb_dual2: "iMULT\<^sup>b \<phi> = iADDI\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol iADDIa_iMULTb_dual1)
text\<open>Duality between iADDI and iMULT.\<close>
lemma iADDI_iMULT_dual1: "iADDI \<phi> = iMULT \<phi>\<^sup>d" using iADDI_char iADDIa_iMULTb_dual1 iMULT_char iMULTa_iADDIb_dual2 by blast
lemma iADDI_iMULT_dual2: "iMULT \<phi> = iADDI \<phi>\<^sup>d" by (simp add: dual_invol iADDI_iMULT_dual1)

text\<open>In fact, infinite additivity (multiplicativity) entails (dual) normality:\<close>
lemma iADDI_NORM: "iADDI \<phi> \<longrightarrow> NORM \<phi>" unfolding cond by (metis bottom_def image_def setequ_ext sup_empty)
lemma iMULT_DNRM: "iMULT \<phi> \<longrightarrow> DNRM \<phi>" by (simp add: NOR_dual2 iADDI_NORM iADDI_iMULT_dual2)

text\<open>Suitable conditions on an operation can make the set of its fixed-points closed under infinite meets/joins.\<close>

lemma fp_sup_closed_cond1: "iADDI \<phi> \<longrightarrow> supremum_closed (fp \<phi>)" unfolding cond order supremum_closed_def fixpoints_def image_def by (smt (verit) supremum_def)
lemma fp_sup_closed_cond2: "iADDI\<^sup>a \<phi> \<and> EXPN \<phi> \<longrightarrow> supremum_closed (fp \<phi>)" unfolding cond by (smt (z3) fixpoints_def image_def setequ_char subset_def supremum_closed_def supremum_def)
lemma fp_sup_closed_cond3: "MONO \<phi> \<and> CNTR \<phi> \<longrightarrow> supremum_closed (fp \<phi>)" unfolding cond by (smt (verit, del_insts) fixpoints_def lub_def setequ_char setequ_ext subset_def sup_lub supremum_closed_def upper_bounds_def)

lemma fp_inf_closed_cond1: "iMULT \<phi> \<longrightarrow> infimum_closed (fp \<phi>)" by (metis fp_dual fp_sup_closed_cond1 iADDI_iMULT_dual2 inf_sup_closed_dc)
lemma fp_inf_closed_cond2: "iMULT\<^sup>b \<phi> \<and> CNTR \<phi> \<longrightarrow> infimum_closed (fp \<phi>)" by (metis EXPN_CNTR_dual2 fp_dual fp_sup_closed_cond2 iADDIa_iMULTb_dual2 inf_sup_closed_dc)
lemma fp_inf_closed_cond3: "MONO \<phi> \<and> EXPN \<phi> \<longrightarrow> infimum_closed (fp \<phi>)" by (metis EXPN_CNTR_dual1 MONO_dual fp_dual fp_sup_closed_cond3 inf_sup_closed_dc)

text\<open>OTOH, the converse conjectures have (finite) countermodels. They need additional assumptions.\<close>
lemma "infimum_closed (fp \<phi>) \<longrightarrow> iMULT \<phi>" nitpick oops \<comment>\<open> countermodel found: needs further assumptions \<close>
lemma "supremum_closed (fp \<phi>) \<longrightarrow> iADDI \<phi>" nitpick oops \<comment>\<open> countermodel found: needs further assumptions \<close>
lemma fp_inf_closed_iMULT: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> infimum_closed (fp \<phi>) \<longrightarrow> iMULT \<phi>"
proof -
assume mono: "MONO \<phi>" and cntr: "CNTR \<phi>" and idem:"IDEM\<^sup>b \<phi>" {
  assume ic:"infimum_closed (fp \<phi>)" {
    fix S
    from ic have "\<forall>D. D \<^bold>\<le> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<And>D)" unfolding infimum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<^bold>= \<phi> X)) \<longrightarrow> \<^bold>\<And>D \<^bold>= \<phi> \<^bold>\<And>D" by (simp add: fixpoints_def setequ_ext subset_def) 
    moreover from idem have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<^bold>= \<phi> X))" by (metis (mono_tags, lifting) CNTR_def IDEM_b_def cntr image_def setequ_char)
    ultimately have aux: "\<^bold>\<And>(\<lbrakk>\<phi> S\<rbrakk>) \<^bold>= \<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    from cntr have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le> \<^bold>\<And>S" by (smt (verit, best) CNTR_def image_def infimum_def subset_def)
    hence "\<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>) \<^bold>\<le> \<phi>(\<^bold>\<And>S)" using mono by (simp add: MONO_def) 
    from this aux have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le> \<phi>(\<^bold>\<And>S)" by (simp add: setequ_ext)
  } hence "infimum_closed (fp \<phi>) \<longrightarrow> iMULT \<phi>" by (simp add: MONO_iMULTa iMULT_b_def iMULT_char mono)
} thus ?thesis by simp 
qed
lemma fp_sup_closed_iADDI: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> supremum_closed (fp \<phi>) \<longrightarrow> iADDI \<phi>" 
  (* by (metis EXPN_CNTR_dual1 IDEM_dual2 MONO_dual dual_invol fp_inf_closed_iMULT fp_inf_sup_closed_dual iADDI_iMULT_dual1) *)
proof -
assume mono: "MONO \<phi>" and expn: "EXPN \<phi>" and idem:"IDEM\<^sup>a \<phi>" {
  assume sc:"supremum_closed (fp \<phi>)" {
    fix S
    from sc have "\<forall>D. D \<^bold>\<le> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<Or>D)" unfolding supremum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<^bold>= \<phi> X)) \<longrightarrow> \<^bold>\<Or>D \<^bold>= \<phi> \<^bold>\<Or>D" by (simp add: fixpoints_def setequ_ext subset_def)
    moreover have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<^bold>= \<phi> X))" by (metis (mono_tags, lifting) EXPN_def IDEM_a_def expn idem image_def setequ_char)
    ultimately have aux: "\<^bold>\<Or>(\<lbrakk>\<phi> S\<rbrakk>) \<^bold>= \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    have "\<^bold>\<Or>S \<^bold>\<le> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis EXPN_CNTR_dual1 EXPN_def IDEM_dual1 MONO_dual dual_invol expn fp_inf_closed_iMULT fp_inf_sup_closed_dual iADDI_def iADDI_iMULT_dual1 idem mono sc setequ_ext)
    hence "\<phi>(\<^bold>\<Or>S) \<^bold>\<le> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" using mono by (simp add: MONO_def) 
    from this aux have "\<phi>(\<^bold>\<Or>S) \<^bold>\<le> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis setequ_ext)
  } hence "supremum_closed (fp \<phi>) \<longrightarrow> iADDI \<phi>" by (simp add: MONO_ADDIb iADDI_a_def iADDI_char iADDIb_equ mono)
} thus ?thesis by simp
qed

section \<open>Alexandrov topologies and (generalized) specialization preorders\<close>

text\<open>A topology is called 'Alexandrov' (after the Russian mathematician Pavel Alexandrov) if the intersection
(resp. union) of any (finite or infinite) family of open (resp. closed) sets is open (resp. closed);
in algebraic terms, this means that the set of fixed points of the interior (closure) operation is closed
under infinite meets (joins). Another common algebraic formulation requires the closure (interior) operation
to satisfy the infinitary variants of additivity (multiplicativity), i.e. iADDI (iMULT) as introduced before.

In the literature, the well-known Kuratowski conditions for the closure (resp. interior) operation are assumed,
namely: ADDI, EXPN, NORM, IDEM (resp. MULT, CNTR, DNRM, IDEM). This makes both formulations equivalent.
However, this is not the case in general if those conditions become negotiable.\<close>

text\<open>Alexandrov topologies have interesting properties relating them to the semantics of modal logic.
Assuming Kuratowski conditions, Alexandrov topological operations defined on subsets of S are in one-to-one
correspondence with preorders on S; in topological terms, Alexandrov topologies are uniquely determined by
their specialization preorders. Since we do not presuppose any Kuratowski conditions to begin with, the
preorders in question are in general not even transitive. Here we just call them 'reachability relations'.
We will still call (generalized) closure/interior-like operations as such (for lack of a better name).
We explore minimal conditions under which some relevant results for the semantics of modal logic obtain.\<close>

text\<open>Closure/interior(-like) operators can be derived from an arbitrary relation (as in modal logic).\<close>
definition Cl_rel::"('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("\<C>[_]") 
  where "\<C>[R] \<equiv> \<lambda>A. \<lambda>w. \<exists>v. R w v \<and> A v"
definition Int_rel::"('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("\<I>[_]") 
  where "\<I>[R] \<equiv> \<lambda>A. \<lambda>w. \<forall>v. R w v \<longrightarrow> A v"

text\<open>Duality between interior and closure follows directly:\<close>
lemma dual_CI: "\<C>[R] = \<I>[R]\<^sup>d" by (simp add: Cl_rel_def Int_rel_def compl_def op_dual_def setequ_char)

text\<open>We explore minimal conditions of the reachability relation under which some operation's conditions obtain.\<close> 
text\<open>Define some relevant properties of relations: \<close>
abbreviation "serial R  \<equiv> \<forall>x. \<exists>y. R x y"
abbreviation "reflexive R  \<equiv> \<forall>x. R x x"
abbreviation "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation "antisymmetric R  \<equiv> \<forall>x y. R x y \<and> R y x \<longrightarrow> x = y"
abbreviation "symmetric R  \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"

lemma rC1: "iADDI \<C>[R]" unfolding iADDI_def Cl_rel_def image_def supremum_def using setequ_def by fastforce
lemma rC2: "reflexive R = EXPN \<C>[R]" by (metis (full_types) CNTR_def EXPN_CNTR_dual2 Int_rel_def dual_CI subset_def)
lemma rC3: "NORM \<C>[R]" by (simp add: iADDI_NORM rC1)
lemma rC4: "transitive R = IDEM\<^sup>a \<C>[R]" proof -
  have l2r: "transitive R \<longrightarrow> IDEM\<^sup>a \<C>[R]"  by (smt (verit, best) Cl_rel_def IDEM_a_def subset_def)
  have r2l: "IDEM\<^sup>a \<C>[R] \<longrightarrow> transitive R" unfolding Cl_rel_def IDEM_a_def subset_def using compl_def by force
  from l2r r2l show ?thesis by blast
qed


text\<open>A reachability (specialization) relation (preorder) can be derived from a given operation (intended as a closure-like operation).\<close>
definition \<R>::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool)" ("\<R>[_]") 
  where "\<R>[\<phi>] \<equiv> \<lambda>w v. \<phi> (\<lambda>x. x = v) w"

text\<open>Preorder properties of the reachability relation follow from the corresponding operation's conditions.\<close>
lemma rel_refl: "EXPN \<phi> \<longrightarrow> reflexive \<R>[\<phi>]" by (simp add: EXPN_def \<R>_def subset_def)
lemma rel_trans: "MONO \<phi> \<and> IDEM\<^sup>a \<phi> \<longrightarrow> transitive \<R>[\<phi>]" by (smt (verit, best) IDEM_a_def MONO_def \<R>_def subset_def)
lemma "IDEM\<^sup>a \<phi> \<longrightarrow> transitive \<R>[\<phi>]" nitpick oops \<comment>\<open> counterexample \<close>

(*The converse directions do not hold*)
lemma "reflexive \<R>[\<phi>] \<longrightarrow> EXPN \<phi>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "transitive \<R>[\<phi>] \<longrightarrow> IDEM\<^sup>a \<phi>" nitpick oops \<comment>\<open> counterexample \<close>
lemma "transitive \<R>[\<phi>] \<longrightarrow> MONO \<phi>" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>However, we can obtain finite countermodels for antisymmetry and symmetry given all relevant conditions.
We will revisit this issue later and examine their relation with the topological separation axioms T0 and T1 resp.\<close>
lemma "iADDI \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> antisymmetric \<R>[\<phi>]" nitpick oops \<comment>\<open> counterexample \<close>
lemma "iADDI \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> symmetric \<R>[\<phi>]" nitpick oops \<comment>\<open> counterexample \<close>

text\<open>As mentioned previously, Alexandrov closure (and by duality interior) operations correspond to 
specialization orderings (reachability relations).
It is worth mentioning that in Alexandrov topologies every point has a minimal/smallest neighborhood,
namely the set of points related to it by the specialization preorder (reachability relation).
We examine below  minimal conditions under which these relations obtain.\<close>

lemma Cl_rel'_a:   "MONO \<phi> \<longrightarrow> (\<forall>A. \<C>[\<R>[\<phi>]] A \<^bold>\<le> \<phi> A)" unfolding Cl_rel_def MONO_def \<R>_def by (smt (verit, ccfv_SIG) subset_def)
lemma Cl_rel'_b: "iADDI\<^sup>a \<phi> \<longrightarrow> (\<forall>A. \<phi> A \<^bold>\<le> \<C>[\<R>[\<phi>]] A)" proof -
{ assume iaddia: "iADDI\<^sup>a \<phi>"
  { fix A::"'a \<sigma>"
    let ?S="\<lambda>B. \<exists>w. A w \<and> B=(\<lambda>u. u=w)"
    have "A \<^bold>= (\<^bold>\<Or>?S)" unfolding supremum_def setequ_def by auto
    hence "\<phi>(A) \<^bold>= \<phi>(\<^bold>\<Or>?S)" by (simp add: setequ_ext)
    moreover have "\<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> \<^bold>= \<C>[\<R>[\<phi>]] A" by (smt (verit) Cl_rel_def \<R>_def image_def setequ_def supremum_def)
    moreover from iaddia have "\<phi>(\<^bold>\<Or>?S) \<^bold>\<le> \<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk>" unfolding iADDI_a_def by simp
    ultimately have "\<phi> A \<^bold>\<le> \<C>[\<R>[\<phi>]] A" by (simp add: setequ_ext)
} } thus ?thesis by simp
qed
lemma Cl_rel': "iADDI \<phi> \<longrightarrow> \<phi> \<^bold>=\<^sup>: \<C>[\<R>[\<phi>]]" by (simp add: MONO_iADDIb iADDI_char setequ_char Cl_rel'_a Cl_rel'_b svfun_equ_def)
lemma Cl_rel: "iADDI \<phi> \<longleftrightarrow> \<phi> = \<C>[\<R>[\<phi>]]" using Cl_rel' by (metis rC1 svfun_equ_ext)

text\<open>It is instructive to expand the definitions in the above result:\<close>
lemma "iADDI \<phi> \<longleftrightarrow> (\<forall>A. \<forall>w. (\<phi> A) w \<longleftrightarrow> (\<exists>v. A v \<and> \<phi> (\<lambda>x. x=v) w))" oops

text\<open>Closure (interior) operations derived from relations are thus closed under infinite joins (meets).\<close>
lemma "supremum_closed (fp \<C>[R])" by (simp add: fp_sup_closed_cond1 rC1)
lemma "infimum_closed  (fp \<I>[R])" by (metis dual_CI fp_inf_closed_cond1 iADDI_iMULT_dual2 rC1)


text\<open>We can now revisit the relationship between (anti)symmetry and the separation axioms T1 and T0.\<close>

text\<open>T0: any two distinct points in the space can be separated by a closed (or open) set (i.e. containing one point and not the other).\<close>
abbreviation "T0 \<C> \<equiv> (\<forall>p q. p \<noteq> q \<longrightarrow> (\<exists>G. (fp \<C>) G \<and> \<not>(G p \<longleftrightarrow> G q)))"
text\<open>T1: any two distinct points can be separated by (two not necessarily disjoint) closed (or open) sets.\<close>
abbreviation "T1 \<C> \<equiv> (\<forall>p q. p \<noteq> q \<longrightarrow> (\<exists>G H. (fp \<C>) G \<and> (fp \<C>) H \<and> G p \<and> \<not>G q \<and> H q \<and> \<not>H p))"

text\<open>We can (sanity) check that T1 entails T0 but not viceversa.\<close>
lemma "T1 \<C> \<Longrightarrow> T0 \<C>" by meson
lemma "T0 \<C> \<Longrightarrow> T1 \<C>" nitpick oops \<comment>\<open> counterexample \<close>


text\<open>Under appropriate conditions, T0-separation corresponds to antisymmetry of the specialization relation (here an ordering).\<close>
lemma "T0 \<C> \<longleftrightarrow> antisymmetric \<R>[\<C>]" nitpick oops (*counterexample*)
lemma T0_antisymm_a: "MONO \<C> \<Longrightarrow> T0 \<C> \<longrightarrow> antisymmetric \<R>[\<C>]" by (smt (verit, best) Cl_rel'_a Cl_rel_def fixpoints_def setequ_ext subset_def)
lemma T0_antisymm_b: "EXPN \<C> \<Longrightarrow> IDEM\<^sup>a \<C> \<Longrightarrow> antisymmetric \<R>[\<C>] \<longrightarrow> T0 \<C>" by (metis EXPN_impl_IDEM_b IDEM_char IDEM_def \<R>_def fixpoints_def rel_refl)
lemma T0_antisymm: "MONO \<C> \<Longrightarrow> EXPN \<C> \<Longrightarrow> IDEM\<^sup>a \<C> \<Longrightarrow> T0 \<C> = antisymmetric \<R>[\<C>]" using T0_antisymm_a T0_antisymm_b by fastforce

text\<open>Also, under the appropriate conditions, T1-separation corresponds to symmetry of the specialization relation.\<close>
lemma T1_symm_a: "MONO \<C> \<Longrightarrow> T1 \<C> \<longrightarrow> symmetric \<R>[\<C>]" by (metis (mono_tags, opaque_lifting) Cl_rel'_a Cl_rel_def fixpoints_def setequ_ext subset_def)
lemma T1_symm_b: "MONO \<C> \<Longrightarrow> EXPN \<C> \<Longrightarrow> T0 \<C> \<Longrightarrow> symmetric \<R>[\<C>] \<longrightarrow> T1 \<C>" by (smt (verit, ccfv_SIG) T0_antisymm_a \<R>_def fixpoints_def rel_refl setequ_def)
lemma T1_symm: "MONO \<C> \<Longrightarrow> EXPN \<C> \<Longrightarrow> T0 \<C> \<Longrightarrow> symmetric \<R>[\<C>] = T1 \<C>" using T1_symm_a T1_symm_b by (smt (verit, ccfv_threshold))

end
