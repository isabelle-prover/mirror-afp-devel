theory logics_LFI
  imports logics_consequence conditions_relativized_infinitary
begin

subsection \<open>Logics of Formal Inconsistency (LFIs)\<close>

text\<open>The LFIs are a family of paraconsistent logics featuring a 'consistency' operator @{text "\<circ>"}
that can be used to recover some classical properties of negation (in particular ECQ).
We show a shallow semantical embedding of a family of self-extensional LFIs using the border operator
as primitive.\<close>

text\<open>Let us assume a concrete type w (for 'worlds' or 'points').\<close>
typedecl w
text\<open>Let us assume the following primitive unary operation intended as a border operator.\<close>
consts \<B>::"w \<sigma> \<Rightarrow> w \<sigma>"

text\<open>From the topological cube of opposition we have that:\<close>
abbreviation "\<C> \<equiv> (\<B>\<^sup>f\<^sup>p)\<^sup>d\<^sup>-" 
abbreviation "\<I> \<equiv> \<B>\<^sup>f\<^sup>p\<^sup>-" 
lemma "\<C>\<^sup>d\<^sup>- = \<B>\<^sup>f\<^sup>p" by (simp add: dualcompl_invol)

text\<open>Let us recall that:\<close>
lemma expn_cntr: "EXPN \<C> = CNTR \<B>" by (metis EXPN_CNTR_dual2 EXPN_fp ofp_comm_dc1)

text\<open>For LFIs we use the negation previously defined as @{text "\<C>\<^sup>d\<^sup>- = \<B>\<^sup>f\<^sup>p"}.\<close>
abbreviation neg ("\<^bold>\<not>_"[70]71) where "neg \<equiv> \<B>\<^sup>f\<^sup>p"

text\<open>In terms of the border operator the negation looks as follows (under appropriate assumptions):\<close>
lemma neg_char: "CNTR \<B> \<Longrightarrow> \<^bold>\<not>A = (\<^bold>\<midarrow>A \<^bold>\<or> \<B> A)" unfolding conn by (metis CNTR_def dimpl_def op_fixpoint_def subset_def)

text\<open>This negation is of course boldly paraconsistent (for both local and global consequence).\<close>
lemma "[a, \<^bold>\<not>a \<turnstile> b]" nitpick oops \<comment>\<open> countermodel \<close>
lemma "[a, \<^bold>\<not>a \<turnstile> \<^bold>\<not>b]" nitpick oops \<comment>\<open> countermodel \<close>
lemma "[a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" nitpick oops \<comment>\<open> countermodel \<close> 
lemma "[a, \<^bold>\<not>a \<turnstile>\<^sub>g \<^bold>\<not>b]" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>We define two pairs of in/consistency operators and show how they relate to each other.
Using LFIs terminology, the minimal logic so encoded corresponds to RmbC + 'ciw' axiom.\<close>
abbreviation op_inc_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<bullet>\<^sup>A_" [57]58) (* \<bullet> as truth-glut *)
  where "\<bullet>\<^sup>AA \<equiv> A \<^bold>\<and> \<^bold>\<not>A"
abbreviation op_con_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<circ>\<^sup>A_" [57]58) 
  where "\<circ>\<^sup>AA \<equiv> \<^bold>\<midarrow>\<bullet>\<^sup>AA"
abbreviation op_inc_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<bullet>\<^sup>B_" [57]58) (* \<bullet> as border *)
  where "\<bullet>\<^sup>BA \<equiv> \<B> A"
abbreviation op_con_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<circ>\<^sup>B_" [57]58) 
  where "\<circ>\<^sup>BA \<equiv> \<B>\<^sup>- A"

text\<open>Observe that assumming CNTR for border we are allowed to exchange A and B variants.\<close>
lemma pincAB: "CNTR \<B> \<Longrightarrow> \<bullet>\<^sup>AA = \<bullet>\<^sup>BA" using neg_char by (metis CNTR_def CNTR_fpc L5 L6 L9 dimpl_char impl_char ofp_invol op_fixpoint_def setequ_ext svfun_compl_def)
lemma pconAB: "CNTR \<B> \<Longrightarrow> \<circ>\<^sup>AA = \<circ>\<^sup>BA" by (metis pincAB setequ_ext svfun_compl_def) 

text\<open>Variants A and B give us slightly different properties (there are countermodels for those not shown).\<close>
lemma Prop1: "\<circ>\<^sup>BA = \<I>\<^sup>f\<^sup>p A" by (simp add: ofp_comm_compl ofp_invol)
lemma Prop2: "\<circ>\<^sup>AA = (A \<^bold>\<rightarrow> \<I> A)" by (simp add: compl_def impl_def meet_def svfun_compl_def)
lemma Prop3: "fp \<C> A \<longleftrightarrow> [\<turnstile> \<circ>\<^sup>B\<^bold>\<midarrow>A]" by (simp add: fp_rel gtrue_def ofp_comm_dc2 ofp_invol op_dual_def svfun_compl_def)
lemma Prop4a: "fp \<I> A \<longleftrightarrow> [\<turnstile> \<circ>\<^sup>BA]" by (simp add: fp_rel gtrue_def ofp_comm_compl ofp_invol)
lemma Prop4b: "fp \<I> A  \<longrightarrow> [\<turnstile> \<circ>\<^sup>AA]" by (simp add: Prop2 fixpoints_def impl_def setequ_ext)

text\<open>The 'principle of gentle explosion' works for both variants (both locally and globally).\<close>
lemma "[\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<turnstile> b]" by (metis (mono_tags, lifting) compl_def meet_def subset_def)
lemma "[\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis compl_def meet_def)
lemma "[\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<turnstile> b]" by (smt (z3) meet_def ofp_fixpoint_compl_def ofp_invol sdiff_def subset_def)
lemma "[\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis compl_def fixpoints_def fp_rel gtrue_def setequ_ext svfun_compl_def)

abbreviation "BORDER \<phi> \<equiv> nMULTr \<phi> \<and> CNTR \<phi> \<and> nDNRM \<phi> \<and> nIDEMr\<^sup>b \<phi>"

text\<open>We show how (local) contraposition variants (among others) can be recovered using the
 consistency operators.\<close>
lemma "[\<circ>\<^sup>Ab, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops \<comment>\<open> countermodel \<close>
lemma cons_lcop0_A: "CNTR \<B> \<longrightarrow> [\<circ>\<^sup>Ab,  a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (smt (verit, del_insts) neg_char compl_def impl_char join_def meet_def subset_def)
lemma "[\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops \<comment>\<open> countermodel \<close>
lemma cons_lcop0_B: "CNTR \<B> \<longrightarrow> [\<circ>\<^sup>Bb,  a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (metis cons_lcop0_A pconAB)
lemma "[\<circ>\<^sup>Ab, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops \<comment>\<open> countermodel \<close>
lemma cons_lcop1_A: "CNTR \<B> \<longrightarrow> [\<circ>\<^sup>Ab, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile>  b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (smt (verit, del_insts) neg_char compl_def impl_char join_def meet_def subset_def)
lemma "[\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops \<comment>\<open> countermodel \<close>
lemma cons_lcop1_B: "CNTR \<B> \<longrightarrow> [\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile>  b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (metis cons_lcop1_A pconAB)
lemma "[\<circ>\<^sup>Ab, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" nitpick oops \<comment>\<open> countermodel \<close>
lemma cons_lcop2_A: "CNTR \<B> \<longrightarrow> [\<circ>\<^sup>Ab, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" by (smt (verit, del_insts) neg_char compl_def impl_char join_def meet_def subset_def)
lemma "[\<circ>\<^sup>Bb, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" nitpick oops \<comment>\<open> countermodel \<close>
lemma cons_lcop2_B: "CNTR \<B> \<longrightarrow> [\<circ>\<^sup>Bb, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" by (metis cons_lcop2_A pconAB)

text\<open>The following axioms are commonly employed in the literature on LFIs to obtain stronger logics.
We explore under which conditions they can be assumed while keeping the logic boldly paraconsistent.\<close>
abbreviation cf where "cf \<equiv> \<forall>P. [\<^bold>\<not>\<^bold>\<not>P \<turnstile> P]"
abbreviation ce where "ce \<equiv> \<forall>P. [P \<turnstile> \<^bold>\<not>\<^bold>\<not>P]"
abbreviation ciw_a where "ciw_a \<equiv> \<forall>P. [\<turnstile> \<circ>\<^sup>AP \<^bold>\<or> \<bullet>\<^sup>AP]"
abbreviation ciw_b where "ciw_b \<equiv> \<forall>P. [\<turnstile> \<circ>\<^sup>BP \<^bold>\<or> \<bullet>\<^sup>BP]"
abbreviation ci_a  where  "ci_a \<equiv> \<forall>P. [\<^bold>\<not>(\<circ>\<^sup>AP) \<turnstile> \<bullet>\<^sup>AP]"
abbreviation ci_b  where  "ci_b \<equiv> \<forall>P. [\<^bold>\<not>(\<circ>\<^sup>BP) \<turnstile> \<bullet>\<^sup>BP]"
abbreviation cl_a  where  "cl_a \<equiv> \<forall>P.  [\<^bold>\<not>(\<bullet>\<^sup>AP) \<turnstile> \<circ>\<^sup>AP]"
abbreviation cl_b  where  "cl_b \<equiv> \<forall>P.  [\<^bold>\<not>(\<bullet>\<^sup>BP) \<turnstile> \<circ>\<^sup>BP]"
abbreviation ca_conj_a where "ca_conj_a \<equiv> \<forall>P Q. [\<circ>\<^sup>AP,\<circ>\<^sup>AQ \<turnstile> \<circ>\<^sup>A(P \<^bold>\<and> Q)]"
abbreviation ca_conj_b where "ca_conj_b \<equiv> \<forall>P Q. [\<circ>\<^sup>BP,\<circ>\<^sup>BQ \<turnstile> \<circ>\<^sup>B(P \<^bold>\<and> Q)]"
abbreviation ca_disj_a where "ca_disj_a \<equiv> \<forall>P Q. [\<circ>\<^sup>AP,\<circ>\<^sup>AQ \<turnstile> \<circ>\<^sup>A(P \<^bold>\<or> Q)]"
abbreviation ca_disj_b where "ca_disj_b \<equiv> \<forall>P Q. [\<circ>\<^sup>BP,\<circ>\<^sup>BQ \<turnstile> \<circ>\<^sup>B(P \<^bold>\<or> Q)]"
abbreviation ca_impl_a where "ca_impl_a \<equiv> \<forall>P Q. [\<circ>\<^sup>AP,\<circ>\<^sup>AQ \<turnstile> \<circ>\<^sup>A(P \<^bold>\<rightarrow> Q)]"
abbreviation ca_impl_b where "ca_impl_b \<equiv> \<forall>P Q. [\<circ>\<^sup>BP,\<circ>\<^sup>BQ \<turnstile> \<circ>\<^sup>B(P \<^bold>\<rightarrow> Q)]"
abbreviation ca_a where "ca_a \<equiv> ca_conj_a \<and> ca_disj_a \<and> ca_impl_a"
abbreviation ca_b where "ca_b \<equiv> ca_conj_b \<and> ca_disj_b \<and> ca_impl_b"

text\<open>cf\<close>
lemma "BORDER \<B> \<Longrightarrow> cf" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>ce\<close>
lemma "BORDER \<B> \<Longrightarrow> ce" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>ciw\<close>
lemma prop_ciw_a: "ciw_a" by (simp add: conn)
lemma prop_ciw_b: "ciw_b" by (simp add: conn svfun_compl_def)

text\<open>ci\<close>
lemma "BORDER \<B> \<Longrightarrow> ci_a" nitpick oops \<comment>\<open> countermodel \<close>
lemma "BORDER \<B> \<Longrightarrow> ci_b" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>cl\<close>
lemma "BORDER \<B> \<Longrightarrow> cl_a" nitpick oops \<comment>\<open> countermodel \<close>
lemma "BORDER \<B> \<Longrightarrow> cl_b" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>ca-conj\<close>
lemma prop_ca_conj_b: "nMULT\<^sup>b \<B> = ca_conj_b" by (metis MULT_b_def nMULTb_compl sfun_compl_invol)
lemma prop_ca_conj_a: "nMULTr\<^sup>b \<B> = ca_conj_a" unfolding cond op_fixpoint_def by (smt (z3) compl_def dimpl_def join_def meet_def op_fixpoint_def subset_def subset_in_def)

text\<open>ca-disj\<close>
lemma prop_ca_disj_b: "ADDI\<^sup>a \<B> = ca_disj_b" by (simp add: nADDI_a_def nADDIa_compl)
lemma prop_ca_disj_a: "nMULTr\<^sup>a \<B> = ca_disj_a" oops (*TODO*)

text\<open>ca-impl\<close>
lemma "BORDER \<B> \<Longrightarrow> ca_impl_a" nitpick oops \<comment>\<open> countermodel \<close>
lemma "BORDER \<B> \<Longrightarrow> ca_impl_b" nitpick oops \<comment>\<open> countermodel \<close>

end
