theory logics_LFU
  imports logics_consequence conditions_relativized_infinitary
begin

subsection \<open>Logics of Formal Undeterminedness (LFUs)\<close>

text\<open>The LFUs are a family of paracomplete logics featuring a 'determinedness' operator @{text "\<currency>"}
that can be used to recover some classical properties of negation (in particular TND).
LFUs behave in a sense dually to LFIs. Both can be semantically embedded as extensions of Boolean algebras.
We show a shallow semantical embedding of a family of self-extensional LFUs using the closure operator
as primitive.\<close>

(*Let us assume a concrete type w (for 'worlds' or 'points').*)
typedecl w
(*Let us assume the following primitive unary operation intended as a closure operator.*)
consts \<C>::"w \<sigma> \<Rightarrow> w \<sigma>"

(*From the topological cube of opposition:*)
abbreviation "\<I> \<equiv> \<C>\<^sup>d" 
abbreviation "\<B> \<equiv> (\<C>\<^sup>f\<^sup>p)\<^sup>d" 

(*let us recall that: *)
lemma "EXPN \<C> = CNTR \<B>" using EXPN_CNTR_dual1 EXPN_fp by blast
lemma "EXPN \<C> = CNTR \<I>" by (simp add: EXPN_CNTR_dual1)

text\<open>For LFUs we use the negation previously defined as @{text "\<I>\<^sup>d\<^sup>- = \<C>\<^sup>-"}.\<close>
abbreviation neg ("\<^bold>\<not>_"[70]71) where "neg \<equiv> \<C>\<^sup>-"

text\<open>In terms of the border operator the negation looks as follows:\<close>
lemma neg_char: "EXPN \<C> \<Longrightarrow> \<^bold>\<not>A = (\<^bold>\<midarrow>A \<^bold>\<and> \<B>\<^sup>d A)" unfolding conn by (metis EXPN_def compl_def dimpl_def dual_invol op_fixpoint_def subset_def svfun_compl_def)

abbreviation "CLOSURE \<phi> \<equiv> ADDI \<phi> \<and> EXPN \<phi> \<and> NORM \<phi> \<and> IDEM \<phi>"

text\<open>This negation is of course paracomplete.\<close>
lemma "CLOSURE \<C> \<Longrightarrow> [\<turnstile> a \<^bold>\<or> \<^bold>\<not>a]" nitpick oops \<comment>\<open> countermodel \<close>

text\<open>We define two pairs of un/determinedness operators and show how they relate to each other.
This logic corresponds to the paracomplete dual of the LFI 'RmbC-ciw'.\<close>
abbreviation op_det_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<currency>\<^sup>A_" [57]58) 
  where "\<currency>\<^sup>AA \<equiv> A \<^bold>\<or> \<^bold>\<not>A"
abbreviation op_und_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<star>\<^sup>A_" [57]58) (* \<star> as truth-gap *)
  where "\<star>\<^sup>AA \<equiv> \<^bold>\<midarrow>\<currency>\<^sup>AA"
abbreviation op_det_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<currency>\<^sup>B_" [57]58) 
  where "\<currency>\<^sup>BA \<equiv> \<B>\<^sup>d A"
abbreviation op_und_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<star>\<^sup>B_" [57]58) (* \<star> as border of the complement *)
  where "\<star>\<^sup>BA \<equiv> \<B>\<^sup>d\<^sup>- A"


text\<open>Observe that assumming EXPN for closure we are allowed to exchange A and B variants.\<close>
lemma pundAB: "EXPN \<C> \<Longrightarrow> \<star>\<^sup>AA = \<star>\<^sup>BA" using neg_char by (metis BA_deMorgan1 BA_dn L4 L9 dimpl_char impl_char ofp_comm_dc2 op_fixpoint_def sdfun_dcompl_def setequ_ext svfun_compl_def)
lemma pdetAB: "EXPN \<C> \<Longrightarrow> \<currency>\<^sup>AA = \<currency>\<^sup>BA" by (metis dual_compl_char1 pundAB sfun_compl_invol svfun_compl_def)

text\<open>Variants A and B give us slightly different properties (there are countermodels for those not shown).\<close>
lemma Prop1: "\<currency>\<^sup>BA = \<C>\<^sup>f\<^sup>p A" by (simp add: dual_invol setequ_ext)
lemma Prop2: "\<currency>\<^sup>AA = (\<C> A \<^bold>\<rightarrow> A)" unfolding conn by (metis compl_def svfun_compl_def)
lemma Prop3: "fp \<I> A \<longleftrightarrow> [\<turnstile> \<currency>\<^sup>B\<^bold>\<midarrow>A]" by (simp add: dual_invol fp_d_rel gtrue_def)
lemma Prop4a: "fp \<C> A \<longleftrightarrow> [\<turnstile> \<currency>\<^sup>BA]" by (simp add: dual_invol fp_rel gtrue_def)
lemma Prop4b: "fp \<C> A  \<longrightarrow> [\<turnstile> \<currency>\<^sup>AA]" by (simp add: compl_def fixpoints_def join_def setequ_ext svfun_compl_def)

text\<open>Recovering TND works for both variants.\<close>
lemma "[\<currency>\<^sup>Aa \<turnstile> a, \<^bold>\<not>a]" by (simp add: subset_def)
lemma "[\<turnstile> \<star>\<^sup>Aa \<^bold>\<or> a \<^bold>\<or> \<^bold>\<not>a]" by (metis compl_def join_def)
lemma "[\<currency>\<^sup>Ba \<turnstile> a, \<^bold>\<not>a]" by (simp add: compl_def dimpl_def dual_invol join_def op_fixpoint_def subset_def svfun_compl_def)
lemma "[\<turnstile> \<star>\<^sup>Ba \<^bold>\<or> a \<^bold>\<or> \<^bold>\<not>a]" by (metis dimpl_def dual_compl_char1 dual_invol join_def ofp_comm_compl op_fixpoint_def)

text\<open>We show how (local) contraposition variants (among others) can be recovered using the
 determinedness operators.\<close>
lemma "[\<currency>\<^sup>Aa, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma det_lcop0_A: "EXPN \<C> \<Longrightarrow> [\<currency>\<^sup>Aa,  a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" using neg_char impl_char unfolding conn order  by fastforce
lemma "[\<currency>\<^sup>Ba, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma det_lcop0_B: "EXPN \<C> \<Longrightarrow> [\<currency>\<^sup>Ba,  a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (metis det_lcop0_A pdetAB)
lemma "[\<currency>\<^sup>Aa, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma det_lcop1_A: "EXPN \<C> \<Longrightarrow> [\<currency>\<^sup>Aa, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile>  b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (smt (verit, ccfv_SIG) impl_char impl_def join_def meet_def neg_char subset_def)
lemma "[\<currency>\<^sup>Ba, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma det_lcop1_B: "EXPN \<C> \<Longrightarrow> [\<currency>\<^sup>Ba, a \<^bold>\<rightarrow> \<^bold>\<not>b \<turnstile>  b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (metis det_lcop1_A pdetAB)
lemma "[\<currency>\<^sup>Aa, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" nitpick oops
lemma det_lcop2_A: "EXPN \<C> \<Longrightarrow> [\<currency>\<^sup>Aa, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" by (smt (verit, del_insts) neg_char compl_def impl_char join_def meet_def subset_def)
lemma "[\<currency>\<^sup>Ba, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" nitpick oops
lemma det_lcop2_B: "EXPN \<C> \<Longrightarrow> [\<currency>\<^sup>Ba, \<^bold>\<not>a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" by (metis det_lcop2_A pdetAB)

end
