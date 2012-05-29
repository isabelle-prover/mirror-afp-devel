(*  Title:       Isabelle/Circus
    Author:      Abderrahmane Feliachi, Burkhart Wolff, Marie-Claude Gaudel
                 Univ. Paris-Sud / LRI
    Maintainer:  Abderrahmane Feliachi
*)

header {* Using Isabelle/\Circus\ for Refinement Proofs
          \label{Refinement} \label{Section:framework}*}

theory Refinement
imports Denotational_Semantics
begin

subsection {* Relational and Functional Refinement in \Circus *}

text{*

The main goal of Isabelle/\Circus\ is to provide a proof environment for \Circus\ processes. 
The ``shallow-embedding'' of \Circus\ and UTP in Isabelle/HOL offers the 
possibility to reuse proof procedures, infrastructure and theorem libraries already 
existing in Isabelle/HOL. In this chapter, we will demonstrate 
Isabelle/\Circus\ 's potential by one of the
potential application areas, namely refinement proofs between processes
(the other important line of interest is the automated generation of
test-cases, which we adress in the future). 

In order to enter Isabelle/\Circus specifications, an own parser has
been developed (the the interested reader is referred to: 
\url{http://www.lri.fr/~feliachi/IsabelleCircus/}). In the
following, we will present our example both in high-level syntax
implementing common textbook notation on \Circus\ as well as the
semantic code resulting from these expressions in the context of 
the denotational semantics theories.
 
The Isabelle/\Circus\ parser (not discussed here), provides a means
to encode a process specification in terms of the presented
semantic theories, such that proofs of, e. g., refinement properties 
can be developped using the ISAR language for structured proofs.

In the following, 
we provide a small example of action refinement proof. 
The refinement relation is defined as the universal reverse implication in the UTP. 
In \Circus ,it is defined as follows: 

\begin{isar}
definition A1 \<sqsubseteq>c A2 \<equiv>  (Rep_Action A1) \<sqsubseteq>utp (Rep_Action A2)
\end{isar}
where A1 and A2 are \Circus\ actions, \inlineisar+\<sqsubseteq>c+ and \inlineisar+\<sqsubseteq>utp+ stands 
respectively for refinement relation on \Circus\ actions and on UTP predicate.

This definition assumes that the actions A1 and A2 share the same alphabet (binding) 
and the same channels. In general, refinement involves an important data evolution and growth. 
The data refinement is defined in \cite{SWC02,CSW03} by backwards and forwards simulations. 
In this paper, we restrict ourselves to a special case, the so-called \emph{functional} 
backwards simulation. This refers to the fact that the abstraction relation 
@{term R} that relates concrete and abstract actions is just a function.
*}

text {* In the following, data (state) simulation and functional backwards simulation
 are defined. The simulation is defined as a function $S$, that corresponds to a state 
 abstraction function.*}

definition "Simul S b = extend (make (ok b) (wait b) (tr b) (ref b)) (S (more b))"

definition 
Simulation::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<sigma>\<^isub>1 \<Rightarrow> '\<sigma>) \<Rightarrow> ('\<theta>, '\<sigma>\<^isub>1) action \<Rightarrow> bool" ("_ \<preceq>_ _") 
where
"A \<preceq>S B \<equiv> \<forall> a b. (relation_of B) (a, b) \<longrightarrow> (relation_of A) (Simul S a, Simul S b)"

text {*
\subsection{Refinement Proofs}

This definition can be used to transform the proof of refinement to a simple 
proof of implication by unfolding the operators using their underlying relational semantics. 
The problem with this approach is the proof size explodes. 
In order to avoid this, general refinement laws have been proposed in \cite{CSW03} to deal 
with the refinement of \Circus\ actions at operators level and not at UTP level. We re-introduced 
and proved a subset of theses laws in our environment (see Table \ref{table:laws}), i.e.
we \emph{derived} them from the definitions of the \Circus\ operators in the denotational
semantics. 

\setlength{\tabcolsep}{9pt}
\begin{table}[h]
\begin{center}{\footnotesize
\begin{tabular}[t]{| c c c |}
\hline
& & \\
\vspace{- 0.7 cm}
& & \\
\infer[\text{Seq-Sim}] {P ; P' \preceq_S Q ; Q'}{P \preceq_S Q & \quad P' \preceq_S Q'} & \multicolumn{2}{c |}{\infer[\text{Guard-Sim}] {g_1 \& P \preceq_S g_2 \& Q}{P \preceq_S Q & \quad g_1 \simeq_S g_2}} \\
& & \\
\vspace{- 0.55 cm}
& & \\
\infer[\text{Var-Sim}] {var~x \bullet P \preceq_S var~ y \bullet Q}{P \preceq_S Q & \quad x \sim_S y} & \multicolumn{2}{c |}{\infer[\text{Read-Sim}] {c?x \rightarrow P \preceq_S c?y \rightarrow Q}{P \preceq_S Q & \quad x \sim_S y}} \\
& & \\
\vspace{- 0.55 cm}
& & \\
\infer[\text{Ndet-Sim}] {P \sqcap P' \preceq_S Q \sqcap Q'}{P \preceq_S Q & \quad P' \preceq_S Q'} & \multicolumn{2}{c |}{\infer[\text{Write-Sim}] {c!x \rightarrow P \preceq_S c!y \rightarrow Q}{P \preceq_S Q & \quad x \sim_S y}} \\
& & \\
\vspace{- 0.55 cm}
& & \\
\infer[\text{Mu-Sim}] {\mu X \bullet P~X \preceq_S \mu Y \bullet Q~Y}{\infer*{P~X \preceq_S Q~Y}{[X \preceq_S Y]} & mono~P & mono~Q} & \multicolumn{2}{c |}{\infer[\text{Det-Sim}] {P \Box P' \preceq_S Q \Box Q'}{P \preceq_S Q & \quad P' \preceq_S Q'}} \\
& & \\
\vspace{- 0.55 cm}
& & \\
\infer[\text{Sch-Sim}] {schema~sc_1 \preceq_S schema~sc_2}{\infer*{Pre~sc_2~A}{[Pre~sc_1~(S~A)]} & \infer*{sc_1~(S~A, S~A')}{[Pre~sc_1~(S~A) & sc_2~(A, A')]}} & \multicolumn{2}{c |}{\infer[\text{Sync-Sim}] {a \rightarrow P \preceq_S a \rightarrow Q}{P \preceq_S Q}} \\
& & \\
\vspace{- 0.55 cm}
& & \\
\multicolumn{2}{| c}{\infer[\text{Par-Sim}] {P \llbracket ns_1 | cs | ns_2 \rrbracket P' \preceq_S Q \llbracket ns'_1 | cs | ns'_2 \rrbracket Q'}{P \preceq_S Q & P' \preceq_S Q' & ns_1 \sim_S ns'_1 & ns_2 \sim_S ns'_2}} &
\infer[\text{Skip-Sim}] {Skip \preceq_S Skip}{} \\
& & \\
\hline
\end{tabular}
  \caption{\label{table:laws} Proved refinement laws}}
\end{center}
\end{table}


In Table \ref{table:laws}, the relations ``$x \sim_S y$'' and ``$g_1 \simeq_S g_2$'' 
record the fact that the variable $x$ (repectively the guard $g_1$) is refined by 
the variable $y$ (repectively by the guard $g_2$) w.r.t the simulation function $S$.

These laws can be used in complex refinement proofs to simplify them at the \Circus\ level. 
More rules can be defined and proved to deal with more complicated statements like combination 
of operators for example. Using these laws, and exploiting the advantages of a shallow embedding, 
the automated proof of refinement becomes surprisingly simple.
The proofs of these laws are given in the following:
*}

lemma Stop_Sim: "Stop \<preceq>S Stop"
by (auto simp: Simulation_def relation_of_Stop rp_defs design_defs Simul_def alpha_rp.defs 
         split: cond_splits)

lemma Skip_Sim: "Skip \<preceq>S Skip"
by (auto simp: Simulation_def relation_of_Skip design_def rp_defs Simul_def alpha_rp.defs 
         split: cond_splits)

lemma Chaos_Sim: "Chaos \<preceq>S Chaos"
by (auto simp: Simulation_def relation_of_Chaos rp_defs design_defs Simul_def alpha_rp.defs 
         split: cond_splits)

lemma Ndet_Sim:
  assumes A: "P  \<preceq>S Q" and B: "P' \<preceq>S Q'"
  shows "(P \<sqinter> P') \<preceq>S (Q \<sqinter> Q')"
by (insert A B, auto simp: Simulation_def relation_of_Ndet)

lemma Det_Sim:
  assumes A: "P  \<preceq>S Q" and B: "P' \<preceq>S Q'"
  shows "(P \<box> P') \<preceq>S (Q \<box> Q')"
by (auto simp: Simulation_def relation_of_Det design_def rp_defs Simul_def alpha_rp.defs spec_def
         split: cond_splits
         dest: A[simplified Simulation_def Simul_def, rule_format]
               B[simplified Simulation_def Simul_def, rule_format])

lemma Sch_Sim:
  assumes A: "\<And> a. (Pre sc1) (S a) \<Longrightarrow> (Pre sc2) a"
  and B: "\<And> a b. \<lbrakk>Pre sc1 (S a) ; sc2 (a, b)\<rbrakk> \<Longrightarrow> sc1 (S a, S b)"
  shows "(Schema sc1) \<preceq>S (Schema sc2)"
by (auto simp: Simulation_def Simul_def relation_of_Schema rp_defs design_defs alpha_rp.defs A B
         split: cond_splits)

lemma Seq_Sim:
  assumes A: "P \<preceq>S Q" and B: "P' \<preceq>S Q'"
  shows "(P `;` P') \<preceq>S (Q `;` Q')"
by (auto simp: Simulation_def relation_of_Seq dest: A[simplified Simulation_def, rule_format]
                                                    B[simplified Simulation_def, rule_format])

lemma Par_Sim:
  assumes A: " P  \<preceq>S Q" and B: " P' \<preceq>S Q'"
  and C: "\<And> a b. S (ns'2 a b) = ns2 (S a) (S b)"
  and D: "\<And> a b. S (ns'1 a b) = ns1 (S a) (S b)"
  shows "(P \<lbrakk> ns1 | cs | ns2 \<rbrakk> P') \<preceq>S (Q \<lbrakk> ns'1 | cs | ns'2 \<rbrakk> Q')"
  apply (auto simp: Simulation_def relation_of_Par fun_eq_iff rp_defs Simul_def design_defs spec_def
                    alpha_rp.defs
              dest: A[simplified Simulation_def Simul_def, rule_format] 
                    B[simplified Simulation_def Simul_def, rule_format])
  apply (split cond_splits)+
  apply (simp, erule disjE, rule disjI1, simp, rule disjI2, simp_all, rule impI)
  apply (auto)
  apply (erule_tac x="tr ba" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S ba\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: A[simplified Simulation_def Simul_def, rule_format])
  apply (erule_tac x="tr bb" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S bb\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: B[simplified Simulation_def Simul_def, rule_format])
  apply (erule_tac x="tr ba" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S ba\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: A[simplified Simulation_def Simul_def, rule_format])
  apply (erule_tac x="tr bb" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S bb\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: B[simplified Simulation_def Simul_def, rule_format])
  apply (rule_tac x="Simul S s1" in exI)
  apply (rule_tac x="Simul S s2" in exI)
  apply (auto simp: Simul_def alpha_rp.defs 
              dest!: B[simplified Simulation_def Simul_def, rule_format]
                     A[simplified Simulation_def Simul_def, rule_format]
              split: cond_splits)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto simp add: M_par_def alpha_rp.defs diff_tr_def fun_eq_iff ParMerge_def Simul_def
            split : cond_splits) 
  apply (rule_tac b="\<lparr>ok = ok bb, wait = wait bb, tr = tr bb, ref = ref bb, 
              \<dots> = S (alpha_rp.more bb)\<rparr>" in comp_intro, auto)
  apply (subst D[where a="(alpha_rp.more s1)" and b="(alpha_rp.more aa)", symmetric], simp)
  apply (subst C[where a="(alpha_rp.more s2)" and b="(alpha_rp.more bb)", symmetric], simp)
  apply (rule_tac b="\<lparr>ok = ok bb, wait = wait bb, tr = tr bb, ref = ref bb, 
              \<dots> = S (alpha_rp.more bb)\<rparr>" in comp_intro, auto)
  apply (subst D[where a="(alpha_rp.more s1)" and b="(alpha_rp.more aa)", symmetric], simp)
  apply (subst C[where a="(alpha_rp.more s2)" and b="(alpha_rp.more bb)", symmetric], simp)
done

lemma Assign_Sim:
  assumes A: "\<And> A. vy A = vx (S A)"
  and B: "\<And> ff A. (S (y_update ff A)) = x_update ff (S A)"
  shows "(x `:=` vx) \<preceq>S (y `:=` vy)"
by (auto simp: Simulation_def relation_of_Assign update_def rp_defs design_defs Simul_def A B
                   alpha_rp.defs split: cond_splits)

lemma Var_Sim:
  assumes A: "P \<preceq>S Q" and B: "\<And> ff A. (S ((snd b) ff A)) = (snd a) ff (S A)"
  shows "(Var a P) \<preceq>S (Var b Q)"
  apply (auto simp: Simulation_def relation_of_Var rp_defs design_defs fun_eq_iff Simul_def B
                    alpha_rp.defs increase_def decrease_def)
  apply (rule_tac b="Simul S ab" in comp_intro)
  apply (split cond_splits)+
  apply (auto simp: B alpha_rp.defs Simul_def elim!: alpha_rp_eqE)
  apply (rule_tac b="Simul S bb" in comp_intro)
  apply (split cond_splits)+
  apply (auto simp: B alpha_rp.defs Simul_def 
              elim!: alpha_rp_eqE dest!: A[simplified Simulation_def Simul_def, rule_format])
  apply (split cond_splits)+
  apply (simp add: alpha_rp.defs)
  apply (erule disjE, rule disjI1, simp, rule disjI2, simp)
  apply (simp_all add: alpha_rp.defs true_def)
  apply (rule impI, (erule conjE | simp)+)
  apply (erule alpha_rp_eqE, simp add: B)
  apply (split cond_splits)+
  apply (simp add: alpha_rp.defs)
  apply (erule disjE, rule disjI1, simp, rule disjI2, simp_all)
  apply (rule impI, (erule conjE | simp)+)
  apply (erule alpha_rp_eqE, simp add: B)
done

lemma Guard_Sim:
  assumes A: "P \<preceq>S Q" and B: "\<And> A. h A = g (S A)"
  shows "(g `&` P) \<preceq>S (h `&` Q)"
apply (auto simp: Simulation_def)
apply (case_tac "h (alpha_rp.more a)")
defer
apply (case_tac "g (S (alpha_rp.more a))")
apply (auto simp: true_Guard1 false_Guard1 Simul_def alpha_rp.defs Simulation_def B
            dest!: A[simplified, rule_format] Stop_Sim[simplified, rule_format])
done

lemma Sync_Sim:
  assumes A: "P \<preceq>S Q"
  shows "a \<rightarrow> P \<preceq>S a \<rightarrow> Q "
  using   A
  apply (auto simp: Simulation_def write0_def relation_of_Prefix0 design_defs rp_defs)
  apply (erule_tac x="ba" in allE)
  apply (erule_tac x="c" in allE, auto)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_def)
done

lemma Read_Sim:
  assumes A: " P \<preceq>S Q" and B: "\<And> A. (d A) = c (S A)"
  shows "a`?`c \<rightarrow> P \<preceq>S a`?`d \<rightarrow> Q"
  using   A
  apply (auto simp: Simulation_def read_def relation_of_Prefix design_defs rp_defs)
  apply (erule_tac x="ba" in allE, erule_tac x="ca" in allE, simp)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_I_def select_def B)
done

lemma Write_Sim:
  assumes A: "P \<preceq>S Q" and B: "\<And> A. (d A) = c (S A)"
  shows "a`!`c \<rightarrow> P \<preceq>S a`!`d \<rightarrow> Q "
  using A
  apply (auto simp: Simulation_def write1_def relation_of_Prefix design_defs rp_defs)
  apply (erule_tac x="ba" in allE, erule_tac x="ca" in allE, simp)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_I_def select_def B)
done

lemma Hide_Sim:
  assumes A: " P \<preceq>S Q"
  shows "(P \\ cs) \<preceq>S (Q \\ cs)"
  apply (auto simp: Simulation_def relation_of_Hide design_defs rp_defs Simul_def alpha_rp.defs)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (split cond_splits)+
  apply (auto simp: Simul_def alpha_rp.defs Simulation_def 
              dest!: A[simplified, rule_format] Skip_Sim[simplified, rule_format])
  apply (rule_tac x=s in exI, auto simp: diff_tr_def)
done

lemma lfp_Siml:
  assumes A: "\<And> X. (X \<preceq>S Q) \<Longrightarrow> ((P X) \<preceq>S Q)" and B: "mono P"
  shows "(lfp P) \<preceq>S Q"
  apply (rule lfp_ordinal_induct, auto simp: B A)
  apply (auto simp add: Simulation_def Sup_action relation_of_bot relation_of_Sup[simplified])
  apply (subst (asm) CSP_is_rd[OF relation_of_CSP])
  apply (auto simp: rp_defs fun_eq_iff Simul_def alpha_rp.defs decrease_def split: cond_splits)
done

lemma Mu_Sim:
  assumes A: "\<And> X Y. X \<preceq>S Y \<Longrightarrow> (P X) \<preceq>S (Q Y)" 
  and B: "mono P" and C: "mono Q"
  shows "(lfp P) \<preceq>S (lfp Q) "
  apply (rule lfp_Siml, drule A)
  apply (subst lfp_unfold, simp_all add: B C)
done

lemma bot_Sim: "bot \<preceq>S bot"
by (auto simp: Simulation_def rp_defs Simul_def relation_of_bot alpha_rp.defs split: cond_splits)

end