theory Broadcast_Thms
  imports Broadcast_Chain Broadcast_Frame Semantics Simulation Bisimulation Sim_Pres
  Sim_Struct_Cong Bisim_Pres Bisim_Struct_Cong Bisim_Subst
begin

context env
begin

  subsection \<open>Syntax\<close>

  subsubsection \<open>Psi calculus agents~-- Definition~2\<close>

  text \<open>
    @{term M}, @{term N} range over message terms. @{term P}, @{term Q} range over processes.
    @{term C} ranges over cases.

    \<^item> Output: @{term "M\<langle>N\<rangle>.P"}
    \<^item> Input: @{term "M\<lparr>\<lambda>*xvec N\<rparr>.P"}
    \<^item> Case: @{term "Case C"}
    \<^item> Par: @{term "(P \<parallel> Q)"}
    \<^item> Res: @{term "\<lparr>\<nu>x\<rparr>(P::('a,'b,'c) psi)"}
    \<^item> Assert: @{term "\<lbrace>\<Psi>\<rbrace>"}
    \<^item> Bang: @{term "!P"}
  \<close>

  text \<open>
    \<^item> Cases: @{term "\<box> \<phi> \<Rightarrow> P C"}
  \<close>

  subsubsection \<open>Parameters~-- Definition~1\<close>

  text \<open>
    \<^item> Channel equivalence: @{term "M \<leftrightarrow> N"}
    \<^item> Composition: @{term "\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q"}
    \<^item> Unit: @{term "\<one>"}
    \<^item> Entailment: @{term "\<Psi> \<turnstile> \<phi>"}
  \<close>

  subsubsection \<open>Extra predicates for broadcast~-- Definition~5\<close>

  text \<open>
    \<^item> Output connectivity: @{term "M \<preceq> N"}
    \<^item> Input connectivity: @{term "M \<succeq> N"}
  \<close>

  subsubsection \<open>Transitions~-- Definition~3\<close>

  text \<open>
    \<^item> @{term "\<Psi> \<rhd> P \<longmapsto>\<alpha> P'"}
  \<close>

  subsubsection \<open>Actions (\texorpdfstring{@{term \<alpha>}}{alpha})~-- Definition~7\<close>

  text \<open>
    \<^item> Input: @{term "M\<lparr>N\<rparr>"}
    \<^item> Output: @{term "M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"}
    \<^item> Broadcast input: @{term "\<questiondown>M\<lparr>N\<rparr>"}
    \<^item> Broadcast output: @{term "\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"}
    \<^item> Silent action: @{term "\<tau>"}
  \<close>

  subsection \<open>Semantics\<close>

  subsubsection \<open>Basic Psi semantics~-- Table~1\<close>

  text \<open>
    \<^item> Theorem {\it Input}:
      @{thm [display] Input[no_vars]}
    \<^item> Theorem {\it Output}:
      @{thm [display] Output[no_vars]}
    \<^item> Theorem {\it Case}:
      @{thm [display] Case[no_vars]}
    \<^item> Theorems {\it Par1} and {\it Par2}:
      @{thm [display] Par1[no_vars]}
      @{thm [display] Par2[no_vars]}
    \<^item> Theorems {\it Comm1} and {\it Comm2}:
      @{thm [display] Comm1[no_vars]}
      @{thm [display] Comm2[no_vars]}
    \<^item> Theorem {\it Open}:
      @{thm [display] Open[no_vars]}
    \<^item> Theorem {\it Scope}:
      @{thm [display] Scope[no_vars]}
    \<^item> Theorem {\it Bang}:
      @{thm [display] Bang[no_vars]}
  \<close>

  subsubsection \<open>Broadcast rules~-- Table~2\<close>

  text \<open>
    \<^item> Theorem {\it BrInput}:
      @{thm [display] BrInput[no_vars]}
    \<^item> Theorem {\it BrOutput}:
      @{thm [display] BrOutput[no_vars]}
    \<^item> Theorem {\it BrMerge}:
      @{thm [display] BrMerge[no_vars]}
    \<^item> Theorems {\it BrComm1} and {\it BrComm2}:
      @{thm [display] BrComm1[no_vars]}
      @{thm [display] BrComm2[no_vars]}
    \<^item> Theorem {\it BrClose}:
      @{thm [display] BrClose[no_vars]}
    \<^item> Theorem {\it BrOpen}:
      @{thm [display] BrOpen[no_vars]}
  \<close>

  subsubsection \<open>Requirements for broadcast~-- Definition~6\<close>

  text \<open>
    \<^item> Theorem {\it chanOutConSupp}:
      @{thm [display] chanOutConSupp[no_vars]}
    \<^item> Theorem {\it chanInConSupp}:
      @{thm [display] chanInConSupp[no_vars]}
  \<close>

  subsubsection \<open>Strong bisimulation~-- Definition~4\<close>

  text \<open>
    \<^item> Theorem {\it bisim.step}:
      @{thm [display] bisim.step[no_vars]}
  \<close>

  subsection \<open>Theorems\<close>

  subsubsection \<open>Congruence properties of strong bisimulation~-- Theorem~8\<close>

  text \<open>
    \<^item> Theorem {\it bisimOutputPres}:
      @{thm [display] bisimOutputPres[no_vars]}
    \<^item> Theorem {\it bisimInputPres}:
      @{thm [display] bisimInputPres[no_vars]}
    \<^item> Theorem {\it bisimCasePres}:
      @{thm [display] bisimCasePres[no_vars]}
    \<^item> Theorems {\it bisimParPres} and {\it bisimParPresSym}:
      @{thm [display] bisimParPres[no_vars]}
      @{thm [display] bisimParPresSym[no_vars]}
    \<^item> Theorem {\it bisimResPres}:
      @{thm [display] bisimResPres[no_vars]}
    \<^item> Theorem {\it bisimBangPres}:
      @{thm [display] bisimBangPres[no_vars]}
  \<close>

  subsubsection \<open>Strong congruence, bisimulation closed under substitution~-- Definition~9\<close>

  text \<open>
    \<^item> Theorem {\it closeSubst\_def}:
      @{thm [display] closeSubst_def[no_vars]}
    \<^item> @{term "\<Psi> \<rhd> P \<sim>\<^sub>s Q"}
  \<close>

  subsubsection \<open>Strong congruence is a process congruence for all \texorpdfstring{@{term \<Psi>}}{Psi}~-- Theorem~10\<close>

  text \<open>
    \<^item> Theorem {\it bisimSubstOutputPres}:
      @{thm [display] bisimSubstOutputPres[no_vars]}
    \<^item> Theorem {\it bisimSubstInputPres}:
      @{thm [display] bisimSubstInputPres[no_vars]}
    \<^item> Theorem {\it bisimSubstCasePres}:
      @{thm [display] bisimSubstCasePres[no_vars]}
    \<^item> Theorem {\it bisimSubstParPres}:
      @{thm [display] bisimSubstParPres[no_vars]}
    \<^item> Theorem {\it bisimSubstResPres}:
      @{thm [display] bisimSubstResPres[no_vars]}
    \<^item> Theorem {\it bisimSubstBangPres}:
      @{thm [display] bisimSubstBangPres[no_vars]}
  \<close>

  subsubsection \<open>Structural equivalence~-- Theorem~11\<close>

  text \<open>
    \<^item> Theorem {\it bisimCasePushRes}:
      @{thm [display] bisimCasePushRes[no_vars]}
    \<^item> Theorem {\it bisimInputPushRes}:
      @{thm [display] bisimInputPushRes[no_vars]}
    \<^item> Theorem {\it bisimOutputPushRes}:
      @{thm [display] bisimOutputPushRes[no_vars]}
    \<^item> Theorem {\it bisimParAssoc}:
      @{thm [display] bisimParAssoc[no_vars]}
    \<^item> Theorem {\it bisimParComm}:
      @{thm [display] bisimParComm[no_vars]}
    \<^item> Theorem {\it bisimResNil}:
      @{thm [display] bisimResNil[no_vars]}
    \<^item> Theorem {\it bisimScopeExt}:
      @{thm [display] bisimScopeExt[no_vars]}
    \<^item> Theorem {\it bisimResComm}:
      @{thm [display] bisimResComm[no_vars]}
    \<^item> Theorem {\it bangExt}:
      @{thm [display] bangExt[no_vars]}
    \<^item> Theorem {\it bisimParNil}:
      @{thm [display] bisimParNil[no_vars]}
  \<close>

  subsubsection \<open>Support of processes in broadcast transitions~-- Lemma~14\<close>

  text \<open>
    \<^item> Theorem {\it brInputTermSupp}:
      @{thm [display] brInputTermSupp[no_vars]}
    \<^item> Theorem {\it brOutputTermSupp}:
      @{thm [display] brOutputTermSupp[no_vars]}
  \<close>

end

end
