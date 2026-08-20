(*  Title:       Non-executable implementation of the DPN pre^* - algorithm
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open> Non-executable implementation of the DPN pre$^*$-algorithm \<close>

theory DPN_impl
imports DPN
begin

text \<open>
  This theory is to explore how to prove the correctness of straightforward implementations of the DPN pre$^*$ algorithm.
  It does not provide an executable specification, but uses set-datatype and the SOME-operator to describe a deterministic refinement
  of the nondeterministic pre$^*$-algorithm. This refinement is then characterized as a recursive function, using recdef.

  This proof uses the same techniques to get the recursive function and prove its correctness as are used for the straightforward executable implementation in DPN\_implEx.
  Differences from the executable specification are: 
  \begin{itemize}
    \item The state of the algorithm contains the transition relation that is saturated, thus making the refinement abstraction just a projection onto this component. The executable specification, however, uses
    list representation of sets, thus making the refinement abstraction more complex.

    \item The termination proof is easier: In this approach, we only do recursion if our state contains a valid M-automata and a consistent transition relation. Using this property,
    we can infer termination easily from the termination of @{text "ps_R"}. The executable implementation does not check wether the state is valid, and thus may also do recursion for
    invalid states. Thus, the termination argument must also regard those invalid states, and hence must be more general.
  \end{itemize}
\<close>


subsection \<open> Definitions \<close>
type_synonym ('c,'l,'s,'m1,'m2) pss_state = "((('c,'l,'m1) DPN_rec_scheme * ('s,'c,'m2) MFSM_rec_scheme) * ('s,'c) LTS)"

text \<open> Function to select next transition to be added\<close>
definition pss_isNext :: "('c,'l,'m1) DPN_rec_scheme \<Rightarrow> ('s,'c,'m2) MFSM_rec_scheme \<Rightarrow> ('s,'c) LTS \<Rightarrow> ('s*'c*'s) \<Rightarrow> bool" where
  "pss_isNext M A D t ==  t\<notin>D \<and> (\<exists>q p \<gamma> q' a c'. t=(sp A q p,\<gamma>,q') \<and> [p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<and> (q,c',q')\<in>trclAD A D)"
definition  "pss_next M A D == if (\<exists> t. pss_isNext M A D t) then Some (SOME t. pss_isNext M A D t) else None"

text \<open> Next state selector function\<close>
definition
  "pss_next_state S == case S of ((M,A),D) \<Rightarrow> if MFSM M A \<and> D\<subseteq>ps_upper M A then (case pss_next M A D of None \<Rightarrow> None | Some t \<Rightarrow> Some ((M,A),insert t D) ) else None"

text \<open> Relation describing the deterministic algorithm \<close>
definition
  "pss_R == graph pss_next_state"

lemma pss_nextE1: "pss_next M A D = Some t \<Longrightarrow> t\<notin>D \<and> (\<exists> q p \<gamma> q' a c'. t=(sp A q p,\<gamma>,q') \<and> [p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<and> (q,c',q')\<in>trclAD A D)" 
proof -
  assume "pss_next M A D = Some t"
  hence "pss_isNext M A D t" 
    apply (unfold pss_next_def)
    apply (cases "\<exists>t. pss_isNext M A D t")
    by (auto intro: someI)
  thus ?thesis by (unfold pss_isNext_def)
qed

lemma pss_nextE2: "pss_next M A D = None \<Longrightarrow> \<not>(\<exists> q p \<gamma> q' a c' t. t\<notin>D \<and> t=(sp A q p,\<gamma>,q') \<and> [p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<and> (q,c',q')\<in>trclAD A D)"
proof -
  assume "pss_next M A D = None"
  hence "\<not>(\<exists>t. pss_isNext M A D t)"
    apply (unfold pss_next_def)
    apply (cases "\<exists>t. pss_isNext M A D t")
    by auto
  thus ?thesis by (unfold pss_isNext_def) blast
qed

lemmas (in MFSM) pss_nextE = pss_nextE1 pss_nextE2

text \<open> The relation of the deterministic algorithm is also the recursion relation of the recursive characterization of the algorithm \<close>
lemma pss_R_alt[termination_simp]: "pss_R == {(((M,A),D),((M,A),insert t D)) | M A D t. MFSM M A \<and> D\<subseteq>ps_upper M A \<and> pss_next M A D = Some t}"
  by (rule eq_reflection, unfold pss_R_def graph_def pss_next_state_def) (auto split: option.split_asm if_splits)

subsection \<open> Refining @{term "ps_R"} \<close>
text \<open> We first show that the next-step relation refines @{text "ps_R M A"}. From this, we will get both termination and correctness \<close>

text \<open> Abstraction relation to project on the second component of a tuple, with fixed first component \<close>
definition "\<alpha>snd f == { (s,(f,s)) | s. True }"
lemma \<alpha>snd_comp_simp: "R O \<alpha>snd f = {(s,(f,s'))| s s'. (s,s')\<in>R}" by (unfold \<alpha>snd_def, blast)

lemma \<alpha>sndI[simp]: "(s,(f,s))\<in>\<alpha>snd f" by (unfold \<alpha>snd_def, auto)
lemma \<alpha>sndE: "(s,(f,s'))\<in>\<alpha>snd f' \<Longrightarrow> f=f' \<and> s=s'" by (unfold \<alpha>snd_def, auto)

text \<open> Relation of @{text "pss_next"} and @{text "ps_R M A"} \<close>
lemma (in MFSM) pss_cons1: "\<lbrakk>pss_next M A D = Some t; D\<subseteq>ps_upper M A\<rbrakk> \<Longrightarrow> (D,insert t D)\<in>ps_R M A" by (auto dest: pss_nextE intro: ps_R.intros)
lemma (in MFSM) pss_cons2: "pss_next M A D = None \<Longrightarrow> D\<notin>Domain (ps_R M A)" by (blast dest: pss_nextE elim: ps_R.cases)

lemma (in MFSM) pss_cons1_rev: "\<lbrakk>D\<subseteq>ps_upper M A; D\<notin>Domain (ps_R M A)\<rbrakk> \<Longrightarrow> pss_next M A D = None" by (cases "pss_next M A D") (auto iff add: pss_cons1 pss_cons2)
lemma (in MFSM) pss_cons2_rev: "\<lbrakk>D\<in>Domain (ps_R M A)\<rbrakk> \<Longrightarrow> \<exists>t. pss_next M A D = Some t \<and> (D,insert t D)\<in>ps_R M A" 
  by (cases "pss_next M A D") (auto iff add: pss_cons1 pss_cons2 ps_R_dom_below)

text \<open> The refinement result \<close>
theorem (in MFSM) pss_refines: "pss_R \<le>\<^bsub>\<alpha>snd (M,A)\<^esub> (ps_R M A)" proof (rule refinesI)
  show "\<alpha>snd (M, A) O pss_R \<subseteq> ps_R M A O \<alpha>snd (M, A)" by (rule refines_compI, unfold \<alpha>snd_def pss_R_alt) (blast intro: pss_cons1)
next
  show "\<alpha>snd (M, A) `` Domain (ps_R M A) \<subseteq> Domain pss_R"
    apply (rule refines_domI)
    unfolding \<alpha>snd_def pss_R_alt Domain_iff
    apply (clarsimp, safe)
    subgoal by unfold_locales
    subgoal by (blast dest: ps_R_dom_below)
    subgoal by (insert pss_cons2_rev, fast)
    done
qed

subsection \<open> Termination \<close>
text \<open> We can infer termination directly from the well-foundedness of @{term ps_R} and @{thm [source] MFSM.pss_refines} \<close>

theorem pss_R_wf: "wf (pss_R\<inverse>)" 
proof -
  {
    fix M A D M' A' D'
    assume A: "(((M,A),D),((M',A'),D'))\<in>pss_R"
    then interpret MFSM "sep M" M A 
      apply (unfold pss_R_alt MFSM_def) 
      apply blast
      apply simp
      done
    from pss_refines ps_R_wf have "pss_R\<le>\<^bsub>\<alpha>snd (M, A)\<^esub>ps_R M A \<and> wf ((ps_R M A)\<inverse>)" by simp
  } note A=this
  show ?thesis
    apply (rule refines_wf[ of pss_R snd "\<lambda>r. \<alpha>snd (fst r)" "\<lambda>r. let (M,A)=fst r in ps_R M A"])
    using A 
    by fastforce
    
qed

subsection "Recursive characterization"
text \<open> Having proved termination, we can characterize our algorithm as a recursive function \<close>

function pss_algo_rec :: "(('c,'l,'s,'m1,'m2) pss_state) \<Rightarrow> (('c,'l,'s,'m1,'m2) pss_state)" where
  "pss_algo_rec ((M,A),D) = (if (MFSM M A \<and> D\<subseteq>ps_upper M A) then (case (pss_next M A D) of None \<Rightarrow> ((M,A),D) | (Some t) \<Rightarrow> pss_algo_rec ((M,A),insert t D)) else ((M,A),D))"
  by pat_completeness auto

termination  
  apply (relation "pss_R\<inverse>")
  apply (simp add: pss_R_wf)
  using pss_R_alt by fastforce

lemma pss_algo_rec_newsimps[simp]: 
  "\<lbrakk>MFSM M A; D\<subseteq>ps_upper M A; pss_next M A D = None\<rbrakk> \<Longrightarrow> pss_algo_rec ((M,A),D) = ((M,A),D)"
  "\<lbrakk>MFSM M A; D\<subseteq>ps_upper M A; pss_next M A D = Some t\<rbrakk> \<Longrightarrow> pss_algo_rec ((M,A),D) = pss_algo_rec ((M,A),insert t D)"
  "\<not>MFSM M A \<Longrightarrow> pss_algo_rec ((M,A),D) = ((M,A),D)"
  "\<not>(D \<subseteq> ps_upper M A) \<Longrightarrow> pss_algo_rec ((M,A),D) = ((M,A),D)"
by auto

declare pss_algo_rec.simps[simp del]

subsection \<open> Correctness \<close>
text \<open> The correctness of the recursive version of our algorithm can be inferred using the results from the locale @{text detRef_impl} \<close>

interpretation det_impl: detRef_impl pss_algo_rec pss_next_state pss_R
  apply (rule detRef_impl.intro)
  apply (simp_all add: detRef_wf_transfer[OF pss_R_wf] pss_R_def)
  subgoal for s s'
    unfolding pss_next_state_def
    by (auto split: if_splits prod.splits option.splits)
  subgoal for s    
    apply (unfold pss_next_state_def)
    apply (clarsimp split: prod.splits if_splits option.splits) 
    using pss_algo_rec_newsimps(3,4) by blast
  done

theorem (in MFSM) pss_correct: "lang (A\<lparr> \<delta>:=snd (pss_algo_rec ((M,A),(\<delta> A))) \<rparr>) = pre_star (rules M) A" 
proof -
  have "(((M,A),\<delta> A), pss_algo_rec ((M,A),\<delta> A))\<in>ndet_algo pss_R" by (rule det_impl.algo_correct)
  moreover have "(\<delta> A, ((M,A),\<delta> A))\<in>\<alpha>snd (M,A)" by simp
  ultimately obtain D' where 1: "(D', pss_algo_rec ((M,A),\<delta> A)) \<in> \<alpha>snd (M,A)" and "(\<delta> A,D')\<in>ndet_algo (ps_R M A)" using pss_refines by (blast dest: refines_ndet_algo)
  with correct have "lang (A\<lparr>\<delta> := D'\<rparr>) = pre\<^sup>* (rules M) A" by auto
  moreover from 1 have "snd (pss_algo_rec ((M,A),\<delta> A)) = D'" by (unfold \<alpha>snd_def, auto)
  ultimately show ?thesis by auto
qed

end
