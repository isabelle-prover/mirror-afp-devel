(*  Title:       Nondeterministic recursive algorithms
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open> Nondeterministic recursive algorithms \<close>
theory NDET
imports Main
begin

text \<open>
  This theory models nondeterministic, recursive algorithms by means of a step relation.

  An algorithm is modelled as follows: 
  \begin{enumerate}
    \item Start with some state @{text "s"}
    \item If there is no @{text "s'"} with @{text "(s,s')\<in>R"}, terminate with state @{text "s"}
    \item Else set @{text "s := s'"} and continue with step 2
  \end{enumerate}

  Thus, @{text R} is the step relation, relating the previous with the next state. If the state is not in the domain of @{text R}, the algorithm terminates.
\<close>

text \<open> The relation @{text "A_rel R"} describes the non-reflexive part of the algorithm, that is all possible mappings for non-terminating initial states.
  We will first explore properties of this non-reflexive part, and then transfer them to the whole algorithm, that also specifies how
  terminating initial states are treated.
\<close>

inductive_set A_rel :: "('s\<times>'s) set \<Rightarrow> ('s\<times>'s) set" for R
where
  A_rel_base: "\<lbrakk>(s,s')\<in>R; s'\<notin>Domain R\<rbrakk> \<Longrightarrow> (s,s')\<in>A_rel R" |
  A_rel_step: "\<lbrakk>(s,sh)\<in>R; (sh,s')\<in>A_rel R\<rbrakk> \<Longrightarrow> (s,s')\<in>A_rel R"

subsection \<open> Basic properties \<close>

text \<open> The algorithm just terminates at terminating states \<close>
lemma termstate: "(s,s')\<in>A_rel R \<Longrightarrow> s'\<notin>Domain R" by (induct rule: A_rel.induct, auto)

lemma dom_subset: "Domain (A_rel R) \<subseteq> Domain R" by (unfold Domain_def) (auto elim: A_rel.induct) 

text \<open> We can use invariants to reason over properties of the algorithm \<close>
definition "is_inv R s0 P == P s0 \<and> (\<forall>s s'. (s,s')\<in>R \<and> P s \<longrightarrow> P s')"

lemma inv: "\<lbrakk>(s0,sf)\<in>A_rel R; is_inv R s0 P\<rbrakk> \<Longrightarrow> P sf" by (unfold is_inv_def, induct rule: A_rel.induct) blast+
lemma invI: "\<lbrakk>P s0; !! s s'. \<lbrakk>(s,s')\<in>R; P s\<rbrakk> \<Longrightarrow> P s'\<rbrakk> \<Longrightarrow> is_inv R s0 P" by (unfold is_inv_def, blast)
lemma inv2: "\<lbrakk>(s0,sf)\<in>A_rel R; P s0; !! s s'. \<lbrakk>(s,s')\<in>R; P s\<rbrakk> \<Longrightarrow> P s'\<rbrakk> \<Longrightarrow> P sf"
  apply (subgoal_tac "is_inv R s0 P")
  apply (blast intro: inv)
  apply (blast intro: invI)
done

text \<open> To establish new invariants, we can use already existing invariants \<close>
lemma inv_useI: "\<lbrakk>P s0; !! s s'. \<lbrakk>(s,s')\<in>R; P s; !!P'. is_inv R s0 P' \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> P s' \<rbrakk> \<Longrightarrow> is_inv R s0 (\<lambda>s. P s \<and> (\<forall>P'. is_inv R s0 P' \<longrightarrow> P' s))"
  apply (rule invI)
  apply (simp (no_asm) only: is_inv_def, blast)
  apply safe
  apply blast
  apply (subgoal_tac "P' s")
  apply (simp (no_asm_use) only: is_inv_def, blast)
  apply fast
  done  
  
text \<open> If the inverse step relation is well-founded, the algorithm will terminate for every state in @{text "Domain R"} (@{text "\<subseteq>"}-direction). The @{text "\<supseteq>"}-direction is from @{thm [source] dom_subset} \<close>
(* TODO: Prove also the other direction of this lemma \<dots> *)
lemma wf_dom_eq: "wf (R\<inverse>) \<Longrightarrow> Domain R = Domain (A_rel R)" proof -
  assume WF: "wf (R\<inverse>)"
  hence "(\<exists>sf. (s,sf) \<in> A_rel R)" if "(s,s')\<in>R" for s s' using that
  proof (induction arbitrary: s')
    case (less x)

    {
      assume "s'\<notin>Domain R"
      with less.prems have "(x,s')\<in>A_rel R" by (blast intro: A_rel_base)
    } moreover {
      assume "s'\<in>Domain R"
      then obtain st where "(s',st)\<in>R" by (unfold Domain_def, auto)
      with less.prems less.IH obtain sf where "(s',sf)\<in>A_rel R" by blast
      with less.prems have "(x,sf)\<in>A_rel R" by (blast intro: A_rel_step)
      hence "\<exists>sf. (x,sf)\<in>A_rel R" by blast
    } ultimately show "\<exists>sf. (x,sf)\<in>A_rel R" by blast
  qed
  hence "Domain R \<subseteq> Domain (A_rel R)" by (unfold Domain_def, auto)
  with dom_subset show ?thesis by force 
qed
  
subsection \<open> Refinement \<close>
text \<open>
  Refinement is a simulation property between step relations.

  We define refinement w.r.t. an abstraction relation @{text "\<alpha>"}, that relates abstract to concrete states. The refining step-relation is called more concrete than the refined one.
\<close>

definition refines :: "('s*'s) set \<Rightarrow> ('r*'s) set \<Rightarrow> ('r*'r) set \<Rightarrow> bool" ("_\<le>\<^bsub>_\<^esub>_" [50,50,50] 50) where
  "R \<le>\<^bsub>\<alpha>\<^esub> S == \<alpha> O R \<subseteq> S O \<alpha> \<and> \<alpha> `` Domain S \<subseteq> Domain R"

lemma refinesI: "\<lbrakk>\<alpha> O R \<subseteq> S O \<alpha>; \<alpha> `` Domain S \<subseteq> Domain R\<rbrakk> \<Longrightarrow> R\<le>\<^bsub>\<alpha>\<^esub>S" by (unfold refines_def, auto)
lemma refinesE: "R\<le>\<^bsub>\<alpha>\<^esub>S \<Longrightarrow> \<alpha> O R \<subseteq> S O \<alpha>"
  "R\<le>\<^bsub>\<alpha>\<^esub>S \<Longrightarrow> \<alpha> `` Domain S \<subseteq> Domain R" 
  by (unfold refines_def, auto)

text \<open> Intuitively, the first condition for refinement means, that for each concrete step 
  @{text "(c,c')\<in>S"} where the start state @{text c} has an abstract counterpart @{text "(a,c)\<in>\<alpha>"}, 
  there is also an abstract counterpart of the end state @{text "(a',c')\<in>\<alpha>"} and 
  the step can also be done on the abstract counterparts @{text "(a,a')\<in>R"}.
\<close>
lemma refines_compI:
  assumes A: "!! a c c'.  \<lbrakk> (a,c)\<in>\<alpha>; (c,c')\<in>S  \<rbrakk> \<Longrightarrow> \<exists>a'. (a,a')\<in>R \<and> (a',c')\<in>\<alpha>"
  shows "\<alpha> O S \<subseteq> R O \<alpha>" using A by blast

lemma refines_compE: "\<lbrakk>\<alpha> O S \<subseteq> R O \<alpha>; (a,c)\<in>\<alpha>; (c,c')\<in>S\<rbrakk> \<Longrightarrow> \<exists>a'. (a,a')\<in>R \<and> (a',c')\<in>\<alpha>" by (auto)

text \<open> Intuitively, the second condition for refinement means, that if there is an abstract step @{text "(a,a')\<in>R"}, where the start state has a concrete counterpart @{text c},
  then there must also be a concrete step from @{text c}. Note that this concrete step is not required to lead to the concrete counterpart of @{text a'}. In fact, it is only
  important that there is such a concrete step, ensuring that the concrete algorithm will not terminate on states on that the abstract algorithm continues execution.
\<close>
lemma refines_domI: 
  assumes A: "!! a a' c. \<lbrakk>(a,c)\<in>\<alpha>; (a,a')\<in>R \<rbrakk> \<Longrightarrow> c\<in>Domain S"
  shows "\<alpha> `` Domain R \<subseteq> Domain S" using A by auto

lemma refines_domE: "\<lbrakk>\<alpha> `` Domain R \<subseteq> Domain S; (a,c)\<in>\<alpha>; (a,a')\<in>R\<rbrakk> \<Longrightarrow> c\<in>Domain S" by auto

lemma refinesI2: 
  assumes A: "!! a c c'.  \<lbrakk> (a,c)\<in>\<alpha>; (c,c')\<in>S  \<rbrakk> \<Longrightarrow> \<exists>a'. (a,a')\<in>R \<and> (a',c')\<in>\<alpha>"
  assumes B: "!! a a' c. \<lbrakk>(a,c)\<in>\<alpha>; (a,a')\<in>R \<rbrakk> \<Longrightarrow> c\<in>Domain S"
  shows "S\<le>\<^bsub>\<alpha>\<^esub>R" by (simp only: refinesI A refines_compI B refines_domI)

lemma refinesE2: 
  "\<lbrakk>S\<le>\<^bsub>\<alpha>\<^esub>R; (a,c)\<in>\<alpha>; (c,c')\<in>S\<rbrakk> \<Longrightarrow> \<exists>a'. (a,a')\<in>R \<and> (a',c')\<in>\<alpha>" 
  "\<lbrakk>S\<le>\<^bsub>\<alpha>\<^esub>R; (a,c)\<in>\<alpha>; (a,a')\<in>R\<rbrakk> \<Longrightarrow> c\<in>Domain S"
  by (blast dest: refinesE refines_compE refines_domE)+

text \<open> Reflexivity of identity refinement\<close>
lemma refines_id_refl[intro!, simp]: "R\<le>\<^bsub>Id\<^esub>R" by (auto intro: refinesI)

text \<open> Transitivity of refinement \<close>
lemma refines_trans: assumes R: "R \<le>\<^bsub>\<alpha>\<^esub> S"   "S \<le>\<^bsub>\<beta>\<^esub> T" shows "R\<le>\<^bsub>\<beta> O \<alpha>\<^esub>T"
proof (rule refinesI)
  {
    fix s s' t'
    assume A: "(s,s')\<in>\<beta> O \<alpha>" "(s',t')\<in>R"
    then obtain sh where "(s,sh)\<in>\<beta> \<and> (sh,s')\<in>\<alpha>" by (blast)
    with A R obtain t th where "(sh,th)\<in>S \<and> (th,t')\<in>\<alpha> \<and> (s,t)\<in>T \<and> (t,th)\<in>\<beta>" by (blast dest: refinesE)
    hence "(s,t')\<in>T O (\<beta> O \<alpha>)" by blast
  } thus "(\<beta> O \<alpha>) O R \<subseteq> T O (\<beta> O \<alpha>)" by blast
next
  {
    fix s s'
    assume A: "s\<in>Domain T" "(s,s')\<in>\<beta> O \<alpha>"
    then obtain sh where "(s,sh)\<in>\<beta> \<and> (sh,s')\<in>\<alpha>" by blast
    (*with R A have "sh\<in>Domain S" by (blast dest!: refinesE)*)
    with R A have "s'\<in>Domain R" by (blast dest!: refinesE)
  } thus "(\<beta> O \<alpha>) `` Domain T \<subseteq> Domain R" by (unfold Domain_def, blast)
qed

text \<open> Property transfer lemma \<close>
lemma refines_A_rel[rule_format]:
  assumes R: "R\<le>\<^bsub>\<alpha>\<^esub>S" and A: "(r,r')\<in>A_rel R" "(s,r)\<in>\<alpha>"
  shows "(\<exists>s'. (s',r')\<in>\<alpha> \<and> (s,s')\<in>A_rel S)"
  using A
proof (induction arbitrary: s)
  case 1: (A_rel_base r r' s)
  assume C: "(r,r')\<in>R" "r'\<notin>Domain R" "(s,r)\<in>\<alpha>"
  with R obtain s' where "(s,s')\<in>S \<and> (s',r')\<in>\<alpha> \<and> s'\<notin>Domain S" by (blast dest: refinesE)
  hence "(s',r')\<in>\<alpha> \<and> (s,s')\<in>A_rel S" by (blast intro: A_rel_base)
  thus "\<exists>s'. (s',r')\<in>\<alpha> \<and> (s,s')\<in>A_rel S" by (blast)
next
  case C: (A_rel_step r rh r')
  assume A: "(r,rh)\<in>R" "(rh,r')\<in>A_rel R" "(s,r)\<in>\<alpha>"
  with R obtain sh where STEP: "(sh,rh)\<in>\<alpha> \<and> (s,sh)\<in>S" by (blast dest: refinesE)
  with C.IH obtain s' where "(s',r')\<in>\<alpha> \<and> (sh,s')\<in>A_rel S" by blast
  with STEP have "(s', r') \<in> \<alpha> \<and> (s, s') \<in> A_rel S" by (blast intro: A_rel_step)
  thus "\<exists>s'. (s', r') \<in> \<alpha> \<and> (s, s') \<in> A_rel S" by (blast)
qed  
  

text \<open> Property transfer lemma for single-valued abstractions (i.e. abstraction functions) \<close>
lemma refines_A_rel_sv: "\<lbrakk>R\<le>\<^bsub>\<alpha>\<^esub>S; (r,r')\<in>A_rel R; single_valued (\<alpha>\<inverse>); (s,r)\<in>\<alpha>; (s',r')\<in>\<alpha>\<rbrakk> \<Longrightarrow> (s,s')\<in>A_rel S" by (blast dest: single_valuedD refines_A_rel)


subsection \<open> Extension to reflexive states \<close>
text \<open> 
  Up to now we only defined how to relate initial states to terminating states if the algorithm makes at least one step. 
  In this section, we also add the reflexive part: Initial states for that no steps can be made are mapped to themselves.  
\<close>
definition
  "ndet_algo R == (A_rel R) \<union> {(s,s) | s. s\<notin>Domain R}"

lemma ndet_algo_A_rel: "\<lbrakk>x\<in>Domain R; (x,y)\<in>ndet_algo R\<rbrakk> \<Longrightarrow> (x,y)\<in>A_rel R" by (unfold ndet_algo_def) auto

lemma ndet_algoE: "\<lbrakk>(s,s')\<in>ndet_algo R; \<lbrakk>(s,s')\<in>A_rel R\<rbrakk> \<Longrightarrow> P; \<lbrakk> s=s'; s\<notin>Domain R\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by (unfold ndet_algo_def, auto)
lemma ndet_algoE': "\<lbrakk>(s,s')\<in>ndet_algo R; \<lbrakk>(s,s')\<in>A_rel R; s\<in>Domain R; s'\<notin>Domain R\<rbrakk> \<Longrightarrow> P; \<lbrakk> s=s'; s\<notin>Domain R\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using dom_subset[of R] termstate[of s s' R]
  by (auto elim!: ndet_algoE)

text \<open> @{text "ndet_algo"} is total (i.e. the algorithm is defined for every initial state), if @{text "R\<inverse>"} is well founded \<close>
lemma ndet_algo_total: "wf (R\<inverse>) \<Longrightarrow> Domain (ndet_algo R) = UNIV" 
  by (unfold ndet_algo_def) (auto simp add: wf_dom_eq)

text \<open> The result of the algorithm is always a terminating state \<close>
lemma termstate_ndet_algo: "(s,s')\<in>ndet_algo R \<Longrightarrow> s'\<notin>Domain R" by (unfold ndet_algo_def, auto dest: termstate) 
  
text \<open> Property transfer lemma for @{text ndet_algo} \<close>
lemma refines_ndet_algo[rule_format]:
  assumes R: "S\<le>\<^bsub>\<alpha>\<^esub>R" and A: "(c,c')\<in>ndet_algo S"
  shows "\<forall>a. (a,c)\<in>\<alpha> \<longrightarrow> (\<exists>a'. (a',c')\<in>\<alpha> \<and> (a,a')\<in>ndet_algo R)"
proof (intro allI impI)
  fix a assume B: "(a,c)\<in>\<alpha>"
  { assume CASE: "c\<in>Domain S"
    with A have "(c,c')\<in>A_rel S" by (blast elim: ndet_algoE)
    with R B obtain a' where "(a',c')\<in>\<alpha> \<and> (a,a')\<in>A_rel R" by (blast dest: refines_A_rel)
    moreover hence "(a,a')\<in>ndet_algo R" by (unfold ndet_algo_def, simp)
    ultimately have "\<exists>a'. (a', c') \<in> \<alpha> \<and> (a, a') \<in> ndet_algo R" by blast
  } moreover {
    assume CASE: "c\<notin>Domain S"
    with A have "c=c'" by (blast elim: ndet_algoE')
    moreover have "a\<notin>Domain R" proof
      assume "a\<in>Domain R"
      with B R have "c\<in>Domain S" by (auto elim: refinesE2)
      with CASE show "False" ..
    qed
    ultimately have "\<exists>a'. (a', c') \<in> \<alpha> \<and> (a, a') \<in> ndet_algo R" using B by (unfold ndet_algo_def, blast)
  } ultimately show "\<exists>a'. (a', c') \<in> \<alpha> \<and> (a, a') \<in> ndet_algo R" by blast
qed

text \<open> Property transfer lemma for single-valued abstractions (i.e. Abstraction functions) \<close>
lemma refines_ndet_algo_sv: "\<lbrakk>S\<le>\<^bsub>\<alpha>\<^esub>R; (c,c')\<in>ndet_algo S; single_valued (\<alpha>\<inverse>); (a,c)\<in>\<alpha>; (a',c')\<in>\<alpha>\<rbrakk> \<Longrightarrow> (a,a')\<in>ndet_algo R" by (blast dest: single_valuedD refines_ndet_algo)

subsection \<open> Well-foundedness \<close>

lemma wf_imp_minimal: "\<lbrakk>wf S; x\<in>Q\<rbrakk> \<Longrightarrow> \<exists>z\<in>Q. (\<forall>x. (x,z)\<in>S \<longrightarrow> x\<notin>Q)" by (auto iff add: wf_eq_minimal)

text \<open> This lemma allows to show well-foundedness of a refining relation by providing a well-founded refined relation for each element
  in the domain of the refining relation.
\<close>
lemma refines_wf:
  assumes A: "!!r. \<lbrakk> r\<in>Domain R \<rbrakk> \<Longrightarrow> (s r,r)\<in>\<alpha> r \<and> R\<le>\<^bsub>\<alpha> r \<^esub>S r \<and> wf ((S r)\<inverse>)"
  shows "wf (R\<inverse>)"
proof (rule wfI_min)    
  fix Q and e :: 'a
  assume NOTEMPTY: "e\<in>Q"
  moreover {
    assume "e\<notin>Domain R"
    hence "\<forall>y. (e,y)\<in>R \<longrightarrow> y\<notin>Q" by blast
  } moreover {
    assume C: "e\<in>Domain R"
    with A have MAP: "(s e,e)\<in>\<alpha> e" and REF: "R\<le>\<^bsub>\<alpha> e\<^esub> S e" and  WF: "wf ((S e)\<inverse>)" by (auto)
    let ?aQ = "((\<alpha> e)\<inverse>) `` Q"
    from MAP NOTEMPTY have "s e\<in>?aQ" by auto
    with WF wf_imp_minimal[of "(S e)\<inverse>", simplified] have "\<exists>z\<in>?aQ. (\<forall>x. (z,x)\<in>S e \<longrightarrow> x\<notin>?aQ)" by auto
    then obtain z where ZMIN: "z\<in>?aQ \<and> (\<forall>x. (z,x)\<in>S e \<longrightarrow> x\<notin>?aQ)" by blast 
    then obtain q where QP: "(z,q)\<in>\<alpha> e \<and> q\<in>Q" by blast
    have "\<forall>x. (q,x)\<in>R \<longrightarrow> x\<notin>Q" proof (intro allI impI)
      fix x
      assume "(q,x)\<in>R"
      with REF QP obtain xt where ZREF: "(z,xt)\<in>S e \<and> (xt,x)\<in>\<alpha> e" by (blast dest: refinesE)
      with ZMIN have "xt\<notin>?aQ" by simp
      moreover from ZREF have "x\<in>Q \<Longrightarrow> xt\<in>?aQ" by blast
      ultimately show "x\<notin>Q" by blast
    qed
    with QP have "\<exists>q\<in>Q. \<forall>y. (q,y)\<in>R \<longrightarrow> y\<notin>Q" by blast
  } ultimately show "\<exists>z\<in>Q. \<forall>y. (y,z)\<in>R\<inverse> \<longrightarrow> y\<notin>Q" by blast
qed

subsubsection \<open> The relations @{text ">"} and @{text "\<supset>"} on finite domains \<close>
definition "greaterN N == {(i,j) . j<i & i\<le>(N::nat)}"
definition "greaterS S == {(a,b) . b\<subset>a & a\<subseteq>(S::'a set)}"

text \<open> @{text ">"} on initial segment of nat is well founded \<close>
lemma wf_greaterN: "wf (greaterN N)"
  apply (unfold greaterN_def)
  apply (rule wf_subset[of "measure (\<lambda>k. (N-k))"], blast)
  apply (clarify, simp add: measure_def inv_image_def)
done

text \<open> Strict version of @{thm [source] card_mono} \<close>
lemma card_mono_strict: "\<lbrakk>finite B; A\<subset>B\<rbrakk> \<Longrightarrow> card A < card B" proof - 
  assume F: "finite B" and S: "A\<subset>B"
  hence FA: "finite A" by (auto intro: finite_subset)
  from S obtain x where P: "x\<in>B \<and> x\<notin>A \<and> A-{x}=A \<and> insert x A \<subseteq> B" by auto
  with FA have "card (insert x A) = Suc (card A)" by (simp)
  moreover from F P have "card (insert x A) \<le> card B" by (fast intro: card_mono)
  ultimately show ?thesis by simp
qed  

text \<open> @{text "\<supset>"} on finite sets is well founded \<close>
text \<open> This is shown here by embedding the @{text "\<supset>"} relation into the @{text ">"} relation, using cardinality \<close>
lemma wf_greaterS: "finite S \<Longrightarrow> wf (greaterS S)" proof -
  assume FS: "finite S" \<comment> \<open> For this purpose, we show that we can embed greaterS into the greaterN by the inverse image of cardinality \<close>
  have "{(a,b) . b\<subset>a \<and> a \<subseteq> S} \<subseteq> inv_image (greaterN (card S)) card" proof -
    { (* Show the necessary per-element proposition *)
      fix a b
      assume A: "b\<subset>a" "a\<subseteq>S"
      with FS have Fab: "finite a" "finite b" by (auto simp add: finite_subset)
      with A FS have "card b < card a & card a \<le> card S" by (fast intro: card_mono card_mono_strict)
    } note R=this
    thus ?thesis by (auto simp add: inv_image_def greaterN_def)
  qed
  thus ?thesis by (unfold greaterS_def, blast intro: wf_greaterN wf_subset)
qed

text \<open> This lemma shows well-foundedness of saturation algorithms, where in each step some set is increased, and this set remains below some finite upper bound \<close>
lemma sat_wf:
  assumes subset: "!!r r'. (r,r')\<in>R \<Longrightarrow> \<alpha> r \<subset> \<alpha> r' \<and> \<alpha> r' \<subseteq> U"
  assumes finite: "finite U"
  shows "wf (R\<inverse>)"
proof -
  have "R\<inverse> \<subseteq> inv_image (greaterS U) \<alpha>" by (auto simp add: inv_image_def greaterS_def dest: subset)
  moreover have "wf (inv_image (greaterS U) \<alpha>)" using finite by (blast intro: wf_greaterS)
  ultimately show ?thesis by (blast intro: wf_subset)
qed

subsection \<open> Implementation \<close>
text \<open>
  The first step to implement a nondeterministic algorithm specified by a relation @{text "R"} is to provide a deterministic refinement w.r.t. the identity abstraction @{text "Id"}. 
  We can describe such a deterministic refinement as the graph of a partial function @{text "sel"}. We call this function a selector function, 
  because it selects the next state from the possible states specified by @{text "R"}.

  In order to get a working implementation, we must prove termination. That is, we have to show that @{text "(graph sel)\<inverse>"} is well-founded. 
  If we already know that @{text "R\<inverse>"} is well-founded, this property transfers to @{text "(graph sel)\<inverse>"}.

  Once obtained well-foundedness, we can use the selector function to implement the following recursive function:

    @{text "algo s = case sel s of None \<Rightarrow> s | Some s' \<Rightarrow> algo s'"}

  And we can show, that @{text "algo"} is consistent with @{text "ndet_algo R"}, that is @{text "(s,algo s)\<in>ndet_algo R"}.
\<close>

subsubsection "Graphs of functions"
text \<open> The graph of a (partial) function is the relation of arguments and function values \<close>
definition "graph f == {(x,x') . f x = Some x'}"

lemma graphI[intro]: "f x = Some x' \<Longrightarrow> (x,x')\<in>graph f" by (unfold graph_def, auto)
lemma graphD[dest]: "(x,x')\<in>graph f \<Longrightarrow> f x = Some x'" by (unfold graph_def, auto)
lemma graph_dom_iff1: "(x\<notin>Domain (graph f)) = (f x = None)" by (cases "f x") auto
lemma graph_dom_iff2: "(x\<in>Domain (graph f)) = (f x \<noteq> None)" by (cases "f x") auto

subsubsection "Deterministic refinement w.r.t. the identity abstraction"
lemma detRef_eq: "(graph sel \<le>\<^bsub>Id\<^esub> R) = ((\<forall>s s'. sel s = Some s' \<longrightarrow> (s,s')\<in>R) \<and> (\<forall>s. sel s = None \<longrightarrow> s\<notin>Domain R))"
  by (unfold refines_def) (auto iff add: graph_dom_iff2)

lemma detRef_wf_transfer: "\<lbrakk>wf (R\<inverse>); graph sel \<le>\<^bsub>Id\<^esub> R \<rbrakk> \<Longrightarrow> wf ((graph sel)\<inverse>)"
  by (rule refines_wf[where s=id and \<alpha>="\<lambda>x. Id" and S="\<lambda>x. R"]) simp

subsubsection "Recursive characterization"

locale detRef_impl =
  fixes algo and sel and R
  assumes detRef: "graph sel \<le>\<^bsub>Id\<^esub> R" 
  assumes algo_rec[simp]: "!! s s'. sel s = Some s' \<Longrightarrow> algo s = algo s'" and algo_term[simp]: "!! s. sel s = None \<Longrightarrow> algo s = s"
  assumes wf: "wf ((graph sel)\<inverse>)"

lemma (in detRef_impl) sel_cons: 
  "sel s = Some s' \<Longrightarrow> (s,s')\<in>R"
  "sel s = None \<Longrightarrow> s\<notin>Domain R"
  "s\<in>Domain R \<Longrightarrow> \<exists>s'. sel s = Some s'"
  "s\<notin>Domain R \<Longrightarrow> sel s = None"
  using detRef 
  by (simp_all only: detRef_eq) (cases "sel s", blast, blast)+

lemma (in detRef_impl) algo_correct: "(s,algo s)\<in>ndet_algo R" proof -
  {
    assume C: "s\<in>Domain R"
    have "!!s. s\<in>Domain R \<longrightarrow> (s,algo s)\<in>A_rel R" 
    proof (rule wf_induct[OF wf, of "\<lambda>s. s\<in>Domain R \<longrightarrow> (s,algo s)\<in>A_rel R"]; intro impI)
      fix s
      assume A: "s \<in> Domain R" and IH: "\<forall>y. (y, s) \<in> (graph sel)\<inverse> \<longrightarrow> y \<in> Domain R \<longrightarrow> (y, algo y) \<in> A_rel R"
      then obtain sh where SH: "sel s = Some sh \<and> (s,sh)\<in>R" using sel_cons by blast
      hence AS: "algo s = algo sh" by auto
      {
        assume C: "sh\<notin>Domain R"
        hence "sel sh=None" by (auto dest: sel_cons)
        hence "algo sh=sh" by (auto)
        moreover from SH C have "(s,sh)\<in>A_rel R" by (blast intro: A_rel_base) 
        ultimately have "(s,algo s)\<in>A_rel R" using AS by simp
      } moreover {
        assume C: "sh\<in>Domain R"
        with SH IH AS A have "(sh,algo s)\<in>A_rel R" by auto
        with SH have "(s,algo s)\<in>A_rel R" by (blast intro: A_rel_step)
      } ultimately show "(s,algo s)\<in>A_rel R" by blast
    qed
    with C have "(s,algo s)\<in>A_rel R" by simp
    hence ?thesis by (unfold ndet_algo_def, auto)
  } moreover {
    assume C: "s\<notin>Domain R"
    hence "s=algo s" by (auto dest: sel_cons)
    with C have ?thesis by (unfold ndet_algo_def, auto)
  } ultimately show ?thesis by blast
qed
   

end
