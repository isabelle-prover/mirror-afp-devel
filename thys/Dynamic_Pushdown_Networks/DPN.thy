(*  Title:       Dynamic pushdown networks
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open> Dynamic pushdown networks \<close>
theory DPN
imports DPN_Setup SRS FSM NDET
begin

text \<open>
  Dynamic pushdown networks (DPNs) are a model for parallel, context free processes where processes can create new processes.

  They have been introduced in \cite{BMT05}. In this theory we formalize DPNs and the automata based algorithm for calculating a representation of the (regular) set of backward reachable configurations, starting at
  a regular set of configurations. 

  We describe the algorithm nondeterministically, and prove its termination and correctness.
\<close>

subsection \<open> Dynamic pushdown networks \<close>

subsubsection \<open> Definition \<close>
record ('c,'l) DPN_rec =
  csyms :: "'c set"
  ssyms :: "'c set"
  sep :: "'c"
  labels :: "'l set"
  rules :: "('c,'l) SRS"

text \<open>
  A dynamic pushdown network consists of a finite set of control symbols, a finite set of stack symbols, a separator symbol\footnote{In the final version of \cite{BMT05}, 
  no separator symbols are used. We use them here because we think it simplifies formalization of the proofs.}, a finite set of labels and a finite set of labelled string rewrite rules.

  The set of control and stack symbols are disjoint, and both do not contain the separator. A string rewrite rule is either of the form @{text "[p,\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p1#w1"} or @{text "[p,\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p1#w1@\<sharp>#p2#w2"} where
  @{text "p,p1,p2"} are control symbols, @{text "w1,w2"} are sequences of stack symbols, @{text a} is a label and @{text "\<sharp>"} is the separator.
\<close>

locale DPN = 
  fixes M
  fixes separator ("\<sharp>")
  defines sep_def: "\<sharp> == sep M"
  assumes sym_finite: "finite (csyms M)" "finite (ssyms M)"
  assumes sym_disjoint: "csyms M \<inter> ssyms M = {}" "\<sharp> \<notin> csyms M \<union> ssyms M"
  assumes lab_finite: "finite (labels M)"
  assumes rules_finite: "finite (rules M)"
  assumes rule_fmt: "r \<in> rules M \<Longrightarrow> 
     (\<exists>p \<gamma> a p' w. p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> p'\<in>csyms M \<and> w\<in>lists (ssyms M) \<and> a\<in>labels M \<and> r=p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p'#w) 
  \<or>  (\<exists>p \<gamma> a p1 w1 p2 w2.  p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> p1\<in>csyms M \<and> w1\<in>lists (ssyms M) \<and> p2\<in>csyms M \<and> w2\<in>lists (ssyms M) \<and> a\<in>labels M \<and> r=p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p1#w1@\<sharp>#p2#w2)"

lemma (in DPN) sep_fold: "sep M == \<sharp>" by (simp add: sep_def)

lemma (in DPN) sym_disjoint': "sep M \<notin> csyms M \<union> ssyms M" using sym_disjoint by (simp add: sep_def) 

subsubsection \<open> Basic properties \<close>
lemma (in DPN) syms_part: "x\<in>csyms M \<Longrightarrow> x\<notin>ssyms M" "x\<in>ssyms M \<Longrightarrow> x\<notin>csyms M" using sym_disjoint by auto
lemma (in DPN) syms_sep: "\<sharp>\<notin>csyms M" "\<sharp>\<notin>ssyms M" using sym_disjoint by auto
lemma (in DPN) syms_sep': "sep M\<notin>csyms M" "sep M\<notin>ssyms M" using syms_sep by (auto simp add: sep_def)

lemma (in DPN) rule_cases[consumes 1, case_names no_spawn spawn]: 
  assumes A: "r\<in>rules M"
  assumes NOSPAWN: "!! p \<gamma> a p' w. \<lbrakk>p\<in>csyms M; \<gamma>\<in>ssyms M; p'\<in>csyms M; w\<in>lists (ssyms M); a\<in>labels M; r=p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p'#w\<rbrakk> \<Longrightarrow> P"
  assumes SPAWN: "!! p \<gamma> a p1 w1 p2 w2. \<lbrakk>p\<in>csyms M; \<gamma>\<in>ssyms M; p1\<in>csyms M; w1\<in>lists (ssyms M); p2\<in>csyms M; w2\<in>lists (ssyms M); a\<in>labels M; r=p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p1#w1@\<sharp>#p2#w2\<rbrakk> \<Longrightarrow> P"
  shows P
  using A NOSPAWN SPAWN
  by (blast dest!: rule_fmt)

lemma (in DPN) rule_cases': 
  "\<lbrakk>r\<in>rules M; 
    !! p \<gamma> a p' w. \<lbrakk>p\<in>csyms M; \<gamma>\<in>ssyms M; p'\<in>csyms M; w\<in>lists (ssyms M); a\<in>labels M; r=p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p'#w\<rbrakk> \<Longrightarrow> P; 
    !! p \<gamma> a p1 w1 p2 w2. \<lbrakk>p\<in>csyms M; \<gamma>\<in>ssyms M; p1\<in>csyms M; w1\<in>lists (ssyms M); p2\<in>csyms M; w2\<in>lists (ssyms M); a\<in>labels M; r=p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p1#w1@(sep M)#p2#w2\<rbrakk> \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P" by (unfold sep_fold) (blast elim!: rule_cases)

lemma (in DPN) rule_prem_fmt: "r\<in>rules M \<Longrightarrow> \<exists> p \<gamma> a c'. p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> a\<in>labels M \<and> set c' \<subseteq> csyms M \<union> ssyms M \<union> {\<sharp>} \<and> r=(p#[\<gamma>] \<hookrightarrow>\<^bsub>a \<^esub> c')" 
  apply (erule rule_cases)
  by (auto)

lemma (in DPN) rule_prem_fmt': "r\<in>rules M \<Longrightarrow> \<exists> p \<gamma> a c'. p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> a\<in>labels M \<and> set c' \<subseteq> csyms M \<union> ssyms M \<union> {sep M} \<and> r=(p#[\<gamma>] \<hookrightarrow>\<^bsub>a \<^esub> c')" by (unfold sep_fold, rule rule_prem_fmt) 
  
lemma (in DPN) rule_prem_fmt2: "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<Longrightarrow> p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> a\<in>labels M \<and> set c' \<subseteq> csyms M \<union> ssyms M \<union> {\<sharp>}" by (fast dest: rule_prem_fmt)
lemma (in DPN) rule_prem_fmt2': "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<Longrightarrow> p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> a\<in>labels M \<and> set c' \<subseteq> csyms M \<union> ssyms M \<union> {sep M}" by (unfold sep_fold, rule rule_prem_fmt2)

lemma (in DPN) rule_fmt_fs: "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> p'#c' \<in> rules M \<Longrightarrow> p\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> a\<in>labels M \<and> p'\<in>csyms M \<and> set c' \<subseteq> csyms M \<union> ssyms M \<union> {\<sharp>}"
  apply (erule rule_cases)
  by (auto)

  
subsubsection \<open>Building DPNs\<close>

text \<open>Sanity check: we can create valid DPNs by adding rules to an empty DPN\<close>

definition "dpn_empty C S s \<equiv> \<lparr>
  csyms = C,
  ssyms = S,
  sep = s,
  labels = {},
  rules = {}
\<rparr>"

definition "dpn_add_local_rule p \<gamma> a p\<^sub>1 w\<^sub>1 D \<equiv> D\<lparr> labels := insert a (labels D), rules := insert ([p,\<gamma>],a,p\<^sub>1#w\<^sub>1) (rules D) \<rparr>"
definition "dpn_add_spawn_rule p \<gamma> a p\<^sub>1 w\<^sub>1 p\<^sub>2 w\<^sub>2 D \<equiv> D\<lparr> labels := insert a (labels D), rules := insert ([p,\<gamma>],a,p\<^sub>1#w\<^sub>1@sep D#p\<^sub>2#w\<^sub>2) (rules D) \<rparr>"

lemma dpn_empty_invar[simp]: "\<lbrakk>finite C; finite S; C\<inter>S={}; s\<notin>C\<union>S\<rbrakk> \<Longrightarrow> DPN (dpn_empty C S s)"
  apply unfold_locales unfolding dpn_empty_def by auto

lemma dpn_add_local_rule_invar[simp]: 
  assumes A: "{p,p\<^sub>1} \<subseteq> csyms D" "insert \<gamma> (set w\<^sub>1) \<subseteq> ssyms D" and "DPN D"   
  shows "DPN (dpn_add_local_rule p \<gamma> a p\<^sub>1 w\<^sub>1 D)"
proof -
  interpret DPN D "sep D" by fact  
  show ?thesis
    unfolding dpn_add_local_rule_def
    apply unfold_locales
    using sym_finite sym_disjoint lab_finite rules_finite
    apply simp_all
    apply (erule disjE)
    subgoal for r using A by auto
    subgoal for r using rule_fmt[of r] by metis
    done
qed  
  

lemma dpn_add_spawn_rule_invar[simp]: 
  assumes A: "{p,p\<^sub>1,p\<^sub>2} \<subseteq> csyms D" "insert \<gamma> (set w\<^sub>1 \<union> set w\<^sub>2) \<subseteq> ssyms D" and "DPN D"   
  shows "DPN (dpn_add_spawn_rule p \<gamma> a p\<^sub>1 w\<^sub>1 p\<^sub>2 w\<^sub>2 D)"
proof -
  interpret DPN D "sep D" by fact  
  show ?thesis
    unfolding dpn_add_spawn_rule_def
    apply unfold_locales
    using sym_finite sym_disjoint lab_finite rules_finite
    apply (simp_all)
    apply (erule disjE)
    subgoal for r apply (rule disjI2) using A apply clarsimp by (metis in_listsI subset_eq)
    subgoal for r using rule_fmt[of r]  by metis
    done
qed  


subsection \<open> M-automata \<close>
text \<open>
  We are interested in calculating the predecessor sets of regular sets of configurations. For this purpose, the regular sets of configurations are represented as finite state machines, that
  conform to certain constraints, depending on the underlying DPN. These FSMs are called M-automata.
\<close>


subsubsection \<open> Definition \<close>
record ('s,'c) MFSM_rec = "('s,'c) FSM_rec" +
  sstates :: "'s set"
  cstates :: "'s set"
  sp :: "'s \<Rightarrow> 'c \<Rightarrow> 's"


text \<open>
  M-automata are FSMs whose states are partioned into control and stack states. For each control state $s$ and control symbol $p$, there is a unique and distinguished stack state @{text "sp A s p"}, and a transition
  @{text "(s,p,sp A s p)\<in>\<delta>"}. The initial state is a control state, and the final states are all stack states.
  Moreover, the transitions are restricted: The only incoming transitions of control states are separator transitions from stack states. 
  The only outgoing transitions are the @{text "(s,p,sp A s p)\<in>\<delta>"} transitions mentioned above. The @{text "sp A s p"}-states have no other incoming transitions.
\<close>
locale MFSM = DPN M + FSM A 
  for M A +
  
  assumes alpha_cons: "\<Sigma> A = csyms M \<union> ssyms M \<union> {\<sharp>}"
  assumes states_part: "sstates A \<inter> cstates A = {}" "Q A = sstates A \<union> cstates A"
  assumes uniqueSp: "\<lbrakk>s\<in>cstates A; p\<in>csyms M\<rbrakk> \<Longrightarrow> sp A s p \<in> sstates A" "\<lbrakk>p\<in>csyms M; p'\<in>csyms M; s\<in>cstates A; s'\<in>cstates A; sp A s p = sp A s' p'\<rbrakk> \<Longrightarrow> s=s' \<and> p=p'"
  assumes delta_fmt: "\<delta> A \<subseteq> (sstates A \<times> ssyms M \<times> (sstates A - {sp A s p | s p . s\<in>cstates A \<and> p\<in>csyms M})) \<union> (sstates A \<times> {\<sharp>} \<times> cstates A) \<union> {(s,p,sp A s p) | s p . s\<in>cstates A \<and> p\<in>csyms M}"
                     "\<delta> A \<supseteq> {(s,p,sp A s p) | s p . s\<in>cstates A \<and> p\<in>csyms M}"
  assumes s0_fmt: "s0 A \<in> cstates A"
  assumes F_fmt: "F A\<subseteq>sstates A" \<comment> \<open> This deviates slightly from \cite{BMT05}, as we cannot represent the empty configuration here. However, this restriction is harmless, since the only predecessor
    of the empty configuration is the empty configuration itself. \<close>
  constrains M::"('c,'l,'e1) DPN_rec_scheme" 
  constrains A::"('s,'c,'e2) MFSM_rec_scheme"

(* TODO: Some sanity-check that M-automata exist. Ideally, that they exist for every regular language over valid configurations *)
  

lemma (in MFSM) alpha_cons': "\<Sigma> A = csyms M \<union> ssyms M \<union> {sep M}" by (unfold sep_fold, rule alpha_cons)
lemma (in MFSM) delta_fmt': "\<delta> A \<subseteq> (sstates A \<times> ssyms M \<times> (sstates A - {sp A s p | s p . s\<in>cstates A \<and> p\<in>csyms M})) \<union> (sstates A \<times> {sep M} \<times> cstates A) \<union> {(s,p,sp A s p) | s p . s\<in>cstates A \<and> p\<in>csyms M}"
                     "\<delta> A \<supseteq> {(s,p,sp A s p) | s p . s\<in>cstates A \<and> p\<in>csyms M}" by (unfold sep_fold, (rule delta_fmt)+)


subsubsection \<open> Basic properties \<close>
lemma (in MFSM) finite_cs_states: "finite (sstates A)" "finite (cstates A)"
proof -
  have "sstates A \<subseteq> Q A \<and> cstates A \<subseteq> Q A" by (auto simp add: states_part)
  then show "finite (sstates A)" "finite (cstates A)" by (auto dest: finite_subset intro: finite_states)
qed

lemma (in MFSM) sep_out_syms: "x\<in>csyms M \<Longrightarrow> x \<noteq> \<sharp>" "x\<in>ssyms M \<Longrightarrow> x \<noteq> \<sharp>" by (auto iff add: syms_sep)
lemma (in MFSM) sepI: "\<lbrakk>x\<in>\<Sigma> A;x\<notin>csyms M; x\<notin>ssyms M\<rbrakk> \<Longrightarrow> x=\<sharp>" using alpha_cons by auto
lemma (in MFSM) sep_out_syms': "x\<in>csyms M \<Longrightarrow> x \<noteq> sep M" "x\<in>ssyms M \<Longrightarrow> x \<noteq> sep M" by (unfold sep_fold, (fast dest: sep_out_syms) +)
lemma (in MFSM) sepI': "\<lbrakk>x\<in>\<Sigma> A;x\<notin>csyms M; x\<notin>ssyms M\<rbrakk> \<Longrightarrow> x=sep M" using alpha_cons' by auto

lemma (in MFSM) states_partI1: "x\<in>sstates A \<Longrightarrow> \<not>x\<in>cstates A" using states_part by (auto)
lemma (in MFSM) states_partI2: "x\<in>cstates A \<Longrightarrow> \<not>x\<in>sstates A" using states_part by (auto)
lemma (in MFSM) states_part_elim[elim]: "\<lbrakk>q\<in>Q A; q\<in>sstates A \<Longrightarrow> P; q\<in>cstates A \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" using states_part by (auto)

lemmas (in MFSM) mfsm_cons = sep_out_syms sepI sep_out_syms' sepI' states_partI1 states_partI2 syms_part syms_sep uniqueSp
lemmas (in MFSM) mfsm_cons' = sep_out_syms sepI sep_out_syms' sepI' states_partI1 states_partI2 syms_part uniqueSp

lemma (in MFSM) delta_cases: "\<lbrakk>(q,p,q')\<in>\<delta> A; q\<in>sstates A \<and> p\<in>ssyms M \<and> q'\<in>sstates A \<and> q'\<notin>{sp A s p | s p . s\<in>cstates A \<and> p\<in>csyms M} \<Longrightarrow> P; 
                                             q\<in>sstates A \<and> p=\<sharp> \<and> q'\<in>cstates A \<Longrightarrow> P;
                                             q\<in>cstates A \<and> p\<in>csyms M \<and> q'=sp A q p \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using delta_fmt by auto

lemma (in MFSM) delta_elems: "(q,p,q')\<in>\<delta> A \<Longrightarrow> q\<in>sstates A \<and> ((p\<in>ssyms M \<and> q'\<in>sstates A \<and> (q'\<notin>{sp A s p | s p . s\<in>cstates A \<and> p\<in>csyms M})) \<or> (p=\<sharp> \<and> q'\<in>cstates A)) \<or> (q\<in>cstates A \<and> p\<in>csyms M \<and> q'=sp A q p)"
  using delta_fmt by auto

lemma (in MFSM) delta_cases': "\<lbrakk>(q,p,q')\<in>\<delta> A; q\<in>sstates A \<and> p\<in>ssyms M \<and> q'\<in>sstates A \<and> q'\<notin>{sp A s p | s p . s\<in>cstates A \<and> p\<in>csyms M} \<Longrightarrow> P; 
                                             q\<in>sstates A \<and> p=sep M \<and> q'\<in>cstates A \<Longrightarrow> P;
                                             q\<in>cstates A \<and> p\<in>csyms M \<and> q'=sp A q p \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using delta_fmt' by auto

lemma (in MFSM) delta_elems': "(q,p,q')\<in>\<delta> A \<Longrightarrow> q\<in>sstates A \<and> ((p\<in>ssyms M \<and> q'\<in>sstates A \<and> (q'\<notin>{sp A s p | s p . s\<in>cstates A \<and> p\<in>csyms M})) \<or> (p=sep M \<and> q'\<in>cstates A)) \<or> (q\<in>cstates A \<and> p\<in>csyms M \<and> q'=sp A q p)"
  using delta_fmt' by auto


subsubsection \<open> Some implications of the M-automata conditions \<close>
text \<open> This list of properties is taken almost literally from \cite{BMT05}. \<close>
text \<open> Each control state @{term s} has @{term "sp A s p"} as its unique @{term p}-successor \<close>
lemma (in MFSM) cstate_succ_ex: "\<lbrakk>p\<in>csyms M; s\<in>cstates A\<rbrakk> \<Longrightarrow> (s,p,sp A s p) \<in> \<delta> A"
  using delta_fmt by (auto)

lemma (in MFSM) cstate_succ_ex': "\<lbrakk>p\<in>csyms M; s\<in>cstates A; \<delta> A \<subseteq> D\<rbrakk> \<Longrightarrow> (s,p,sp A s p) \<in> D" using cstate_succ_ex by auto

lemma (in MFSM) cstate_succ_unique: "\<lbrakk>s\<in>cstates A; (s,p,x)\<in>\<delta> A\<rbrakk> \<Longrightarrow> p\<in>csyms M \<and> x=sp A s p" by (auto elim: delta_cases dest: mfsm_cons')

text \<open> Transitions labeled with control symbols only leave from control states \<close>
lemma (in MFSM) csym_from_cstate: "\<lbrakk>(s,p,s')\<in>\<delta> A; p\<in>csyms M\<rbrakk> \<Longrightarrow> s\<in>cstates A" by (auto elim: delta_cases dest: mfsm_cons')


text \<open> @{term s} is the only predecessor of @{term "sp A s p"} \<close>
lemma (in MFSM) sp_pred_ex: "\<lbrakk>s\<in>cstates A; p\<in>csyms M\<rbrakk> \<Longrightarrow> (s,p,sp A s p)\<in>\<delta> A" using delta_fmt by auto
lemma (in MFSM) sp_pred_unique: "\<lbrakk>s\<in>cstates A; p\<in>csyms M; (s',p',sp A s p)\<in>\<delta> A\<rbrakk> \<Longrightarrow> s'=s \<and> p'=p \<and> s'\<in>cstates A \<and> p'\<in>csyms M" by (erule delta_cases) (auto dest: mfsm_cons')

text \<open> Only separators lead from stack states to control states \<close>
lemma (in MFSM) sep_in_between: "\<lbrakk>s\<in>sstates A; s'\<in>cstates A; (s,p,s')\<in>\<delta> A\<rbrakk> \<Longrightarrow> p=\<sharp>" by (auto elim: delta_cases dest: mfsm_cons') 
lemma (in MFSM) sep_to_cstate: "\<lbrakk>(s,\<sharp>,s')\<in>\<delta> A\<rbrakk> \<Longrightarrow> s\<in>sstates A \<and> s'\<in>cstates A" by (auto elim: delta_cases dest: mfsm_cons')


text \<open> Stack states do not have successors labelled with control symbols \<close>
lemma (in MFSM) sstate_succ: "\<lbrakk>s\<in>sstates A; (s,\<gamma>,s')\<in>\<delta> A\<rbrakk> \<Longrightarrow> \<gamma> \<notin> csyms M" by (auto elim: delta_cases dest: mfsm_cons') 
lemma (in MFSM) sstate_succ2: "\<lbrakk>s\<in>sstates A; (s,\<gamma>,s')\<in>\<delta> A; \<gamma>\<noteq>\<sharp>\<rbrakk> \<Longrightarrow> \<gamma>\<in>ssyms M \<and> s'\<in>sstates A" by (auto elim: delta_cases dest: mfsm_cons')

text \<open> M-automata do not accept the empty word \<close>
lemma (in MFSM) not_empty[iff]: "[]\<notin>lang A"
  apply (unfold lang_def langs_def)
  apply (clarsimp)
  apply (insert s0_fmt F_fmt)
  apply (subgoal_tac "s0 A = f")
  apply (auto dest: mfsm_cons')
done


text \<open> The paths through an M-automata have a very special form: Paths starting at a stack state are either labelled entirely with stack symbols, or have a prefix labelled with stack symbols followed by a separator \<close>
lemma (in MFSM) path_from_sstate: "!!s . \<lbrakk>s\<in>sstates A; (s,w,f)\<in>trclA A\<rbrakk> \<Longrightarrow> (f\<in>sstates A \<and> w\<in>lists (ssyms M)) \<or> (\<exists>w1 w2 t. w=w1@\<sharp>#w2 \<and> w1\<in>lists (ssyms M) \<and> t\<in>sstates A \<and> (s,w1,t)\<in>trclA A \<and> (t,\<sharp>#w2,f)\<in>trclA A)"
proof (induct w)
  case Nil thus ?case by (subgoal_tac "s=f") auto
next
  case (Cons e w)
  note IHP[rule_format]=this
  then obtain s' where STEP: "(s,e,s')\<in>(\<delta> A) \<and> s\<in>Q A \<and> e\<in>\<Sigma> A \<and> (s',w,f)\<in>trclA A" by (fast dest: trclAD_uncons)
  show ?case proof (cases "e=\<sharp>")
    assume "e=\<sharp>"
    with IHP have "e#w=[]@\<sharp>#w \<and> []\<in>lists (ssyms M) \<and> s\<in>sstates A \<and> (s,[],s)\<in>trclA A \<and> (s,e#w,f)\<in>trclA A" using states_part by (auto)
    thus ?case by force
  next
    assume "e\<noteq>\<sharp>"
    with IHP STEP sstate_succ2 have EC: "e\<in>ssyms M \<and> s'\<in>sstates A" by blast
    with IHP STEP have "(f \<in> sstates A \<and> w \<in> lists (ssyms M)) \<or> (\<exists>w1 w2 t. w = w1 @ \<sharp> # w2 \<and> w1 \<in> lists (ssyms M) \<and> t\<in>sstates A \<and> (s',w1,t)\<in>trclA A \<and> (t,\<sharp>#w2,f)\<in>trclA A)" (is "?C1\<or>?C2") by auto
    moreover {
      assume ?C1
      with EC have "f\<in>sstates A \<and> e#w \<in> lists (ssyms M)" by auto
    } moreover {
      assume ?C2
      then obtain w1 w2 t where CASE: "w = w1 @ \<sharp> # w2 \<and> w1 \<in> lists (ssyms M) \<and> t\<in>sstates A \<and> (s',w1,t)\<in>trclA A \<and> (t,\<sharp>#w2,f)\<in>trclA A" by (fast)
      with EC have "e#w = (e#w1) @ \<sharp> # w2 \<and> e#w1 \<in> lists (ssyms M)" by auto
      moreover from CASE STEP IHP  have "(s,e#w1,t)\<in>trclA A" using states_part by auto
      moreover note CASE
      ultimately have "\<exists>w1 w2 t. e#w = w1 @ \<sharp> # w2 \<and> w1 \<in> lists (ssyms M) \<and> t\<in>sstates A \<and> (s,w1,t)\<in>trclA A \<and> (t,\<sharp>#w2,f)\<in>trclA A" by fast
    } ultimately show ?case by blast
  qed
qed

text \<open> Using @{thm [source] MFSM.path_from_sstate}, we can describe the format of paths from control states, too.
  A path from a control state @{term s} to some final state starts with a transition @{term "(s,p,sp A s p)"} for some control symbol @{term p}. It then continues with a sequence of transitions labelled by stack symbols.
  It then either ends or continues with a separator transition, bringing it to a control state again, and some further transitions from there on. 
\<close>
lemma (in MFSM) path_from_cstate: 
  assumes A: "s\<in>cstates A" "(s,c,f)\<in>trclA A" "f\<in>sstates A"
  assumes SINGLE: "!! p w . \<lbrakk>c=p#w; p\<in>csyms M; w\<in>lists (ssyms M); (s,p,sp A s p)\<in>\<delta> A; (sp A s p,w,f)\<in>trclA A\<rbrakk> \<Longrightarrow> P"
  assumes CONC: "!! p w cr t s' . \<lbrakk>c=p#w@\<sharp>#cr; p\<in>csyms M; w\<in>lists (ssyms M); t\<in>sstates A; s'\<in>cstates A; (s,p,sp A s p)\<in>\<delta> A; (sp A s p,w,t)\<in>trclA A; (t,\<sharp>,s')\<in>\<delta> A; (s',cr,f)\<in>trclA A\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases c)
  case Nil thus P using A by (subgoal_tac "s=f", auto dest: mfsm_cons')
next
  case (Cons p w) note CFMT=this
  with cstate_succ_unique A have SPLIT: "p\<in>csyms M \<and> (s,p,sp A s p)\<in>\<delta> A \<and> (sp A s p,w,f)\<in>trclA A" by (blast dest: trclAD_uncons)
  with path_from_sstate A CFMT uniqueSp have CASES: "(f\<in>sstates A \<and> w\<in>lists (ssyms M)) \<or> (\<exists>w1 w2 t. w=w1@\<sharp>#w2 \<and> w1\<in>lists (ssyms M) \<and> t\<in>sstates A \<and> (sp A s p,w1,t)\<in>trclA A \<and> (t,\<sharp>#w2,f)\<in>trclA A)" (is "?C1 \<or> ?C2") by blast
  moreover {
    assume CASE: ?C1
    with SPLIT SINGLE A CFMT have P by fast
  } moreover {
    assume CASE: ?C2
    then obtain w1 w2 t where WFMT: "w=w1@\<sharp>#w2 \<and> w1\<in>lists (ssyms M) \<and> t\<in>sstates A \<and> (sp A s p,w1,t)\<in>trclA A \<and> (t,\<sharp>#w2,f)\<in>trclA A" by fast
    with sep_to_cstate obtain s' where "s'\<in>cstates A \<and> (t,\<sharp>,s')\<in>\<delta> A \<and> (s',w2,f)\<in>trclA A" by (fast dest: trclAD_uncons)
    with SPLIT CASE WFMT have "p#w=p#w1@\<sharp>#w2 \<and> p\<in>csyms M \<and> w1\<in>lists (ssyms M) \<and> t\<in>sstates A \<and> s'\<in>cstates A \<and> (s,p,sp A s p)\<in>\<delta> A \<and> (sp A s p,w1,t)\<in>trclA A \<and> (t,\<sharp>,s')\<in>\<delta> A \<and> (s',w2,f)\<in>trclA A" by auto
    with CFMT CONC have P by (fast)
  } ultimately show P by blast
qed


subsection \<open> $pre^*$-sets of regular sets of configurations \<close>
text \<open> Given a regular set @{term L} of configurations and a set @{term "\<Delta>"} of string rewrite rules, @{text "pre\<^sup>* \<Delta> L"} is the set of configurations that can be rewritten to some configuration in @{term L}, using rules from
  @{term "\<Delta>"} arbitrarily often.

  We first define this set inductively based on rewrite steps, and then provide the characterization described above as a lemma.
 \<close>

inductive_set "pre_star" :: "('c,'l) SRS \<Rightarrow> ('s,'c,'e) FSM_rec_scheme \<Rightarrow> 'c list set" ("pre\<^sup>*") 
  for \<Delta> L
where
  pre_refl: "c\<in>lang L \<Longrightarrow> c\<in>pre\<^sup>* \<Delta> L" |
  pre_step: "\<lbrakk>c'\<in>pre\<^sup>* \<Delta> L; (c,a,c')\<in>tr \<Delta>\<rbrakk> \<Longrightarrow> c\<in>pre\<^sup>* \<Delta> L"

text \<open> Alternative characterization of @{term "pre\<^sup>* \<Delta> L"} \<close> (* FIXME: Proof is not nice *)
lemma pre_star_alt: "pre\<^sup>* \<Delta> L = {c . \<exists>c'\<in>lang L . \<exists>as . (c,as,c')\<in>trcl (tr \<Delta>)}"
proof - 
  {
    fix x c' as
    have "\<lbrakk>x \<hookrightarrow>\<^bsub>as\<^esub> c' \<in> trcl (tr \<Delta>); c' \<in> lang L\<rbrakk> \<Longrightarrow> x \<in> pre\<^sup>* \<Delta> L"
      by (induct rule: trcl.induct) (auto intro: pre_step pre_refl)
  }  
  then show ?thesis
    by (auto elim!: pre_star.induct intro: trcl.intros)
  
qed

lemma pre_star_altI: "\<lbrakk>c'\<in>lang L; c\<hookrightarrow>\<^bsub>as\<^esub> c'\<in>trcl (tr \<Delta>)\<rbrakk> \<Longrightarrow> c\<in>pre\<^sup>* \<Delta> L" by (unfold pre_star_alt, auto)
lemma pre_star_altE: "\<lbrakk>c\<in>pre\<^sup>* \<Delta> L; !!c' as. \<lbrakk>c'\<in>lang L; c\<hookrightarrow>\<^bsub>as\<^esub> c'\<in>trcl (tr \<Delta>)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by (unfold pre_star_alt, auto)


subsection \<open> Nondeterministic algorithm for pre$^*$\<close>
text \<open>
  In this section, we formalize the saturation algorithm for computing @{term "pre\<^sup>* \<Delta> L"} from \cite{BMT05}.
  Roughly, the algorithm works as follows: 
  \begin{enumerate}
    \item Set @{term "D=\<delta> A"}
    \item Choose a rule @{term "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M"} and states @{text "q,q'\<in>Q A"}, such that @{term D} can read the configuration @{term "c'"} from state @{term "q"} and end in state @{term "q'"} 
      (i.e. @{term "(q,c',q')\<in>trclAD A D"}) and such that @{term "(sp A q p,\<gamma>,q')\<notin>D"}. If this is not possible, terminate.
    \item Add the transition @{term "(sp A q p,\<gamma>,q')\<notin>D"} to @{term D} and continue with step 2
  \end{enumerate}

  Intuitively, the behaviour of this algorithm can be explained as follows: 
    If there is a configuration @{term "c\<^sub>1@c'@c\<^sub>2 \<in> pre\<^sup>* \<Delta> L"}, and a rule @{term "p#\<gamma> \<hookrightarrow>\<^bsub>a\<^esub> c' \<in> \<Delta>"}, then we also have @{term "c\<^sub>1@p#\<gamma>@c\<^sub>2\<in>pre\<^sup>* \<Delta> L"}. The effect of step 3 is exactly adding
    these configurations @{term "c\<^sub>1@p#\<gamma>@c\<^sub>22"} to the regular set of configurations.

  We describe the algorithm nondeterministically by its step relation @{text "ps_R"}. Each step describes the addition of one transition.
\<close>

text \<open>
  In this approach, we directly restrict the domain of the step-relation to transition relations below some upper bound @{text "ps_upper"}.
  We will later show, that the initial transition relation of an M-automata is below this upper bound, and that the step-relation preserves the property of being below this upper bound.  
  
  We define  @{term "ps_upper M A"} as a finite set, and show that the initial transition relation @{term "\<delta> A"} of an M-automata is below @{term "ps_upper M A"}, 
  and that @{term "ps_R M A"} preserves the property of being below the finite set @{term "ps_upper M A"}.
  Note that we use the more fine-grained @{term "ps_upper M A"} as upper bound for the termination proof rather than @{term "Q A \<times> \<Sigma> A \<times> Q A"}, as @{text "sp A q p"} is only specified
  for control states @{text "q"} and control symbols @{text "p"}. Hence we need the finer structure of @{term "ps_upper M A"} to guarantee that @{text "sp"} is only applied
  to arguments it is specified for. Anyway, the fine-grained @{term "ps_upper M A"} bound is also needed for the correctness proof.
\<close>
definition ps_upper :: "('c,'l,'e1) DPN_rec_scheme \<Rightarrow> ('s,'c,'e2) MFSM_rec_scheme \<Rightarrow> ('s,'c) LTS" where
  "ps_upper M A == (sstates A \<times> ssyms M \<times> sstates A) \<union> (sstates A \<times> {sep M} \<times> cstates A) \<union> {(s,p,sp A s p) | s p . s\<in>cstates A \<and> p\<in>csyms M}"

inductive_set ps_R :: "('c,'l,'e1) DPN_rec_scheme \<Rightarrow> ('s,'c,'e2) MFSM_rec_scheme \<Rightarrow> (('s,'c) LTS * ('s,'c) LTS) set" for M A 
where
  "\<lbrakk>[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M; (q,c',q')\<in>trclAD A D; (sp A q p,\<gamma>,q')\<notin>D; D\<subseteq>ps_upper M A\<rbrakk> \<Longrightarrow> (D,insert (sp A q p,\<gamma>,q') D)\<in>ps_R M A"

lemma ps_R_dom_below: "(D,D')\<in>ps_R M A \<Longrightarrow> D\<subseteq>ps_upper M A" by (auto elim: ps_R.cases)

subsubsection \<open> Termination \<close>

text \<open>
  Termination of our algorithm is equivalent to well-foundedness of its (converse) step relation, that is, we have to show @{term "wf ((ps_R M A)\<inverse>)"}.
  
  In the following, we also establich some properties of transition relations below @{term "ps_upper M A"}, that will be used later in the correctness proof.
\<close>

lemma (in MFSM) ps_upper_cases: "\<lbrakk>(s,e,s')\<in>ps_upper M A;
  \<lbrakk>s\<in>sstates A; e\<in>ssyms M; s'\<in>sstates A\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s\<in>sstates A; e=\<sharp>; s'\<in>cstates A\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s\<in>cstates A; e\<in>csyms M; s'=sp A s e\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P" 
  by (unfold ps_upper_def sep_def, auto)

lemma (in MFSM) ps_upper_cases': "\<lbrakk>(s,e,s')\<in>ps_upper M A;
  \<lbrakk>s\<in>sstates A; e\<in>ssyms M; s'\<in>sstates A\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s\<in>sstates A; e=sep M; s'\<in>cstates A\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s\<in>cstates A; e\<in>csyms M; s'=sp A s e\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P" 
  apply (rule ps_upper_cases)
  by (unfold sep_def) auto

lemma (in MFSM) ps_upper_below_trivial: "ps_upper M A \<subseteq> Q A \<times> \<Sigma> A \<times> Q A" by (unfold ps_upper_def, auto simp add: states_part alpha_cons uniqueSp sep_def)

lemma (in MFSM) ps_upper_finite: "finite (ps_upper M A)" using ps_upper_below_trivial finite_delta_dom by (auto simp add: finite_subset)

text \<open> The initial transition relation of the M-automaton is below @{term "ps_upper M A"} \<close>
lemma (in MFSM) initial_delta_below: "\<delta> A \<subseteq> ps_upper M A" using delta_fmt by (unfold ps_upper_def sep_def) auto


text \<open> Some lemmas about structure of transition relations below @{term "ps_upper M A"} \<close>
lemma (in MFSM) cstate_succ_unique': "\<lbrakk>s\<in>cstates A; (s,p,x)\<in>D; D\<subseteq>ps_upper M A\<rbrakk> \<Longrightarrow> p\<in>csyms M \<and> x=sp A s p" by (auto elim: ps_upper_cases dest: mfsm_cons')
lemma (in MFSM) csym_from_cstate': "\<lbrakk>(s,p,s')\<in>D; D\<subseteq>ps_upper M A; p\<in>csyms M\<rbrakk> \<Longrightarrow> s\<in>cstates A" by (auto elim: ps_upper_cases dest: mfsm_cons')

text \<open> The only way to end up in a control state is after executing a separator. \<close>
lemma (in MFSM) ctrl_after_sep: assumes BELOW: "D \<subseteq> ps_upper M A"
  assumes A: "(q,c',q')\<in>trclAD A D"    "c'\<noteq>[]"
  shows "q'\<in>cstates A = (last c' = \<sharp>)"
proof -
  from A have "(q,butlast c' @ [last c'],q')\<in>trclAD A D" by auto
  with A obtain qh where "(qh,[last c'],q')\<in>trclAD A D" by (blast dest: trclAD_unconcat)
  hence "(qh,last c',q')\<in> D" by (fast dest: trclAD_single)
  with BELOW have IS: "(qh,last c',q')\<in>ps_upper M A" by fast
  thus ?thesis by (erule_tac ps_upper_cases) (auto dest: mfsm_cons' simp add: sep_out_syms) (* This proof behaves somewhat odd, perhaps there's something in simp/dest that makes problems. *)
qed  

text \<open> When applying a rules right hand side to a control state, we will get to a stack state \<close>
lemma (in MFSM) ctrl_rule: assumes BELOW: "D \<subseteq> ps_upper M A"
  assumes A: "([p,\<gamma>],a,c')\<in>rules M" and B: "q\<in>cstates A" "(q,c',q')\<in>trclAD A D"
  shows "q'\<in>sstates A"
proof -
  from A show ?thesis
  proof (cases rule: rule_cases)
    case (no_spawn p \<gamma> a p' w)
    hence C: "q \<hookrightarrow>\<^bsub>p' # w\<^esub> q' \<in> trclAD A D" "\<forall>x\<in>set w. x \<in> ssyms M" "p' \<in> csyms M" using B by auto
    hence "last (p'#w) \<noteq> \<sharp> \<and> q'\<in>Q A" by (unfold sep_def) (auto dest: mfsm_cons' trclAD_elems)
    with C BELOW ctrl_after_sep[of D q "p'#w" q'] show "(q' \<in> sstates A)" by (fast dest: mfsm_cons')
  next
    case (spawn p \<gamma> a p1 w1 p2 w2)
    hence C: "q \<hookrightarrow>\<^bsub>p1 # w1 @ \<sharp> # p2 # w2\<^esub> q' \<in> trclAD A D" "\<forall>x\<in>set w2. x \<in> ssyms M" "p2 \<in> csyms M" using B by auto
    hence "last (p1 # w1 @ \<sharp> # p2 # w2) \<noteq> sep M \<and> q'\<in>Q A" by (auto dest: mfsm_cons' trclAD_elems)
    with C BELOW ctrl_after_sep[of D q "p1 # w1 @ \<sharp> # p2 # w2" q'] show "(q' \<in> sstates A)" by (unfold sep_def, fast dest: mfsm_cons')
  qed
qed


text \<open> @{term "ps_R M A"} preserves the property of being below @{term "ps_upper M A"}, and the transition relation becomes strictly greater in each step \<close>
lemma (in MFSM) ps_R_below: assumes E: "(D,D')\<in>ps_R M A" 
  shows "D\<subset>D' \<and> D' \<subseteq> ps_upper M A"
proof -
  from E have BELOW: "D\<subseteq>ps_upper M A" by (simp add: ps_R_dom_below)

  {
    fix p \<gamma> a c' q q'
    assume A: "[p, \<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M" "q \<hookrightarrow>\<^bsub>c'\<^esub> q' \<in> trclAD A D"
    obtain p' cr' where CSPLIT: "p\<in>csyms M \<and> p'\<in>csyms M \<and> c'=p'#cr' \<and> \<gamma>\<in>ssyms M" by (insert A) (erule rule_cases, fast+)
    with BELOW A obtain qh where SPLIT: "(q,p',qh)\<in>D" "(q,p',qh)\<in>ps_upper M A" by (fast dest: trclAD_uncons)
    with CSPLIT have QC: "q\<in>cstates A \<and> qh=sp A q p'" by (auto elim: ps_upper_cases dest: syms_part iff add: syms_sep)
    with BELOW A ctrl_rule[of D p \<gamma> a c' q q'] have Q'S: "q'\<in>sstates A" by simp
    from QC CSPLIT have "sp A q p \<in> sstates A" by (simp add: uniqueSp)
    with Q'S CSPLIT have "sp A q p \<hookrightarrow>\<^bsub>\<gamma>\<^esub> q' \<in> ps_upper M A" by (unfold ps_upper_def, simp)
  }
  with E show ?thesis by (auto elim!: ps_R.cases)
qed

text \<open> As a result of this section, we get the well-foundedness of @{term "ps_R M A"}, 
  and that the transition relations that occur during the saturation algorithm stay above the initial transition relation @{term "\<delta> A"} and below @{term "ps_upper M A"}\<close>
theorem (in MFSM) ps_R_wf: "wf ((ps_R M A)\<inverse>)" using ps_upper_finite sat_wf[where \<alpha>=id, simplified] ps_R_below by (blast)

theorem (in MFSM) ps_R_above_inv: "is_inv (ps_R M A) (\<delta> A) (\<lambda>D. \<delta> A \<subseteq> D)" by (auto intro: invI elim: ps_R.cases)

theorem (in MFSM) ps_R_below_inv: "is_inv (ps_R M A) (\<delta> A) (\<lambda>D. D\<subseteq>ps_upper M A)" by (rule invI) (auto simp add: initial_delta_below ps_R_below) 

text \<open> We can also show that the algorithm is defined for every possible initial automata \<close>
theorem (in MFSM) total: "\<exists>D. (\<delta> A, D)\<in>ndet_algo(ps_R M A)" using ps_R_wf ndet_algo_total by blast

subsubsection \<open> Soundness \<close>
text \<open>
  The soundness (over-approximation) proof works by induction over the definition of @{text "pre\<^sup>*"}. 
  
  In the reflexive case, a configuration from the original language is also in the saturated language, because no transitions are killed
  during saturation.

  In the step case, we assume that a configuration @{text "c'"} is in the saturated language, and show for a rewriting step @{text "c\<hookrightarrow>\<^bsub>a\<^esub>c'"} that also @{text c} is in the saturated language. 
\<close>
theorem (in MFSM) sound: "\<lbrakk>c\<in>pre_star (rules M) A; (\<delta> A,s')\<in>ndet_algo (ps_R M A)\<rbrakk> \<Longrightarrow> c\<in>lang (A\<lparr> \<delta>:=s' \<rparr>)" (*is "\<lbrakk>_;_\<rbrakk>\<Longrightarrow>_ \<in> lang ?A'"*)
proof -
  let ?A' = "A\<lparr> \<delta>:=s' \<rparr>"
  assume A:"(\<delta> A,s')\<in>ndet_algo (ps_R M A)"
  \<comment> \<open>Some little helpers\<close>
  from A ps_R_above_inv have SUBSET: "\<delta> A \<subseteq> s'" by (unfold ndet_algo_def) (auto dest: inv)
  have TREQ: "!!D . trclAD A D = trclAD ?A' D" by (rule trclAD_eq, simp_all)
  from A ps_R_below_inv have SATSETU: "\<delta> ?A' \<subseteq> ps_upper M A" by (erule_tac ndet_algoE) (auto dest: inv iff add: initial_delta_below) 

  assume "c\<in>pre_star (rules M) A"
  \<comment> \<open> Make an induction over the definition of @{term "pre\<^sup>*"} \<close>
  thus ?thesis proof (induct c rule: pre_star.induct)
    fix c assume "c\<in>lang A" (*case (pre_refl c)*) \<comment> \<open>Reflexive case: The configuration comes from the original regular language\<close>
    then obtain f where F: "f\<in>F A \<and> (s0 A,c,f)\<in>trclA A" by (unfold lang_def langs_def, fast) \<comment> \<open> That is, @{term c} can bring the initial automata from its start state to some final state @{term f} \<close>
    with SUBSET trclAD_mono_adv[of "\<delta> A" "s'" A ?A'] have "(s0 A,c,f)\<in>trclA ?A'" by (auto) \<comment> \<open> Because the original transition relation @{term "\<delta> A"} is a subset of the saturated one @{term "s'"} (@{thm [source] SUBSET}) and 
      the transitive closure is monotonous, @{term "(s0 A,c,f)"} is also in the transitive closure of the saturated transition relation \<close>
    with F show "c\<in>lang ?A'" by (unfold lang_def langs_def) auto \<comment> \<open> and thus in the language of the saturated automaton \<close>
  next
    \<comment> \<open>Step case: \<close>
    fix a c c' 
    assume IHP: "c' \<in> pre\<^sup>* (rules M) A" "(c, a, c') \<in> tr (rules M)" \<comment> \<open> We take some configurations @{term "c"} and @{term "c' \<in> pre\<^sup>* (rules M) A"} and assume that @{term "c"} can be rewritten to @{term "c'"} in one step \<close>
      "c' \<in> lang ?A'" \<comment> \<open> We further assume that @{term "c'"} is in the saturated language, and we have to show that also @{term c} is in that language \<close>

    from IHP obtain f where F: "f\<in>F ?A' \<and> (s0 ?A',c',f) \<in> trclA ?A'" by (unfold lang_def langs_def, fast) \<comment> \<open> Unfolding the definition of @{term "lang"} \<close>
    from IHP obtain w1 w2 r r' where CREW: "c=w1@(r@w2) \<and> c'=w1@(r'@w2) \<and> (r,a,r')\<in>rules M" by (auto elim!: tr.cases) \<comment> \<open> Get the rewrite rule that rewrites @{term c} to @{term "c'"} \<close>
    then obtain p \<gamma> p' w' where RFMT: "p\<in>csyms M \<and> p'\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> r=[p,\<gamma>] \<and> r'=p'#w'" by (auto elim!: rule_cases) \<comment> \<open> This rewrite rule rewrites some control symbol @{term p} followed by a stack symbol @{term "\<gamma>"} to 
      another control symbol @{term "p'"} and a sequence of further symbols @{term "w'"} \<close>
    with F CREW obtain q qh q' where SPLIT: "(s0 ?A',w1,q)\<in>trclA ?A' \<and> (q,p'#w',q')\<in>trclA ?A' \<and> (q',w2,f)\<in>trclA ?A' \<and> (q,p',qh)\<in>\<delta> ?A'" 
      by (blast dest: trclAD_unconcat trclAD_uncons) \<comment> \<open> Get the states in the transition relation generated by the algorithm, that correspond to the splitting of @{term "c'"} as established in @{thm [source] CREW} \<close>


    have SHORTCUT: "(q,[p,\<gamma>],q')\<in>trclA ?A'" \<comment> \<open> In the transition relation generated by our algorithm, we can get from @{term q} to @{term "q'"} also by @{term "[p,\<gamma>]"} \<close>
    proof -
      have S1: "(q,p,sp A q p)\<in>\<delta> ?A'" and QINC: "q\<in>cstates A" \<comment> \<open> The first transition, from @{term q} with @{term p} to @{term "sp A q p"} is already contained in the initial M-automata. 
        We also need to know for further proofs, that @{term q} is a control state. \<close>
      proof -
        from SPLIT SATSETU have "(q,p',qh)\<in>ps_upper M A" by auto
        with RFMT show "q\<in>cstates A" by (auto elim!: ps_upper_cases dest: mfsm_cons' simp add: sep_def)
        with RFMT have "(q,p,sp A q p)\<in>\<delta> A" by (fast intro: cstate_succ_ex)
        with SUBSET show "(q,p,sp A q p)\<in>\<delta> ?A'" by auto
      qed
      moreover
      have S2: "(sp A q p,\<gamma>,q')\<in>\<delta> ?A'" \<comment> \<open> The second transition, from @{term "sp A q p"} with @{term "\<gamma>"} to @{term "q'"} has been added during the algorithm's execution \<close>
      proof -
        from A have "s'\<notin>Domain (ps_R M A)" by (blast dest: termstate_ndet_algo)
        moreover from CREW RFMT SPLIT TREQ SATSETU have "(sp A q p,\<gamma>,q')\<notin>s' \<Longrightarrow> (s',insert (sp A q p,\<gamma>,q') s') \<in> (ps_R M A)" by (auto intro: ps_R.intros)
        ultimately show ?thesis by auto
      qed
      moreover
      have "sp A q p \<in> Q ?A' \<and> q'\<in>Q ?A' \<and> q\<in>Q ?A' \<and> p\<in>\<Sigma> ?A' \<and> \<gamma>\<in>\<Sigma> ?A'" \<comment> \<open>The intermediate states and labels have also the correct types\<close>        
      proof -
        from S2 SATSETU have "(sp A q p,\<gamma>,q')\<in>ps_upper M A" by auto
        with QINC RFMT show ?thesis by (auto elim: ps_upper_cases dest: mfsm_cons' simp add: states_part alpha_cons)
      qed
      ultimately show ?thesis by simp
    qed

    have "(s0 ?A',w1@(([p,\<gamma>])@w2),f)\<in>trclA ?A'" \<comment> \<open> Now we put the pieces together and construct a path from @{term "s0 A"} with @{term "w1"} to @{term q}, from there 
      with @{term "[p,\<gamma>]"} to @{term q'} and then with @{term w2} to the final state @{term f} \<close>    
    proof -
      from SHORTCUT SPLIT have "(q,([p,\<gamma>])@w2,f)\<in>trclA ?A'" by (fast dest: trclAD_concat)
      with SPLIT show ?thesis by (fast dest: trclAD_concat)
    qed
    with CREW RFMT have "(s0 ?A',c,f)\<in>trclA ?A'" by auto \<comment> \<open> this is because @{term "c = w1@[p,\<gamma>]@w2"} \<close>
    with F show "c\<in>lang ?A'" by (unfold lang_def langs_def, fast) \<comment> \<open> And thus @{term c} is in the language of the saturated automaton \<close>
  qed
qed

subsubsection \<open> Precision \<close>

text \<open>
  In this section we show the precision of the algorithm, that is we show that the saturated language is below the backwards reachable set.
\<close>

text \<open> 
  The following induction scheme makes an induction over the number of occurences of a certain transition in words accepted by a FSM: 

  To prove a proposition for all words from state @{term "qs"} to state @{term "qf"} in FSM @{term A} that has a transition rule @{term "(s,a,s')\<in>\<delta> A"}, we have to show the following:
  \begin{itemize}
    \item Show, that the proposition is valid for words that do not use the transition rule @{term "(s,a,s')\<in>\<delta> A"} at all
    \item Assuming that there is a prefix @{term "wp"} from @{term "qs"} to @{term "s"} and a suffix @{term "ws"} from @{term "s'"} to @{term "qf"}, and that @{term "wp"} does not use the new rule,
       and further assuming that for all prefixes @{term "wh"} from @{term "qs"} to @{term "s'"}, the proposition holds for @{term "wh@ws"}, show that the proposition also holds for
       @{term "wp@a#ws"}.
  \end{itemize}

  We actually do use @{term D} here instead of @{term "\<delta> A"}, for use with @{term "trclAD"}.
\<close>
lemma ins_trans_induct[consumes 1, case_names base step]:
  fixes qs and qf
  assumes A: "(qs,w,qf)\<in>trclAD A (insert (s,a,s') D)"
  assumes BASE_CASE: "!! w . (qs,w,qf)\<in>trclAD A D \<Longrightarrow> P w"
  assumes STEP_CASE: "!! wp ws . \<lbrakk>(qs,wp,s)\<in>trclAD A D; (s',ws,qf)\<in>trclAD A (insert (s,a,s') D); !! wh . (qs,wh,s')\<in>trclAD A D \<Longrightarrow> P (wh@ws)\<rbrakk> \<Longrightarrow> P (wp@a#ws)"
  shows "P w"
proof -
  \<comment> \<open> Essentially, the proof works by induction over the suffix @{term "ws"} \<close>
  {
    fix ws
    have "!!qh wp. \<lbrakk>(qs,wp,qh)\<in>trclAD A D; (qh,ws,qf)\<in>trclAD A (insert (s,a,s') D)\<rbrakk> \<Longrightarrow> P (wp@ws)" proof (induct ws)
      case (Nil qh wp) with BASE_CASE show ?case by (subgoal_tac "qh=qf", auto)
    next
      case (Cons e w qh wp) note IHP=this
      then obtain qhh where SPLIT: "(qh,e,qhh)\<in>(insert (s \<hookrightarrow>\<^bsub>a\<^esub> s') D) \<and> (qhh,w,qf)\<in>trclAD A (insert (s \<hookrightarrow>\<^bsub>a\<^esub> s') D) \<and> qh\<in>Q A \<and> e\<in>\<Sigma> A" by (fast dest: trclAD_uncons)
      show ?case proof (cases "(qh,e,qhh) = (s,a,s')")
        case False 
        with SPLIT have "(qh,[e],qhh)\<in>trclAD A D" by (auto intro: trclAD_one_elem dest: trclAD_elems)
        with IHP have "(qs,wp@[e],qhh)\<in>trclAD A D" by (fast intro: trclAD_concat)
        with IHP SPLIT have "P ((wp@[e])@w)" by fast
        thus ?thesis by simp
      next
        case True note CASE=this
        with SPLIT IHP have "(qs,wp,s) \<in> trclAD A D \<and> s' \<hookrightarrow>\<^bsub>w\<^esub> qf \<in> trclAD A (insert (s \<hookrightarrow>\<^bsub>a\<^esub> s') D)" "!!wh. (qs,wh,s')\<in>trclAD A D \<Longrightarrow> P (wh@w)" by simp_all
        with STEP_CASE CASE show ?thesis by simp
      qed
    qed
  } note C=this
  from A C[of "[]" qs w] show ?thesis by (auto dest: trclAD_elems)
qed


text \<open> 
  The following lemma is a stronger elimination rule than @{thm [source] ps_R.cases}. It makes a more fine-grained distinction.
  In words: A step of the algorithm adds a transition  @{term "(sp A q p,\<gamma>,s')"}, if there is a rule @{term "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> p'#c'"}, and a transition sequence @{term "(q,p'#c',s')\<in>trclAD A D"}. That is, if we have 
  @{term "(sp A q p',c',s')\<in>trclAD A D"}.
 \<close>

lemma (in MFSM) ps_R_elims_adv: 
  assumes "(D,D')\<in>ps_R M A"
  obtains \<gamma> s' a p' c' p q where 
    "D'=insert (sp A q p,\<gamma>,s') D" "(sp A q p,\<gamma>,s')\<notin>D" "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> p'#c' \<in> rules M" "(q,p'#c',s')\<in>trclAD A D"
    "p\<in>csyms M" "\<gamma>\<in>ssyms M" "q\<in>cstates A" "p'\<in>csyms M" "a\<in>labels M" "(q,p',sp A q p')\<in>D" "(sp A q p',c',s')\<in>trclAD A D"
  using assms  
proof (cases rule: ps_R.cases)
  case A: (1 p \<gamma> a c' q q')
  then obtain p' cc' where RFMT: "p\<in>csyms M \<and> c'=p'#cc' \<and> p'\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> a\<in>labels M" by (auto elim!: rule_cases)
  with A obtain qh where SPLIT: "(q,p',qh)\<in>D \<and> (qh,cc',q')\<in> trclAD A D" by (fast dest: trclAD_uncons)
  with A RFMT have "q\<in>cstates A \<and> qh=sp A q p'" by (subgoal_tac "(q,p',qh)\<in>ps_upper M A") (auto elim!: ps_upper_cases dest: syms_part sep_out_syms)
  then show ?thesis using A RFMT SPLIT that by blast
qed

text \<open> Now follows a helper lemma to establish the precision result. In the original paper \cite{BMT05} it is called the {\em crucial point} of the precision proof.

  It states that for transition relations that occur during the execution of the algorithm, for each word @{term w} that leads from the start state to a state @{term "sp A q p"}, there is a word
  @{term "ws@[p]"} that leads to @{term "sp A q p"} in the initial automaton and @{term w} can be rewritten to @{term "ws@[p]"}.

  In the initial transition relation, a state of the form @{term "sp A q p"} has only one incoming edge labelled @{term "p"} (@{thm [source] MFSM.sp_pred_ex MFSM.sp_pred_unique}).
  Intuitively, this lemma explains why it is correct to add further incoming edges to @{term "sp A q p"}: All words using such edges can be rewritten to a word using the original edge.  
\<close>

lemma (in MFSM) sp_property:
  shows "is_inv (ps_R M A) (\<delta> A) (\<lambda>D. 
     (\<forall> w . \<forall>p\<in>csyms M. \<forall>q\<in>cstates A. (s0 A,w,sp A q p)\<in>trclAD A D \<longrightarrow> (\<exists>ws as. (s0 A,ws,q)\<in>trclA A \<and> (w,as,ws@[p])\<in>trcl (tr (rules M)))) \<and> 
     (\<forall>P'. is_inv (ps_R M A) (\<delta> A) P' \<longrightarrow> P' D))"
  \<comment> \<open>We show the thesis by proving that it is an invariant of the saturation procedure\<close>
proof (rule inv_useI; intro allI ballI impI conjI)  
  \<comment> \<open>Base case, show the thesis for the initial automata \<close>
  fix w p q
  assume A: "p \<in> csyms M" "q \<in> cstates A" "s0 A \<hookrightarrow>\<^bsub>w\<^esub> sp A q p \<in> trclA A"
  show "\<exists>ws as. s0 A \<hookrightarrow>\<^bsub>ws\<^esub> q \<in> trclA A \<and> (w,as,ws@[p])\<in>trcl (tr (rules M))" 
  proof (cases w rule: rev_cases) \<comment> \<open> Make a case distinction wether @{term w} is empty \<close>
    case Nil \<comment> \<open> @{term w} cannot be empty, because @{term "s0"} is a control state, and @{term "sp"} is a stack state, and by definition of M-automata, these cannot be equal \<close>
    with A have "s0 A = sp A q p" by (auto)
    with A s0_fmt uniqueSp have False by (auto dest: mfsm_cons')
    thus ?thesis ..
  next
    case (snoc ws p') note CASE=this 
    with A obtain qh where "(s0 A,ws,qh)\<in>trclA A \<and> (qh,[p'],sp A q p)\<in>trclA A \<and> (qh,p',sp A q p)\<in>\<delta> A" by (fast dest: trclAD_unconcat trclAD_single) \<comment> \<open> Get the last state @{term "qh"} and 
      symbol @{term "p'"} before reaching @{term "sp"} \<close>
    moreover with A have "p=p' \<and> qh=q" by (blast dest: sp_pred_unique) \<comment> \<open> This symbol is @{term p}, because the @{term p}-edge from @{term q} is the only edge to @{term "sp A q p"} in an M-automata \<close>
    moreover with CASE have "(w,[],ws@[p]) \<in> trcl (tr (rules M))" by (fast intro: trcl.empty)
    ultimately show ?thesis by (blast)
  qed
next
  \<comment> \<open> Step case \<close>
  fix D1 D2 w p q
  assume 
    IH: "\<forall>w. \<forall>p\<in>csyms M. \<forall>q\<in>cstates A. s0 A \<hookrightarrow>\<^bsub>w\<^esub> sp A q p \<in> trclAD A D1 
      \<longrightarrow> (\<exists>ws as. s0 A \<hookrightarrow>\<^bsub>ws\<^esub> q \<in> trclAD A (\<delta> A) \<and> (w \<hookrightarrow>\<^bsub>as\<^esub> ws @ [p] \<in> trcl (tr (rules M))))" \<comment> \<open> By induction hypothesis, our proposition is valid for @{term "D1"} \<close>
    and SUCC: "(D1,D2)\<in>ps_R M A" \<comment> \<open> We have to show the proposition for some @{term "D2"}, that is a successor state of @{term "D1"} w.r.t. @{term "ps_R M A"} \<close>
    and P1: "p \<in> csyms M" "q \<in> cstates A" and P2: "s0 A \<hookrightarrow>\<^bsub>w\<^esub> sp A q p \<in> trclAD A D2" \<comment> \<open> Premise of our proposition: We reach some state @{term "sp A q p"} \<close> 
    and USE_INV: "\<And>P'. is_inv (ps_R M A) (\<delta> A) P' \<Longrightarrow> P' D1" \<comment> \<open> We can use known invariants \<close>

  from SUCC have SS: "D1 \<subseteq> ps_upper M A" by (blast dest: ps_R_dom_below)
  from USE_INV have A2: "\<delta> A \<subseteq> D1" by (blast intro: ps_R_above_inv)

  from SUCC obtain \<gamma> s' pp aa cc' qq where ADD: "insert (sp A qq pp,\<gamma>,s') D1 = D2 \<and> (sp A qq pp,\<gamma>,s')\<notin>D1" and 
                                           RCONS: "([pp,\<gamma>],aa,cc')\<in>rules M \<and> (qq,cc',s')\<in>trclAD A D1 \<and> qq\<in>cstates A \<and> pp\<in>csyms M \<and> aa\<in>labels M"
    by (blast elim!: ps_R_elims_adv) \<comment> \<open> Because of @{thm [source] SUCC}, we obtain @{term "D2"} by adding a (new) transition @{term "(sp A qq pp,\<gamma>,s')"} to @{term "D1"}, such that there is a rule 
    @{term "[pp,\<gamma>]\<hookrightarrow>\<^bsub>aa\<^esub> cc' \<in> rules M"} and the former transition relation can do @{term "(qq,cc',s')\<in>trclAD A D1"} \<close>
  from P2 ADD have P2': "s0 A \<hookrightarrow>\<^bsub>w\<^esub> sp A q p \<in> trclAD A (insert (sp A qq pp \<hookrightarrow>\<^bsub>\<gamma>\<^esub> s') D1)" by simp
      
  show "\<exists>ws as. s0 A \<hookrightarrow>\<^bsub>ws\<^esub> q \<in> trclA A \<and> w \<hookrightarrow>\<^bsub>as\<^esub> ws @ [p] \<in> trcl (tr (rules M))" using P2' 
    \<comment> \<open> We show the proposition by induction on how often the new rule was used. For this, we regard a prefix until the first usage of the added rule, and a suffix that may use the added rule arbitrarily often \<close>
  proof (induction rule: ins_trans_induct)
    case (base) \<comment> \<open> Base case, the added rule is not used at all. The proof is straighforward using the induction hypothesis of the outer (invariant) induction \<close>
    thus ?case using IH P1 by simp
  next
    fix wpre wsfx \<comment> \<open> Step case: We have a prefix that does not use the added rule, then a usage of the added rule and a suffix. 
      We know that our proposition holds for all prefixes that do not use the added rule. \<close>
    assume IP1: "(s0 A,wpre, sp A qq pp) \<in> trclAD A D1" and IP2: "(s', wsfx, sp A q p) \<in> trclAD A (insert (sp A qq pp, \<gamma>, s') D1)"
    assume IIH: "!!wh. (s0 A, wh, s') \<in> trclAD A D1 \<Longrightarrow> \<exists>ws as. (s0 A, ws, q) \<in> trclAD A (\<delta> A) \<and> ((wh @ wsfx, as, ws @ [p]) \<in> trcl (tr (rules M)))"
    from IP1 IH RCONS obtain wps aps where C1: "(s0 A,wps,qq) \<in> trclAD A (\<delta> A) \<and> wpre \<hookrightarrow>\<^bsub>aps\<^esub> wps @ [pp] \<in> trcl (tr (rules M))" by fast \<comment> \<open> This is an instance of a configuration reaching a sp-state, 
      thus by induction hypothesis of the outer (invariant) induction, we find a successor configuration @{term "wps@[pp]"} that reaches this state using @{term "pp"} as last edge in @{term "\<delta> A"} \<close>
    with A2 have "(s0 A,wps,qq) \<in> trclAD A D1" by (blast dest: trclAD_mono) \<comment> \<open> And because @{thm "A2"}, we can do the transitions also in @{term "D1"} \<close>
    with RCONS have "(s0 A,wps@cc', s') \<in> trclAD A D1" by (blast intro: trclAD_concat) \<comment> \<open> From above (@{thm [source] RCONS}) we know @{term "(qq,cc',s')\<in>trclAD A D1"}, and we can concatenate these transition sequences \<close>
    then obtain ws as where C2: "(s0 A,ws,q) \<in> trclAD A (\<delta> A) \<and> (wps@cc') @ wsfx \<hookrightarrow>\<^bsub>as\<^esub> ws @ [p] \<in> trcl (tr (rules M))" by (fast dest: IIH) \<comment> \<open> This concatenation is a prefix to a usage of the added transition, 
      that does not use the added transition itself. (The whole configuration bringing us to @{term "sp A q p"} is @{term "wps@cc'@wsfx"}). 
      For those prefixes, we can apply the induction hypothesis of the inner induction and obtain a configuration @{term "ws@[p]"} that is a successor configuration of @{term "wps@cc'@wsfx"}, and with which 
      we can reach @{term "sp A q p"} using @{term p} as last edge \<close>

    have "\<exists>as. wpre @ \<gamma> # wsfx \<hookrightarrow>\<^bsub>as\<^esub> ws @ [p] \<in> trcl (tr (rules M))" \<comment> \<open> Now we obtained some configuration @{term "ws@[p]"}, that reaches @{term "sp A q p"} using @{term p} as last edge in @{term "\<delta> A"}. 
      Now we show that this is indeed a successor configuration of @{term "wpre@\<gamma>#wsfx"}. \<close>
    proof -
      \<comment> \<open> This is done by putting together the transitions and using the extensibility of string rewrite systems, i.e. that we can still do a rewrite step if we add context \<close>
      from C1 have "wpre@(\<gamma>#wsfx) \<hookrightarrow>\<^bsub>aps\<^esub> (wps@[pp])@(\<gamma>#wsfx) \<in> trcl (tr (rules M))" by (fast intro: srs_ext)
      hence "wpre@\<gamma>#wsfx \<hookrightarrow>\<^bsub>aps\<^esub> wps@([pp,\<gamma>])@wsfx \<in> trcl (tr (rules M))" by simp
      moreover from RCONS have "wps@([pp,\<gamma>])@wsfx \<hookrightarrow>\<^bsub>[aa]\<^esub> wps@cc'@wsfx \<in> trcl (tr (rules M))" by (fast intro: tr.rewrite trcl_one_elem)
      hence "wps@([pp,\<gamma>])@wsfx \<hookrightarrow>\<^bsub>[aa]\<^esub> (wps@cc')@wsfx \<in> trcl (tr (rules M))" by simp
      moreover note C2
      ultimately have "wpre@\<gamma>#wsfx \<hookrightarrow>\<^bsub>aps@[aa]@as\<^esub> ws@[p] \<in> trcl (tr (rules M))" by (fast intro: trcl_concat)
      thus ?thesis by fast
    qed
    with C2 show "\<exists>ws as. s0 A \<hookrightarrow>\<^bsub>ws\<^esub> q \<in> trclA A \<and> wpre @ \<gamma> # wsfx \<hookrightarrow>\<^bsub>as\<^esub> ws @ [p] \<in> trcl (tr (rules M))" by fast \<comment> \<open> Finally, we have the proposition for the configuration @{term "wpre@\<gamma>#wsfx"}, 
      that contains the added rule @{term "s\<hookrightarrow>\<^bsub>\<gamma>\<^esub>s'"} one time more \<close>
  qed
qed  
  





text \<open> Helper lemma to clarify some subgoal in the precision proof: \<close>
lemma trclAD_delta_update_inv: "trclAD (A\<lparr>\<delta>:=X\<rparr>) D = trclAD A D" by (simp add: trclAD_by_trcl')

text \<open> The precision is proved as an invariant of the saturation algorithm: \<close>
theorem (in MFSM) precise_inv: 
  shows "is_inv (ps_R M A) (\<delta> A) (\<lambda>D. (lang (A\<lparr>\<delta>:=D\<rparr>) \<subseteq> pre\<^sup>* (rules M) A) \<and> (\<forall>P'. is_inv (ps_R M A) (\<delta> A) P' \<longrightarrow> P' D))"
proof -  

  {
    fix D1 D2 w f
    assume IH: "{w. \<exists>f\<in>F A. s0 A \<hookrightarrow>\<^bsub>w\<^esub> f \<in> trclAD A D1} \<subseteq> pre\<^sup>* (rules M) A" \<comment> \<open> By induction hypothesis, we know @{term "lang (A\<lparr>\<delta>:=D1\<rparr>)\<subseteq>pre\<^sup>* (rules M) A"} \<close>
    assume SUCC: "(D1,D2)\<in>ps_R M A" \<comment> \<open> We regard a successor @{term "D2"} of @{term "D1"} w.r.t. @{term "ps_R M A"} \<close>
    assume P1: "f\<in>F A" and P2: "s0 A \<hookrightarrow>\<^bsub>w\<^esub> f \<in> trclAD A D2" \<comment> \<open> And a word @{term "w\<in>lang (A\<lparr>\<delta>:=D2\<rparr>)"} \<close>
    assume USE_INV: "\<And>P'. is_inv (ps_R M A) (\<delta> A) P' \<Longrightarrow> P' D1" \<comment> \<open> For the proof, we can use any known invariants \<close>
  
    from SUCC obtain \<gamma> s' p a c' q where ADD: "insert (sp A q p,\<gamma>,s') D1 = D2 \<and> (sp A q p,\<gamma>,s')\<notin>D1" and 
                                             RCONS: "([p,\<gamma>],a,c')\<in>rules M \<and> (q,c',s')\<in>trclAD A D1 \<and> q\<in>cstates A \<and> p\<in>csyms M \<and> a\<in>labels M \<and> \<gamma>\<in>ssyms M"
      by (blast elim!: ps_R_elims_adv) \<comment> \<open> Because of @{thm SUCC}, we obtain @{term "D2"} by adding a (new) transition @{term "(sp A q p,\<gamma>,s')"} to @{term "D1"}, 
        such that there is a rule @{term "[p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c'"} and we have @{term "(q,c',s')\<in>trclAD A D1"} \<close>
    from P2 ADD have P2': "s0 A \<hookrightarrow>\<^bsub>w\<^esub> f \<in> trclAD A (insert (sp A q p \<hookrightarrow>\<^bsub>\<gamma>\<^esub> s') D1)" by simp
    from SUCC have SS: "D1 \<subseteq> ps_upper M A" by (blast dest: ps_R_dom_below) \<comment> \<open>We know, that the intermediate value is below the upper saturation bound\<close>
    from USE_INV have A2: "\<delta> A \<subseteq> D1" by (blast intro: ps_R_above_inv) \<comment> \<open>... and above the start value\<close>
    from SS USE_INV sp_property have SP_PROP: "(\<forall> w . \<forall>p\<in>csyms M. \<forall>q\<in>cstates A. (s0 A,w,sp A q p)\<in>trclAD A D1 \<longrightarrow> (\<exists>ws as. (s0 A,ws,q)\<in>trclA A \<and> (w,as,ws@[p])\<in>trcl (tr (rules M))))" 
      by blast \<comment> \<open> And we have just shown @{thm [source] sp_property}, that tells us that each configuration @{term w} that leads to a state @{term "sp A q p"}, 
        can be rewritten to a configuration in the initial automaton, that uses @{term p} as its last transition \<close>
  
    have "w \<in> pre\<^sup>* (rules M) A" using P2' \<comment> \<open> We have to show that the word @{term w} from the new automaton is also in @{term "pre\<^sup>* (rules M) A"}. 
      We show this by induction on how often the new transition is used by @{term w} \<close>
    proof (rule ins_trans_induct)
      fix wa assume "(s0 A, wa, f) \<in> trclAD A D1" \<comment> \<open> Base case: @{term w} does not use the new transition at all \<close>
      with IH P1 show "wa \<in> pre\<^sup>* (rules M) A" by (fast) \<comment> \<open> The proposition follows directly from the outer (invariant) induction and can be solved automatically \<close>
    next
      fix wpre wsfx \<comment> \<open>Step case\<close>
      assume IP1: "(s0 A, wpre, sp A q p) \<in> trclAD A D1" \<comment> \<open> We assume that we have a prefix @{term wpre} leading to the start state @{term s} of the new transition and not using the new transition \<close>
      assume IP2: "(s', wsfx, f) \<in> trclAD A (insert (sp A q p, \<gamma>, s') D1)" \<comment> \<open> We also have a suffix from the end state @{term s'} to @{term f} \<close>
      assume IIH: "!!wh. (s0 A, wh, s') \<in> trclAD A D1 \<Longrightarrow> wh @ wsfx \<in> pre\<^sup>* (rules M) A" \<comment> \<open> And we assume that our proposition is valid for prefixes @{term wh} that do not use the new transition \<close>
      \<comment> \<open> We have to show that the proposition is valid for @{term "wpre@\<gamma>#wsfx"} \<close>
      from IP1 SP_PROP RCONS obtain wpres apres where SPP: "(s0 A,wpres,q)\<in>trclA A \<and> wpre \<hookrightarrow>\<^bsub>apres\<^esub> wpres@[p] \<in> trcl (tr (rules M))" by (blast) \<comment> \<open> We can apply @{thm [source] SP_PROP}, 
        to find a successor @{term "wpres@[p]"} of @{term "wpre"} in the initial automata \<close>
      with A2 have "s0 A \<hookrightarrow>\<^bsub>wpres\<^esub> q \<in> trclAD A D1" by (blast dest: trclAD_mono) \<comment> \<open> @{term "wpres"} can also be read by D1 because of @{thm A2} \<close>
      with RCONS have "s0 A \<hookrightarrow>\<^bsub>wpres@c'\<^esub> s' \<in> trclAD A D1" by (fast intro: trclAD_concat) \<comment> \<open> Altogether we get a prefix @{term "wpres@c'"} that leads to @{term "s'"}, without using the added transition \<close>
      with IIH have "(wpres@c')@wsfx \<in>pre_star (rules M) A" by fast \<comment> \<open> We can apply the induction hypothesis \<close>
      then obtain as wo where C1: "wpres@c'@wsfx \<hookrightarrow>\<^bsub>as\<^esub> wo \<in> trcl (tr (rules M)) \<and> wo\<in>lang A" by (auto elim!: pre_star_altE) \<comment> \<open> And find that there is a @{term "wo"} in the original automata, 
        that is a successor of @{term "wpres@c'@wsfx"} \<close>
      moreover have "\<exists>as. wpre@\<gamma>#wsfx \<hookrightarrow>\<^bsub>as\<^esub> wo \<in> trcl (tr (rules M))" \<comment> \<open> Next we show that @{term "wo"} is a successor of @{term "wpre@\<gamma>#wsfx"} \<close>
      proof -
        from SPP have "wpre@\<gamma>#wsfx \<hookrightarrow>\<^bsub>apres\<^esub> (wpres@[p])@\<gamma>#wsfx \<in> trcl (tr (rules M))" by (fast intro: srs_ext)
        hence "wpre@\<gamma>#wsfx \<hookrightarrow>\<^bsub>apres\<^esub> wpres@([p,\<gamma>])@wsfx \<in> trcl (tr (rules M))" by simp
        moreover from RCONS have "wpres@([p,\<gamma>])@wsfx \<hookrightarrow>\<^bsub>[a]\<^esub> wpres@c'@wsfx \<in> trcl (tr (rules M))" by (fast intro: tr.rewrite trcl_one_elem)
        moreover note C1
        ultimately show ?thesis by (fast intro: trcl_concat)
      qed
      ultimately show "wpre @ \<gamma> # wsfx \<in> pre\<^sup>* (rules M) A" by (fast intro: pre_star_altI) \<comment> \<open> And altogether we have @{term "wpre@\<gamma>#wsfx \<in> pre\<^sup>* (rules M) A"} \<close>
    qed
  } note A=this

  show ?thesis  
    apply (rule inv_useI)
    subgoal by (auto intro: pre_refl) \<comment> \<open> The base case is solved automatically, it follows from the reflexivity of @{term "pre\<^sup>*"}. \<close>
    subgoal for D s'
      unfolding lang_def langs_def
      using A by (fastforce simp add: trclAD_delta_update_inv) 
    done      
qed

text \<open> As precision is an invariant of the saturation algorithm, and is trivial for the case of an already saturated initial automata, the result of the saturation algorithm is precise \<close>
corollary (in MFSM) precise: "\<lbrakk>(\<delta> A,D)\<in>ndet_algo (ps_R M A); x\<in>lang (A\<lparr> \<delta>:=D \<rparr>)\<rbrakk> \<Longrightarrow> x\<in>pre_star (rules M) A"
  by (auto elim!: ndet_algoE dest: inv intro: precise_inv pre_refl)

text \<open> And finally we get correctness of the algorithm, with no restrictions on valid states \<close>
theorem (in MFSM) correct: "\<lbrakk>(\<delta> A,D)\<in>ndet_algo (ps_R M A)\<rbrakk> \<Longrightarrow> lang (A\<lparr> \<delta>:=D \<rparr>) = pre_star (rules M) A" by (auto intro: precise sound)

text \<open>
  So the main results of this theory are, that the algorithm is defined for every possible initial automata 
    
    @{thm MFSM.total} 

  and returns the correct result
  
    @{thm MFSM.correct}

\<close>

text \<open> We could also prove determination, i.e. the terminating state is uniquely determined by the initial state (though there may be many ways to get there). This is not really needed here, because for correctness, we do not
  look at the structure of the final automaton, but just at its language. The language of the final automaton is determined, as implied by @{thm [source] MFSM.correct}. \<close>

end
