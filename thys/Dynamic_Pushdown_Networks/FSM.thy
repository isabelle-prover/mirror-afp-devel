(*  Title:       Finite state machines
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open> Finite state machines \<close>
theory FSM
imports DPN_Setup
begin

text \<open>
  This theory models nondeterministic finite state machines with explicit set of states and alphabet. @{text \<epsilon>}-transitions are not supported.
\<close>

subsection \<open> Definitions \<close>

record ('s,'a) FSM_rec =
  Q :: "'s set" \<comment> \<open>The set of states\<close>
  \<Sigma> :: "'a set" \<comment> \<open>The alphabet\<close>
  \<delta> :: "('s, 'a) LTS" \<comment> \<open>The transition relation\<close>
  s0 :: "'s" \<comment> \<open>The initial state\<close>
  F :: "'s set" \<comment> \<open>The set of final states\<close>

locale FSM = 
  fixes A
  assumes delta_cons: "(q,l,q')\<in>\<delta> A \<Longrightarrow> q\<in>Q A \<and> l\<in>\<Sigma> A \<and> q'\<in>Q A" \<comment> \<open>The transition relation is consistent with the set of states and the alphabet\<close>
  assumes s0_cons: "s0 A \<in> Q A" \<comment> \<open>The initial state is a state\<close>
  assumes F_cons: "F A \<subseteq> Q A" \<comment> \<open>The final states are states\<close>
  assumes finite_states: "finite (Q A)" \<comment> \<open>The set of states is finite\<close>
  assumes finite_alphabet: "finite (\<Sigma> A)" \<comment> \<open>The alphabet is finite\<close>

subsection \<open> Basic properties \<close>
lemma (in FSM) finite_delta_dom: "finite (Q A \<times> \<Sigma> A \<times> Q A)" proof -
  from finite_states finite_alphabet finite_cartesian_product[of "\<Sigma> A" "Q A"] have "finite (\<Sigma> A \<times> Q A)" by fast
  with finite_states finite_cartesian_product[of "Q A" "\<Sigma> A \<times> Q A"] show "finite (Q A \<times> \<Sigma> A \<times> Q A)" by fast
qed

lemma (in FSM) finite_delta: "finite (\<delta> A)" proof -
  have "\<delta> A \<subseteq> Q A \<times> \<Sigma> A \<times> Q A" by (auto simp add: delta_cons)
  with finite_delta_dom show ?thesis by (simp add: finite_subset)
qed

subsection \<open>Constructing FSMs\<close>

definition "fsm_empty s\<^sub>0 \<equiv> \<lparr> Q={s\<^sub>0}, \<Sigma>={}, \<delta>={}, s0=s\<^sub>0, F={} \<rparr>"
definition "fsm_add_F s fsm \<equiv> fsm\<lparr> Q:=insert s (Q fsm), F:=insert s (F fsm) \<rparr>"
definition "fsm_add_tr q a q' fsm \<equiv> fsm\<lparr> Q:={q,q'} \<union> (Q fsm), \<Sigma>:=insert a (\<Sigma> fsm), \<delta> := insert (q,a,q') (\<delta> fsm) \<rparr>"

lemma fsm_empty_invar[simp]: "FSM (fsm_empty s)"
  apply unfold_locales unfolding fsm_empty_def by auto
  
lemma fsm_add_F_invar[simp]: assumes "FSM fsm" shows "FSM (fsm_add_F s fsm)"  
proof -
  interpret FSM fsm by fact
  show ?thesis
    apply unfold_locales
    unfolding fsm_add_F_def
    using delta_cons s0_cons F_cons finite_states finite_alphabet
    by auto
qed

lemma fsm_add_tr_invar[simp]: assumes "FSM fsm" shows "FSM (fsm_add_tr q a q' fsm)"  
proof -
  interpret FSM fsm by fact
  show ?thesis
    apply unfold_locales
    unfolding fsm_add_tr_def
    using delta_cons s0_cons F_cons finite_states finite_alphabet
    by auto
qed



subsection \<open> Reflexive, transitive closure of transition relation \<close>

text \<open> Reflexive transitive closure on restricted domain \<close>

inductive_set trclAD :: "('s,'a,'c) FSM_rec_scheme \<Rightarrow> ('s,'a) LTS \<Rightarrow> ('s,'a list) LTS" 
for A D
where
  empty[simp]: "s\<in>Q A \<Longrightarrow> (s,[],s)\<in>trclAD A D" |
  cons[simp]: "\<lbrakk>(s,e,s')\<in>D; s\<in>Q A; e\<in>\<Sigma> A; (s',w,s'')\<in>trclAD A D\<rbrakk> \<Longrightarrow> (s,e#w,s'')\<in>trclAD A D"

abbreviation "trclA A == trclAD A (\<delta> A)"
(*syntax trclA :: "('s,'a,'c) FSM_rec_scheme \<Rightarrow> ('s,'a list) LTS"
translations "trclA A" => "trclAD A (\<delta> A)"*)

lemma trclAD_empty_cons[simp]: "(c,[],c')\<in>trclAD A D \<Longrightarrow> c=c'" by (auto elim: trclAD.cases)
lemma trclAD_single: "(c,[a],c') \<in> trclAD A D \<Longrightarrow> (c,a,c') \<in> D" by (auto elim: trclAD.cases)
lemma trclAD_elems: "(c,w,c')\<in>trclAD A D \<Longrightarrow> c\<in>Q A \<and> w\<in>lists (\<Sigma> A) \<and> c'\<in>Q A" by (erule trclAD.induct, auto)
lemma trclAD_one_elem: "\<lbrakk>c\<in>Q A; e\<in>\<Sigma> A; c'\<in>Q A; (c,e,c')\<in>D\<rbrakk> \<Longrightarrow> (c,[e],c')\<in>trclAD A D" by auto


lemma trclAD_uncons: "(c,a#w,c')\<in>trclAD A D \<Longrightarrow> \<exists>ch . (c,a,ch)\<in>D \<and> (ch,w,c') \<in> trclAD A D \<and> c\<in>Q A \<and> a\<in>\<Sigma> A" 
  by (auto elim: trclAD.cases)

lemma trclAD_concat: "!! c . \<lbrakk> (c,w1,c')\<in>trclAD A D; (c',w2,c'')\<in>trclAD A D \<rbrakk> \<Longrightarrow> (c,w1@w2,c'')\<in>trclAD A D" 
proof (induct w1)
  case Nil thus ?case by (subgoal_tac "c=c'") auto
next
  case (Cons a w) thus ?case by (auto dest: trclAD_uncons)
qed    
 
lemma trclAD_unconcat: "!! c . (c,w1@w2,c')\<in>trclAD A D \<Longrightarrow> \<exists>ch . (c,w1,ch)\<in>trclAD A D \<and> (ch,w2,c')\<in>trclAD A D" proof (induct w1)
  case Nil hence "(c,[],c)\<in>trclAD A D \<and> (c,w2,c')\<in>trclAD A D" by (auto dest: trclAD_elems)
  thus ?case by fast
next
  case (Cons a w1) note IHP = this
  hence "(c,a#(w1@w2),c')\<in>trclAD A D" by simp (* Auto/fast/blast do not get the point _#(_@_) = (_#_)@_ in next step, so making it explicit *)
  with trclAD_uncons obtain chh where "(c,a,chh)\<in>D \<and> (chh,w1@w2,c')\<in>trclAD A D \<and> c\<in>Q A \<and> a\<in>\<Sigma> A" by fast
  moreover with IHP obtain ch where "(chh,w1,ch)\<in>trclAD A D \<and> (ch,w2,c')\<in>trclAD A D" by fast
  ultimately have "(c,a#w1,ch)\<in>trclAD A D \<and> (ch,w2,c')\<in>trclAD A D" by auto
  thus ?case by fast
qed

lemma trclAD_eq: "\<lbrakk>Q A = Q A'; \<Sigma> A = \<Sigma> A'\<rbrakk> \<Longrightarrow> trclAD A D = trclAD A' D" 
  apply (safe)
  subgoal by (erule trclAD.induct) auto
  subgoal by (erule trclAD.induct) auto
  done

lemma trclAD_mono: "D\<subseteq>D' \<Longrightarrow> trclAD A D \<subseteq> trclAD A D'"
  apply (clarsimp)
  apply (erule trclAD.induct)
  apply auto
  done

lemma trclAD_mono_adv: "\<lbrakk>D\<subseteq>D'; Q A = Q A'; \<Sigma> A = \<Sigma> A'\<rbrakk> \<Longrightarrow> trclAD A D \<subseteq> trclAD A' D'" by (subgoal_tac "trclAD A D = trclAD A' D") (auto dest: trclAD_eq trclAD_mono)


subsubsection \<open> Relation of @{term trclAD} and @{term LTS.trcl} \<close>
lemma trclAD_by_trcl1: "trclAD A D \<subseteq> (trcl (D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)) \<inter> (Q A \<times> lists (\<Sigma> A) \<times> Q A))"
  by (auto 0 3 dest: trclAD_elems elim: trclAD.induct simp: trclAD_elems intro: trcl.cons)

lemma trclAD_by_trcl2: "(trcl (D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)) \<inter> (Q A \<times> lists (\<Sigma> A) \<times> Q A)) \<subseteq> trclAD A D " proof -
  { fix c
    have "!! s s' . \<lbrakk>(s, c, s') \<in> trcl (D \<inter> Q A \<times> \<Sigma> A \<times> Q A); s\<in>Q A; s'\<in>Q A; c\<in>lists (\<Sigma> A)\<rbrakk> \<Longrightarrow> (s,c,s')\<in>trclAD A D" proof (induct c)
      case Nil thus ?case by (auto dest: trcl_empty_cons)
    next
      case (Cons e w) note IHP=this
      then obtain sh where SPLIT: "(s,e,sh)\<in>(D \<inter> Q A \<times> \<Sigma> A \<times> Q A) \<and> (sh,w,s')\<in>trcl (D \<inter> Q A \<times> \<Sigma> A \<times> Q A)" by (fast dest: trcl_uncons)
      hence "(sh,w,s')\<in>trcl (D \<inter> Q A \<times> \<Sigma> A \<times> Q A) \<inter> (Q A \<times> lists (\<Sigma> A) \<times> Q A)" by (auto elim!: trcl_structE)
      hence "(sh,w,s')\<in>trclAD A D" by (blast intro: IHP)
      with SPLIT show ?case by auto
    qed
  }
  thus ?thesis by (auto)
qed
    
lemma trclAD_by_trcl: "trclAD A D = (trcl (D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)) \<inter> (Q A \<times> lists (\<Sigma> A) \<times> Q A))" 
  apply (rule equalityI)
  apply (rule trclAD_by_trcl1)
  apply (rule trclAD_by_trcl2)
  done

lemma trclAD_by_trcl': "trclAD A D = (trcl (D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)) \<inter> (Q A \<times> UNIV \<times> UNIV))"
  by (auto iff add: trclAD_by_trcl elim!: trcl_structE)

lemma trclAD_by_trcl'': "\<lbrakk> D\<subseteq>Q A \<times> \<Sigma> A \<times> Q A \<rbrakk> \<Longrightarrow> trclAD A D = trcl D \<inter> (Q A \<times> UNIV \<times> UNIV)"
  using trclAD_by_trcl'[of A D] by (simp add: Int_absorb2)

lemma trclAD_subset_trcl: "trclAD A D \<subseteq> trcl (D)" proof -
  have "trclAD A D \<subseteq> (trcl (D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)))" by (auto simp add: trclAD_by_trcl)
  also with trcl_mono[of "D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)" D] have "\<dots> \<subseteq> trcl D" by auto
  finally show ?thesis .
qed

subsection \<open> Language of a FSM \<close>
  

definition "langs A s == { w . (\<exists> f\<in>(F A) . (s,w,f) \<in> trclA A) }"
definition "lang A == langs A (s0 A)"

lemma langs_alt_def: "(w\<in>langs A s) == (\<exists>f . f\<in>F A & (s,w,f) \<in> trclA A)" by (intro eq_reflection, unfold langs_def, auto)

subsection \<open> Example: Product automaton \<close>

definition "prod_fsm A1 A2 == \<lparr> Q=Q A1 \<times> Q A2, \<Sigma>=\<Sigma> A1 \<inter> \<Sigma> A2, \<delta> = { ((s,t),a,(s',t')) . (s,a,s')\<in>\<delta> A1 \<and> (t,a,t')\<in>\<delta> A2 }, s0=(s0 A1,s0 A2), F = {(s,t) . s\<in>F A1 \<and> t\<in>F A2} \<rparr>"

lemma prod_inter_1: "!! s s' f f' . ((s,s'),w,(f,f')) \<in> trclA (prod_fsm A A') \<Longrightarrow> (s,w,f) \<in> trclA A \<and> (s',w,f') \<in> trclA A'" proof (induct w) 
  case Nil note P=this 
  moreover hence "s=f \<and> s'=f'" by (fast dest: trclAD_empty_cons)
  moreover from P have "s\<in>Q A \<and> s'\<in>Q A'" by (unfold prod_fsm_def, auto dest: trclAD_elems)
  ultimately show ?case by (auto)
next
  case (Cons e w)
  note IHP=this
  then obtain m m' where I: "((s,s'),e,(m,m')) \<in> \<delta> (prod_fsm A A') \<and> (s,s')\<in>Q (prod_fsm A A') \<and> e\<in>\<Sigma> (prod_fsm A A') \<and> ((m,m'),w,(f,f'))\<in>trclA (prod_fsm A A')" by (fast dest: trclAD_uncons)
  hence "(s,e,m)\<in>\<delta> A \<and> (s',e,m')\<in>\<delta> A' \<and> s\<in>Q A \<and> s'\<in>Q A' \<and> e\<in>\<Sigma> A \<and> e\<in>\<Sigma> A'" by (unfold prod_fsm_def, simp)
  moreover from I IHP have "(m,w,f)\<in>trclA A \<and> (m',w,f')\<in>trclA A'" by auto
  ultimately show ?case by auto
qed
  
lemma prod_inter_2: "!! s s' f f' . (s,w,f) \<in> trclA A \<and> (s',w,f') \<in> trclA A' \<Longrightarrow> ((s,s'),w,(f,f')) \<in> trclA (prod_fsm A A')" proof (induct w)
  case Nil note P=this
  moreover hence "s=f \<and> s'=f'" by (fast dest: trclAD_empty_cons)
  moreover from P have "(s,s')\<in>Q (prod_fsm A A')" by (unfold prod_fsm_def, auto dest: trclAD_elems)
  ultimately show ?case by simp
next
  case (Cons e w)
  note IHP=this
  then obtain m m' where I: "(s,e,m)\<in>\<delta> A \<and> (m,w,f)\<in>trclA A \<and> (s',e,m')\<in>\<delta> A' \<and> (m',w,f')\<in>trclA A' \<and> s\<in>Q A \<and> s'\<in>Q A' \<and> e\<in>\<Sigma> A \<and> e\<in>\<Sigma> A'" by (fast dest: trclAD_uncons)
  hence "((s,s'),e,(m,m')) \<in> \<delta> (prod_fsm A A') \<and> (s,s')\<in>Q (prod_fsm A A') \<and> e\<in>\<Sigma> (prod_fsm A A')" by (unfold prod_fsm_def, simp)
  moreover from I IHP have "((m,m'),w,(f,f')) \<in> trclA (prod_fsm A A')" by auto
  ultimately show ?case by auto
qed
  
lemma prod_F: "(a,b)\<in>F (prod_fsm A B) = (a\<in>F A \<and> b\<in>F B)" by (unfold prod_fsm_def, auto)
lemma prod_FI: "\<lbrakk>a\<in>F A; b\<in>F B\<rbrakk> \<Longrightarrow> (a,b)\<in>F (prod_fsm A B)" by (unfold prod_fsm_def, auto)

lemma prod_fsm_langs: "langs (prod_fsm A B) (s,t) = langs A s \<inter> langs B t"
  apply (unfold langs_def)
  apply (insert prod_inter_1 prod_F)
  apply (fast intro: prod_inter_2 prod_FI)
done

lemma prod_FSM_intro: "FSM A1 \<Longrightarrow> FSM A2 \<Longrightarrow> FSM (prod_fsm A1 A2)" by (rule FSM.intro) (auto simp add: FSM_def prod_fsm_def)


end
