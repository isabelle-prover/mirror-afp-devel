(*  Title:       String rewrite systems
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open> String rewrite systems \<close>

theory SRS
imports DPN_Setup
begin

text \<open>
  This formalizes systems of labelled string rewrite rules and the labelled transition systems induced by them. 
  DPNs are special string rewrite systems.
\<close>

subsection \<open> Definitions \<close>
type_synonym ('c,'l) rewrite_rule = "'c list \<times> 'l \<times> 'c list" 
type_synonym ('c,'l) SRS = "('c,'l) rewrite_rule set"

syntax
  syn_rew_rule :: "'c list \<Rightarrow> 'l \<Rightarrow> 'c list \<Rightarrow> ('c,'l) rewrite_rule" ("_ \<hookrightarrow>\<^bsub>_\<^esub> _" [51,51,51] 51)

translations (* FIXME: This translates all triples, regardless of their type. *)
  "s \<hookrightarrow>\<^bsub>a\<^esub> s'" => "(s,a,s')" 

text \<open> A (labelled) rewrite rule @{term "s \<hookrightarrow>\<^bsub>a\<^esub> s'"} consists of the left side @{text s}, the label @{text a} and the right side @{text s'}. Intuitively, it means that a substring @{text s} can be 
  rewritten to @{text s'} by an @{text a}-step. A string rewrite system is a set of labelled rewrite rules \<close>


subsection \<open> Induced Labelled Transition System \<close>
text \<open> A string rewrite systems induces a labelled transition system on strings by rewriting substrings according to the rules \<close>

inductive_set tr :: "('c,'l) SRS \<Rightarrow> ('c list, 'l) LTS" for S 
where
  rewrite: "(s \<hookrightarrow>\<^bsub>a\<^esub> s') \<in> S \<Longrightarrow> (ep@s@es,a,ep@s'@es) \<in> tr S"


subsection \<open> Properties of the induced LTS \<close>
text \<open> Adding characters at the start or end of a state does not influence the capability of making a transition \<close>
lemma srs_ext_s: "(s,a,s')\<in>tr S \<Longrightarrow> (wp@s@ws,a,wp@s'@ws)\<in>tr S" proof -
  assume "(s,a,s')\<in>tr S"
  then obtain ep es r r' where "s=ep@r@es \<and> s'=ep@r'@es \<and> (r,a,r')\<in>S" by (fast elim: tr.cases)
  moreover hence "((wp@ep)@r@(es@ws),a,(wp@ep)@r'@(es@ws)) \<in> tr S" by (fast intro: tr.rewrite)
  ultimately show ?thesis by auto
qed  

lemma srs_ext_both: "(s,w,s')\<in>trcl (tr S) \<Longrightarrow> (wp@s@ws,w,wp@s'@ws)\<in>trcl (tr S)"
  apply (induct s w s' rule: trcl.induct)
  apply (simp)
  apply (subgoal_tac "wp @ c @ ws \<hookrightarrow>\<^bsub>a\<^esub> wp @ c' @ ws \<in> tr S")
  apply (auto intro: srs_ext_s)
  done  
  
corollary srs_ext_cons: "(s,w,s')\<in>trcl (tr S) \<Longrightarrow> (e#s,w,e#s')\<in>trcl (tr S)" by (rule srs_ext_both[where wp="[e]" and ws="[]", simplified])
corollary srs_ext_pre: "(s,w,s')\<in>trcl (tr S) \<Longrightarrow> (wp@s,w,wp@s')\<in>trcl (tr S)" by (rule srs_ext_both[where ws="[]", simplified])
corollary srs_ext_post: "(s,w,s')\<in>trcl (tr S) \<Longrightarrow> (s@ws,w,s'@ws)\<in>trcl (tr S)" by (rule srs_ext_both[where wp="[]", simplified])

lemmas srs_ext = srs_ext_both srs_ext_pre srs_ext_post


end
