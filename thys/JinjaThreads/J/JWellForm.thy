(*  Title:      JinjaThreads/J/JWellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Well-formedness Constraints} *}

theory JWellForm
imports "../Common/WellForm" WWellForm WellType DefAss
begin

constdefs
  wf_J_mdecl :: "J_prog \<Rightarrow> cname \<Rightarrow> J_mb mdecl \<Rightarrow> bool"
  "wf_J_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  (\<exists>T'. P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>"

lemma wf_J_mdecl[simp]:
  "wf_J_mdecl P C (M,Ts,T,pns,body) \<equiv>
  (length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  (\<exists>T'. P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>)"
(*<*)by(simp add:wf_J_mdecl_def)(*>*)


syntax 
  wf_J_prog :: "J_prog \<Rightarrow> bool"
translations
  "wf_J_prog"  ==  "wf_prog wf_J_mdecl"

lemma wf_J_prog_wf_J_mdecl:
  "\<lbrakk> wf_J_prog P; (C, D, fds, mths) \<in> set P; jmdcl \<in> set mths \<rbrakk>
  \<Longrightarrow> wf_J_mdecl P C jmdcl"
(*<*)
apply (simp add: wf_prog_def)
apply (simp add: wf_cdecl_def)
apply (erule conjE)+
apply (drule bspec, assumption)
apply simp
apply (erule conjE)+
apply (drule bspec, assumption)
apply (simp add: wf_mdecl_def split_beta)
done
(*>*)



lemma wf_mdecl_wwf_mdecl: "wf_J_mdecl P C Md \<Longrightarrow> wwf_J_mdecl P C Md"
(*<*)
apply(clarsimp simp add: wwf_J_mdecl_def)
apply(frule WT_fv)
apply(auto)
done

lemma wf_mdecl_mono: "\<lbrakk> wf_mdecl wf_md1 P C Md; wf_md1 P C Md \<Longrightarrow> wf_md2 P C Md \<rbrakk> \<Longrightarrow> wf_mdecl wf_md2 P C Md"
apply(clarsimp simp add:  wf_mdecl_def)
done

lemma wf_prog_wwf_prog: "wf_J_prog P \<Longrightarrow> wwf_J_prog P"
(*<*)
apply(clarsimp simp add:wf_prog_def wf_cdecl_def)
apply(drule bspec, assumption)
apply(clarsimp)
apply(drule bspec, assumption)
apply(erule wf_mdecl_mono)
apply(erule wf_mdecl_wwf_mdecl)
done
(*>*)


end
