(*  Title:      JinjaThreads/J/JWellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory J/JWellForm by Tobias Nipkow
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
apply(simp)
apply(erule WT_contains_addr)
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

lemma sub_Thread_sees_run:
  assumes wf: "wf_J_prog P"
  and PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
  and isclassThread: "is_class P Thread"
  shows "\<exists>D body. P \<turnstile> C sees run: []\<rightarrow>Void = ([], body) in D"
proof -
  from isclassThread obtain T' fsT MsT where classT: "class P Thread = \<lfloor>(T', fsT, MsT)\<rfloor>"
    by(auto simp: is_class_def)
  with wf have wfcThread: "wf_cdecl wf_J_mdecl P (Thread, T', fsT, MsT)"
    by(auto dest: map_of_is_SomeD bspec simp add: wf_prog_def class_def)
  then obtain mrunT where runThread: "(run, [], Void, mrunT) \<in> set MsT"
    by(auto simp add: wf_cdecl_def)
  moreover have "\<exists>MmT. P \<turnstile> Thread sees_methods MmT \<and>
                       (\<forall>(M,Ts,T,m) \<in> set MsT. MmT M = Some((Ts,T,m),Thread))"
    by(rule mdecls_visible[OF wf isclassThread classT])
  then obtain MmT where ThreadMmT: "P \<turnstile> Thread sees_methods MmT"
    and MmT: "\<forall>(M,Ts,T,m) \<in> set MsT. MmT M = Some((Ts,T,m),Thread)"
    by blast
  ultimately obtain pnsT bodyT
    where "MmT run = \<lfloor>(([], Void, pnsT, bodyT), Thread)\<rfloor>"
    by(fastsimp)
  with ThreadMmT have Tseesrun: "P \<turnstile> Thread sees run: []\<rightarrow>Void = (pnsT, bodyT) in Thread"
    by(auto simp add: Method_def)
  have "\<exists>D' Ts' T' m'. P \<turnstile> C sees run: Ts'\<rightarrow>T' = m' in D' \<and>
                       P \<turnstile> [] [\<le>] Ts' \<and> P \<turnstile> T' \<le> Void"
    by(rule sees_method_mono[OF PCThread wf Tseesrun])
  then obtain D pnsD bodyD
    where Cseesrun: "P \<turnstile> C sees run: []\<rightarrow>Void = (pnsD, bodyD) in D" by(auto)
  then obtain D' fsD MsD
    where classD: "class P D = \<lfloor>(D', fsD, MsD)\<rfloor>"
    and runD: "map_of MsD run = \<lfloor>([], Void, pnsD, bodyD)\<rfloor>"
    by(auto dest!: visible_method_exists)
  with wf have "pnsD = []"
    apply(clarsimp simp: wf_prog_def wf_cdecl_def wf_mdecl_def class_def)
    apply(drule bspec, erule map_of_is_SomeD, clarsimp)
    apply(drule bspec, erule map_of_is_SomeD, clarsimp)
    done
  with Cseesrun show ?thesis by auto
qed

end
