(*  Title:      JinjaDCI/J/JWellForm.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/JWellForm.thy by Tobias Nipkow
*)

section \<open> Well-formedness Constraints \<close>

theory JWellForm
imports "../Common/WellForm" WWellForm WellType DefAss
begin

definition wf_J_mdecl :: "J_prog \<Rightarrow> cname \<Rightarrow> J_mb mdecl \<Rightarrow> bool"
where
  "wf_J_mdecl P C  \<equiv>  \<lambda>(M,b,Ts,T,(pns,body)).
  length Ts = length pns \<and>
  distinct pns \<and>
  \<not>sub_RI body \<and>
 (case b of
    NonStatic \<Rightarrow> this \<notin> set pns \<and>
        (\<exists>T'. P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
        \<D> body \<lfloor>{this} \<union> set pns\<rfloor>
  | Static \<Rightarrow> (\<exists>T'. P,[pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
        \<D> body \<lfloor>set pns\<rfloor>)"

lemma wf_J_mdecl_NonStatic[simp]:
  "wf_J_mdecl P C (M,NonStatic,Ts,T,pns,body) \<equiv>
  (length Ts = length pns \<and>
  distinct pns \<and>
  \<not>sub_RI body \<and>
  this \<notin> set pns \<and>
  (\<exists>T'. P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>)"
(*<*)by(simp add:wf_J_mdecl_def)(*>*)

lemma wf_J_mdecl_Static[simp]:
  "wf_J_mdecl P C (M,Static,Ts,T,pns,body) \<equiv>
  (length Ts = length pns \<and>
  distinct pns \<and>
  \<not>sub_RI body \<and>
  (\<exists>T'. P,[pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
  \<D> body \<lfloor>set pns\<rfloor>)"
(*<*)by(simp add:wf_J_mdecl_def)(*>*)


abbreviation
  wf_J_prog :: "J_prog \<Rightarrow> bool" where
  "wf_J_prog == wf_prog wf_J_mdecl"

lemma wf_J_prog_wf_J_mdecl:
  "\<lbrakk> wf_J_prog P; (C, D, fds, mths) \<in> set P; jmdcl \<in> set mths \<rbrakk>
  \<Longrightarrow> wf_J_mdecl P C jmdcl"
(*<*)by(fastforce simp: wf_prog_def wf_cdecl_def wf_mdecl_def)(*>*)
                                  
lemma wf_mdecl_wwf_mdecl: "wf_J_mdecl P C Md \<Longrightarrow> wwf_J_mdecl P C Md"
(*<*)
proof -
  obtain M b Ts T pns body where "Md = (M, b, Ts, T, pns, body)" by(cases Md) simp
  then show "wf_J_mdecl P C Md \<Longrightarrow> wwf_J_mdecl P C Md"
    by(case_tac b) (fastforce simp:wwf_J_mdecl_def dest!:WT_fv)+
qed
(*>*)

lemma wf_prog_wwf_prog: "wf_J_prog P \<Longrightarrow> wwf_J_prog P"
(*<*)
by (simp add:wf_prog_def wf_cdecl_def wf_mdecl_def)
   (fast intro:wf_mdecl_wwf_mdecl)
(*>*)


end
