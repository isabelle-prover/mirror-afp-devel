(*  Title:      JinjaThreads/J/JWellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Well-formedness Constraints} *}

theory JWellForm
imports
  WWellForm
  WellType_Exec
  DefAss
begin

definition wf_J_mdecl :: "J_prog \<Rightarrow> cname \<Rightarrow> J_mb mdecl \<Rightarrow> bool"
where
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


abbreviation wf_J_prog :: "J_prog \<Rightarrow> bool"
where "wf_J_prog == wf_prog wf_J_mdecl"

lemma wf_J_prog_wf_J_mdecl:
  "\<lbrakk> wf_J_prog P; class P C = \<lfloor>(D, fds, mths)\<rfloor>; jmdcl \<in> set mths \<rbrakk>
  \<Longrightarrow> wf_J_mdecl P C jmdcl"
apply(cases P)
apply (simp add: wf_prog_def)
apply (simp add: wf_cdecl_def)
apply (erule conjE)+
apply(drule map_of_SomeD)
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

subsection {* Code generation *}

definition typeable_with :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
where [simp]: "typeable_with P E e T \<longleftrightarrow> (\<exists>T'. P,E \<turnstile> e ::' T' \<and> P \<turnstile> T' \<le> T)"

definition wf_J_mdecl' :: "J_prog \<Rightarrow> cname \<Rightarrow> J_mb mdecl \<Rightarrow> bool"
where
  "wf_J_mdecl' P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  typeable_with P [this\<mapsto>Class C,pns[\<mapsto>]Ts] body T \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>"

definition wf_J_prog' :: "J_prog \<Rightarrow> bool"
where "wf_J_prog' = wf_prog wf_J_mdecl'"

lemma wf_J_prog_wf_J_prog':
  "wf_J_prog P \<Longrightarrow> wf_J_prog' P"
unfolding wf_J_prog'_def
apply(erule wf_prog_lift)
apply(clarsimp simp add: wf_J_mdecl'_def)
apply(drule (1) WT_into_WT_code)
apply(auto simp add: ran_def map_upds_def dest!: map_of_SomeD set_zip_rightD)
done

lemma wf_J_prog'_wf_J_prog:
  "wf_J_prog' P \<Longrightarrow> wf_J_prog P"
unfolding wf_J_prog'_def
apply(erule wf_prog_lift)
apply(clarsimp simp add: wf_J_mdecl'_def)
apply(drule (1) WT_code_into_WT)
apply(auto simp add: ran_def map_upds_def dest!: map_of_SomeD set_zip_rightD)
done

lemma wf_J_prog_eq_wf_J_prog' [code_inline]:
  "wf_J_prog = wf_J_prog'"
by(blast intro: ext wf_J_prog'_wf_J_prog wf_J_prog_wf_J_prog' del: equalityI)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  typeable_with 
.

lemma [code_inline]: "Predicate.bind (eq_i_o x) f = f x"
by(blast elim: bindE eq_i_oE eq.cases intro: bindI eq_i_oI eq.intros pred_eqI)

lemmas [code_inline] = single_bind split

declare set.equation(3) [code del]
declare set.simps[code]

text {* Formal code generation test *}
ML {* @{code wf_J_prog'}  *}

end
