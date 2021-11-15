section \<open>Trivial security properties\<close>

text \<open>Here we formalize some cases when BD Security holds trivially. \<close>

theory Trivial_Security
imports Bounded_Deducibility_Security.Abstract_BD_Security
begin

definition B_id :: "'value \<Rightarrow> 'value \<Rightarrow> bool"
where "B_id vl vl1 \<equiv> (vl1 = vl)"

context Abstract_BD_Security
begin

(* ... when the bound is as fine-grained as equality: *)
lemma B_id_secure:
assumes "\<And>tr vl vl1. B (V tr) vl1 \<Longrightarrow> validSystemTrace tr \<Longrightarrow> B_id (V tr) vl1"
shows "secure"
using assms unfolding secure_def B_id_def by auto

(* ... when the observation function is constant: *)
lemma O_const_secure:
assumes "\<And>tr. validSystemTrace tr \<Longrightarrow> O tr = ol"
and "\<And>tr vl vl1. B (V tr) vl1 \<Longrightarrow> validSystemTrace tr \<Longrightarrow> (\<exists>tr1. validSystemTrace tr1 \<and> V tr1 = vl1)"
shows "secure"
unfolding secure_def proof (intro allI impI, elim conjE)
  fix tr vl vl1
  assume "B vl vl1" and "validSystemTrace tr" and "V tr = vl"
  moreover then obtain tr1 where "validSystemTrace tr1" "V tr1 = vl1" using assms(2) by auto
  ultimately show "\<exists>tr1. validSystemTrace tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1" using assms(1) by auto
qed

definition OV_compatible :: "'observations \<Rightarrow> 'values \<Rightarrow> bool" where
  "OV_compatible obs vl \<equiv> (\<exists>tr. O tr = obs \<and> V tr = vl)"

definition V_compatible :: "'values \<Rightarrow> 'values \<Rightarrow> bool" where
  "V_compatible vl vl1 \<equiv> (\<forall>obs. OV_compatible obs vl \<longrightarrow> OV_compatible obs vl1)"

definition validObs :: "'observations \<Rightarrow> bool" where
  "validObs obs \<equiv> (\<exists>tr. validSystemTrace tr \<and> O tr = obs)"

definition validVal :: "'values \<Rightarrow> bool" where
  "validVal vl \<equiv> (\<exists>tr. validSystemTrace tr \<and> V tr = vl)"

lemma OV_total_secure:
assumes OV: "\<And>obs vl. validObs obs \<Longrightarrow> validVal vl \<Longrightarrow> OV_compatible obs vl
                  \<Longrightarrow> (\<exists>tr. validSystemTrace tr \<and> O tr = obs \<and> V tr = vl)"
and BV: "\<And>vl vl1. B vl vl1 \<Longrightarrow> validVal vl \<Longrightarrow> V_compatible vl vl1 \<and> validVal vl1"
shows "secure"
unfolding secure_def proof (intro allI impI, elim conjE)
  fix tr vl vl1
  assume tr: "validSystemTrace tr" and B: "B vl vl1" and vl: "V tr = vl"
  then have "validObs (O tr)" and "validVal (V tr)" and "OV_compatible (O tr) (V tr)"
    unfolding validObs_def validVal_def OV_compatible_def by blast+
  moreover then have "validVal vl1" and "OV_compatible (O tr) vl1"
    using B BV unfolding V_compatible_def vl by blast+
  ultimately show "\<exists>tr1. validSystemTrace tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1"
    using OV by blast
qed

lemma unconstrained_secure:
assumes "\<And>tr. validSystemTrace tr"
and BV: "\<And>vl vl1. B vl vl1 \<Longrightarrow> validVal vl \<Longrightarrow> V_compatible vl vl1 \<and> validVal vl1"
shows "secure"
using assms by (intro OV_total_secure) (auto simp: OV_compatible_def)

end

end
