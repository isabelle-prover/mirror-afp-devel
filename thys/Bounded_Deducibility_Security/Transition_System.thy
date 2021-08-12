subsection \<open>Transition Systems\<close>

text \<open> We define transition systems, their valid traces,
and state rechability.\<close>

(*<*)
theory Transition_System
  imports Trivia
begin
(*>*)

subsubsection \<open>Traces\<close>

type_synonym 'trans trace = "'trans list"


locale Transition_System =
fixes istate :: "'state"
  and validTrans :: "'trans \<Rightarrow> bool"
  and srcOf :: "'trans \<Rightarrow> 'state"
  and tgtOf :: "'trans \<Rightarrow> 'state"
begin


fun srcOfTr where "srcOfTr tr = srcOf(hd tr)" (* source of *)
fun tgtOfTr where "tgtOfTr tr = tgtOf(last tr)" (* target of *)

fun srcOfTrFrom where
  "srcOfTrFrom s [] = s"
| "srcOfTrFrom s tr = srcOfTr tr"

lemma srcOfTrFrom_srcOfTr[simp]:
  "tr \<noteq> [] \<Longrightarrow> srcOfTrFrom s tr = srcOfTr tr"
  by (cases tr) auto

fun tgtOfTrFrom where
  "tgtOfTrFrom s [] = s"
| "tgtOfTrFrom s tr = tgtOfTr tr"

lemma tgtOfTrFrom_tgtOfTr[simp]:
  "tr \<noteq> [] \<Longrightarrow> tgtOfTrFrom s tr = tgtOfTr tr"
  by (cases tr) auto


text \<open>Traces allowed by the system (starting in any given state),
with two alternative definitions: growing from the left and growing from the right:\<close>

inductive valid :: "'trans trace \<Rightarrow> bool" where
Singl[simp,intro!]:
"validTrans trn
 \<Longrightarrow>
 valid [trn]"
|
Cons[intro]:
"\<lbrakk>validTrans trn; tgtOf trn = srcOf (hd tr); valid tr\<rbrakk>
 \<Longrightarrow>
 valid (trn # tr)"

inductive_cases valid_SinglE[elim!]: "valid [trn]"
inductive_cases valid_ConsE[elim]: "valid (trn # tr)"


inductive valid2 :: "'trans trace \<Rightarrow> bool" where
Singl[simp,intro!]:
"validTrans trn
 \<Longrightarrow>
 valid2 [trn]"
|
Rcons[intro]:
"\<lbrakk>valid2 tr; tgtOf (last tr) = srcOf trn; validTrans trn\<rbrakk>
 \<Longrightarrow>
 valid2 (tr ## trn)"

inductive_cases valid2_SinglE[elim!]: "valid2 [trn]"
inductive_cases valid2_RconsE[elim]: "valid2 (tr ## trn)"

lemma Nil_not_valid[simp]: "\<not> valid []"
by (metis valid.simps neq_Nil_conv)

lemma Nil_not_valid2[simp]: "\<not> valid2 []"
by (metis valid2.cases append_Nil butlast.simps butlast_snoc not_Cons_self2)

lemma valid_Rcons:
assumes "valid tr" and "tgtOf (last tr) = srcOf trn" and "validTrans trn"
shows "valid (tr ## trn)"
using assms proof(induct arbitrary: trn)
  case (Cons trn tr trna)
  thus ?case by (cases tr) auto
qed auto

lemma valid_hd_Rcons[simp]:
assumes "valid tr"
shows "hd (tr ## tran) = hd tr"
by (metis Nil_not_valid assms hd_append)

lemma valid2_hd_Rcons[simp]:
assumes "valid2 tr"
shows "hd (tr ## tran) = hd tr"
by (metis Nil_not_valid2 assms hd_append)

lemma valid2_last_Cons[simp]:
assumes "valid2 tr"
shows "last (tran # tr) = last tr"
by (metis Nil_not_valid2 assms last.simps)

lemma valid2_Cons:
assumes "valid2 tr" and "tgtOf trn = srcOf (hd tr)" and "validTrans trn"
shows "valid2 (trn # tr)"
using assms proof(induct arbitrary: trn)
  case Singl  show ?case
  unfolding two_singl_Rcons apply(rule valid2.Rcons) using Singl
  by (auto intro: valid2.Singl)
next
  case Rcons show ?case
  unfolding append.append_Cons[symmetric] apply(rule valid2.Rcons) using Rcons by auto
qed

lemma valid_valid2: "valid = valid2"
proof(rule ext, safe)
  fix tr assume "valid tr"  thus "valid2 tr"
  by (induct) (auto intro: valid2.Singl valid2_Cons)
next
  fix tr assume "valid2 tr"  thus "valid tr"
  by (induct) (auto intro: valid.Singl valid_Rcons)
qed

lemma valid_Cons_iff:
"valid (trn # tr) \<longleftrightarrow> validTrans trn \<and> ((tgtOf trn = srcOf (hd tr) \<and> valid tr) \<or> tr = [])"
unfolding valid.simps[of "trn # tr"] by auto

lemma valid_append:
"tr \<noteq> [] \<Longrightarrow> tr1 \<noteq> [] \<Longrightarrow>
 valid (tr @ tr1) \<longleftrightarrow> valid tr \<and> valid tr1 \<and> tgtOf (last tr) = srcOf (hd tr1)"
by (induct tr) (auto simp add: valid_Cons_iff)


lemmas valid2_valid = valid_valid2[symmetric]

(* validFrom includes empty traces too (unlike valid): *)
definition validFrom :: "'state \<Rightarrow> 'trans trace \<Rightarrow> bool" where
"validFrom s tr \<equiv> tr = [] \<or> (valid tr \<and> srcOf (hd tr) = s)"

lemma validFrom_Nil[simp,intro!]: "validFrom s []"
unfolding validFrom_def by auto

lemma validFrom_valid[simp,intro]: "valid tr \<and> srcOf (hd tr) = s \<Longrightarrow> validFrom s tr"
unfolding validFrom_def by auto

lemma validFrom_append:
"validFrom s (tr @ tr1) \<longleftrightarrow> (tr = [] \<and> validFrom s tr1) \<or> (tr \<noteq> [] \<and> validFrom s tr \<and> validFrom (tgtOf (last tr)) tr1)"
unfolding validFrom_def using valid_append
by (cases "tr = [] \<or> tr1 = []") fastforce+

lemma validFrom_Cons:
"validFrom s (trn # tr) \<longleftrightarrow> validTrans trn \<and> srcOf trn = s \<and> validFrom (tgtOf trn) tr"
unfolding validFrom_def by auto


subsubsection \<open>Reachability\<close>

(* Reachable states: *)
inductive reach :: "'state \<Rightarrow> bool" where
Istate: "reach istate"
|
Step: "reach s \<Longrightarrow> validTrans trn \<Longrightarrow> srcOf trn = s \<Longrightarrow> tgtOf trn = s' \<Longrightarrow> reach s'"


(* traces versus reachability: *)
lemma valid_reach_src_tgt:
assumes "valid tr" and "reach (srcOf (hd tr))"
shows "reach (tgtOf (last tr))"
using assms Step by induct auto

lemma valid_init_reach:
assumes "valid tr" and "srcOf (hd tr) = istate"
shows "reach (tgtOf (last tr))"
using valid_reach_src_tgt assms reach.Istate by metis

lemma reach_init_valid:
assumes "reach s"
shows
"s = istate
 \<or>
 (\<exists> tr. valid tr \<and> srcOf (hd tr) = istate \<and> tgtOf (last tr) = s)"
using assms proof induction
  case (Step s trn s')
  thus ?case proof(elim disjE exE conjE)
    assume s: "s = istate"
    show ?thesis
    apply (intro disjI2 exI[of _ "[trn]"])
    using s Step by auto
  next
    fix tr assume v: "valid tr" and s: "srcOf (hd tr) = istate" and t: "tgtOf (last tr) = s"
    show ?thesis
    apply (intro disjI2 exI[of _ "tr ## trn"])
    using Step v t s by (auto intro: valid_Rcons)
  qed
qed auto

lemma reach_validFrom:
assumes "reach s'"
shows "\<exists> s tr. s = istate \<and> (s = s' \<or> (validFrom s tr \<and> tgtOf (last tr) = s'))"
using reach_init_valid[OF assms] unfolding validFrom_def by auto

inductive reachFrom :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
  for s :: "'state"
where
  Refl[intro]: "reachFrom s s"
| Step: "\<lbrakk>reachFrom s s'; validTrans trn; srcOf trn = s'; tgtOf trn = s''\<rbrakk> \<Longrightarrow> reachFrom s s''"

lemma reachFrom_Step1:
"\<lbrakk>validTrans trn; srcOf trn = s; tgtOf trn = s'\<rbrakk> \<Longrightarrow> reachFrom s s'"
by (auto intro: reachFrom.Step)

lemma reachFrom_Step_Left:
"reachFrom s' s'' \<Longrightarrow> validTrans trn \<Longrightarrow> srcOf trn = s \<Longrightarrow> tgtOf trn = s' \<Longrightarrow> reachFrom s s''"
by (induction s'' rule: reachFrom.induct) (auto intro: reachFrom.Step)

lemma reachFrom_trans: "reachFrom s0 s1 \<Longrightarrow> reachFrom s1 s2 \<Longrightarrow> reachFrom s0 s2"
by (induction s1 arbitrary: s2 rule: reachFrom.induct) (auto intro: reachFrom_Step_Left)

lemma reachFrom_reach: "reachFrom s s' \<Longrightarrow> reach s \<Longrightarrow> reach s'"
by (induction rule: reachFrom.induct) (auto intro: reach.Step)

lemma valid_validTrans_set:
assumes "valid tr" and "trn \<in>\<in> tr"
shows "validTrans trn"
using assms by (induct tr arbitrary: trn) auto

lemma validFrom_validTrans_set:
assumes "validFrom s tr" and "trn \<in>\<in> tr"
shows "validTrans trn"
by (metis assms validFrom_def empty_iff list.set valid_validTrans_set)

lemma valid_validTrans_nth:
assumes v: "valid tr" and i: "i < length tr"
shows "validTrans (tr!i)"
using valid_validTrans_set[OF v] i by auto

lemma valid_validTrans_nth_srcOf_tgtOf:
assumes v: "valid tr" and i: "Suc i < length tr"
shows "srcOf (tr!(Suc i)) = tgtOf (tr!i)"
by (metis Cons_nth_drop_Suc valid_append Suc_lessD append_self_conv2 hd_drop_conv_nth i id_take_nth_drop list.distinct(1) v valid_ConsE)

lemma validFrom_reach: "validFrom s tr \<Longrightarrow> reach s \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> reach (tgtOf (last tr))"
by (intro valid_reach_src_tgt) (auto simp add: validFrom_def)


end (* locale Transition_System *)

(*<*)
end
(*>*)
