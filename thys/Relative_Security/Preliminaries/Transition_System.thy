section \<open>Transition Systems and System Models\<close>

text \<open> This theory formalizes transition systems (where transitions have a separate identity) 
and what we call ``simple transition systems'', where transitions are just certain pairs of states. 
The latter are what in the ``Relative Security'' paper we call ``system models''. 
We introduce system models as a separate locale. Basic notions such as reachability are introduced, 
and basic facts about them are being proved. \<close>

theory Transition_System
  imports Trivia
begin


subsection \<open>The relevant locales\<close>

locale Transition_System =
fixes istate :: "'state \<Rightarrow> bool"
  and validTrans :: "'trans \<Rightarrow> bool"
  and srcOf :: "'trans \<Rightarrow> 'state"
  and tgtOf :: "'trans \<Rightarrow> 'state"

(* Transition system where transitions are just pairs of states: *)
locale Simple_Transition_System = 
Transition_System istate validTrans fst snd 
for istate :: "'state \<Rightarrow> bool"
and validTrans :: "'state \<times> 'state  \<Rightarrow> bool"

(* System models are just transition systems -- but for later ease of instantiation, 
they include the definition of finality as an assumption.
*)
locale System_Mod = 
Simple_Transition_System istate validTrans   
for istate :: "'state \<Rightarrow> bool"
and validTrans :: "'state \<times> 'state  \<Rightarrow> bool"
+
fixes final :: "'state \<Rightarrow> bool"
assumes final_def: "final s1 \<longleftrightarrow> (\<forall>s2. \<not> validTrans (s1,s2))" 

(* Assuming the transitions are deterministic: *)
locale System_Mod_Deterministic = 
System_Mod istate validTrans final
for istate :: "'state \<Rightarrow> bool"
and validTrans :: "'state \<times> 'state  \<Rightarrow> bool"
and final :: "'state \<Rightarrow> bool"
+  
fixes "next" :: "'state \<Rightarrow> 'state"
assumes validTrans_iff_next: "validTrans (s1,s2) \<longleftrightarrow> \<not> final s1 \<and> next s1 = s2"


context Transition_System
begin

subsection \<open>Reachability\<close>

(* Reachable states: *)
inductive reach :: "'state \<Rightarrow> bool" where
Istate: "istate s \<Longrightarrow> reach s"
|
Step: "reach s \<Longrightarrow> validTrans trn \<Longrightarrow> srcOf trn = s \<Longrightarrow> tgtOf trn = s' \<Longrightarrow> reach s'"

(* holds at the initial state: *)
definition holdsIstate :: "('state \<Rightarrow> bool) \<Rightarrow> bool" where
"holdsIstate \<phi> \<equiv> \<forall>s. istate s \<longrightarrow> \<phi> s"

(* is invariant: *)
definition invar :: "('state \<Rightarrow> bool) \<Rightarrow> bool" where
"invar \<phi> \<equiv> \<forall> trn. validTrans trn \<and> reach (srcOf trn) \<and> \<phi> (srcOf trn) \<longrightarrow> \<phi> (tgtOf trn)"

lemma holdsIstate_invar:
assumes h: "holdsIstate \<phi>" and i: "invar \<phi>" and a: "reach s"
shows "\<phi> s"
using a apply (induct rule: reach.induct)
using h i unfolding holdsIstate_def invar_def by auto

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

end (* context Transition_System *)


subsection \<open>Finite traces in transition systems \<close>

type_synonym 'trans trace = "'trans list"


context Transition_System
begin

(* Traces allowed by the system (starting in any given state) *)

(* Two alternative definitions: growing from the left and growing from the right: *)
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

lemma valid_nth: 
  "valid tr \<longleftrightarrow> 
     tr \<noteq> [] \<and> 
     list_all validTrans tr \<and> 
     (\<forall>i<length tr-1. tgtOf (tr!i) = srcOf (tr!(Suc i)))"
unfolding list_all_length proof (induct tr)
  case (Cons a tr)
  then show ?case 
    apply (subst valid.simps)
    apply safe
    apply simp_all
    apply (metis diff_Suc_1 less_Suc_eq_0_disj nth_Cons')
    using Transition_System.valid_append append_self_conv2 drop_Suc_Cons hd_drop_conv_nth id_take_nth_drop 
    length_Cons less_Suc_eq list.simps(3) not_less valid.Cons valid_ConsE 
    apply (smt (verit) drop_eq_Nil2 list.discI)
    apply (metis hd_conv_nth length_greater_0_conv nth_Cons_0 zero_less_Suc)
    apply (metis Suc_less_eq nth_Cons_Suc)
    by (metis Suc_pred length_greater_0_conv less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc)
qed simp_all


(* validFrom includes empty traces too (unlike "valid"): *)
definition validFrom :: "'state \<Rightarrow> 'trans trace \<Rightarrow> bool" where
"validFrom s tr \<equiv> tr = [] \<or> (valid tr \<and> srcOf (hd tr) = s)"

lemma validFrom_Nil[simp,intro!]: "validFrom s []"
unfolding validFrom_def by auto

lemma validFrom_single: 
  assumes \<open>validFrom s [trn]\<close>
    shows \<open>srcOf trn = s\<close>
  using assms by (simp add: validFrom_def)

lemma validFrom_valid[simp,intro]: "valid tr \<and> srcOf (hd tr) = s \<Longrightarrow> validFrom s tr"
unfolding validFrom_def by auto

lemma validFrom_append:
"validFrom s (tr @ tr1) \<longleftrightarrow> (tr = [] \<and> validFrom s tr1) \<or> (tr \<noteq> [] \<and> validFrom s tr \<and> validFrom (tgtOf (last tr)) tr1)"
unfolding validFrom_def using valid_append
by (cases "tr = [] \<or> tr1 = []") fastforce+

lemma validFrom_Cons:
"validFrom s (trn # tr) \<longleftrightarrow> validTrans trn \<and> srcOf trn = s \<and> validFrom (tgtOf trn) tr"
unfolding validFrom_def by auto

lemma validFrom_sameState: "validFrom s tr \<and> validFrom s' tr \<Longrightarrow> tr = [] \<or> s = s'" 
by (metis validFrom_def)

lemma validFrom_nth: 
"validFrom s tr \<longleftrightarrow> 
 tr = [] \<or> 
 srcOf (hd tr) = s \<and>  
 list_all validTrans tr \<and> 
 (\<forall>i<length tr-1. tgtOf (tr!i) = srcOf (tr!(Suc i)))"
unfolding validFrom_def valid_nth by auto

lemma validFrom_nth_NE: 
"tr \<noteq> [] \<Longrightarrow> 
 validFrom s tr \<longleftrightarrow>  
 srcOf (hd tr) = s \<and>  
 list_all validTrans tr \<and> 
 (\<forall>i<length tr-1. tgtOf (tr!i) = srcOf (tr!(Suc i)))"
unfolding validFrom_nth by auto


(* Traces versus reachability: *)

lemma valid_reach_src_tgt:
assumes "valid tr" and "reach (srcOf (hd tr))"
shows "reach (tgtOf (last tr))"
using assms reach.Step apply induct by auto

lemma valid_init_reach:
assumes "valid tr" and "istate (srcOf (hd tr))"
shows "reach (tgtOf (last tr))"
using valid_reach_src_tgt assms reach.Istate by metis

lemma reach_init_valid:
assumes "reach s"
shows
"istate s
 \<or>
 (\<exists> tr. valid tr \<and> istate (srcOf (hd tr)) \<and> tgtOf (last tr) = s)"
using assms proof induction
  case (Step s trn s')
  thus ?case proof(elim disjE exE conjE)
    assume s: "istate s"
    show ?thesis
    apply (intro disjI2 exI[of _ "[trn]"])
    using s Step by auto
  next
    fix tr assume v: "valid tr" and s: "istate (srcOf (hd tr))" and t: "tgtOf (last tr) = s"
    show ?thesis
    apply (intro disjI2 exI[of _ "tr ## trn"])
    using Step v t s by (auto intro: valid_Rcons)
  qed
qed auto

lemma reach_validFrom:
assumes "reach s'"
shows "\<exists> s tr. istate s \<and> (s = s' \<or> (validFrom s tr \<and> tgtOf (last tr) = s'))"
using reach_init_valid[OF assms] unfolding validFrom_def by auto

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


subsection \<open>Finite traces in simple transition systems \<close>

definition "lastt s tr \<equiv> if tr = [] then s else last tr"

lemma lastt_Nil[simp]: "lastt s [] = s"
unfolding lastt_def by auto

context Simple_Transition_System
begin

(* The traces will no longer need to be stored heavy-duty, 
but can use "simple traces" which are just lists of states. 
Suffix "S" will signify "simple".
*)

definition validS :: "'state list \<Rightarrow> bool" where 
"validS sl \<equiv> \<forall>i<length sl-1. validTrans (sl!i, sl!(Suc i))"

definition validFromS :: "'state \<Rightarrow> 'state list \<Rightarrow> bool" where 
"validFromS s sl \<equiv> sl = [] \<or> (hd sl = s \<and> validS sl)"

lemma validS_Nil[simp,intro!]: 
"validS []"
unfolding validS_def by auto

lemma validS_singl[simp,intro!]: 
"validS [s]"
unfolding validS_def by auto

lemma validFromS_Nil[simp,intro!]: 
"validFromS s []"
unfolding validFromS_def by auto

lemma validFromS[simp,intro!]: 
"validFromS s [s]"
unfolding validFromS_def by auto

lemma validFromS_Cons_iff:
"validFromS s (s' # sl) \<longleftrightarrow> s = s' \<and> (sl = [] \<or> (validTrans (s,hd sl) \<and> validFromS (hd sl) sl))"
unfolding validFromS_def validS_def apply safe
  subgoal by auto
  subgoal using hd_conv_nth by fastforce
  subgoal by simp (metis One_nat_def add.commute less_diff_conv nth_Cons_Suc plus_1_eq_Suc)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp (metis One_nat_def Suc_less_eq Suc_pred diff_0_eq_0 hd_conv_nth list.size(3) not_gr_zero nth_Cons' zero_less_diff) .
  
lemma validFromS_Cons[intro]:
"validTrans (s,s') \<Longrightarrow> validFromS s' sl \<Longrightarrow> validFromS s (s # sl)"
by (cases "sl", auto simp: validFromS_Cons_iff)

(* *)

lemma lastt_Cons[simp]: "validTrans (s,s') \<Longrightarrow> validFromS s' tr \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> lastt s (s # tr) = lastt s' tr"
unfolding lastt_def by auto

(* Switching between traces and simple traces: *)

definition fromS :: "'a list \<Rightarrow> ('a \<times> 'a) list" where 
"fromS sl \<equiv> if sl = [] then [] else zip (butlast sl) (tl sl)"

lemma fromS_Nil[simp]: "fromS [] = []"
unfolding fromS_def by auto

lemma fromS_singl[simp]: "fromS [s] = []"
unfolding fromS_def by auto

lemma fromS_eq_Nil[simp]: "fromS sl = [] \<longleftrightarrow> length sl \<le> Suc 0"
unfolding fromS_def by (cases sl) (auto simp: zip_eq_Nil_iff)

lemma length_fromS_notNil[simp]: 
"sl \<noteq> [] \<Longrightarrow> length (fromS sl) = length sl - 1"
unfolding fromS_def by auto

lemma fromS_nth: "i < length sl-1 \<Longrightarrow> fromS sl ! i = (sl!i, sl!(Suc i))"
unfolding fromS_def by (auto simp: nth_butlast nth_tl) 

lemma length_fromS_less1: "length (fromS sl) = length sl - 1"
  by (auto simp add: fromS_def)

(* *)

definition toS :: "('state \<times> 'state) list \<Rightarrow> 'state list" where 
"toS tr \<equiv> if tr = [] then [] else (fst (hd tr)) # map snd tr"

lemma toS_Nil[simp]: "toS [] = []"
unfolding toS_def by auto

lemma toS_eq_Nil[simp]: "toS tr = [] \<longleftrightarrow> tr = []"
unfolding toS_def by auto

lemma length_toS[simp]: 
"tr \<noteq> [] \<Longrightarrow> length (toS tr) = Suc (length tr)"
unfolding toS_def by auto

lemma toS_nth_0: "tr \<noteq> [] \<Longrightarrow> toS tr ! 0 = fst (tr!0)"
unfolding toS_def by (simp add: hd_conv_nth)

lemma toS_nth_Suc: "i < length tr-1 \<Longrightarrow> toS tr ! (Suc i) = snd (tr!i)"
unfolding toS_def by auto 

lemma toS_last: "tr \<noteq> [] \<Longrightarrow> last (toS tr) = snd (last tr)"
unfolding toS_def by (simp add: last_map)

lemma toS_nth_valid: "valid tr \<Longrightarrow> i < length tr-1 \<Longrightarrow> toS tr ! i = fst (tr!i)"
unfolding toS_def by (simp add: hd_conv_nth nth_Cons' valid_nth)

lemma toS_length_gt_eq: \<open>length tr \<le> length (toS tr)\<close>
  by (cases \<open>tr = []\<close>, simp_all)

(* *)

lemma fromS_toS_valid[simp]: "valid tr \<Longrightarrow> fromS (toS tr) = tr"
apply(rule nth_equalityI)
  subgoal by (cases tr, auto)
  subgoal apply (cases tr)
    subgoal by simp
    subgoal 
    	by (smt (verit, best) fromS_nth length_fromS_notNil toS_eq_Nil 
       toS_last \<open>valid tr \<Longrightarrow> length (fromS (toS tr)) = length tr\<close> 
        diff_Suc_1 last_conv_nth le_eq_less_or_eq le_zero_eq length_Cons 
        less_Suc_eq_le not_less 
       prod.collapse toS_nth_0 toS_nth_Suc valid_nth zero_induct) . . 

lemma fromS_toS_validFrom[simp]: "validFrom s tr \<Longrightarrow> fromS (toS tr) = tr"
unfolding validFrom_def by auto
  
lemma toS_fromS_singl[simp]: "toS (fromS [s]) = []"
by simp
 
lemma toS_fromS_nonSingl[simp]: 
"length sl \<noteq> Suc 0 \<Longrightarrow> toS (fromS sl) = sl"
apply(rule nth_equalityI)  
  subgoal by (cases sl, auto)
  subgoal for i apply(cases "sl = []")
    subgoal by auto
    subgoal apply (cases i)
      subgoal by simp (metis toS_nth_0 fromS_eq_Nil fromS_nth fst_eqD 
           length_fromS_notNil length_greater_0_conv)
      subgoal for j apply simp 
      	by (metis (no_types, lifting) toS_def Suc_less_eq2 
        \<open>\<lbrakk>length sl \<noteq> Suc 0\<rbrakk> \<Longrightarrow> length (toS (fromS sl)) = length sl\<close> 
          diff_Suc_1 fromS_nth 
           length_fromS_notNil list.size(3) nth_Cons_Suc nth_map snd_conv) . . .

(* Transfer: *)
lemma valid_fromS[simp]: 
"length sl > Suc 0 \<Longrightarrow> valid (fromS sl) \<longleftrightarrow> validS sl" 
unfolding valid_nth validS_def list_all_length  apply(cases sl)
  subgoal by auto
  subgoal for s ssl apply(cases ssl)
    subgoal by auto
    subgoal by (simp add: fromS_nth) . .
    
lemma validFrom_fromS[simp]: 
"length sl \<noteq> Suc 0 \<Longrightarrow> validFrom s (fromS sl) \<longleftrightarrow> validFromS s sl"
unfolding validFrom_def validFromS_def apply(cases sl)  
  apply (metis Simple_Transition_System.toS_fromS_nonSingl length_0_conv 
     list.distinct(1) toS_def)
  by (metis fromS_eq_Nil hd_conv_nth length_greater_0_conv nat_less_le 
    not_less not_less_eq toS_fromS_nonSingl toS_nth_0 valid_fromS)

lemma validS_toS[simp]: 
"valid tr \<Longrightarrow> validS (toS tr)" 
by (metis fromS_eq_Nil fromS_toS_valid not_less valid_fromS valid_nth)

lemma validFromS_toS[simp]: 
"validFrom s tr \<Longrightarrow> validFromS s (toS tr)" 
by (metis validFrom_def list.sel(1) toS_def validFromS_def validS_toS)

lemma validFromS_singl_iff[simp]: "validFromS s [s'] \<longleftrightarrow> s = s'"
using validFromS_def by auto

end (* context Simple_Transition_System *)


subsection \<open>Possibly infinite traces \<close>

(* "Lazy", i.e., possibly infinite trace, modelled using lazy lists: *)
type_synonym 'trans ltrace = "'trans llist"


context Transition_System
begin

(* Ltraces allowed by the system (starting in any given state) *)

(* Two alternative definitions: growing from the left and growing from the right: *)
coinductive lvalid :: "'trans ltrace \<Rightarrow> bool" where
Singl[simp,intro!]:
"validTrans trn
 \<Longrightarrow>
 lvalid [[trn]]"
|
Cons[intro]:
"\<lbrakk>validTrans trn; tgtOf trn = srcOf (lhd tr); lvalid tr\<rbrakk>
 \<Longrightarrow>
 lvalid (trn $ tr)"

inductive_cases lvalid_SinglE[elim!]: "lvalid [[trn]]"
inductive_cases lvalid_ConsE[elim]: "lvalid (trn $ tr)"

lemma Nil_not_lvalid[simp]: "\<not> lvalid [[]]"
using lvalid.cases by blast 

lemma lvalid_LCons_iff:
"lvalid (trn $ tr) \<longleftrightarrow> validTrans trn \<and> ((tgtOf trn = srcOf (lhd tr) \<and> lvalid tr) \<or> tr = [[]])"
by blast 

(* lvalidFrom includes empty ltraces too (unlike lvalid): *)

definition lvalidFrom :: "'state \<Rightarrow> 'trans ltrace \<Rightarrow> bool" where
"lvalidFrom s tr \<equiv> tr = [[]] \<or> (lvalid tr \<and> srcOf (lhd tr) = s)"

lemma lvalidFrom_Nil[simp,intro!]: "lvalidFrom s [[]]"
unfolding lvalidFrom_def by auto

lemma lvalidFrom_single: 
  assumes \<open>lvalidFrom s [[trn]]\<close>
    shows \<open>srcOf trn = s\<close>
  using assms by (simp add: lvalidFrom_def)

lemma lvalidFrom_lvalid[simp,intro]: "lvalid tr \<and> srcOf (lhd tr) = s \<Longrightarrow> lvalidFrom s tr"
unfolding lvalidFrom_def by auto

lemma lvalidFrom_Cons:
"lvalidFrom s (trn $ tr) \<longleftrightarrow> validTrans trn \<and> srcOf trn = s \<and> lvalidFrom (tgtOf trn) tr"
unfolding lvalidFrom_def by auto

lemma lvalidFrom_sameState: "lvalidFrom s tr \<and> lvalidFrom s' tr \<Longrightarrow> tr = [[]] \<or> s = s'" 
by (metis lvalidFrom_def)

end (* locale Transition_System *)


subsection \<open>Possibly infinite traces in simple transition systems \<close>

context Simple_Transition_System
begin

definition lvalidS :: "'state llist \<Rightarrow> bool" where 
"lvalidS sl \<equiv> \<forall>i<llength sl-1. validTrans (lnth sl i, lnth sl (Suc i))"

definition lvalidFromS :: "'state \<Rightarrow> 'state llist \<Rightarrow> bool" where 
"lvalidFromS s sl \<equiv> sl = [[]] \<or> (lhd sl = s \<and> lvalidS sl)"

lemma lvalidS_LNil[simp,intro!]: 
"lvalidS [[]]"
unfolding lvalidS_def by auto

lemma lvalidS_singl[simp,intro!]: 
"lvalidS [[s]]"
unfolding lvalidS_def by auto

lemma lvalidFromS_LNil[simp,intro!]: 
"lvalidFromS s [[]]"
unfolding lvalidFromS_def by auto

lemma lvalidFromS[simp,intro!]: 
"lvalidFromS s [[s]]"
unfolding lvalidFromS_def by auto

lemma lvalidFromS_Cons_iff:
"lvalidFromS s (s' $ sl) \<longleftrightarrow> s = s' \<and> (sl = [[]] \<or> (validTrans (s,lhd sl) \<and> lvalidFromS (lhd sl) sl))"
unfolding lvalidFromS_def lvalidS_def apply safe
  subgoal by auto
  subgoal by simp (metis i0_less lhd_conv_lnth llength_eq_0 lnth_0 lnull_def zero_enat_def) 
  subgoal by simp (metis Suc_ile_eq co.enat.exhaust eSuc_minus_1 idiff_0 iless_Suc_eq lnth_Suc_LCons not_less_zero)  
  subgoal by auto   
  subgoal by auto  
  subgoal by auto  
  subgoal by auto   
  subgoal by auto  
  subgoal by simp (metis One_nat_def Suc_ile_eq Suc_pred epred_conv_minus epred_llength iless_Suc_eq less_Suc_eq 
  llength_LCons llength_eq_0 llist.disc(1) llist.exhaust_sel lnth_LCons' zero_less_Suc zero_order(3)) .

lemma lvalidFromS_Cons[intro]:
"validTrans (s,s') \<Longrightarrow> lvalidFromS s' sl \<Longrightarrow> lvalidFromS s (s $ sl)"
by (cases "sl", auto simp: lvalidFromS_Cons_iff)

(* Alternative coinductive definition of validity :  *)
coinductive lvalidFromS' :: "'state \<Rightarrow> 'state llist \<Rightarrow> bool" where 
lvalidFromS: "lvalidFromS s ltr \<Longrightarrow> lvalidFromS' s ltr"
|
LNil: "lvalidFromS' s [[]]"
|
Singl: "lvalidFromS' s [[s]]"
|
lappend: "validFromS s tr \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> validTrans (last tr, s'') \<Longrightarrow> 
 lvalidFromS' s'' ltr \<Longrightarrow> 
 lvalidFromS' s (lappend (llist_of tr) ltr)"

lemma lvalidFromS'_lnth_validTrans: 
assumes "lvalidFromS' s lltr"
and "i < llength lltr - 1"
shows "validTrans (lnth lltr i, lnth lltr (Suc i))"
using assms proof(induct i arbitrary: s lltr rule: less_induct)
  case (less i s lltr)
  note vltr = `lvalidFromS' s lltr`
  note ii = `i < llength lltr - 1`
  show ?case using `lvalidFromS' s lltr` proof cases
    case lvalidFromS
    then show ?thesis 
      by (metis Simple_Transition_System.lvalidFromS_def Simple_Transition_System.lvalidS_LNil ii lvalidS_def)
  next
    case LNil
    then show ?thesis using less(3) by auto
  next
    case Singl
    then show ?thesis using less(3) by auto
  next
    case (lappend tr s'' ltr)
    note lltr = `lltr = lappend (llist_of tr) ltr`
    have "i < length tr - 1 \<or> i = length tr - 1 \<or> i = length tr \<or> i \<ge> Suc (length tr)" by auto
    then show ?thesis proof(elim disjE)
      assume i: "i < length tr - 1"
      hence 0: "lnth lltr i = nth tr i" "lnth lltr (Suc i) = nth tr (Suc i)"
      unfolding lltr   
      apply (metis Suc_diff_1 length_greater_0_conv less_SucI lnth_lappend_llist_of local.lappend(3))
      by (metis Suc_diff_1 Suc_less_eq i length_greater_0_conv lnth_lappend_llist_of local.lappend(3))   
      show ?thesis using `validFromS s tr` i unfolding 0  
      by (simp add: Simple_Transition_System.validS_def local.lappend(3) validFromS_def)
    next
      assume i: "i = length tr - 1"
      hence 0: "lnth lltr i = last tr" "lnth lltr (Suc i) = s''"
      unfolding lltr 
      apply (simp add: last_conv_nth lnth_lappend_llist_of local.lappend(3)) 
      apply(subst lnth_lappend) using i `tr \<noteq> []` apply simp
      by (smt (verit, best) One_nat_def Simple_Transition_System.lvalidFromS'.cases 
      Simple_Transition_System.lvalidFromS_def Simple_Transition_System.validFromS_def 
      idiff_enat_enat ii lappend_lnull2 lhd_lappend lhd_llist_of linorder_neq_iff llength_llist_of 
      llist.disc(1) lltr lnth_0 lnth_0_conv_lhd lnull_llist_of local.lappend(5) one_enat_def)
      show ?thesis unfolding 0 by fact 
    next
      assume i: "i = length tr"
      hence ll: "llength ltr > Suc 0"  
      by (metis One_nat_def Suc_ile_eq add.right_neutral 
      diff_le_self eSuc_minus_1 epred_conv_minus epred_enat gr_zeroI ii linorder_not_less 
      llength_lappend llength_llist_of lltr of_nat_eq_enat of_nat_less_iff one_enat_def order_less_le 
      plus_1_eSuc(2) zero_enat_def)
      hence ltrne: "ltr \<noteq> [[]]"  
      using ii lltr epred_conv_minus epred_enat by fastforce
      hence 0: "lnth lltr i = lnth ltr 0" "lnth lltr (Suc i) = lnth ltr (Suc 0)"
      unfolding lltr i lnth_lappend by auto
      thus ?thesis using ll `lvalidFromS' s'' ltr` 
      by (metis One_nat_def eSuc_minus_1 enat_0 enat_diff_cancel_left gr_zeroI i le_numeral_extra(4) 
      length_greater_0_conv less.hyps local.lappend(3) nless_le one_eSuc one_enat_def) 
    next
      assume i: "i \<ge> Suc (length tr)"
      hence ltrne: "ltr \<noteq> [[]]"  
      using ii lltr epred_conv_minus epred_enat by fastforce
      from i obtain j where ij: "i = length tr + j"  
      using less_imp_add_positive  
      using le_Suc_ex Suc_le_eq by auto
      hence jli: "j < i"  by (simp add: local.lappend(3)) 
      hence 0: "lnth lltr i = lnth ltr j" "lnth lltr (Suc i) = lnth ltr (Suc j)"
      using ij unfolding lltr by (auto simp: lnth_lappend_llist_of) 
      have jj: "j < llength ltr - 1" using i ltrne ii unfolding ij lltr apply simp 
      by (metis add_diff_assoc_enat enat_add_mono i0_less ileI1 llength_eq_0 lnull_def one_eSuc plus_enat_simps(1))
      have lhdltr: "lvalidFromS' (lhd ltr) ltr"
      by (smt (verit) lhd_lappend lhd_llist_of llist.exhaust_sel llist.inject lnull_llist_of 
      local.lappend(5) lvalidFromS'.simps lvalidFromS_def validFromS_def) 
      show ?thesis unfolding 0 by (rule less(1)[OF jli lhdltr jj]) 
    qed
  qed
qed

proposition lvalidFromS'_imp_lvalidFromS:
assumes "lvalidFromS' s ltr"
shows "lvalidFromS s ltr"
unfolding lvalidFromS_def lvalidS_def apply safe
  subgoal using assms 
  by (metis Simple_Transition_System.validFromS_def lhd_LCons lhd_lappend 
   lhd_llist_of lnull_llist_of lvalidFromS'.simps lvalidFromS_def) 
  subgoal for i using assms lvalidFromS'_lnth_validTrans by blast .

lemmas lvalidFromS_imp_lvalidFromS' = lvalidFromS'.intros(1)

lemma lvalidFromS_lvalidFromS':
"lvalidFromS = lvalidFromS'"
using lvalidFromS'_imp_lvalidFromS lvalidFromS_imp_lvalidFromS' by blast

lemma lvalidFromS'_lvalidFromS:
"lvalidFromS' = lvalidFromS"
using lvalidFromS'_imp_lvalidFromS lvalidFromS_imp_lvalidFromS' by blast

(* *)

coinductive llvalidFromS :: "enat \<Rightarrow> 'state \<Rightarrow> 'state llist \<Rightarrow> bool" where 
Delay: "n' < n \<Longrightarrow> llvalidFromS n' s ltr \<Longrightarrow> llvalidFromS n s ltr"
|
lvalidFromS: "lvalidFromS s ltr \<Longrightarrow> llvalidFromS n s ltr"
|
LNil: "llvalidFromS n s [[]]"
|
Singl: "llvalidFromS n s [[s]]"
|
lappend: "validFromS s tr \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> validTrans (last tr, s'') \<Longrightarrow> 
 llvalidFromS n' s'' ltr \<Longrightarrow> 
 llvalidFromS n s (lappend (llist_of tr) ltr)"

lemmas llvalidFromS_selectDelay = disjI1
lemmas llvalidFromS_selectlvalidFromS = disjI2[OF disjI1]
lemmas llvalidFromS_selectLNil = disjI2[OF disjI2[OF disjI1]]
lemmas llvalidFromS_selectSingl = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas llvalidFromS_selectlappend = disjI2[OF disjI2[OF disjI2[OF disjI2]]]

lemma llvalidFromS_imp_lvalidFromS:
assumes "llvalidFromS n s ltr"
shows "lvalidFromS s ltr"
proof-
  have 0: "\<exists>n. llvalidFromS n s ltr" using assms by auto
  show ?thesis apply(rule lvalidFromS'_imp_lvalidFromS)
  using 0 proof(coinduct rule: lvalidFromS'.coinduct)
    case (lvalidFromS' s tr1)
    then obtain n where 0: "llvalidFromS n s tr1" by auto
    then show ?case proof(induct n rule: less_induct)
      case (less n)
      hence 0: "llvalidFromS n s tr1" by simp
      then show ?case proof cases
        case (Delay n')
        show ?thesis using less(1)[OF `n' < n` `llvalidFromS n' s tr1`] .
      next
        case lvalidFromS 
        thus ?thesis by auto         
      next
        case LNil
        then show ?thesis by auto
      next
        case Singl
        then show ?thesis by auto
      next
        case (lappend tr s'' n' ltr)
        then show ?thesis by auto
      qed 
    qed
  qed      
qed

(* *)

coinductive lllvalidFromS :: "turn \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'state \<Rightarrow> 'state llist \<Rightarrow> bool" where 
DelayLR: "lllvalidFromS L wL' wR' s ltr \<Longrightarrow> lllvalidFromS R wL wR s ltr"
|
DelayL: "wL' < wL \<Longrightarrow> lllvalidFromS L wL' wR' s ltr \<Longrightarrow> lllvalidFromS L wL wR s ltr"
|
DelayR: "wR' < wR \<Longrightarrow> lllvalidFromS R wL' wR' s ltr \<Longrightarrow> lllvalidFromS R wL wR s ltr"
| 
LNil: "lllvalidFromS trn wL wR s [[]]"
|
Singl: "lllvalidFromS trn wL wR s [[s]]"
|
lappend: "validFromS s tr \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> validTrans (last tr, s'') \<Longrightarrow> 
 lllvalidFromS trn' wL' wR' s'' ltr \<Longrightarrow> 
 lllvalidFromS trn wL wR s (lappend (llist_of tr) ltr)"

lemmas lllvalidFromS_selectDelayLR = disjI1
lemmas lllvalidFromS_selectDelayL = disjI2[OF disjI1]
lemmas lllvalidFromS_selectDelayR = disjI2[OF disjI2[OF disjI1]]
lemmas lllvalidFromS_selectLNil = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas lllvalidFromS_selectSingl = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI1]]]]
lemmas lllvalidFromS_selectlappend = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI2]]]]

lemma lllvalidFromS_imp_lvalidFromS:
assumes "lllvalidFromS trn wL wR s ltr"
shows "lvalidFromS s ltr" 
proof-
  have 0: "\<exists>trn wL wR . lllvalidFromS trn wL wR s ltr" using assms by auto
  show ?thesis apply(rule lvalidFromS'_imp_lvalidFromS)
  using 0 proof(coinduct rule: lvalidFromS'.coinduct)
    case (lvalidFromS' s tr1)
    then obtain trn wL wR where 0: "lllvalidFromS trn wL wR s tr1" by auto
    then show ?case proof(induct "(trn,wL,wR)" arbitrary: trn wL wR rule: wf_induct_rule[OF "wf_TWW"]) 
      case (1 trn wL wR)
      hence 0: "lllvalidFromS trn wL wR s tr1" by simp
      then show ?case proof cases
        case (DelayLR wL' wR')
        show ?thesis apply(rule 1(1)[OF _ `lllvalidFromS L wL' wR' s tr1`])
        using DelayLR unfolding TWW_def less_turn_def by auto        
      next
        case (DelayL wL' wR')
        show ?thesis apply(rule 1(1)[OF _ `lllvalidFromS L wL' wR' s tr1`]) 
        using DelayL unfolding TWW_def less_turn_def by auto       
      next
        case (DelayR wR' wL')
        show ?thesis apply(rule 1(1)[OF _ `lllvalidFromS R wL' wR' s tr1`]) 
        using DelayR unfolding TWW_def less_turn_def by auto       
      next
        case LNil
        then show ?thesis by auto
      next
        case Singl
        then show ?thesis by auto
      next
        case  (lappend tr s'' trn' wL' wR' ltr)
        then show ?thesis by blast
      qed 
    qed
  qed      
qed

(* *)

(* Switching between ltraces and simple ltraces: *)

definition lfromS :: "'a llist \<Rightarrow> ('a \<times> 'a) llist" where 
"lfromS sl \<equiv> if sl = [[]] then [[]] else lzip (lbutlast sl) (ltl sl)"

lemma lfromS_LNil[simp]: "lfromS [[]] = [[]]"
unfolding lfromS_def by auto

lemma lfromS_singl[simp]: "lfromS [[s]] = [[]]"
unfolding lfromS_def by auto

lemma lfromS_eq_LNil[simp]: "lfromS sl = [[]] \<longleftrightarrow> lfinite sl \<and> length (list_of sl) \<le> Suc 0"
unfolding lfromS_def apply(cases sl)  
  subgoal by auto
  subgoal by simp (metis add_is_0 add_is_1 lbutlast_Cons le_0_eq le_Suc_eq 
  length_0_conv lfinite.simps list.size(4) list_of_LCons list_of_LNil 
  lstrict_prefix_code(1) lstrict_prefix_code(2) lzip_eq_LNil_conv n_not_Suc_n) .

lemma llength_lfromS_notLNil[simp]: 
"sl \<noteq> [[]] \<Longrightarrow> lfinite sl \<Longrightarrow> llength (lfromS sl) = llength sl - 1"
unfolding lfromS_def  
by simp (metis One_nat_def epred_conv_minus epred_enat epred_llength length_list_of min.idem)  

lemma llength_lfromS_not_lfinite[simp]: 
"\<not> lfinite sl \<Longrightarrow> llength (lfromS sl) = \<infinity>"
unfolding lfromS_def by (auto simp: not_lfinite_llength)  

lemma llength_lfromS_less1: "llength (lfromS sl) = llength sl - 1"
by (metis idiff_0 idiff_infinity lfromS_LNil llength_LNil llength_eq_infty_conv_lfinite 
llength_lfromS_notLNil llength_lfromS_not_lfinite)

(* Switching between finite and infinite validity: *)

lemma lfinite_lvalidFromS_validFromS: "lfinite tr \<Longrightarrow> lvalidFromS s tr \<longleftrightarrow> validFromS s (list_of tr)"
apply(induct arbitrary: s rule: lfinite.induct)
  subgoal by simp  
  subgoal by simp (metis lvalidFromS_Cons_iff hd_list_of lfinite_LNil list_of_LNil llist_of_list_of 
   validFromS_Cons_iff) .

lemma lvalidFromS_llist_of_validFromS: "lvalidFromS s (llist_of tr) \<longleftrightarrow> validFromS s tr"
by (simp add: lfinite_lvalidFromS_validFromS)

lemma validS_append: 
assumes tr1: "validS tr1" and tr12: "validTrans (last tr1, hd tr2)" 
and tr2: "validS tr2"
shows "validS (append tr1 tr2)" 
apply(cases "tr1 = [] \<or> tr2 = []")
  subgoal using assms by auto
  subgoal 
  using assms unfolding validS_def nth_append apply safe
    subgoal for i apply(cases "i < length tr1 - Suc 0")
      subgoal by auto
      subgoal apply(cases "i = length tr1 - Suc 0")
        subgoal by auto (metis One_nat_def hd_conv_nth last_conv_nth)
        subgoal apply(subgoal_tac "i - length tr1 < length tr2 - Suc 0")
          subgoal by auto (metis Suc_diff_le linorder_not_less)
          subgoal by auto . . . . .

lemma lvalidS_lappend: 
assumes tr1: "lvalidS tr1" and tr12: "validTrans (llast tr1, lhd tr2)" 
and tr2: "lvalidS tr2"
shows "lvalidS (lappend tr1 tr2)" 
unfolding lvalidS_def proof safe
  fix i assume i: "enat i < llength (lappend tr1 tr2) - 1"
  show "validTrans (lnth (lappend tr1 tr2) i, lnth (lappend tr1 tr2) (Suc i))"
  proof(cases "Suc i < llength tr1")
    case True
    hence l: "lnth (lappend tr1 tr2) i = lnth tr1 i"
    and l': "lnth (lappend tr1 tr2) (Suc i) = lnth tr1 (Suc i)"
    using lnth_lappend1 by (metis Suc_ile_eq order_less_le)+
    show ?thesis unfolding l l' using tr1 True unfolding lvalidS_def  
      by (metis Suc_ile_eq diff_Suc_1 enat_llength_ldropn llength_ldropn one_enat_def)
  next
    case False note s = False
    show ?thesis proof(cases "i < llength tr1")
      case True
      have si: "Suc i = llength tr1" using s True 
        by (simp add: Suc_ile_eq order_less_le)
      hence l: "lnth (lappend tr1 tr2) i = llast tr1"
      and l': "lnth (lappend tr1 tr2) (Suc i) = lhd tr2"     
      apply (metis True eSuc_enat llast_conv_lnth lnth_lappend1)  
        by (metis diff_Suc_1 diff_self_eq_0 i idiff_enat_enat lappend_lnull2 lhd_conv_lnth 
        linorder_neq_iff lnth_lappend one_enat_def si the_enat.simps) 
      show ?thesis using tr12 unfolding l l'  .
    next
      case False  
      then obtain n1 where n1: "llength tr1 = enat n1"  
        by fastforce
      hence l: "lnth (lappend tr1 tr2) i = lnth tr2 (i - n1)"
      and l': "lnth (lappend tr1 tr2) (Suc i) = lnth tr2 (Suc (i - n1))" 
      apply (metis False lnth_lappend the_enat.simps) 
      by (metis False Suc_diff_le enat_ord_simps(2) linorder_le_less_linear lnth_lappend n1 s the_enat.simps)
      have nn1: "i - n1 < llength tr2 - 1" using i n1 
      apply(cases "llength tr2", auto simp: algebra_simps) 
        by (metis False add_diff_cancel_right' diff_commute diff_diff_left enat_ord_simps(2) idiff_enat_enat 
       linordered_semidom_class.add_diff_inverse one_enat_def zero_less_diff) 
      show ?thesis using tr2 nn1 unfolding l l' unfolding lvalidS_def by auto
    qed
  qed
qed

lemma validS_append1: 
assumes "validS (append tr1 tr2)" "tr1 \<noteq> []"
shows "validS tr1"
using assms apply(induct tr1, auto)
by (metis Simple_Transition_System.validFromS_Cons_iff append_Cons neq_Nil_conv validFromS_def)

lemma lvalidS_lappend1: 
assumes "lvalidS (lappend tr1 tr2)"
shows "lvalidS tr1"
using assms unfolding lvalidS_def apply clarify subgoal for i apply simp
apply(erule allE[of _ i])
apply(subst (asm) lnth_lappend1)
  subgoal by (metis co.enat.exhaust dual_order.strict_trans1 eSuc_minus_1 enat_le_plus_same(1) idiff_0 plus_1_eSuc(2))
  subgoal apply(subst (asm) lnth_lappend1)
    subgoal by (metis \<open>enat i < llength tr1 - 1 \<Longrightarrow> enat i < llength tr1\<close> eSuc_enat eSuc_minus_1 ileI1 order_less_le)
    subgoal by (meson dual_order.strict_trans1 enat_le_plus_same(1) enat_minus_mono1) . . .

lemma validS_append2: 
assumes "validS (append tr1 tr2)" "tr2 \<noteq> []"
shows "validS tr2"
using assms apply(induct tr1, auto)
by (metis validFromS_def validS_Nil validFromS_Cons_iff)

lemma lvalidS_lappend2: 
assumes "lfinite tr1" "lvalidS (lappend tr1 tr2)"
shows "lvalidS tr2"
using assms unfolding lvalidS_def apply clarify subgoal for i apply simp
apply(cases "llength tr1")
  subgoal for n1 
  apply(erule allE[of _ "n1+i"])
  apply(subst (asm) lnth_lappend2[of _ n1])
    subgoal by simp
    subgoal by simp
    subgoal apply(subst (asm) lnth_lappend2[of _ n1])
      subgoal by simp
      subgoal by simp
      subgoal by simp (metis add_diff_assoc_enat enat_less_enat_plusI2 ldropn_eq_LNil 
       llength_LNil llength_ldropn nle_le not_less_zero one_enat_def) . .
  subgoal using llength_eq_infty_conv_lfinite by blast . . 

lemma validS_validTrans: 
assumes tr1: "tr1 \<noteq> []" and tr2: "tr2 \<noteq> []" and v: "validS (append tr1 tr2)"
shows "validTrans (last tr1, hd tr2)"
using tr1 tr2 v[unfolded validS_def, rule_format, of "length tr1 - Suc 0"] 
unfolding nth_append hd_conv_nth[OF tr2] last_conv_nth[OF tr1]
by simp (metis Suc_pred add_gr_0 add_less_cancel_left length_greater_0_conv less_add_same_cancel1 plus_1_eq_Suc)

lemma lvalidS_validTrans: 
assumes "tr1 \<noteq> [[]]" "tr2 \<noteq> [[]]" "lfinite tr1" "lvalidS (lappend tr1 tr2)"
shows "validTrans (llast tr1, lhd tr2)"
apply(cases "llength tr1")
  subgoal for n1 
  using assms unfolding lvalidS_def apply(elim allE[of _ "n1-1"])
  apply(subst (asm) lnth_lappend1)
    subgoal  
    by simp (metis diff_less llength_eq_0 lnull_def not_gr_zero zero_enat_def zero_less_Suc)
    subgoal apply(subst (asm) lnth_lappend2[of _ n1])
      subgoal by simp
      subgoal by simp
      subgoal by simp (metis One_nat_def Suc_ile_eq Suc_pred add_diff_assoc_enat 
       cancel_comm_monoid_add_class.diff_cancel eSuc_enat enat_le_plus_same(1) 
       enat_ord_simps(2) i0_less lhd_conv_lnth llast_conv_lnth llength_eq_0 lnull_def one_enat_def zero_enat_def) . .
  subgoal using assms(3) llength_eq_infty_conv_lfinite by blast .

(* *)

lemma validS_reach: 
assumes "istate (hd tr)" "validS tr" 
shows "reach (last tr)"
by (metis (no_types, lifting) Istate fromS_eq_Nil hd_Nil_eq_last 
 hd_conv_nth assms last_conv_nth length_fromS_less1 linorder_not_less list.size(3) 
 nat_neq_iff toS_fromS_nonSingl toS_last toS_nth_0 valid_fromS valid_reach_src_tgt)

lemma validFromS_reach: 
assumes "istate s" "validFromS s tr" "tr \<noteq> []"
shows "reach (last tr)"
using assms unfolding validFromS_def using validS_reach by blast

lemma reach_validFromS_reach: 
assumes "reach s" "validFromS s tr" "tr \<noteq> []"
shows "reach (last tr)"
by (metis (no_types, lifting) Simple_Transition_System.validFromS_reach 
  Transition_System.reach_init_valid assms valid_reach_src_tgt)

lemma lvalidFromS_reach: 
assumes i: "istate s" and l: "lvalidFromS s tr" and s': "s' \<in> lset tr"
shows "reach s'"
proof-
  obtain tr1 tr2 where tr1: "lfinite tr1" "llast tr1 = s'" "tr1 \<noteq> [[]]" "tr = lappend tr1 tr2"
  using s'  
  by (metis LNil_eq_lappend_iff lappend_snocL1_conv_LCons2 lfinite_LConsI lfinite_lappend 
  llast_lappend_LCons llast_singleton llist.distinct(1) split_llist_first)
  hence "lvalidFromS s tr1" 
   by (metis LNil_eq_lappend_iff l lhd_lappend lnull_def lvalidFromS_def lvalidS_lappend1)
  hence "validFromS s (list_of tr1) \<and> last (list_of tr1) = s'" using tr1
  by (metis lfinite_lvalidFromS_validFromS llast_llist_of llist_of_list_of)
  thus ?thesis 
  by (metis i llist_of.simps(1) llist_of_list_of tr1(1) tr1(3) validFromS_reach)
qed

(* *)

lemma validFromS_append: 
"tr1 \<noteq> [] \<Longrightarrow> tr1' \<noteq> [] \<Longrightarrow> validFromS s1 tr1 \<Longrightarrow> validFromS (lastt s1 tr1) tr1' \<Longrightarrow> 
 validFromS s1 (butlast tr1 @ tr1')"
apply(cases "butlast tr1 = []")
  subgoal apply simp by(cases tr1, auto split: if_splits simp: lastt_def)
  subgoal unfolding validFromS_def apply(rule disjI2)
  apply(rule conjI)
    subgoal by (metis append_butlast_last_id hd_append2)
    subgoal by (metis validS_append append_butlast_last_id lastt_def list.sel(1) list.simps(3) validS_append1 validS_validTrans) 
  . .  

(* *)

lemma lprefix_lvalidS: "lvalidS tr \<Longrightarrow> lprefix tr' tr \<Longrightarrow> lvalidS tr'"
by (metis lvalidS_lappend1 lprefix_conv_lappend)

lemma lprefix_lvalidFromS: "lvalidFromS s tr \<Longrightarrow> lprefix tr' tr \<Longrightarrow> lvalidFromS s tr'"
by (metis lvalidFromS_def lhd_LCons llist.distinct(1) lprefix.cases lprefix_lvalidS)

lemma lprefix_lvalidFrom_validFrom: "lvalidFromS s tr \<Longrightarrow> lprefix (llist_of tr') tr \<Longrightarrow> validFromS s tr'"
using lprefix_lvalidFromS lvalidFromS_llist_of_validFromS by blast

lemma lsublist_lvalidS: "lvalidS tr \<Longrightarrow> lsublist tr' tr \<Longrightarrow> lvalidS tr'"
by (metis lvalidS_lappend1 lvalidS_lappend2 lsublist_def)

lemma lsublist_lvalidromS: "lvalidFromS s tr \<Longrightarrow> lsublist tr' tr \<Longrightarrow> tr' \<noteq> LNil \<Longrightarrow> lvalidFromS (lhd tr') tr'"
using lsublist_lvalidS lvalidFromS_def by auto

lemma lvalidS_LCons_iff: 
"lvalidS (s $ tr) = (validTrans (s,lhd tr) \<and> lvalidS tr \<or> tr = [[]])"
using lvalidFromS_Cons_iff lvalidFromS_def by auto

lemma lvalidS_lappend_finite: 
"tr \<noteq> [] \<Longrightarrow> tr1 \<noteq> [[]] \<Longrightarrow> 
 lvalidS (lappend (llist_of tr) tr1) = (validS tr \<and> lvalidS tr1 \<and> validTrans (last tr,lhd tr1))"
apply (induct tr)  
  apply blast 
  by simp (metis Simple_Transition_System.validFromS_def lappend_eq_LNil_iff lhd_lappend lhd_llist_of list.simps(3) lnull_llist_of lvalidS_LCons_iff validFromS_Cons_iff)

lemma lvalidS_llist_of[simp]: "lvalidS (llist_of tr) \<longleftrightarrow> validS tr"
by (metis lvalidFromS_def lvalidFromS_llist_of_validFromS 
lvalidS_LNil Simple_Transition_System.validFromS_def Simple_Transition_System.validS_Nil)

lemma lvalidFromS_lappend_finite: 
"lvalidFromS s (lappend (llist_of tr) tr1) \<longleftrightarrow> 
 validFromS s tr \<and> 
 (tr1 = [[]] \<or> 
  lvalidFromS (lhd tr1) tr1 \<and>
  (tr = [] \<and> s = lhd tr1 \<or> (tr \<noteq> [] \<and> validTrans (last tr, lhd tr1))))"
apply(cases "tr \<noteq> [] \<and> tr1 \<noteq> [[]]")
  subgoal unfolding validFromS_def lvalidFromS_def lastt_def 
  by (auto simp: lvalidS_lappend_finite lappend_eq_LNil_iff)
  subgoal
  by (metis lappend_LNil2 lappend_code(1) llist_of.simps(1) 
   lvalidFromS_def lvalidFromS_llist_of_validFromS) .

lemma lvalidFromS_lappend_finite': 
"tr1 \<noteq> [[]] \<Longrightarrow> 
 lvalidFromS s (lappend (llist_of tr) tr1) \<longleftrightarrow> 
 validFromS s tr \<and> 
 lvalidFromS (lhd tr1) tr1 \<and>
 (tr = [] \<and> s = lhd tr1 \<or> 
  tr \<noteq> [] \<and> validTrans (last tr, lhd tr1))"
unfolding lvalidFromS_lappend_finite by auto

lemma lvalidFromS_lappend_LCons: 
"lvalidFromS s (lappend (llist_of tr) (s' $ tr1)) \<longleftrightarrow> 
 validFromS s tr \<and> 
 lvalidFromS s' ((s' $ tr1)) \<and>
 (tr = [] \<and> s = s' \<or> 
  tr \<noteq> [] \<and> validTrans (last tr, s'))"
apply(subst lvalidFromS_lappend_finite') by auto


end (*context Simple_Transition_System *)


subsection \<open>Completed finite and possibly infinite traces in simple transition systems \<close>

(* A completed possibly infinite trace is one that is either infinite or, if finite, 
ends up in final state. In the "Relative Security" paper, we just call these 
:traces:.  *)

context System_Mod
begin

definition completedFrom :: "'state \<Rightarrow> 'state list \<Rightarrow> bool" where 
"completedFrom s sl \<equiv> (sl = [] \<and> final s) \<or> (sl \<noteq> [] \<and> final (last sl))"

lemma completed_Nil[simp,intro]: "completedFrom s [] \<longleftrightarrow> final s"
unfolding completedFrom_def by auto

lemma completed_Cons[simp]: "completedFrom s' (s # sl) \<longleftrightarrow> (sl = [] \<and> final s) \<or> (sl \<noteq> [] \<and> completedFrom s sl)"
unfolding completedFrom_def by auto

definition lcompletedFrom :: "'state \<Rightarrow> 'state llist \<Rightarrow> bool" where 
"lcompletedFrom s sl \<equiv> 
 lfinite sl \<longrightarrow>  
 (sl \<noteq> [[]] \<and> final (last (list_of sl)))"

lemma lcompletedFrom_LCons[simp]: "lcompletedFrom s' (s $ sl) \<longleftrightarrow> 
 (lfinite sl \<longrightarrow>  (sl = [[]] \<and> final s) \<or> (sl \<noteq> [[]] \<and> lcompletedFrom s sl))"
unfolding lcompletedFrom_def using llist_of_list_of by auto fastforce+

lemma lvalid_lappend_finite: 
"tr \<noteq> [] \<Longrightarrow> tr1 \<noteq> [[]] \<Longrightarrow> 
 lvalid (lappend (llist_of tr) tr1) = (valid tr \<and> lvalid tr1 \<and> snd (last tr) = fst (lhd tr1))"
apply (induct tr) by (auto simp add: lvalid_LCons_iff lappend_eq_LNil_iff)  

lemma lcompletedFrom_singl: "llength tr = enat (Suc 0) \<Longrightarrow> 
    lvalidFromS s tr \<Longrightarrow> 
    lcompletedFrom s tr \<longleftrightarrow> tr = [[s]] \<and> final s"
apply(cases tr)
  subgoal by (simp add: enat_0_iff(1)) 
  subgoal for s' tr' unfolding lcompletedFrom_def  
  by simp (metis lvalidFromS_Cons_iff One_nat_def eSuc_inject 
   lfinite_LNil list_of_LNil llength_eq_0 lnull_def one_eSuc one_enat_def) .

end (* context System_Mod *)



end


