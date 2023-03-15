(*  Title:       POSIX Lexing with Derivatives of Extended Regular Expressions
    Author:      Christian Urban <christian.urban at kcl.ac.uk>, 2022
    Maintainer:  Christian Urban <christian.urban at kcl.ac.uk>
*) 

theory Lexer3
  imports "Derivatives3"
begin

section \<open>Values\<close>

datatype 'a val = 
  Void
| Atm 'a
| Seq "'a val" "'a val"
| Right "'a val"
| Left "'a val"
| Stars "('a val) list"
| Recv string "'a val"


section \<open>The string behind a value\<close>

fun 
  flat :: "'a val \<Rightarrow> 'a list"
where
  "flat (Void) = []"
| "flat (Atm c) = [c]"
| "flat (Left v) = flat v"
| "flat (Right v) = flat v"
| "flat (Seq v1 v2) = (flat v1) @ (flat v2)"
| "flat (Stars []) = []"
| "flat (Stars (v#vs)) = (flat v) @ (flat (Stars vs))" 
| "flat (Recv l v) = flat v"

abbreviation
  "flats vs \<equiv> concat (map flat vs)"

lemma flat_Stars [simp]:
 "flat (Stars vs) = concat (map flat vs)"
  by (induct vs) (auto)

lemma flats_empty:
  assumes "(\<forall>v\<in>set vs. flat v = [])"
  shows "flats vs = []"
using assms
by(induct vs) (simp_all)

section \<open>Relation between values and regular expressions\<close>

inductive 
  Prf :: "'a val \<Rightarrow> 'a rexp \<Rightarrow> bool" ("\<turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<turnstile> Seq v1 v2 : Times r1 r2"
| "\<turnstile> v1 : r1 \<Longrightarrow> \<turnstile> Left v1 : Plus r1 r2"
| "\<turnstile> v2 : r2 \<Longrightarrow> \<turnstile> Right v2 : Plus r1 r2"
| "\<turnstile> Void : One"
| "\<turnstile> Atm c : Atom c"
| "\<lbrakk>\<forall>v \<in> set vs. \<turnstile> v : r \<and> flat v \<noteq> []\<rbrakk> \<Longrightarrow> \<turnstile> Stars vs : Star r"
| "\<lbrakk>\<forall>v \<in> set vs1. \<turnstile> v : r \<and> flat v \<noteq> []; 
    \<forall>v \<in> set vs2. \<turnstile> v : r \<and> flat v = []; 
    length (vs1 @ vs2) = n\<rbrakk> \<Longrightarrow> \<turnstile> Stars (vs1 @ vs2) : NTimes r n"
| "\<lbrakk>\<forall>v \<in> set vs. \<turnstile> v : r \<and> flat v \<noteq> []; length vs \<le> n\<rbrakk> \<Longrightarrow> \<turnstile> Stars vs : Upto r n"
| "\<lbrakk>\<forall>v \<in> set vs1. \<turnstile> v : r  \<and> flat v \<noteq> []; 
    \<forall>v \<in> set vs2. \<turnstile> v : r \<and> flat v = []; 
    length (vs1 @ vs2) = n\<rbrakk> \<Longrightarrow> \<turnstile> Stars (vs1 @ vs2) : From r n"
| "\<lbrakk>\<forall>v \<in> set vs. \<turnstile> v : r  \<and> flat v \<noteq> []; length vs > n\<rbrakk> \<Longrightarrow> \<turnstile> Stars vs : From r n"
| "\<turnstile> v : r \<Longrightarrow> \<turnstile> Recv l v : Rec l r"
| "c \<in> cs \<Longrightarrow> \<turnstile> Atm c : Charset cs"

inductive_cases Prf_elims:
  "\<turnstile> v : Zero"
  "\<turnstile> v : Times r1 r2"
  "\<turnstile> v : Plus r1 r2"
  "\<turnstile> v : One"
  "\<turnstile> v : Atom c"
  "\<turnstile> v : Star r"
  "\<turnstile> v : NTimes r n"
  "\<turnstile> v : Upto r n"
  "\<turnstile> v : From r n"
  "\<turnstile> v : Rec l r"
  "\<turnstile> v : Charset cs"

lemma Prf_NTimes_empty:
  assumes "\<forall>v \<in> set vs. \<turnstile> v : r \<and> flat v = []" 
  and     "length vs = n"
  shows "\<turnstile> Stars vs : NTimes r n"
  using assms
  by (metis Prf.intros(7) empty_iff eq_Nil_appendI list.set(1))
  

lemma Times_decomp:
  assumes "s \<in> A @@ B"
  shows "\<exists>s1 s2. s = s1 @ s2 \<and> s1 \<in> A \<and> s2 \<in> B"
  using assms
  by blast

lemma pow_string:
  assumes "s \<in> A ^^ n"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A) \<and> length ss = n"
using assms
  apply(induct n arbitrary: s)
  apply(auto dest!: Times_decomp)
  apply(drule_tac x="s2" in meta_spec)
  apply(auto)
  apply(rule_tac x="s1 # ss" in exI)
  apply(simp)
  done

lemma pow_Prf:
  assumes "\<forall>v\<in>set vs. \<turnstile> v : r \<and> flat v \<in> A"
  shows "flats vs \<in> A ^^ (length vs)"
  using assms
  by (induct vs) (auto)

lemma Star_string:
  assumes "s \<in> star A"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A)"
using assms
by (metis in_star_iff_concat subsetD)

lemma Star_val:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<turnstile> v : r"
  shows "\<exists>vs. flats vs = concat ss \<and> (\<forall>v\<in>set vs. \<turnstile> v : r \<and> flat v \<noteq> [])"
using assms
apply(induct ss)
apply(auto)
apply (metis empty_iff list.set(1))
by (metis append.simps(1) flat.simps(7) flat_Stars set_ConsD)

lemma Aux:
  assumes "\<forall>s\<in>set ss. s = []"
  shows "concat ss = []"
using assms
by (induct ss) (auto)

lemma pow_cstring:
  assumes "s \<in> A ^^ n"
  shows "\<exists>ss1 ss2. concat (ss1 @ ss2) = s \<and> length (ss1 @ ss2) = n \<and> 
         (\<forall>s \<in> set ss1. s \<in> A \<and> s \<noteq> []) \<and> (\<forall>s \<in> set ss2. s \<in> A \<and> s = [])"
using assms
apply(induct n arbitrary: s)
  apply(auto)[1]
  apply(auto dest!: Times_decomp simp add: Seq_def)
  apply(drule_tac x="s2" in meta_spec)
  apply(simp)
apply(erule exE)+
  apply(clarify)
apply(case_tac "s1 = []")
apply(simp)
apply(rule_tac x="ss1" in exI)
apply(rule_tac x="s1 # ss2" in exI)
apply(simp)
apply(rule_tac x="s1 # ss1" in exI)
apply(rule_tac x="ss2" in exI)
  apply(simp)
  done

lemma flats_cval:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<turnstile> v : r"
  shows "\<exists>vs1 vs2. flats vs1 = concat ss \<and> length (vs1 @ vs2) = length ss \<and> 
          (\<forall>v\<in>set vs1. \<turnstile> v : r \<and> flat v \<noteq> []) \<and>
          (\<forall>v\<in>set vs2. \<turnstile> v : r \<and> flat v = [])"
using assms
apply(induct ss rule: rev_induct)
apply(rule_tac x="[]" in exI)+
apply(simp)
apply(simp)
  apply(clarify)
  apply(case_tac "flat v = []")
  apply(rule_tac x="vs1" in exI)
  apply(simp)
apply(rule_tac x="v#vs2" in exI)
apply(simp)
  apply(rule_tac x="vs1 @ [v]" in exI)
  apply(simp)
apply(rule_tac x="vs2" in exI)
apply(simp)
  done

lemma flats_cval2:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<turnstile> v : r"
  shows "\<exists>vs. flats vs = concat ss \<and> length vs \<le> length ss \<and> (\<forall>v\<in>set vs. \<turnstile> v : r \<and> flat v \<noteq> [])"
  using assms
  apply -
  apply(drule flats_cval)
  apply(auto)
  done


lemma Prf_flat_lang:
  assumes "\<turnstile> v : r" shows "flat v \<in> lang r"
using assms
  apply(induct v r rule: Prf.induct) 
  apply(auto simp add: concat_in_star subset_eq lang_pow_add)
  apply(meson concI pow_Prf)
  apply(meson atMost_iff pow_Prf)
  apply(subgoal_tac "flats vs1 @ flats vs2 \<in> lang r ^^ length vs1")
  apply (metis add_diff_cancel_left' atLeast_iff diff_is_0_eq empty_pow_add last_in_set length_0_conv order_refl)
  apply (metis (no_types, opaque_lifting) Aux imageE list.set_map pow_Prf self_append_conv)
  apply (meson atLeast_iff less_imp_le_nat pow_Prf)
  done

lemma L_flat_Prf2:
  assumes "s \<in> lang r" 
  shows "\<exists>v. \<turnstile> v : r \<and> flat v = s"
using assms
proof(induct r arbitrary: s)
  case (Star r s)
  have IH: "\<And>s. s \<in> lang r \<Longrightarrow> \<exists>v.\<turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> lang (Star r)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> lang r \<and> s \<noteq> []"
    by (smt (z3) IH Prf_flat_lang Star_val imageE in_star_iff_concat lang.simps(6) list.set_map subset_iff)  
  then obtain vs where "flats vs = s" "\<forall>v\<in>set vs. \<turnstile> v : r \<and> flat v \<noteq> []"
  using IH by (metis Star_val) 
  then show "\<exists>v. \<turnstile> v : Star r \<and> flat v = s"
  using Prf.intros(6) flat_Stars by blast
next 
  case (Times r1 r2 s)
  then show "\<exists>v. \<turnstile> v : Times r1 r2 \<and> flat v = s"
  unfolding Seq_def lang.simps by (fastforce intro: Prf.intros)
next
  case (Plus r1 r2 s)
  then show "\<exists>v. \<turnstile> v : Plus r1 r2 \<and> flat v = s"
  unfolding lang.simps by (fastforce intro: Prf.intros)
next
  case (NTimes r n)
  have IH: "\<And>s. s \<in> lang r \<Longrightarrow> \<exists>v. \<turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> lang (NTimes r n)" by fact
  then obtain ss1 ss2 where "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = n" 
    "\<forall>s \<in> set ss1. s \<in> lang r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> lang r \<and> s = []"
  using pow_cstring by force
  then obtain vs1 vs2 where "flats (vs1 @ vs2) = s" "length (vs1 @ vs2) = n" 
      "\<forall>v\<in>set vs1. \<turnstile> v : r \<and> flat v \<noteq> []" "\<forall>v\<in>set vs2. \<turnstile> v : r \<and> flat v = []"
    using IH flats_cval  
  apply -
  apply(drule_tac x="ss1 @ ss2" in meta_spec)
  apply(drule_tac x="r" in meta_spec)
  apply(drule meta_mp)
  apply(simp)
  apply (metis Un_iff)
  apply(clarify)
  apply(drule_tac x="vs1" in meta_spec)
  apply(drule_tac x="vs2" in meta_spec)
  apply(simp)
  done
  then show "\<exists>v. \<turnstile> v : NTimes r n \<and> flat v = s"
    using Prf.intros(7) flat_Stars by blast
next
  case (Upto r n)
  have IH: "\<And>s. s \<in> lang r \<Longrightarrow> \<exists>v.\<turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> lang (Upto r n)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> lang r \<and> s \<noteq> []" "length ss \<le> n"
    apply(auto)
    by (smt (verit) Nil_eq_concat_conv pow_cstring concat_append le0 le_add_same_cancel1 le_trans length_append self_append_conv)    
  then obtain vs where "flats vs = s" "\<forall>v\<in>set vs. \<turnstile> v : r \<and> flat v \<noteq> []" "length vs \<le> n"
  using IH flats_cval2
  by (smt (verit, best) le_trans) 
  then show "\<exists>v. \<turnstile> v : Upto r n \<and> flat v = s"
    by (meson Prf.intros(8) flat_Stars) 
next
  case (From r n)
  have IH: "\<And>s. s \<in> lang r \<Longrightarrow> \<exists>v. \<turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> lang (From r n)" by fact
  then obtain ss1 ss2 k where "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = k"  "n \<le> k"
    "\<forall>s \<in> set ss1. s \<in> lang r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> lang r \<and> s = []"
    using pow_cstring by force 
  then obtain vs1 vs2 where "flats (vs1 @ vs2) = s" "length (vs1 @ vs2) = k" "n \<le> k"
      "\<forall>v\<in>set vs1. \<turnstile> v : r \<and> flat v \<noteq> []" "\<forall>v\<in>set vs2. \<turnstile> v : r \<and> flat v = []"
    using IH flats_cval  
  apply -
  apply(drule_tac x="ss1 @ ss2" in meta_spec)
  apply(drule_tac x="r" in meta_spec)
  apply(drule meta_mp)
  apply(simp)
  apply (metis Un_iff)
  apply(clarify)
  apply(drule_tac x="vs1" in meta_spec)
  apply(drule_tac x="vs2" in meta_spec)
  apply(simp)
  done
  then show "\<exists>v. \<turnstile> v : From r n \<and> flat v = s"
    apply(case_tac "length vs1 \<le> n")
    apply(rule_tac x="Stars (vs1 @ take (n - length vs1) vs2)" in exI)
     apply(simp)
     apply(subgoal_tac "flats (take (n - length vs1) vs2) = []")
      apply(auto)
       apply(rule Prf.intros(9))
       apply(auto)
    apply (meson in_set_takeD)
    apply (simp add: Aux)
    apply (meson in_set_takeD)
    apply(rule_tac x="Stars vs1" in exI)
    by (simp add: Prf.intros(10))
next
  case (Rec l r)
  then show ?case apply(auto)
    using Prf.intros(11) flat.simps(8) by blast
qed (auto intro: Prf.intros)

lemma L_flat_Prf:
  "lang r = {flat v | v. \<turnstile> v : r}"
  using L_flat_Prf2 Prf_flat_lang by blast


section \<open>Sulzmann and Lu functions\<close>

fun 
  mkeps :: "'a rexp \<Rightarrow> 'a val"
where
  "mkeps(One) = Void"
| "mkeps(Times r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(Plus r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(Star r) = Stars []"
| "mkeps(Upto r n) = Stars []"
| "mkeps(NTimes r n) = Stars (replicate n (mkeps r))"
| "mkeps(From r n) = Stars (replicate n (mkeps r))"
| "mkeps(Rec l r) = Recv l (mkeps r)"

fun injval :: "'a rexp \<Rightarrow> 'a \<Rightarrow> 'a val \<Rightarrow> 'a val"
where
  "injval (Atom d) c Void = Atm c"
| "injval (Plus r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (Plus r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (Times r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (Times r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (Times r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"
| "injval (Star r) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 
| "injval (NTimes r n) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 
| "injval (Upto r n) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 
| "injval (From r n) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)"
| "injval (Rec l r) c v = Recv l (injval r c v)"
| "injval (Charset cs) c Void = Atm c"

section \<open>Mkeps, injval\<close>

lemma mkeps_flat:
  assumes "nullable(r)" 
  shows "flat (mkeps r) = []"
using assms
  by (induct rule: mkeps.induct) (auto)

lemma mkeps_nullable:
  assumes "nullable r" 
  shows "\<turnstile> mkeps r : r"
using assms
  apply (induct r) 
  apply (auto intro: Prf.intros split: if_splits)
  apply (metis Prf.intros(7) append_Nil2 in_set_replicate list.size(3) replicate_0)
  apply(rule Prf_NTimes_empty)
  apply(auto simp add: mkeps_flat)
  apply (metis Prf.intros(9) append_Nil empty_iff list.set(1) list.size(3))
  by (metis Prf.intros(9) append_Nil empty_iff in_set_replicate length_replicate list.set(1) mkeps_flat)

lemma Prf_injval_flat:
  assumes "\<turnstile> v : deriv c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct c r arbitrary: v rule: deriv.induct)
apply(auto elim!: Prf_elims intro: mkeps_flat split: if_splits)
done

lemma Prf_injval:
  assumes "\<turnstile> v : deriv c r" 
  shows "\<turnstile> (injval r c v) : r"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims simp add: Prf_injval_flat split: if_splits)[7]
(* NTimes *)
apply(case_tac x2)
apply(simp)
apply(simp)
apply(subst append.simps(2)[symmetric])
apply(rule Prf.intros)
apply(auto simp add: Prf_injval_flat)[4]
(* Upto *)
apply(case_tac x2)
apply(simp)
using Prf_elims(1) apply blast
apply(simp)
apply(erule Prf_elims)
apply(erule Prf_elims(8))
apply(simp)
apply(rule Prf.intros(8))
apply(auto simp add: Prf_injval_flat)[2]  
(* From *)
apply(simp)  
apply(case_tac x2)
apply(simp)
apply(erule Prf_elims)
apply(simp)
apply(erule Prf_elims(6))
apply(simp)
apply (simp add: Prf.intros(10) Prf_injval_flat)
apply(simp)
apply(erule Prf_elims)
apply(simp)
apply(erule Prf_elims(9))
apply(simp)
apply (smt (verit, best) Cons_eq_appendI Prf.intros(9) Prf_injval_flat length_Cons length_append list.discI set_ConsD)
apply(simp add: Prf.intros(10) Prf_injval_flat)
apply(simp add: Prf.intros(11))
by (metis Prf.intros(12) Prf_elims(1) Prf_elims(4) deriv.simps(11) injval.simps(12))


section \<open>Our Alternative Posix definition\<close>

inductive 
  Posix :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> 'a val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  Posix_One: "[] \<in> One \<rightarrow> Void"
| Posix_Atom: "[c] \<in> (Atom c) \<rightarrow> (Atm c)"
| Posix_Plus1: "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (Plus r1 r2) \<rightarrow> (Left v)"
| Posix_Plus2: "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> lang r1\<rbrakk> \<Longrightarrow> s \<in> (Plus r1 r2) \<rightarrow> (Right v)"
| Posix_Times: "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (Times r1 r2) \<rightarrow> (Seq v1 v2)"
| Posix_Star1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> Star r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> Star r \<rightarrow> Stars (v # vs)"
| Posix_Star2: "[] \<in> Star r \<rightarrow> Stars []"
| Posix_NTimes1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> NTimes r n \<rightarrow> Stars vs; flat v \<noteq> []; 
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r \<and> s\<^sub>4 \<in> lang (NTimes r n))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> NTimes r (n + 1) \<rightarrow> Stars (v # vs)"
| Posix_NTimes2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n\<rbrakk>
    \<Longrightarrow> [] \<in> NTimes r n \<rightarrow> Stars vs" 
| Posix_Upto1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> Upto r n \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r \<and> s\<^sub>4 \<in> lang (Upto r n))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> Upto r (n + 1) \<rightarrow> Stars (v # vs)"
| Posix_Upto2: "[] \<in> Upto r n \<rightarrow> Stars []"
| Posix_From2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n\<rbrakk>
    \<Longrightarrow> [] \<in> From r n \<rightarrow> Stars vs"
| Posix_From1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> From r (n - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < n;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r \<and> s\<^sub>4 \<in> lang (From r (n - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> From r n \<rightarrow> Stars (v # vs)"  
| Posix_From3: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> Star r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> From r 0 \<rightarrow> Stars (v # vs)"  
| Posix_Rec: "s \<in> r \<rightarrow> v \<Longrightarrow> s \<in> (Rec l r) \<rightarrow> (Recv l v)"
| Posix_Cset: "c \<in> cs \<Longrightarrow> [c] \<in> (Charset cs) \<rightarrow> (Atm c)"

inductive_cases Posix_elims:
  "s \<in> Zero \<rightarrow> v"
  "s \<in> One \<rightarrow> v"
  "s \<in> Atom c \<rightarrow> v"
  "s \<in> Plus r1 r2 \<rightarrow> v"
  "s \<in> Times r1 r2 \<rightarrow> v"
  "s \<in> Star r \<rightarrow> v"
  "s \<in> NTimes r n \<rightarrow> v"
  "s \<in> Upto r n \<rightarrow> v"
  "s \<in> From r n \<rightarrow> v"
  "s \<in> Rec l r \<rightarrow> v"
  "s \<in> Charset cs \<rightarrow> v"

lemma Posix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> lang r" "flat v = s"
using assms
  apply (induct s r v rule: Posix.induct) 
  apply(auto simp add: pow_empty_iff)
  apply (meson ex_in_conv set_empty)
  apply(metis Suc_pred atMost_iff concI lang_pow.simps(2) not_less_eq_eq)
  apply (meson atLeast_iff dual_order.refl in_set_conv_nth)
  apply (metis Suc_le_mono Suc_pred atLeast_iff concI lang_pow.simps(2))
  by (simp add: star_pow)
  

lemma Posix1a:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r"
using assms
  apply(induct s r v rule: Posix.induct)
  apply(auto intro: Prf.intros)
  apply (metis Prf.intros(6) Prf_elims(6) set_ConsD val.inject(5))
  prefer 2
  using Posix1(2) Prf_NTimes_empty apply blast
  apply(erule Prf_elims)
  apply(auto)
  apply(subst append.simps(2)[symmetric])
  apply(rule Prf.intros)
  apply(auto)
  apply (metis (no_types, lifting) Prf.intros(8) Prf_elims(8) Suc_le_mono length_Cons set_ConsD val.inject(5))
  apply (metis Posix1(2) Prf.intros(9) append_Nil empty_iff list.set(1))
  apply(erule Prf_elims)
  apply(auto)
  apply (smt (verit, best) Cons_eq_appendI Prf.intros(9) Suc_pred length_Cons length_append set_ConsD)
  apply (simp add: Prf.intros(10))
  apply(erule Prf_elims)
  apply(auto)
  by (simp add: Prf.intros(10))
      

lemma Posix_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
using assms
apply(induct r)
apply(auto intro: Posix.intros simp add: nullable_iff)
apply(subst append.simps(1)[symmetric])
apply(rule Posix.intros)
apply(auto)
apply(simp add: Posix_NTimes2 pow_empty_iff)
apply(simp add: Posix_From2 pow_empty_iff)
done

lemma List_eq_zipI:
  assumes "\<forall>(v1, v2) \<in> set (zip vs1 vs2). v1 = v2" 
  and "length vs1 = length vs2"
  shows "vs1 = vs2"  
 using assms
  apply(induct vs1 arbitrary: vs2)
   apply(case_tac vs2)
   apply(simp)    
   apply(simp)
   apply(case_tac vs2)
   apply(simp)
  apply(simp)
done  


text \<open>Our Posix definition determines a unique value.\<close>

lemma Posix_determ:
  assumes "s \<in> r \<rightarrow> v1" "s \<in> r \<rightarrow> v2"
  shows "v1 = v2"
using assms
proof (induct s r v1 arbitrary: v2 rule: Posix.induct)
  case (Posix_One v2)
  have "[] \<in> One \<rightarrow> v2" by fact
  then show "Void = v2" by cases auto
next 
  case (Posix_Atom c v2)
  have "[c] \<in> Atom c \<rightarrow> v2" by fact
  then show "Atm c = v2" by cases auto
next 
  case (Posix_Plus1 s r1 v r2 v2)
  have "s \<in> Plus r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<in> r1 \<rightarrow> v" by fact
  then have "s \<in> lang r1" by (simp add: Posix1)
  ultimately obtain v' where eq: "v2 = Left v'" "s \<in> r1 \<rightarrow> v'" by cases auto 
  moreover
  have IH: "\<And>v2. s \<in> r1 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Left v = v2" using eq by simp
next 
  case (Posix_Plus2 s r2 v r1 v2)
  have "s \<in> Plus r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<notin> lang r1" by fact
  ultimately obtain v' where eq: "v2 = Right v'" "s \<in> r2 \<rightarrow> v'" 
    by cases (auto simp add: Posix1) 
  moreover
  have IH: "\<And>v2. s \<in> r2 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Right v = v2" using eq by simp
next
  case (Posix_Times s1 r1 v1 s2 r2 v2 v')
  have "(s1 @ s2) \<in> Times r1 r2 \<rightarrow> v'" 
       "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" by fact+
  then obtain v1' v2' where "v' = Seq v1' v2'" "s1 \<in> r1 \<rightarrow> v1'" "s2 \<in> r2 \<rightarrow> v2'"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) by fastforce+
  moreover
  have IHs: "\<And>v1'. s1 \<in> r1 \<rightarrow> v1' \<Longrightarrow> v1 = v1'"
            "\<And>v2'. s2 \<in> r2 \<rightarrow> v2' \<Longrightarrow> v2 = v2'" by fact+
  ultimately show "Seq v1 v2 = v'" by simp
next
  case (Posix_Star1 s1 r v s2 vs v2)
  have "(s1 @ s2) \<in> Star r \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> Star r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (Star r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) apply fastforce
  apply (metis Posix1(1) Posix_Star1.hyps(6) append_Nil append_Nil2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> Star r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_Star2 r v2)
  have "[] \<in> Star r \<rightarrow> v2" by fact
  then show "Stars [] = v2" by cases (auto simp add: Posix1)
next
  case (Posix_NTimes2 vs r n v2)
  then show "Stars vs = v2"
    apply(erule_tac Posix_elims)
     apply(auto)
     apply (simp add: Posix1(2))    
    apply(rule List_eq_zipI)
     apply(auto)
    by (meson in_set_zipE)
next
  case (Posix_NTimes1 s1 r v s2 n vs)
  have "(s1 @ s2) \<in> NTimes r (n + 1) \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> NTimes r n \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (NTimes r n))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (NTimes r n) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) apply fastforce
    apply (metis Posix1(1) Posix_NTimes1.hyps(6) append.right_neutral append_Nil)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> NTimes r n \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_Upto1 s1 r v s2 n vs)
  have "(s1 @ s2) \<in> Upto r (n + 1) \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> Upto r n \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Upto r n))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (Upto r n) \<rightarrow> (Stars vs')"
    apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) apply fastforce
    apply (metis Posix1(1) Posix_Upto1.hyps(6) append.right_neutral append_Nil)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> Upto r n \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_Upto2 r n)
  have "[] \<in> Upto r n \<rightarrow> v2" by fact
  then show "Stars [] = v2" by cases (auto simp add: Posix1)
next
  case (Posix_From2 vs r n v2)
  then show "Stars vs = v2"
    apply(erule_tac Posix_elims)
     apply(auto)
    apply(rule List_eq_zipI)
     apply(auto)
      apply(meson in_set_zipE)
     apply (simp add: Posix1(2))
    using Posix1(2) by blast
next
  case (Posix_From1 s1 r v s2 n vs)
  have "(s1 @ s2) \<in> From r n \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> From r (n - 1) \<rightarrow> Stars vs" "flat v \<noteq> []" "0 < n"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (From r (n - 1 )))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (From r (n - 1)) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) Posix1(2) apply blast 
     apply(case_tac n)
      apply(simp)
     apply(simp)
    apply (smt (verit, ccfv_threshold) Posix1(1) UN_E append_eq_append_conv2 lang.simps(9))
    by (metis One_nat_def Posix1(1) Posix_From1.hyps(7) append_Nil2 append_self_conv2)
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> From r (n - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_From3 s1 r v s2 vs)
  have "(s1 @ s2) \<in> From r 0 \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> Star r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (Star r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(2) apply fastforce
    using Posix1(1) apply fastforce
    by (metis Posix1(1) Posix_From3.hyps(6) append.right_neutral append_Nil)
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> Star r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto  
next
  case (Posix_Rec s r v l v2)
  then show "Recv l v = v2" by (metis Posix_elims(10))
next 
  case (Posix_Cset c cs v2)
  have "[c] \<in> Charset cs \<rightarrow> v2" by fact
  then show "Atm c = v2" by cases auto
qed


lemma Posix_injval:
  assumes "s \<in> (deriv c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (injval r c v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case Zero
  have "s \<in> deriv c Zero \<rightarrow> v" by fact
  then have "s \<in> Zero \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> Zero \<rightarrow> (injval Zero c v)" by simp
next
  case One
  have "s \<in> deriv c One \<rightarrow> v" by fact
  then have "s \<in> Zero \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> One \<rightarrow> (injval One c v)" by simp
next 
  case (Atom d)
  consider (eq) "c = d" | (ineq) "c \<noteq> d" by blast
  then show "(c # s) \<in> (Atom d) \<rightarrow> (injval (Atom d) c v)"
  proof (cases)
    case eq
    have "s \<in> deriv c (Atom d) \<rightarrow> v" by fact
    then have "s \<in> One \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> Atom d \<rightarrow> injval (Atom d) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> deriv c (Atom d) \<rightarrow> v" by fact
    then have "s \<in> Zero \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> Atom d \<rightarrow> injval (Atom d) c v" by simp
  qed
next
  case (Plus r1 r2)
  have IH1: "\<And>s v. s \<in> deriv c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> deriv c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> deriv c (Plus r1 r2) \<rightarrow> v" by fact
  then have "s \<in> Plus (deriv c r1) (deriv c r2) \<rightarrow> v" by simp
  then consider (left) v' where "v = Left v'" "s \<in> deriv c r1 \<rightarrow> v'" 
              | (right) v' where "v = Right v'" "s \<notin> lang (deriv c r1)" "s \<in> deriv c r2 \<rightarrow> v'" 
              by cases auto
  then show "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c v"
  proof (cases)
    case left
    have "s \<in> deriv c r1 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r1 \<rightarrow> injval r1 c v'" using IH1 by simp
    then have "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c (Left v')" by (auto intro: Posix.intros)
    then show "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c v" using left by simp
  next 
    case right
    have "s \<notin> lang (deriv c r1)" by fact
    then have "c # s \<notin> lang r1" by (simp add: lang_deriv Deriv_def)
    moreover 
    have "s \<in> deriv c r2 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r2 \<rightarrow> injval r2 c v'" using IH2 by simp
    ultimately have "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c (Right v')" 
      by (auto intro: Posix.intros)
    then show "(c # s) \<in> Plus r1 r2 \<rightarrow> injval (Plus r1 r2) c v" using right by simp
  qed
next
  case (Times r1 r2)
  have IH1: "\<And>s v. s \<in> deriv c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> deriv c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> deriv c (Times r1 r2) \<rightarrow> v" by fact
  then consider 
        (left_nullable) v1 v2 s1 s2 where 
        "v = Left (Seq v1 v2)"  "s = s1 @ s2" 
        "s1 \<in> deriv c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)"
      | (right_nullable) v1 s1 s2 where 
        "v = Right v1" "s = s1 @ s2"  
        "s \<in> deriv c r2 \<rightarrow> v1" "nullable r1" "s1 @ s2 \<notin> lang (Times (deriv c r1) r2)"
      | (not_nullable) v1 v2 s1 s2 where
        "v = Seq v1 v2" "s = s1 @ s2" 
        "s1 \<in> deriv c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "\<not>nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)"
        by (force split: if_splits elim!: Posix_elims simp add: lang_deriv Deriv_def)   
  then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" 
    proof (cases)
      case left_nullable
      have "s1 \<in> deriv c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" 
         by (simp add: lang_deriv Deriv_def)
      ultimately have "((c # s1) @ s2) \<in> Times r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using left_nullable by (rule_tac Posix.intros)
      then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" using left_nullable by simp
    next
      case right_nullable
      have "nullable r1" by fact
      then have "[] \<in> r1 \<rightarrow> (mkeps r1)" by (rule Posix_mkeps)
      moreover
      have "s \<in> deriv c r2 \<rightarrow> v1" by fact
      then have "(c # s) \<in> r2 \<rightarrow> (injval r2 c v1)" using IH2 by simp
      moreover
      have "s1 @ s2 \<notin> lang (Times (deriv c r1) r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" 
        using right_nullable 
        apply (auto simp add: lang_deriv Deriv_def append_eq_Cons_conv)
        by (metis concI mem_Collect_eq)
      ultimately have "([] @ (c # s)) \<in> Times r1 r2 \<rightarrow> Seq (mkeps r1) (injval r2 c v1)"
      by(rule Posix.intros)
      then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" using right_nullable by simp
    next
      case not_nullable
      have "s1 \<in> deriv c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r1) \<and> s\<^sub>4 \<in> lang r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" by (simp add: lang_deriv Deriv_def)
      ultimately have "((c # s1) @ s2) \<in> Times r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using not_nullable 
        by (rule_tac Posix.intros) (simp_all) 
      then show "(c # s) \<in> Times r1 r2 \<rightarrow> injval (Times r1 r2) c v" using not_nullable by simp
    qed
next
  case (Star r)
  have IH: "\<And>s v. s \<in> deriv c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> deriv c (Star r) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> deriv c r \<rightarrow> v1" "s2 \<in> (Star r) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Star r))" 
        apply(auto elim!: Posix_elims(1-5) simp add: lang_deriv Deriv_def intro: Posix.intros)
        apply(rotate_tac 3)
        apply(erule_tac Posix_elims(6))
        apply (simp add: Posix.intros(6))
        using Posix.intros(7) by blast
    then show "(c # s) \<in> Star r \<rightarrow> injval (Star r) c v" 
    proof (cases)
      case cons
          have "s1 \<in> deriv c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> Star r \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Star r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" 
            by (simp add: lang_deriv Deriv_def)
        ultimately 
        have "((c # s1) @ s2) \<in> Star r \<rightarrow> Stars (injval r c v1 # vs)" by (rule Posix.intros)
        then show "(c # s) \<in> Star r \<rightarrow> injval (Star r) c v" using cons by(simp)
      qed
next
  case (NTimes r n)
  have IH: "\<And>s v. s \<in> deriv c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> deriv c (NTimes r n) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> deriv c r \<rightarrow> v1" "s2 \<in> (NTimes r (n - 1)) \<rightarrow> (Stars vs)" "0 < n"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (NTimes r (n - 1)))" 
    apply(auto elim: Posix_elims simp add: lang_derivs Deriv_def intro: Posix.intros split: if_splits)
    apply(erule Posix_elims)
    apply(simp)
    apply(subgoal_tac "\<exists>vss. v2 = Stars vss")
    apply(clarify)
    apply(drule_tac x="vss" in meta_spec)
    apply(drule_tac x="s1" in meta_spec)
    apply(drule_tac x="s2" in meta_spec)
     apply(simp add: lang_derivs Deriv_def)
    apply(erule Posix_elims)
     apply(auto)
      done
    then show "(c # s) \<in> (NTimes r n) \<rightarrow> injval (NTimes r n) c v" 
    proof (cases)
      case cons
          have "s1 \<in> deriv c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> (NTimes r (n - 1)) \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (NTimes r (n - 1)))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (NTimes r (n - 1)))"
            by (simp add: lang_deriv Deriv_def)
        ultimately 
        have "((c # s1) @ s2) \<in> NTimes r n \<rightarrow> Stars (injval r c v1 # vs)"
          by (metis One_nat_def Posix_NTimes1 Suc_pred add.commute cons(5) plus_1_eq_Suc)
        then show "(c # s) \<in> NTimes r n \<rightarrow> injval (NTimes r n) c v" using cons by(simp)
      qed  
next
  case (Upto r n)
  have IH: "\<And>s v. s \<in> deriv c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> deriv c (Upto r n) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> deriv c r \<rightarrow> v1" "s2 \<in> (Upto r (n - 1)) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Upto r (n - 1)))" 
    apply(auto elim!: Posix_elims simp add: lang_deriv Deriv_def intro: Posix.intros)    
    apply(case_tac n)
     apply(auto)
    using Posix_elims(1) apply blast
    apply(erule_tac Posix_elims)
    apply(auto)
    by (metis Posix1a Prf_elims(8) UN_E cons diff_Suc_1 lang.simps(8))
    then show "(c # s) \<in> Upto r n \<rightarrow> injval (Upto r n) c v" 
    proof (cases)
      case cons
          have "s1 \<in> deriv c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> Upto r (n - 1) \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Upto r (n - 1)))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Upto r (n - 1)))" 
            by (simp add: lang_deriv Deriv_def)
        ultimately 
        have "((c # s1) @ s2) \<in> Upto r n \<rightarrow> Stars (injval r c v1 # vs)"
          by (metis One_nat_def Posix_Upto1 Posix_elims(1) Suc_pred Upto.prems add.commute bot_nat_0.not_eq_extremum deriv.simps(8) plus_1_eq_Suc)
        then show "(c # s) \<in> Upto r n \<rightarrow> injval (Upto r n) c v" using cons by(simp)
      qed
next
  case (From r n)
  have IH: "\<And>s v. s \<in> deriv c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> deriv c (From r n) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> deriv c r \<rightarrow> v1" "s2 \<in> (From r (n - 1)) \<rightarrow> (Stars vs)" "0 < n"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (From r (n - 1)))"
     | (null) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2"  "s2 \<in> (Star r) \<rightarrow> (Stars vs)" 
        "s1 \<in> deriv c r \<rightarrow> v1" "n = 0"
         "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Star r))"  
    apply(auto elim: Posix_elims simp add: lang_deriv Deriv_def intro: Posix.intros split: if_splits)
    apply(erule Posix_elims)
    apply(auto)
    apply(auto elim: Posix_elims simp add: lang_deriv Deriv_def intro: Posix.intros split: if_splits)
    apply(metis Posix1a Prf_elims(6))     
    apply(erule Posix_elims)
    apply(auto)
    apply(erule Posix_elims(9))
    apply (metis (no_types, lifting) Nil_is_append_conv Posix_From2)
     apply (simp add: Posix_From1 that(1))
    by (simp add: Posix_From3 that(1))
    then show "(c # s) \<in> (From r n) \<rightarrow> injval (From r n) c v" 
    proof (cases)
      case cons
          have "s1 \<in> deriv c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> (From r (n - 1)) \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (From r (n - 1)))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (From r (n - 1)))" 
            by (simp add: lang_deriv Deriv_def)
        ultimately 
        have "((c # s1) @ s2) \<in> From r n \<rightarrow> Stars (injval r c v1 # vs)"
          by (meson Posix_From1 cons(5))
        then show "(c # s) \<in> From r n \<rightarrow> injval (From r n) c v" using cons by(simp)
      next 
       case null
          have "s1 \<in> deriv c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
          moreover 
            have "s2 \<in> Star r \<rightarrow> Stars vs" by fact
          moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
          moreover
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang (deriv c r) \<and> s\<^sub>4 \<in> lang (Star r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" 
            by (simp add: lang_deriv Deriv_def)
        ultimately 
        have "((c # s1) @ s2) \<in> From r 0 \<rightarrow> Stars (injval r c v1 # vs)"
          by (metis Posix_From3) 
        then show "(c # s) \<in> From r n \<rightarrow> injval (From r n) c v" using null by (simp)
      qed  
next
  case (Rec l r)
  then show "(c # s) \<in> Rec l r \<rightarrow> injval (Rec l r) c v"
    by (simp add: Posix_Rec)
next 
  case (Charset cs)
  consider (eq) "c \<in> cs" | (ineq) "c \<notin> cs" by blast
  then show "(c # s) \<in> (Charset cs) \<rightarrow> (injval (Charset cs) c v)"
  proof (cases)
    case eq
    have "s \<in> deriv c (Charset cs) \<rightarrow> v" by fact
    then have "s \<in> One \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> Charset cs \<rightarrow> injval (Charset cs) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> deriv c (Charset cs) \<rightarrow> v" by fact
    then have "s \<in> Zero \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> Charset cs \<rightarrow> injval (Charset cs) c v" by simp
  qed
qed


section \<open>The Lexer by Sulzmann and Lu\<close>

fun 
  lexer :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> ('a val) option"
where
  "lexer r [] = (if nullable r then Some(mkeps r) else None)"
| "lexer r (c#s) = (case (lexer (deriv c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"


lemma lexer_correct_None:
  shows "s \<notin> lang r \<longleftrightarrow> lexer r s = None"
apply(induct s arbitrary: r)
apply(simp add: nullable_iff)
apply(drule_tac x="deriv a r" in meta_spec)
apply(auto simp add: lang_deriv Deriv_def)
done

lemma lexer_correct_Some:
  shows "s \<in> lang r \<longleftrightarrow> (\<exists>v. lexer r s = Some(v) \<and> s \<in> r \<rightarrow> v)"
apply(induct s arbitrary: r)
apply(auto simp add: Posix_mkeps nullable_iff)[1]
apply(drule_tac x="deriv a r" in meta_spec)
apply(simp add: lang_deriv Deriv_def)
apply(rule iffI)
apply(auto intro: Posix_injval simp add: Posix1(1))
done 

lemma lexer_correctness:
  shows "(lexer r s = Some v) \<longleftrightarrow> s \<in> r \<rightarrow> v"
  and   "(lexer r s = None) \<longleftrightarrow> \<not>(\<exists>v. s \<in> r \<rightarrow> v)"
apply(auto)
using lexer_correct_None lexer_correct_Some apply fastforce
using Posix1(1) Posix_determ lexer_correct_Some apply blast
using Posix1(1) lexer_correct_None apply blast
using lexer_correct_None lexer_correct_Some by blast



end
