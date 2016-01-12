(*<*)
(* AUTHOR : Peter Chapman  *)
(* License: LGPL *)

section "Modal Sequents"

theory ModalSequents
imports "~~/src/HOL/Library/Multiset"

begin

(* -------------------------------
   -------------------------------
            Multiset2.thy
   -------------------------------
   ------------------------------- *)

abbreviation multiset_abbrev ("\<LM> _  \<RM>" [75]75) where
   "\<LM> A \<RM> \<equiv> {# A #}"

abbreviation multiset_empty ("\<Empt>" 75) where
  "\<Empt> \<equiv> {#}"

abbreviation
multiset_plus (infixl "\<oplus>" 80) where
   "(\<Gamma> :: 'a multiset) \<oplus> (A :: 'a) \<equiv> \<Gamma> + \<LM>A\<RM>"
abbreviation
multiset_minus (infixl "\<ominus>" 80) where
   "(\<Gamma> :: 'a multiset) \<ominus>  (A :: 'a) \<equiv> \<Gamma> - \<LM>A\<RM>"


abbreviation
multiset_map (infixl "\<cdot>\<cdot>" 100) where
   "(f :: 'a \<Rightarrow> 'a)\<cdot>\<cdot>(\<Gamma> :: 'a multiset) \<equiv> image_mset f \<Gamma>" 


lemma nonEmpty_contain:
assumes "\<Gamma> \<noteq> \<Empt>"
shows "\<exists> a. a :# \<Gamma>"
using assms
by (induct \<Gamma>) auto

lemma nonEmpty_neq:
assumes "\<Gamma> \<noteq> \<Empt>"
shows "\<Gamma> + C \<noteq> C"
proof-
from assms and nonEmpty_contain obtain a where "a :# \<Gamma>" by auto
then have "count \<Gamma> a \<ge> 1" by auto
then have "count (\<Gamma> + C) a \<noteq> count C a" by auto
then show "\<Gamma> + C \<noteq> C" by (auto simp add:multiset_eq_iff)
qed 

lemma nonEmpty_image:
assumes "\<Gamma> \<noteq> \<Empt>"
shows "f \<cdot>\<cdot> \<Gamma> \<noteq> \<Empt>"
using image_mset_is_empty_iff assms by auto

lemma single_plus_obtain:
assumes "A :# \<Gamma>"
shows "\<exists> \<Delta>. \<Gamma> = \<Delta> \<oplus> A"
proof-
from assms have "\<Gamma> = \<Gamma> \<ominus> A \<oplus> A" by (auto simp add:multiset_eq_iff)
then show ?thesis by (rule_tac x="\<Gamma>\<ominus>A" in exI) simp
qed

lemma singleton_add_means_equal:
assumes "\<LM>A\<RM> = \<Gamma> \<oplus> B"
shows "A = B"
proof-
from assms have "size (\<LM>A\<RM>) = size (\<Gamma> \<oplus> B)" by auto
then have "size (\<LM>A\<RM>) = size \<Gamma> + size (\<LM>B\<RM>)" by auto
then have "\<Gamma> = \<Empt>" by auto
with assms have "\<LM>A\<RM> = \<LM>B\<RM>" by auto
then show ?thesis by auto
qed

lemma singleton_add_means_empty:
assumes "\<LM>A\<RM> = \<Gamma> \<oplus> B"
shows "\<Gamma> = \<Empt>"
proof-
from assms have "size (\<LM>A\<RM>) = size (\<Gamma> \<oplus> B)" by auto
then have "size (\<LM>A\<RM>) = size \<Gamma> + size (\<LM>B\<RM>)" by auto
then show "\<Gamma> = \<Empt>" by auto
qed

lemma single_multiset_eq_non_empty:
assumes "\<LM>A\<RM> = \<Delta> + \<Delta>'"
and     "\<Delta> \<noteq> \<Empt>"
shows "\<Delta>' = \<Empt> \<and> \<Delta> = \<LM>A\<RM>"
proof-
 from assms have "size (\<LM>A\<RM>) = size \<Delta> + size \<Delta>'" by auto
 then have "1 = size \<Delta> + size \<Delta>'" by auto
 moreover from `\<Delta> \<noteq> \<Empt>` have "0 \<noteq> size \<Delta>" by auto
 ultimately have "size \<Delta> = 1 \<and> size \<Delta>' = 0" by arith
 then have a: "\<Delta>' = \<Empt>" by auto
 with `\<LM>A\<RM> = \<Delta> + \<Delta>'` have b: "\<Delta> = \<LM>A\<RM>" by auto
 from a b show ?thesis by auto
qed

lemma two_neq_one_aux:
assumes "(\<LM>A\<RM>) \<oplus> B = \<LM>C\<RM>"
shows "False"
proof-
 from assms have "size ((\<LM>A\<RM>) \<oplus> B) = size (\<LM>C\<RM>)" by auto
 then have "size (\<LM>A\<RM>) + size (\<LM>B\<RM>) = size (\<LM>C\<RM>)" by auto
 then show ?thesis by auto
qed

lemma two_neq_one:
assumes "((\<LM>A\<RM>) \<oplus> B) + \<Gamma> = \<LM>C\<RM>"
shows "False"
proof-
 from assms have "size (((\<LM>A\<RM>)\<oplus> B) + \<Gamma>) = size (\<LM>C\<RM>)" by auto
 then have "size (\<LM>A\<RM>) + size (\<LM>B\<RM>) + size \<Gamma> = 1" by auto
 then show ?thesis by auto
qed


lemma add_equal_means_equal:
assumes "\<Gamma> \<oplus> A = \<Delta> \<oplus> A"
shows "\<Gamma> = \<Delta>"
proof-
 from assms and add_eq_conv_diff[where M=\<Gamma> and N=\<Delta> and a=A and b=A] show "\<Gamma> = \<Delta>" by auto
qed





(* -------------------------------
   -------------------------------
        SequentRulesModal2.thy
   -------------------------------
   ------------------------------- *)

(*>*)
text{*
\section{Modal Calculi \label{isamodal}}
Some new techniques are needed when formalising results about modal calculi.  A set of modal operators must index formulae (and sequents and rules), there must be a method for modalising a multiset of formulae and we need to be able to handle implicit weakening rules.

The first of these is easy; instead of indexing formulae by a single type variable, we index on a pair of type variables, one which contains the propositional connectives, and one which contains the modal operators:
*}
datatype ('a, 'b) form = At "nat"
                                 | Compound "'a" "('a, 'b) form list"
                                 | Modal "'b" "('a, 'b) form list"
                                 | ff

datatype_compat form

(*<*)
datatype ('a,'b) sequent = Sequent "(('a,'b) form) multiset" "(('a,'b) form) multiset" (" (_) \<Rightarrow>* (_)" [6,6] 5)

type_synonym ('a,'b) rule = "('a,'b) sequent list * ('a,'b) sequent"

type_synonym ('a,'b) deriv = "('a,'b) sequent * nat"

consts
  (* extend a sequent by adding another one.  A form of weakening.  *)
  extend :: "('a,'b) sequent \<Rightarrow> ('a,'b) sequent \<Rightarrow> ('a,'b) sequent"
  extendRule :: "('a,'b) sequent \<Rightarrow> ('a,'b) rule \<Rightarrow> ('a,'b) rule"
  extendRule2 :: "('a,'b) sequent \<Rightarrow> ('a,'b) sequent \<Rightarrow> ('a,'b) rule \<Rightarrow> ('a,'b) rule"
  extendConc :: "('a,'b) sequent \<Rightarrow> ('a,'b) rule \<Rightarrow> ('a,'b) rule"

  (* Unique conclusion Property *)
  uniqueConclusion :: "('a,'b) rule set \<Rightarrow> bool"

  (* Transform a multiset using a modal operator.  "Boxing" a context, effectively *)
  modaliseMultiset :: "'b \<Rightarrow> ('a,'b) form multiset \<Rightarrow> ('a,'b) form multiset" (infixl "\<cdot>" 200)

  (* functions to get at components of sequents *)

primrec antec :: "('a,'b) sequent \<Rightarrow> ('a,'b) form multiset" where
  "antec (Sequent ant suc) = ant"

primrec succ :: "('a,'b) sequent \<Rightarrow> ('a,'b) form multiset" where
  "succ (Sequent ant suc) = suc"

primrec mset :: "('a,'b) sequent \<Rightarrow> ('a,'b) form multiset" where
  "mset (Sequent ant suc) = ant + suc"

primrec seq_size :: "('a,'b) sequent \<Rightarrow> nat" where
  "seq_size (Sequent ant suc) = size ant + size suc"

(* Extend a sequent, and then a rule by adding seq to all premisses and the conclusion *)
overloading
  extend \<equiv> extend
  extendRule \<equiv> extendRule
  extendRule2 \<equiv> extendRule2
begin

definition extend
  where "extend forms seq \<equiv> (antec forms + antec seq) \<Rightarrow>* (succ forms + succ seq)"

definition extendRule
  where "extendRule forms R \<equiv> (map (extend forms) (fst R), extend forms (snd R))"

definition extendRule2 :: "('a,'b) sequent \<Rightarrow> ('a,'b) sequent \<Rightarrow> ('a,'b) rule \<Rightarrow> ('a,'b) rule"
  where "extendRule2 S1 S2 r \<equiv> (map (extend S1) (fst r), extend S2 (snd r))"

end

(*>*)

(* The unique conclusion property.  A set of rules has unique conclusion property if for any pair of rules,
   the conclusions being the same means the rules are the same*)
overloading
  uniqueConclusion \<equiv> uniqueConclusion
  modaliseMultiset \<equiv> modaliseMultiset
begin

definition uniqueConclusion :: "('a,'b) rule set \<Rightarrow> bool"
  where "uniqueConclusion R \<equiv> \<forall> r1 \<in> R. \<forall> r2 \<in> R. (snd r1 = snd r2) \<longrightarrow> (r1 =r2)"

text{*
\noindent Modalising multisets is relatively straightforward.  We use the notation $!\cdot \Gamma$, where $!$ is a modal operator and $\Gamma$ is a multiset of formulae:
*}
definition modaliseMultiset :: "'b \<Rightarrow> ('a,'b) form multiset \<Rightarrow> ('a,'b) form multiset"
  where "modaliseMultiset a \<Gamma> \<equiv> {# Modal a [p]. p :# \<Gamma> #}"

end

(*<*) 
(* The formulation of various rule sets *)

(* Ax is the set containing all identity RULES and LBot *)
inductive_set "Ax" where
   id[intro]: "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) \<in> Ax"
|  Lbot[intro]: "([], \<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<in> Ax"

(* upRules is the set of all rules which have a single conclusion.  This is akin to each rule having a 
   single principal formula.  We don't want rules to have no premisses, hence the restriction
   that ps \<noteq> [] *)
inductive_set "upRules" where
   I[intro]: "\<lbrakk> mset c = \<LM> Compound R Fs \<RM> ; ps \<noteq> [] \<rbrakk> \<Longrightarrow> (ps,c) \<in> upRules"


(*>*)
text{*
\noindent Similarly to \S\ref{isafirstorder}, two new rule sets are created.  The first are the normal modal rules:
*}
inductive_set "modRules2" where
   (*<*)I[intro]:(*>*) "\<lbrakk> ps \<noteq> [] ; mset c = \<LM> Modal M Ms \<RM> \<rbrakk> \<Longrightarrow> (ps,c) \<in> modRules2"

text{*
\noindent The second are the \textit{modalised context rules}.  Taking a subset of the normal modal rules, we extend using a pair of modalised multisets for context.  We create a new inductive rule set called \texttt{p-e}, for ``prime extend'', which takes a set of modal active parts and a pair of modal operators (say $!$ and $\bullet$), and returns the set of active parts extended with $!\cdot \Gamma \Rightarrow \bullet\cdot\Delta$:
*}
inductive_set p_e :: "('a,'b) rule set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a,'b) rule set" 
  for R :: "('a,'b) rule set" and M N :: "'b" 
  where
  (*<*)I[intro]:(*>*) "\<lbrakk> (Ps, c) \<in> R ; R \<subseteq> modRules2 \<rbrakk> \<Longrightarrow> extendRule (M\<cdot>\<Gamma> \<Rightarrow>* N\<cdot>\<Delta>) (Ps, c) \<in> p_e R M N"

text{*
\noindent We need a method for extending the conclusion of a rule without extending the premisses.  Again, this is simple:*}

overloading extendConc \<equiv> extendConc
begin

definition extendConc :: "('a,'b) sequent \<Rightarrow> ('a,'b) rule \<Rightarrow> ('a,'b) rule"
  where "extendConc S r \<equiv> (fst r, extend S (snd r))"

end

text{* \noindent  The extension of a rule set is now more complicated; the inductive definition has four clauses, depending on the type of rule:
*}
inductive_set ext :: "('a,'b) rule set \<Rightarrow> ('a,'b) rule set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a,'b) rule set" 
  for R R' :: "('a,'b) rule set" and M N :: "'b"
  where
   ax(*<*)[intro](*>*):    "\<lbrakk> r \<in> R ; r \<in> Ax \<rbrakk> \<Longrightarrow> extendRule seq r \<in> ext R R' M N"
|  up(*<*)[intro](*>*):    "\<lbrakk> r \<in> R ; r \<in> upRules\<rbrakk> \<Longrightarrow> extendRule seq r \<in> ext R R' M N"
| mod1(*<*)[intro](*>*): "\<lbrakk> r \<in> p_e R' M N ; r \<in> R \<rbrakk> \<Longrightarrow> extendConc seq r \<in> ext R R' M N"
| mod2(*<*)[intro](*>*): "\<lbrakk> r \<in> R ; r \<in> modRules2 \<rbrakk> \<Longrightarrow> extendRule seq r \<in> ext R R' M N"

text{* 
\noindent Note the new rule set carries information about which set contains the modalised context rules and which modal operators which extend those prime parts.
*}

(*<*)
(* A formulation of what it means to be a principal formula for a rule.   *)

inductive leftPrincipal :: "('a,'b) rule \<Rightarrow> ('a,'b) form \<Rightarrow> ('a,'b) rule set \<Rightarrow> bool"
  where
  up[intro]: "\<lbrakk> C = (\<LM> A \<RM> \<Rightarrow>* \<Empt>) ; A \<noteq> ff ; (Ps,C) \<in> R \<rbrakk>  \<Longrightarrow> 
                   leftPrincipal (Ps,C) A R"



inductive rightPrincipal :: "('a,'b) rule \<Rightarrow> ('a,'b) form \<Rightarrow> ('a,'b) rule set \<Rightarrow> bool"
  where
  up[intro]: "\<lbrakk> C = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) ; (Ps,C) \<in> R \<rbrakk>\<Longrightarrow> rightPrincipal (Ps,C) A R"



(* What it means to be a derivable sequent.  Can have this as a predicate or as a set.
   The two formation rules say that the supplied premisses are derivable, and the second says
   that if all the premisses of some rule are derivable, then so is the conclusion. *)

inductive_set derivable :: "('a,'b) rule set \<Rightarrow> ('a,'b) deriv set"
  for R :: "('a,'b) rule set"
  where
   base[intro]: "\<lbrakk>([],C) \<in> R\<rbrakk> \<Longrightarrow> (C,0) \<in> derivable R"
|  step[intro]: "\<lbrakk> r \<in> R ; (fst r)\<noteq>[] ; \<forall> p \<in> set (fst r). \<exists> n \<le> m. (p,n) \<in> derivable R \<rbrakk> 
                       \<Longrightarrow> (snd r,m + 1) \<in> derivable R"


(* Characterisation of a sequent *)
lemma characteriseSeq:
shows "\<exists> A B. (C :: ('a,'b) sequent) = (A \<Rightarrow>* B)"
apply (rule_tac x="antec C" in exI, rule_tac x="succ C" in exI) by (cases C) (auto)

(* Obvious connection *)
lemma extend1_to_2:
shows "extendRule2 S S r = extendRule S r"
by (auto simp add:extendRule_def extendRule2_def)

(* Helper function for later *)
lemma nonEmptySet:
shows "A \<noteq> [] \<longrightarrow> (\<exists> a. a \<in> set A)"
by (auto simp add:neq_Nil_conv)


(* Lemma which says that if we have extended an identity rule, then the propositional variable is
   contained in the extended multisets *)
lemma extendID:
assumes "extend S (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "At i :# \<Gamma> \<and> At i :# \<Delta>"
using assms
proof-
  from assms have "\<exists> \<Gamma>' \<Delta>'. \<Gamma> = \<Gamma>' \<oplus> At i \<and> \<Delta> = \<Delta>' \<oplus> At i" 
     using extend_def[where forms=S and seq="\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>"]
     by (rule_tac x="antec S" in exI,rule_tac x="succ S" in exI) auto
  then show ?thesis by auto
qed

lemma extendFalsum:
assumes "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "ff :# \<Gamma>"
proof-
  from assms have "\<exists> \<Gamma>'. \<Gamma> = \<Gamma>' \<oplus> ff" 
     using extend_def[where forms=S and seq="\<LM>ff \<RM> \<Rightarrow>* \<Empt>"]
     by (rule_tac x="antec S" in exI) auto
  then show ?thesis by auto
qed


(* Lemma that says if a propositional variable is in both the antecedent and succedent of a sequent,
   then it is derivable from idupRules *)
lemma containID:
assumes a:"At i :# \<Gamma> \<and> At i :# \<Delta>"
    and b:"Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable (ext R R' M N)"
proof-
from a have "\<Gamma> = \<Gamma> \<ominus> At i \<oplus> At i \<and> \<Delta> = \<Delta> \<ominus> At i \<oplus> At i" by auto
then have "extend ((\<Gamma> \<ominus> At i) \<Rightarrow>* (\<Delta> \<ominus> At i)) (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)" 
     using extend_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i" and seq="\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>"] by auto
moreover
have "([],\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) \<in> R" using b by auto
ultimately
have "([],\<Gamma> \<Rightarrow>* \<Delta>) \<in> ext R R' M N" 
     using ext.ax[where R=R and r="([],  \<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)" and seq="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i"] 
       and extendRule_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i" and R="([],  \<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)"] by auto
then show ?thesis using derivable.base[where R="ext R R' M N" and C="\<Gamma> \<Rightarrow>* \<Delta>"] by auto
qed

lemma containFalsum:
assumes a: "ff :# \<Gamma>"
   and  b: "Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable (ext R R' M N)"
proof-
from a have "\<Gamma> = \<Gamma> \<ominus> ff \<oplus> ff" by auto
then have "extend (\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>) (\<LM>ff\<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
     using extend_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>" and seq="\<LM>ff\<RM> \<Rightarrow>* \<Empt>"] by auto 
moreover
have "([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>) \<in> R" using b by auto
ultimately have "([],\<Gamma> \<Rightarrow>* \<Delta>) \<in> ext R R' M N"
     using ext.ax[where R=R and r="([],  \<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and seq="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>"] 
       and extendRule_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>" and R="([],  \<LM>ff\<RM> \<Rightarrow>* \<Empt>)"] by auto
then show ?thesis using derivable.base[where R="ext R R' M N" and C="\<Gamma> \<Rightarrow>* \<Delta>"] by auto
qed 

(* Lemma which says that if r is an identity rule, then r is of the form
   ([], P \<Rightarrow>* P) *)
lemma characteriseAx:
shows "r \<in> Ax \<Longrightarrow> r = ([],\<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<or> (\<exists> i. r = ([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>))"
apply (cases r) by (rule Ax.cases) auto

(* A lemma about the last rule used in a derivation, i.e. that one exists *)
lemma characteriseLast:
assumes "(C,m+1) \<in> derivable R"
shows "\<exists> Ps. Ps \<noteq> [] \<and>
             (Ps,C) \<in> R \<and> 
             (\<forall> p \<in> set Ps. \<exists> n\<le>m. (p,n) \<in> derivable R)"
using assms
by (cases) auto


(* Lemma which says that if rule is an upRule, then the succedent is either empty, or a single formula *)
lemma succ_upRule:
assumes "(Ps,\<Phi> \<Rightarrow>* \<Psi>) \<in> upRules"
shows "\<Psi> = \<Empt> \<or> (\<exists> A. \<Psi> = \<LM>A\<RM>)"
using assms 
proof (cases)
    case (I R Rs)
    then show "\<Psi> = \<Empt> \<or> (\<exists> A. \<Psi> = \<LM>A\<RM>)" using mset.simps [where ant=\<Phi> and suc=\<Psi>] 
         and union_is_single[where M=\<Phi> and N=\<Psi> and a="Compound R Rs"] by (simp,elim disjE) (auto)
qed

(* Equivalent, but the antecedent *)
lemma antec_upRule:
assumes "(Ps,\<Phi> \<Rightarrow>* \<Psi>) \<in> upRules"
shows "\<Phi> = \<Empt> \<or> (\<exists> A. \<Phi> = \<LM>A\<RM>)"
using assms 
proof (cases)
    case (I R Rs)
    then show "\<Phi> = \<Empt> \<or> (\<exists> A. \<Phi> = \<LM>A\<RM>)" using mset.simps[where ant=\<Phi> and suc=\<Psi>] 
         and union_is_single[where M=\<Phi> and N=\<Psi> and a="Compound R Rs"] by (simp,elim disjE) (auto)
qed

lemma upRule_Size:
assumes "r \<in> upRules"
shows "seq_size (snd r) = 1"
using assms
proof-
    obtain Ps C where "r = (Ps,C)" by (cases r)
    then have "(Ps,C) \<in> upRules" using assms by simp
    then show ?thesis
       proof (cases)
          case (I R Rs)
          obtain G H where "C = (G \<Rightarrow>* H)" by (cases C) (auto)
          then have "G + H = \<LM>Compound R Rs\<RM>" using mset.simps and `mset C = \<LM>Compound R Rs\<RM>` by auto
          then have "size (G+H) = 1" by auto 
          then have "size G + size H = 1" by auto
          then have "seq_size C = 1" using seq_size.simps[where ant=G and suc=H] and `C = (G \<Rightarrow>* H)` by auto
          moreover have "snd r = C" using `r = (Ps,C)` by simp
          ultimately show "seq_size (snd r) = 1" by simp
       qed
qed

lemma upRuleCharacterise:
assumes "(Ps,C) \<in> upRules"
shows "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<or> C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)"
using assms
proof (cases)
  case (I F Fs)
  then obtain \<Gamma> \<Delta> where "C = (\<Gamma> \<Rightarrow>* \<Delta>)" using characteriseSeq[where C=C] by auto
  then have "(Ps,\<Gamma> \<Rightarrow>* \<Delta>) \<in> upRules" using assms by simp
  then show "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<or> C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)" 
    using `mset C = \<LM>Compound F Fs\<RM>` and `C = (\<Gamma> \<Rightarrow>* \<Delta>)`
      and mset.simps [where ant=\<Gamma> and suc=\<Delta>] and union_is_single[where M=\<Gamma> and N=\<Delta> and a="Compound F Fs"]
    by auto
qed

lemma modRule2Characterise:
assumes "(Ps,C) \<in> modRules2"
shows "Ps \<noteq> [] \<and> (\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> C = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>))"
using assms
proof (cases)
  case (I F Fs)
  then have "Ps \<noteq> []" by simp
  obtain \<Gamma> \<Delta> where "C = (\<Gamma> \<Rightarrow>* \<Delta>)" using characteriseSeq[where C=C] by auto
  then have "(Ps,\<Gamma> \<Rightarrow>* \<Delta>) \<in> modRules2" using assms by simp
  then have "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> C = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)" 
    using `mset C = \<LM>Modal F Fs\<RM>` and `C = (\<Gamma> \<Rightarrow>* \<Delta>)`
      and mset.simps[where ant=\<Gamma> and suc=\<Delta>] and union_is_single[where M=\<Gamma> and N=\<Delta> and a="Modal F Fs"]
    by auto
  thus ?thesis using `Ps \<noteq> []` by auto
qed

lemma modRule1Characterise:
assumes "(Ps,C) \<in> p_e R M N" and "R \<subseteq> modRules2"
shows "\<exists> F Fs \<Gamma> \<Delta> ps r. (Ps,C) = extendRule (M\<cdot>\<Gamma>\<Rightarrow>*N\<cdot>\<Delta>) r \<and> r \<in> R \<and> 
                    (r = (ps,\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> 
                     r = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>))"
using assms
proof (cases)
  case (I ps c \<Gamma> \<Delta>)
  then have "(ps, c) \<in> modRules2" by auto
  with `(ps, c) \<in> modRules2` obtain F Fs where "c = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> c = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
    using modRule2Characterise[where C=c and Ps=ps] by auto
  with I show ?thesis
    apply -
    apply (rule_tac x=F in exI) apply (rule_tac x=Fs in exI) apply (rule_tac x=\<Gamma> in exI)
    apply (rule_tac x=\<Delta> in exI) apply auto done
qed

lemma extendEmpty:
shows "extend (\<Empt> \<Rightarrow>* \<Empt>) C = C"
apply (auto simp add:extend_def) by (cases C) auto

lemma mapExtendEmpty:
shows "map (extend (\<Empt> \<Rightarrow>* \<Empt>)) ps = ps"
using extendEmpty
by (induct ps) auto

lemma extendRuleEmpty:
shows "extendRule (\<Empt> \<Rightarrow>* \<Empt>) r = r"
by (auto simp add:extendRule_def extendEmpty mapExtendEmpty)

lemma extendNonEmpty:
assumes "\<not> (\<Gamma> = \<Empt> \<and> \<Delta> = \<Empt>)"
shows "extend (\<Gamma> \<Rightarrow>* \<Delta>) C \<noteq> C"
using assms
by (cases C) (auto simp add:extend_def nonEmpty_neq)

lemma extendRuleNonEmpty:
assumes "\<not> (\<Gamma> = \<Empt> \<and> \<Delta> = \<Empt>)"
shows "extendRule (\<Gamma> \<Rightarrow>* \<Delta>) r \<noteq> r"
using assms
by (cases r) (auto simp add:extendRule_def extendNonEmpty)

lemma extendRuleEmptyRev:
assumes "extendRule S r = r"
shows "S = (\<Empt> \<Rightarrow>* \<Empt>)"
using assms extendRuleNonEmpty apply (cases r) by (cases S) (auto)

lemma modaliseEmpty:
shows "a \<cdot> (\<Empt>) = \<Empt>"
using modaliseMultiset_def[where a=a and \<Gamma>="\<Empt>"] by auto

lemma modaliseNonEmpty:
assumes "\<Gamma> \<noteq> \<Empt>"
shows "a \<cdot> \<Gamma> \<noteq> \<Empt>"
using assms nonEmpty_image[where \<Gamma>=\<Gamma>] modaliseMultiset_def[where \<Gamma>=\<Gamma> and a=a] by auto

lemma mset_extend:
shows "mset (extend S c) = mset S + mset c"
using mset.simps extend_def apply (cases S) apply (cases c)
by (auto simp add: union_ac extend_def)

lemma mset_extend_size:
assumes "\<not> (\<Gamma> = \<Empt> \<and> \<Delta> = \<Empt>)"
shows "size (mset ((extend (\<Gamma> \<Rightarrow>* \<Delta>) c))) > size (mset c)"
using assms
proof-
from assms have "mset (\<Gamma> \<Rightarrow>* \<Delta>) \<noteq> \<Empt>" by auto
then have "size (mset (\<Gamma> \<Rightarrow>* \<Delta>)) > 0" apply auto by (induct \<Gamma>) auto
moreover have "mset (extend (\<Gamma> \<Rightarrow>* \<Delta>) c) = mset (\<Gamma>\<Rightarrow>*\<Delta>) + mset c"
     using mset_extend[where S="\<Gamma> \<Rightarrow>* \<Delta>" and c=c] by auto
then have "size (mset (extend (\<Gamma> \<Rightarrow>* \<Delta>) c)) = size (mset (\<Gamma> \<Rightarrow>* \<Delta>)) + size (mset c)" by simp
ultimately show ?thesis by arith
qed



lemma extendContain:
assumes "r = (ps,c)"
    and "(Ps,C) = extendRule S r"
    and "p \<in> set ps"
shows "extend S p \<in> set Ps"
proof-
from `p \<in> set ps` have "extend S p \<in> set (map (extend S) ps)" by auto
moreover from `(Ps,C) = extendRule S r` and `r = (ps,c)` have "map (extend S) ps = Ps" by (simp add:extendRule_def) 
ultimately show ?thesis by auto
qed



lemma extendCommute:
shows "(extend S) (extend R c) = (extend R) (extend S c)"
by (auto simp add:extend_def union_ac)

lemma mapCommute:
shows "map (extend S) (map (extend R) c) = map (extend R) (map (extend S) c)"
by (induct_tac c) (auto simp add:extendCommute)

lemma extendAssoc:
shows "(extend S) (extend R c) = extend (extend S R) c" 
by (auto simp add:extend_def union_ac)

lemma mapAssoc:
shows "map (extend S) (map (extend R) c) = map (extend (extend S R)) c"
by (induct_tac c) (auto simp add:extendAssoc)


(* Disjointness of the various rule sets *)
lemma disjoint_Aux:
assumes "mset c = \<LM>A\<RM>"
shows "A :# mset (extend S c)"
proof-
from assms have "c = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<or> c = (\<LM>A\<RM> \<Rightarrow>* \<Empt>)" by (cases c) (auto simp add:mset.simps union_is_single)
then show ?thesis by (auto simp add:extend_def mset.simps)
qed

lemma disjoint_Aux2:
assumes "mset c = \<LM>A\<RM>"
    and "A \<noteq> B"
    and "mset (extend S c) = \<LM>B\<RM>"
shows "False"
proof-
from assms have "A :# \<LM>B\<RM>" using disjoint_Aux[where c=c and A=A and S=S] by auto
with `A \<noteq> B` show ?thesis by auto
qed

lemma disjoint_Ax_up:
shows "Ax \<inter> upRules = {}"
apply auto apply (rule Ax.cases) apply auto by (rotate_tac 1,rule upRules.cases,auto)+

lemma disjoint_Ax_mod2:
shows "Ax \<inter> modRules2 = {}"
apply auto apply (rule Ax.cases) apply auto by (rotate_tac 1,rule modRules2.cases,auto)+

lemma disjoint_Ax_mod1:
shows "Ax \<inter> p_e modRules2 M N = {}"
apply auto apply (rule Ax.cases) apply auto apply (rule p_e.cases) apply auto apply (rule modRules2.cases) 
apply (auto simp add:extendRule_def extend_def) apply (rule p_e.cases) apply auto apply (rule modRules2.cases)
by (auto simp add:extendRule_def extend_def)

lemma disjoint_up_mod2:
shows "upRules \<inter> modRules2 = {}"
apply auto apply (rule upRules.cases) apply auto by (rotate_tac 1,rule modRules2.cases,auto)

lemma disjoint_up_mod1:
shows "upRules \<inter> p_e modRules2 M N = {}"
using disjoint_Aux2
apply auto apply (rule upRules.cases) apply auto
apply (rule p_e.cases)  apply auto apply (rule modRules2.cases) 
apply (auto simp add:extendRule_def extend_def union_ac)
apply (drule_tac x=cb in meta_spec) apply (drule_tac x="Modal Ma Ms" in meta_spec)
apply (drule_tac x="Compound R Fs" in meta_spec) apply (drule_tac x="M\<cdot>\<Gamma> \<Rightarrow>* N\<cdot>\<Delta>" in meta_spec) by (auto simp:union_ac)

lemmas disjoint = disjoint_Ax_up disjoint_Ax_mod1 disjoint_Ax_mod2 
                  disjoint_up_mod2 disjoint_up_mod1


lemma Ax_subset_false_aux:
assumes "A \<subseteq> B" and "A \<inter> B = {}" and "A \<noteq> {}"
shows "False"
proof-
 from `A \<noteq> {}` have "\<exists> a. a \<in> A" by auto
 then obtain a where a: "a \<in> A" by auto
 with `A \<subseteq> B` have "a \<in> B" by auto
 with a have "a \<in> A \<inter> B" by simp
 with `A \<inter> B = {}` show ?thesis by auto
qed

lemma Ax_subset_false:
assumes "Ax \<subseteq> modRules2"
shows "False"
proof-
 have a: "([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>) \<in> Ax" by auto
 then have "Ax \<noteq> {}" by auto
 with disjoint_Ax_mod2 and assms show ?thesis using Ax_subset_false_aux[where A=Ax and B="modRules2"] by auto
qed



lemma modal_not_contain:
assumes "M \<noteq> N"
shows "\<not> (Modal M A :# N\<cdot>\<Gamma>)"
using assms by (induct \<Gamma>) (auto simp add:modaliseMultiset_def)

lemma nonPrincipalID:
fixes A :: "('a,'b) form"
assumes "r \<in> Ax"
shows "\<not> rightPrincipal r A R \<and> \<not> leftPrincipal r A R"
proof-
from assms obtain i where r1:"r = ([], \<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<or> r = ([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i\<RM>)" 
     using characteriseAx[where r=r] by auto
{ assume "rightPrincipal r A R" then obtain Ps where r2:"r = (Ps, \<Empt> \<Rightarrow>* \<LM> A \<RM>)" by (cases r) auto
  with r1 and disjoint and `r \<in> Ax` have "False" by auto
}
then have "\<not> rightPrincipal r A R" by auto
moreover
{ assume "leftPrincipal r A R" then obtain Ps' 
          where r3:"r = (Ps', \<LM>A\<RM> \<Rightarrow>* \<Empt>) \<and> A \<noteq> ff" by (cases r) auto
  with r1 and disjoint and `r \<in> Ax` have "False" by auto
}
then have "\<not> leftPrincipal r A R" by auto
ultimately show ?thesis by simp
qed

lemma compound_not_in_modal_multi:
shows "\<not> (Compound M Ms :# N\<cdot>\<Gamma>)"
by (induct \<Gamma>) (auto simp add:modaliseMultiset_def)

lemma not_principal_aux:
assumes "mset c = \<LM>Modal T Ts\<RM>"
    and "M\<cdot>\<Gamma> + succ c = N\<cdot>\<Delta> \<oplus> Compound F Fs"
shows "False"
proof-
from assms and single_is_union have "c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<or> c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)" apply (cases c)
     apply (rename_tac multiset1 multiset2)
     apply auto
     by (drule_tac x="Modal T Ts" in meta_spec,drule_tac x="multiset1" in meta_spec,
         drule_tac x="multiset2" in meta_spec,simp)+
moreover
   {assume "c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)"
    with assms have "M\<cdot>\<Gamma> \<oplus> Modal T Ts = N\<cdot>\<Delta> \<oplus> Compound F Fs" by auto
    then have "Compound F Fs :# M\<cdot>\<Gamma> \<oplus> Modal T Ts" by auto
    then have "Compound F Fs :# M\<cdot>\<Gamma>" by auto
    then have "False" using compound_not_in_modal_multi[where M=F and Ms=Fs and N=M and \<Gamma>=\<Gamma>] by auto
   }
moreover
   {assume "c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
    with assms have "Compound F Fs :# M\<cdot>\<Gamma>" by auto
    then have "False" using compound_not_in_modal_multi[where M=F and Ms=Fs and N=M and \<Gamma>=\<Gamma>] by auto
   }
ultimately show ?thesis by blast
qed

lemma not_principal_aux2:
assumes "mset c = \<LM>Modal T Ts\<RM>"
    and "M\<cdot>\<Gamma> + antec c = N\<cdot>\<Delta> \<oplus> Compound F Fs"
shows "False"
proof-
from assms and single_is_union have "c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<or> c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)" apply (cases c)
     apply (rename_tac multiset1 multiset2)
     apply (auto simp add:mset.simps)
     by (drule_tac x="Modal T Ts" in meta_spec,drule_tac x="multiset1" in meta_spec,
         drule_tac x="multiset2" in meta_spec,simp)+
moreover
   {assume "c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)"
    with assms have "Compound F Fs :# M\<cdot>\<Gamma>" by auto
    then have "False" using compound_not_in_modal_multi[where M=F and Ms=Fs and N=M and \<Gamma>=\<Gamma>] by auto
   }
moreover
   {assume "c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
    with assms have "M\<cdot>\<Gamma> \<oplus> Modal T Ts = N\<cdot>\<Delta> \<oplus> Compound F Fs" by auto
    then have "Compound F Fs :# M\<cdot>\<Gamma> \<oplus> Modal T Ts" by auto
    then have "Compound F Fs :# M\<cdot>\<Gamma>" by auto
    then have "False" using compound_not_in_modal_multi[where M=F and Ms=Fs and N=M and \<Gamma>=\<Gamma>] by auto
   }
ultimately show ?thesis by blast
qed

lemma modRules_not_right_principal_for_compound:
assumes "r \<in> p_e modRules2 S T"
shows "\<not> rightPrincipal r (Compound M Ms) R"
using assms
proof-
from assms have "fst r \<noteq> []" apply (rule p_e.cases) apply (insert modRule2Characterise)
     apply (drule_tac x=Ps in meta_spec) apply (drule_tac x=c in meta_spec)
     by (auto simp add:extendRule_def)
{assume "rightPrincipal r (Compound M Ms) R"
 with assms obtain ps c where "r = (ps,c)" and "c = (\<Empt> \<Rightarrow>* \<LM>Compound M Ms\<RM>)" using not_principal_aux
      apply (cases r) by (rule rightPrincipal.cases) auto 
 then have "r \<in> upRules" using `fst r \<noteq> []` by auto
 with assms have "False" using disjoint_up_mod1[where M=S and N=T] by auto
}
thus ?thesis by auto
qed

lemma modRules_not_left_principal_for_compound:
assumes "r \<in> p_e modRules2 T S"
shows "\<not> leftPrincipal r (Compound M Ms) R"
using assms
proof-
from assms have "fst r \<noteq> []" apply (rule p_e.cases) apply (insert modRule2Characterise)
     apply (drule_tac x=Ps in meta_spec) apply (drule_tac x=c in meta_spec)
     by (auto simp add:extendRule_def)
{assume "leftPrincipal r (Compound M Ms) R"
 with assms obtain ps c where "r = (ps,c)" and "c = (\<LM>Compound M Ms\<RM> \<Rightarrow>* \<Empt>)" using not_principal_aux2
      apply (cases r) by (rule leftPrincipal.cases) auto 
 then have "r \<in> upRules" using `fst r \<noteq> []` by auto
 with assms have "False" using disjoint_up_mod1[where M=T and N=S] by auto
}
thus ?thesis by auto
qed

lemma modRules2_not_left_principal_for_compound:
assumes "r \<in> modRules2"
shows "\<not> leftPrincipal r (Compound M Ms) R"
using assms
proof-
from assms obtain ps T Ts where "r = (ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<or> r = (ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
     using modRule2Characterise apply (cases r) apply auto apply (rotate_tac 2) apply (drule_tac x=a in meta_spec)
     apply (rotate_tac 2) by (drule_tac x=b in meta_spec) auto
moreover
   {assume "r = (ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)"
    then have "\<not> leftPrincipal r (Compound M Ms) R" apply auto apply (rule leftPrincipal.cases) 
         by (auto simp add:extendRule_def extend_def)
   }
moreover
  {assume "r = (ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
   then have "\<not> leftPrincipal r (Compound M Ms) R" apply auto apply (rule leftPrincipal.cases)
        by (auto simp add:extendRule_def extend_def)
  }
ultimately show "\<not> leftPrincipal r (Compound M Ms) R" by blast
qed

lemma modRules2_not_right_principal_for_compound:
assumes "r \<in> modRules2"
shows "\<not> rightPrincipal r (Compound M Ms) R"
using assms
proof-
from assms obtain ps T Ts where "r = (ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<or> r = (ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
     using modRule2Characterise apply (cases r) apply auto apply (rotate_tac 2) apply (drule_tac x=a in meta_spec)
     apply (rotate_tac 2) by (drule_tac x=b in meta_spec) auto
moreover
   {assume "r = (ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)"
    then have "\<not> rightPrincipal r (Compound M Ms) R" apply auto apply (rule rightPrincipal.cases) 
         by (auto simp add:extendRule_def extend_def)  
   }
moreover
  {assume "r = (ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
   then have "\<not> rightPrincipal r (Compound M Ms) R" apply auto apply (rule rightPrincipal.cases)
        by (auto simp add:extendRule_def extend_def)        
  }
ultimately show "\<not> rightPrincipal r (Compound M Ms) R" by blast
qed

lemma upRules_not_right_principal_for_modal:
assumes "r \<in> upRules"
  shows "\<not> rightPrincipal r (Modal M Ms) R"
proof-
from assms obtain ps T Ts where "r = (ps,\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> r = (ps,\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
     using upRuleCharacterise apply (cases r) apply auto apply (rotate_tac 2) apply (drule_tac x=a in meta_spec)
     apply (rotate_tac 2) by (drule_tac x=b in meta_spec) auto
moreover
   {assume "r = (ps,\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)"
    then have "\<not> rightPrincipal r (Modal M Ms) R" apply auto apply (rule rightPrincipal.cases)
         by (auto simp add:extendRule_def extend_def) 
   }
moreover
   {assume "r = (ps,\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
    then have "\<not> rightPrincipal r (Modal M Ms) R" apply auto apply (rule rightPrincipal.cases)
         by (auto simp add:extendRule_def extend_def)
   }
ultimately show "\<not> rightPrincipal r (Modal M Ms) R" by blast
qed

lemma upRules_not_left_principal_for_modal:
assumes "r \<in> upRules"
shows "\<not> leftPrincipal r (Modal M Ms) R"
using assms
proof-
from assms obtain ps T Ts where "r = (ps,\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> r = (ps,\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
     using upRuleCharacterise apply (cases r) apply auto apply (rotate_tac 2) apply (drule_tac x=a in meta_spec)
     apply (rotate_tac 2) by (drule_tac x=b in meta_spec) auto
moreover
   {assume "r = (ps,\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)"
    then have "\<not> leftPrincipal r (Modal M Ms) R" apply auto apply (rule leftPrincipal.cases) 
         by (auto simp add:extendRule_def extend_def)
   }
moreover
  {assume "r = (ps,\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
   then have "\<not> leftPrincipal r (Modal M Ms) R" apply auto apply (rule leftPrincipal.cases)
        by (auto simp add:extendRule_def extend_def)
  }
ultimately show "\<not> leftPrincipal r (Modal M Ms) R" by blast
qed

lemmas nonPrincipalRight = upRules_not_right_principal_for_modal
                           modRules_not_right_principal_for_compound
                           modRules2_not_right_principal_for_compound

lemmas nonPrincipalLeft = upRules_not_left_principal_for_modal
                          modRules_not_left_principal_for_compound
                          modRules2_not_left_principal_for_compound




(* Bunch of results about modalising multisets *)
lemma modalise_characterise:
fixes A :: "('a,'b) form"
and   M :: "'b"
and  \<Delta>  :: "('a,'b) form multiset"
assumes "A :# M\<cdot>\<Delta>"
shows "\<exists> B. A = Modal M [B]"
proof-
 from assms have "\<Delta> \<noteq> \<Empt>" by (auto simp add:modaliseEmpty)
 with `A :# M\<cdot>\<Delta>` show "\<exists> B. A = Modal M [B]" 
      proof (induct \<Delta>)
      case empty
      then show ?case by simp
  next
      case (add \<Delta>' x)
      then have IH: "\<lbrakk> A :# M\<cdot>\<Delta>' ; \<Delta>' \<noteq> \<Empt> \<rbrakk> \<Longrightarrow> \<exists> B. A = Modal M [B]"
            and b: "A :# M \<cdot> (\<Delta>' \<oplus> x)" by auto
      from b have "A :# M\<cdot>\<Delta>' \<or> A :# M\<cdot>(\<LM>x\<RM>)" by (auto simp add:modaliseMultiset_def image_mset_insert)
      moreover
         {assume "A :# M\<cdot>\<Delta>'"
          then have "\<Delta>' \<noteq> \<Empt>" by (auto simp add:modaliseEmpty)
          with `A :# M\<cdot>\<Delta>'` have "\<exists> B. A = Modal M [B]" using IH by simp
         }
      moreover
         {assume "A :# M\<cdot>(\<LM>x\<RM>)"
          then have "A :# \<LM> Modal M [x] \<RM>" by (auto simp add:modaliseMultiset_def)
          then have "A \<in> set_mset (\<LM>Modal M [x]\<RM>)" by (auto simp only:set_mset_def)
          then have "A \<in> {Modal M [x]}" by auto
          then have "A = Modal M [x]" by auto
          then have "\<exists> B. A = Modal M [B]" by blast
         }
      ultimately show ?case by blast
  qed
qed


lemma non_contain:
fixes \<Delta> \<Delta>' :: "('a,'b) form multiset"
assumes "\<Delta> \<noteq> \<Empt>" and "\<Delta>' \<noteq> \<Empt>" and "M \<noteq> N"
shows "set_mset (M\<cdot>\<Delta>) \<inter> set_mset (N\<cdot>\<Delta>') = {}"
proof-
{
assume "set_mset (M\<cdot>\<Delta>) \<inter> set_mset (N\<cdot>\<Delta>') \<noteq> {}"
then have "\<exists> A. A \<in> set_mset (M\<cdot>\<Delta>) \<inter> set_mset (N\<cdot>\<Delta>')" by auto
then obtain A where a: "A \<in> set_mset (M\<cdot>\<Delta>) \<inter> set_mset (N\<cdot>\<Delta>')" by blast
then have "False"
 proof- 
   from a have box: "A \<in> set_mset (M\<cdot>\<Delta>)" and dia: "A \<in> set_mset (N\<cdot>\<Delta>')" by auto
   from box have "A :# M\<cdot>\<Delta>" by auto
   with `\<Delta> \<noteq> \<Empt>` have "\<exists> B. A = Modal M [B]" using modalise_characterise[where M=M] by (auto)
   then obtain B where "A = Modal M [B]" by blast
   moreover 
   from dia have "A :# N\<cdot>\<Delta>'" by auto
   with `\<Delta>' \<noteq> \<Empt>` have "\<exists> C. A = Modal N [C]" using modalise_characterise[where M=N] by auto
   then obtain C where "A = Modal N [C]" by blast
   ultimately show "False" using `M\<noteq>N` by auto
 qed
}
then show ?thesis by auto
qed


lemma modal_neq:
fixes A :: "('a,'b) form" and ps :: "('a,'b) form list"
shows "A \<noteq> Modal M [A]" and "ps \<noteq> [Modal M ps]"
by (induct A and ps rule: compat_form.induct compat_form_list.induct) auto

lemma p_e_non_empty: 
 "r \<in> p_e R M N \<Longrightarrow> fst r \<noteq> []"
apply (rule p_e.cases) apply auto
apply (subgoal_tac "(Ps, c) \<in> modRules2")
apply (rule modRules2.cases) by (auto simp add:extendRule_def)


(* -------------------------------
   -------------------------------
        ModalWeakening2.thy
   -------------------------------
   ------------------------------- *)


lemma dpWeak:
assumes a:"(\<Gamma> \<Rightarrow>* \<Delta>,n) \<in> derivable (ext R R2 M N)"
   and  b: "R1 \<subseteq> upRules"
   and  c: "R2 \<subseteq> modRules2"
   and  d: "R3 \<subseteq> modRules2"
   and  e: "R = Ax \<union> R1 \<union> (p_e R2 M N) \<union> R3" 
shows "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n) \<in> derivable (ext R R2 M N)"
using a
proof (induct n arbitrary: \<Gamma> \<Delta> rule:nat_less_induct)
case (1 n \<Gamma> \<Delta>)
then have IH: "\<forall>m<n. \<forall> \<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta>, m) \<in> derivable (ext R R2 M N) \<longrightarrow> ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M N)" 
      and a': "( \<Gamma> \<Rightarrow>* \<Delta>, n) \<in> derivable (ext R R2 M N)" by auto
show ?case
proof (cases n)
case 0
 then have "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable (ext R R2 M N)" using a' by simp
 then have "([], \<Gamma> \<Rightarrow>* \<Delta>) \<in> (ext R R2 M N)" by (cases) auto      
 then obtain  r S where "r \<in> R" and split:"(extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta>) \<or> extendConc S r = ([],\<Gamma> \<Rightarrow>* \<Delta>))" 
      apply (rule ext.cases) by (auto simp add:extendRule_def extend_def extendConc_def)
 then obtain c where "r = ([],c)" by (cases r) (auto simp add:extendRule_def extendConc_def)
 with `r \<in> R` have "r \<in> Ax \<or> (r \<in> upRules \<union> (p_e R2 M N) \<union> modRules2)" using b c d e by auto
 with `r = ([],c)` have "r \<in> Ax" apply auto apply (rule upRules.cases,auto)
                                 defer
                                 apply (rule modRules2.cases, auto)
                                 apply (rule p_e.cases,auto simp add:extendRule_def)
                                 apply hypsubst_thin
                                 apply (insert p_e_non_empty[where R=R2 and M=M and N=N])
                                 apply (drule_tac x="([], extend ( M \<cdot> \<Gamma> \<Rightarrow>* N \<cdot> \<Delta>) c)" in meta_spec) by auto
 with `r = ([],c)` obtain i where "c = (\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>) \<or> c = (\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
      using characteriseAx[where r=r] by auto
 moreover
    {assume "c = (\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)"
     then have "extend S (\<LM>At i\<RM> \<Rightarrow>*\<LM>At i\<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)" using split and `r = ([],c)`
          by (auto simp add:extendRule_def extendConc_def)
     then have "At i :# \<Gamma> \<and> At i :# \<Delta>" using extendID by auto
     then have "At i :# \<Gamma> + \<Gamma>' \<and> At i :# \<Delta> + \<Delta>'" by auto
     then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M N)" 
          using e and containID[where \<Gamma>="\<Gamma>+\<Gamma>'" and \<Delta>="\<Delta>+\<Delta>'" and R=R and i=i] by auto
    }
 moreover
    {assume "c = (\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
     then have "extend S (\<LM>ff\<RM> \<Rightarrow>*\<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)" using split and `r = ([],c)`
          by (auto simp add:extendRule_def extendConc_def)
     then have "ff :# \<Gamma>" using extendFalsum by auto
     then have "ff :# \<Gamma> + \<Gamma>'" by auto
     then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M N)" 
          using e and containFalsum[where \<Gamma>="\<Gamma>+\<Gamma>'" and \<Delta>="\<Delta>+\<Delta>'" and R=R] by auto
    }
 ultimately show "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n) \<in> derivable (ext R R2 M N)" using `n=0` by auto
next
case (Suc n')
 then have "(\<Gamma> \<Rightarrow>* \<Delta>, n'+1) \<in> derivable (ext R R2 M N)" using a' by simp
 then obtain Ps where f:"Ps \<noteq> []"
                  and g:"(Ps, \<Gamma> \<Rightarrow>* \<Delta>) \<in> (ext R R2 M N)" 
                  and h:"\<forall> p \<in> set Ps. \<exists> m\<le>n'. (p,m) \<in> derivable (ext R R2 M N)" 
      using characteriseLast[where C="\<Gamma> \<Rightarrow>* \<Delta>" and m=n' and R="ext R R2 M N"] by auto
 from g c obtain S r where "r \<in> R" and "((r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>)) \<or>
                                  (r \<in> p_e R2 M N \<and> extendConc S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>))"
      by (cases) auto
 moreover
    {assume as:"(r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>)"
     then have eq:"map (extend (\<Gamma>' \<Rightarrow>* \<Delta>')) Ps = fst (extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)"
           using mapCommute[where S="\<Gamma>'\<Rightarrow>*\<Delta>'" and R=S and c="fst r"]
           by (auto simp add:extendRule_def extend_def mapAssoc simp del: map_map)
     from as have eq2: "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') = snd (extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)"
           by (auto simp add:extendRule_def extend_def union_ac)
     from as f have "fst r \<noteq> []" by (auto simp add:extendRule_def map_is_Nil_conv)
     with as have "r \<in> upRules \<or> r \<in> modRules2" apply (cases r,auto) by (rule Ax.cases) auto
     have "\<forall> p' \<in> set (map (extend (\<Gamma>' \<Rightarrow>* \<Delta>')) Ps). \<exists> m\<le>n'. (p',m) \<in> derivable (ext R R2 M N)"
          proof-
          {fix p
           assume "p \<in> set (map (extend (\<Gamma>' \<Rightarrow>* \<Delta>')) Ps)"
           then obtain p' where t:"p' \<in> set Ps \<and> p = extend (\<Gamma>' \<Rightarrow>* \<Delta>') p'" by auto
           with h obtain m where "m\<le>n'" and "(p',m) \<in> derivable (ext R R2 M N)" by auto
           moreover obtain \<Phi> \<Psi> where eq:"p' = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases p') auto 
           then have "p = (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')" using t by (auto simp add:extend_def union_ac)
           ultimately have "(p,m) \<in> derivable (ext R R2 M N)" using IH and `n = Suc n'` and eq
                apply- by (drule_tac x=m in spec) simp
           then have "\<exists> m\<le>n'. (p,m) \<in> derivable (ext R R2 M N)" using `m\<le>n'` by auto
           }
           then show ?thesis by auto
           qed
     then have "\<forall> p' \<in> set (fst (extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)).
                \<exists> m\<le>n'. (p',m) \<in> derivable (ext R R2 M N)" using eq by auto
     moreover have "extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r \<in> (ext R R2 M N)" 
              using `r \<in> upRules \<or> r \<in> modRules2` and `r \<in> R` by auto
     ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable (ext R R2 M N)"
              using derivable.step[where r="extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r" and R="ext R R2 M N" and m="n'"]
              and `fst r \<noteq> []` and eq2 by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
     }
 moreover
     {assume as:"r \<in> p_e R2 M N \<and> extendConc S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>)"
      then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') = snd (extendConc (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)"
           by (auto simp add:extendConc_def extend_def union_ac)
      moreover from as have "Ps = fst (extendConc (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)"
           by (auto simp add:extendConc_def)
      moreover have "extendConc S r \<in> ext R R2 M N" using as and g by auto
      moreover have "extendConc (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r \<in> ext R R2 M N" using as and `r \<in> R` and c
            and ext.mod1[where r=r and R'=R2 and M=M and N=N and R=R and seq="extend S (\<Gamma>' \<Rightarrow>* \<Delta>')"]
            by auto
      ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable (ext R R2 M N)"
           using h f and 
           derivable.step[where r="extendConc (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r" and R="ext R R2 M N" and m="n'"]
           by auto
     }
 ultimately show "( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', n) \<in> derivable (ext R R2 M N)" using `n = Suc n'` by auto
 qed
qed



(* -------------------------------
   -------------------------------
        ModalInvertibility.thy
   -------------------------------
   ------------------------------- *)

lemma nonPrincipalInvertRight:
assumes "R1 \<subseteq> upRules" and "R2 \<subseteq> modRules2" and "R3 \<subseteq> modRules2"
    and "R = Ax \<union> R1 \<union> p_e R2 M1 M2 \<union> R3" and "r \<in> R" and "r = (ps,c)"
    and "R' = Ax \<union> R1 \<union> R2 \<union> R3"
    and IH: "\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms, m) \<in> derivable (ext R R2 M1 M2) \<longrightarrow>
              (\<forall>r' \<in> R'. rightPrincipal r' (Modal M Ms) R' \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>              
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable (ext R R2 M1 M2))"
    and a': "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms,n) \<in> derivable (ext R R2 M1 M2)" 
    and b': "\<forall> r' \<in> R'. rightPrincipal r' (Modal M Ms) R' \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and np: "\<not> rightPrincipal r (Modal M Ms) R'"
    and ext: "(r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
    and num: "n = n' + 1"
    and all: "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)"
    and nonempty: "Ps \<noteq> []"  
shows "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
proof-
 from ext nonempty have "r \<in> upRules \<or> r \<in> modRules2" apply (auto simp add:extendRule_def) apply (cases r) 
       apply (rotate_tac 3) by (rule Ax.cases) auto
 obtain \<Phi> \<Psi> where "S = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases S) (auto)
 from `r = (ps,c)` obtain G H where "c = (G \<Rightarrow>* H)" by (cases c) (auto)
 then have "\<LM> Modal M Ms \<RM> \<noteq> H" 
      proof-
      {assume "r \<in> upRules"
       with `r = (ps,c)` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
             using upRuleCharacterise[where Ps=ps and C=c] by auto
       moreover
         {assume "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)"
          with `c = (G \<Rightarrow>* H)` have "\<LM> Modal M Ms \<RM> \<noteq> H" by auto
         }
       moreover
         {assume "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
          then have "\<LM>Modal M Ms \<RM> \<noteq> H" using `c = (G \<Rightarrow>* H)` by auto
         }
       ultimately have "\<LM> Modal M Ms \<RM> \<noteq> H" by blast
      }
      moreover
      {assume "r \<in> modRules2" 
       with `r = (ps,c)` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>) \<or> c = (\<LM> Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
             using modRule2Characterise[where Ps=ps and C=c] by auto
       moreover
         {assume "c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>)"
          then have "rightPrincipal r (Modal T Ts) R'" using `r = (ps,c)` and `r \<in> R`
               proof-
               from `c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)` and `r = (ps,c)` and `r \<in> R` and `r \<in> modRules2`
                    have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R" by auto
               with `R = Ax \<union> R1 \<union> p_e R2 M1 M2 \<union> R3`
                    have "(ps,  \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> p_e R2 M1 M2 \<or>
                          (ps,  \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R3" apply auto apply (rule Ax.cases) apply auto
                    apply (subgoal_tac "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> upRules") apply (insert `R1 \<subseteq> upRules`)
                    apply auto apply (rule upRules.cases) by auto
               moreover
                  {assume "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R3"
                   then have "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" using `R' = Ax \<union> R1 \<union> R2 \<union> R3` by auto
                  }
               moreover
                  {assume "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> p_e R2 M1 M2"
                   then obtain \<Gamma>' \<Delta>' r' where aa: "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<and> r' \<in> R2"
                        apply (rule p_e.cases) by auto
                   then have "r' \<in> modRules2" using `R2 \<subseteq> modRules2` by auto
                   then obtain F Fs where 
                        "snd r' = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> snd r' = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                        using modRule2Characterise[where Ps="fst r'" and C="snd r'"] by auto
                   with aa have "(\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs) \<or>
                                 (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                        by (auto simp add:extendRule_def extend_def)
                   moreover
                      {assume "(\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs)"
                       then have "M1\<cdot>\<Gamma>' = \<Empt>" and "\<LM>Modal T Ts\<RM> = M2\<cdot>\<Delta>' \<oplus> Modal F Fs" by auto
                       then have "M1\<cdot>\<Gamma>' = \<Empt>" and "Modal T Ts = Modal F Fs" and "M2\<cdot>\<Delta>' = \<Empt>"
                            using 
                            singleton_add_means_equal[where A="Modal T Ts" and \<Gamma>="M2\<cdot>\<Delta>'" and B="Modal F Fs"]
                            and singleton_add_means_empty[where A="Modal T Ts" and \<Gamma>="M2\<cdot>\<Delta>'" and B="Modal F Fs"] 
                            by (auto simp add:modaliseMultiset_def)
                       then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' = r'" using extendRuleEmpty[where r=r'] by auto
                       then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<in> R2" using aa by auto
                       then have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R2" using aa by auto
                       then have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" using `R' = Ax\<union>R1 \<union>R2 \<union> R3 ` by simp
                      }
                   moreover
                      {assume "(\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                       then have "\<Empt> = M1\<cdot>\<Gamma>' \<oplus> Modal F Fs" by auto
                       then have "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" by auto
                      }
                   ultimately have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" by blast
                  }
              ultimately have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" by auto
              then show ?thesis using `r = (ps,c)` and `c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)` by auto
              qed
          with `\<not> rightPrincipal r (Modal M Ms) R'` have "Modal T Ts \<noteq> Modal M Ms" by auto
          with `c = (G \<Rightarrow>* H)` have "\<LM> Modal M Ms \<RM> \<noteq> H" using `c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>)` by auto
         }
       moreover
         {assume "c = (\<LM>Modal T Ts \<RM> \<Rightarrow>* \<Empt>)"
          then have "\<LM>Modal M Ms \<RM> \<noteq> H" using `c = (G \<Rightarrow>* H)` by auto
         }
       ultimately have "\<LM> Modal M Ms \<RM> \<noteq> H" by blast
      }
      ultimately show ?thesis using `r \<in> upRules \<or> r \<in> modRules2` by blast
      qed
 moreover have "succ S + succ (snd r) = (\<Delta> \<oplus> Modal M Ms)" 
          using ext and extendRule_def[where forms=S and R=r]
                    and extend_def[where forms=S and seq="snd r"] by auto
 then have "\<Psi> + H = \<Delta> \<oplus> Modal M Ms" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` and `r = (ps,c)` and `c = (G \<Rightarrow>* H)` by auto
 moreover from `r = (ps,c)` and `r \<in> upRules \<or> r \<in> modRules2` have "(ps,c) \<in> upRules \<or> (ps,c) \<in> modRules2" by auto
 then have "\<exists> A. c = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<or> c = (\<LM>A\<RM> \<Rightarrow>* \<Empt>)"
      using upRuleCharacterise[where Ps=ps and C=c]
        and modRule2Characterise[where Ps=ps and C=c] by auto
 then have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" using `c = (G \<Rightarrow>* H)` by auto
 ultimately have "Modal M Ms :# \<Psi>"
     proof-
     have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" by fact
     moreover
     {assume "H = \<Empt>"
      then have "\<Psi> = \<Delta> \<oplus> Modal M Ms" using `\<Psi> + H = \<Delta> \<oplus> Modal M Ms` by auto
      then have "Modal M Ms :# \<Psi>" by auto
     }
     moreover
     {assume "\<exists> A. H = \<LM>A\<RM>"
      then obtain T where "H = \<LM>T\<RM>" by auto
      then have "\<Psi> \<oplus> T = \<Delta> \<oplus> Modal M Ms" using `\<Psi> + H = \<Delta> \<oplus> Modal M Ms` by auto
      then have "set_mset (\<Psi> \<oplus> T) = set_mset (\<Delta> \<oplus> Modal M Ms)" by auto
      then have "set_mset \<Psi> \<union> {T} = set_mset \<Delta> \<union> {Modal M Ms}" by auto
      moreover from `H = \<LM>T\<RM>` and `\<LM>Modal M Ms\<RM> \<noteq> H` have "Modal M Ms \<noteq> T" by auto
      ultimately have "Modal M Ms \<in> set_mset \<Psi>" by auto
      then have "Modal M Ms :# \<Psi>" by auto
     }
     ultimately show "Modal M Ms :# \<Psi>" by blast
     qed
 then have "\<exists> \<Psi>1. \<Psi> = \<Psi>1 \<oplus> Modal M Ms" 
      by (rule_tac x="\<Psi> \<ominus> Modal M Ms" in exI) (auto simp add:multiset_eq_iff)
 then obtain \<Psi>1 where "S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms)" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` by auto
 have "Ps = map (extend S) ps" using ext and extendRule_def[where forms=S and R=r] and `r = (ps,c)` by auto
 then have "\<forall> p \<in> set Ps. (\<exists> p'. p = extend S p')" using ex_map_conv[where ys=Ps and f="extend S"] by auto
 then have "\<forall> p \<in> set Ps. (Modal M Ms :# succ p)" 
      using `Modal M Ms :# \<Psi>` and `S = (\<Phi> \<Rightarrow>* \<Psi>)` apply (auto simp add:Ball_def) 
      by (drule_tac x=x in spec) (auto simp add:extend_def)
 then have a1:"\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms)" using characteriseSeq
      apply (auto simp add:Ball_def) apply (drule_tac x=x in spec,simp) 
      apply (rule_tac x="antec x" in exI,rule_tac x="succ x \<ominus> Modal M Ms" in exI) 
      by (drule_tac x=x in meta_spec) (auto simp add:multiset_eq_iff)
 with all have "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> 
                             (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms,n) \<in> derivable (ext R R2 M1 M2) \<and> 
                              p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus>Modal M Ms)"
                  by (auto simp add:Ball_def)
 then have a2: "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' m. m\<le>n' \<and> 
                              (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',m) \<in> derivable (ext R R2 M1 M2) \<and> 
                              p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms)"
                  using num and b' and IH
                  apply (auto simp add:Ball_def) apply (drule_tac x=x in spec) apply simp
                  apply hypsubst_thin
                  apply (elim exE conjE) apply (drule_tac x=n in spec) apply simp
                  apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)
                  apply (simp) apply (elim exE conjE) by (rule_tac x=m' in exI) arith
 obtain Ps' where eq: "Ps' = map (extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>')) ps" by auto
 have "length Ps = length Ps'" using `Ps' = map (extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>')) ps`
                               and `Ps = map (extend S) ps` by auto
 then have "Ps' \<noteq> []" using nonempty by auto
 from `r \<in> upRules \<or> r \<in> modRules2` and `r \<in> R` have "extendRule (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') r \<in> (ext R R2 M1 M2)" by auto
 moreover have "extendRule (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') r = (Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')"
          using `S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms)` and ext and `r = (ps,c)` and eq
          by (auto simp add:extendRule_def extend_def union_ac multiset_eq_iff)
 ultimately have "(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> (ext R R2 M1 M2)" by simp
 have c1:"\<forall> p \<in> set ps. extend S p \<in> set Ps" using `Ps = map (extend S) ps` by (simp add:Ball_def)           
 have c2:"\<forall> p \<in> set ps. extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p \<in> set Ps'" using eq by (simp add:Ball_def)
 then have eq2:"\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq
           apply (auto simp add:Ball_def extend_def) 
           apply (rule_tac x="\<Phi> + antec xa" in exI) apply (simp add:union_ac) 
           by (rule_tac x="\<Psi>1 + succ xa" in exI) (simp add: union_ac)
 have d1:"\<forall> p \<in> set Ps. \<exists> p' \<in> set ps. p = extend S p'" using `Ps = map (extend S) ps` by (auto simp add:Ball_def Bex_def)
 then have "\<forall> p \<in> set Ps. \<exists> p'. p' \<in> set Ps'" using c2 by (auto simp add:Ball_def Bex_def)
 moreover have d2: "\<forall> p \<in> set Ps'. \<exists> p' \<in> set ps. p = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p'" using eq
             by (auto simp add:Ball_def Bex_def)
 then have "\<forall> p \<in> set Ps'. \<exists> p'. p' \<in> set Ps" using c1 by (auto simp add:Ball_def Bex_def)
 have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) \<in> set Ps \<longrightarrow> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"
                proof-
                 {fix \<Phi>' \<Psi>'
                  assume "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) \<in> set Ps"  
                  then have "\<exists> p \<in> set ps. extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms) p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms)"
                       using `Ps = map (extend S) ps` and `S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms)` and a1 and d1
                            apply (simp only:Ball_def Bex_def) apply (drule_tac x=" \<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms" in spec)
                            by (drule_tac x="\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms" in spec) (auto)
                  then obtain p where t:"p \<in> set ps \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms) p"
                       apply auto by (drule_tac x=p in meta_spec) (simp)
                  then obtain D B where "p = (D \<Rightarrow>* B)" by (cases p) 
                  then have "(D \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms) (D \<Rightarrow>* B)"
                       using t by auto
                  then have ant: "\<Phi>' = \<Phi> + D" and suc: "\<Psi>' \<oplus> Modal M Ms = \<Psi>1 \<oplus> Modal M Ms + B" 
                       using extend_def[where forms="\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms" and seq="D \<Rightarrow>* B"] by auto
                  from ant have "\<Phi>' + \<Gamma>' = (\<Phi> + \<Gamma>') + D" by (auto simp add:union_ac)
                  moreover
                  from suc have "\<Psi>' = \<Psi>1 + B" by (auto simp add:union_ac multiset_eq_iff)
                  then have "\<Psi>' + \<Delta>' = (\<Psi>1 + \<Delta>') + B" by (auto simp add:union_ac)
                  ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (D \<Rightarrow>* B)" 
                       using extend_def[where forms="\<Phi>+\<Gamma>'\<Rightarrow>*\<Psi>1+\<Delta>'" and seq="D\<Rightarrow>*B"] by auto
                  moreover have "extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (D \<Rightarrow>* B) \<in> set Ps'" using `p = (D \<Rightarrow>* B)` and t and c2 by auto
                  ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'" by simp
                  }
                  thus ?thesis by blast
                qed
             moreover
             have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps' \<longrightarrow> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) \<in> set Ps"
                proof-
                  {fix \<Phi>' \<Psi>'
                  assume "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"  
                  then have "\<exists> p \<in> set ps. extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')"
                       using eq and eq2 and d2
                            apply (simp only:Ball_def Bex_def) apply (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec)
                           by (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec) (auto)
                  then obtain p where t:"p \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p"
                       apply auto by (drule_tac x=p in meta_spec) (simp)
                  then obtain D B where "p = (D \<Rightarrow>* B)" by (cases p) 
                  then have "(D \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (D \<Rightarrow>* B)"
                       using t by auto
                  then have ant: "\<Phi>' + \<Gamma>' = \<Phi> + \<Gamma>' + D" and suc: "\<Psi>' + \<Delta>' = \<Psi>1 + \<Delta>' + B" 
                       using extend_def[where forms="\<Phi>+\<Gamma>'\<Rightarrow>*\<Psi>1+\<Delta>'" and seq="D\<Rightarrow>*B"] by auto
                  from ant have "\<Phi>' + \<Gamma>' = (\<Phi> + D) + \<Gamma>'" by (auto simp add:union_ac)
                  then have "\<Phi>' = \<Phi> + D" by simp
                  moreover
                  from suc have "\<Psi>' + \<Delta>' = (\<Psi>1 + B) + \<Delta>'" by (auto simp add:union_ac)
                  then have "\<Psi>' = \<Psi>1 + B" by simp
                  then have "\<Psi>' \<oplus> Modal M Ms = (\<Psi>1 \<oplus> Modal M Ms) + B" by (auto simp add:union_ac)
                  ultimately have "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms) (D \<Rightarrow>* B)" 
                       using extend_def[where forms="\<Phi>\<Rightarrow>*\<Psi>1\<oplus>Modal M Ms" and seq="D\<Rightarrow>*B"] by auto
                  moreover have "extend (\<Phi>  \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms) (D \<Rightarrow>* B) \<in> set Ps" using `p = (D \<Rightarrow>* B)` and t and c1
                       and `S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Modal M Ms)` by auto
                  ultimately have "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) \<in> set Ps" by simp
                  }
                  thus ?thesis by blast
                qed
 ultimately
 have "\<forall> \<Phi>' \<Psi>'. ((\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms) \<in> set Ps) = ((\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps')" by auto
 then have "\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',n) \<in> derivable (ext R R2 M1 M2)
                 \<and> p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq2 and a2
      apply (simp add:Ball_def) apply (intro allI impI) apply (drule_tac x=x in spec) apply simp
      apply (elim exE) apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)  
      by (drule_tac x="\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Modal M Ms" in spec) (simp)
 then have all:"\<forall> p \<in> set Ps'. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)" by auto
 then show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using num
      and `(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> (ext R R2 M1 M2)` and `Ps' \<noteq> []`
      and derivable.step[where r="(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" and R="ext R R2 M1 M2"]
      by (auto simp add:Ball_def Bex_def)
qed



(* Check this later. *)

lemma nonPrincipalInvertLeft:
assumes "R1 \<subseteq> upRules" and "R2 \<subseteq> modRules2" and "R3 \<subseteq> modRules2"
    and "R = Ax \<union> R1 \<union> p_e R2 M1 M2 \<union> R3" and "r \<in> R" and "r = (ps,c)" and "R' = Ax \<union> R1 \<union> R2 \<union> R3"
    and IH: "\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>, m) \<in> derivable (ext R R2 M1 M2) \<longrightarrow>
              (\<forall>r' \<in> R'. leftPrincipal r' (Modal M Ms) R' \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable (ext R R2 M1 M2) )"
    and a': "(\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>,n) \<in> derivable (ext R R2 M1 M2)" 
    and b': "\<forall> r' \<in> R'. leftPrincipal r' (Modal M Ms) R' \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and np: "\<not> leftPrincipal r (Modal M Ms) R'"
    and ext: "((r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>))"
    and num: "n = n' + 1"
    and all: "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)"
    and nonempty: "Ps \<noteq> []"  
shows "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
proof-
 from ext nonempty have "r \<in> upRules \<or> r \<in> modRules2" apply (auto simp add:extendRule_def) apply (cases r) 
       apply (rotate_tac 3) by (rule Ax.cases) auto
 obtain \<Phi> \<Psi> where "S = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases S) (auto)
 from `r = (ps,c)` obtain G H where "c = (H \<Rightarrow>* G)" by (cases c) (auto)
 then have "\<LM> Modal M Ms \<RM> \<noteq> H" 
      proof-
      {assume "r \<in> upRules"
       with `r = (ps,c)` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
             using upRuleCharacterise[where Ps=ps and C=c] by auto
       moreover
         {assume "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)"
          with `c = (H \<Rightarrow>* G)` have "\<LM> Modal M Ms \<RM> \<noteq> H" by auto
         }
       moreover
         {assume "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
          then have "\<LM>Modal M Ms \<RM> \<noteq> H" using `c = (H \<Rightarrow>* G)` by auto
         }
       ultimately have "\<LM> Modal M Ms \<RM> \<noteq> H" by blast
      }
      moreover
      {assume "r \<in> modRules2" 
       with `r = (ps,c)` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>) \<or> c = (\<LM> Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
             using modRule2Characterise[where Ps=ps and C=c] by auto
       moreover
         {assume "c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>)"
          then have "\<LM>Modal M Ms \<RM> \<noteq> H" using `c = (H \<Rightarrow>* G)` by auto          
         }
       moreover
         {assume "c = (\<LM>Modal T Ts \<RM> \<Rightarrow>* \<Empt>)"
          then have "leftPrincipal r (Modal T Ts) R'" using `r = (ps,c)` and `r \<in> R`
               proof-
               from `c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)` and `r = (ps,c)` and `r \<in> R` and `r \<in> modRules2`
                    have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R" by auto
               with `R = Ax \<union> R1 \<union> p_e R2 M1 M2 \<union> R3`
                    have "(ps,  \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> p_e R2 M1 M2 \<or>
                          (ps,  \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R3" apply auto apply (rule Ax.cases) apply auto
                    apply (subgoal_tac "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> upRules") apply (insert `R1 \<subseteq> upRules`)
                    apply auto apply (rule upRules.cases) by auto
               moreover
                  {assume "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R3"
                   then have "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" using `R' = Ax \<union> R1 \<union> R2 \<union> R3` by auto
                  }
               moreover
                  {assume "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> p_e R2 M1 M2"
                   then obtain \<Gamma>' \<Delta>' r' where aa: "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<and> r' \<in> R2"
                        apply (rule p_e.cases) by auto
                   then have "r' \<in> modRules2" using `R2 \<subseteq> modRules2` by auto
                   then obtain F Fs where 
                        "snd r' = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> snd r' = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                        using modRule2Characterise[where Ps="fst r'" and C="snd r'"] by auto
                   with aa have "(\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs) \<or>
                                 (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                        by (auto simp add:extendRule_def extend_def)
                   moreover
                      {assume "(\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs)"
                       then have "\<Empt> = M2\<cdot>\<Delta>' \<oplus> Modal F Fs" by auto
                       then have "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" by auto 
                      }
                   moreover
                      {assume "(\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                       then have "M1\<cdot>\<Gamma>' \<oplus> Modal F Fs = \<LM>Modal T Ts\<RM>" and "\<Empt> = M2\<cdot>\<Delta>'" by auto
                       then have "M1\<cdot>\<Gamma>' = \<Empt>" and "Modal T Ts = Modal F Fs" and "M2\<cdot>\<Delta>' = \<Empt>"
                            using 
                            singleton_add_means_equal[where A="Modal T Ts" and \<Gamma>="M1\<cdot>\<Gamma>'" and B="Modal F Fs"]
                            and singleton_add_means_empty[where A="Modal T Ts" and \<Gamma>="M1\<cdot>\<Gamma>'" and B="Modal F Fs"] 
                            by (auto simp add:modaliseMultiset_def)
                       then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' = r'" using extendRuleEmpty[where r=r'] by auto
                       then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<in> R2" using aa by auto
                       then have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R2" using aa by auto
                       then have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" using `R' = Ax\<union>R1 \<union>R2 \<union> R3 ` by simp
                      }
                   ultimately have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" by blast
                  }
              ultimately have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" by auto
              then show ?thesis using `r = (ps,c)` and `c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)` by auto
              qed
          then have "leftPrincipal r (Modal T Ts) R'" using `r = (ps,c)` by auto
          with `\<not> leftPrincipal r (Modal M Ms) R'` have "Modal T Ts \<noteq> Modal M Ms" by auto
          with `c = (H \<Rightarrow>* G)` have "\<LM> Modal M Ms \<RM> \<noteq> H" using `c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)` by auto
         }
       ultimately have "\<LM> Modal M Ms \<RM> \<noteq> H" by blast
      }
      ultimately show ?thesis using `r \<in> upRules \<or> r \<in> modRules2` by blast
      qed
 moreover have "antec S + antec (snd r) = (\<Gamma> \<oplus> Modal M Ms)" 
          using ext and extendRule_def[where forms=S and R=r]
                    and extend_def[where forms=S and seq="snd r"] by auto
 then have "\<Phi> + H = \<Gamma> \<oplus> Modal M Ms" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` and `r = (ps,c)` and `c = (H \<Rightarrow>* G)` by auto
 moreover from `r = (ps,c)` and `r \<in> upRules \<or> r \<in> modRules2` have "(ps,c) \<in> upRules \<or> (ps,c) \<in> modRules2" by auto
 then have "\<exists> A. c = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<or> c = (\<LM>A\<RM> \<Rightarrow>* \<Empt>)"
      using upRuleCharacterise[where Ps=ps and C=c]
        and modRule2Characterise[where Ps=ps and C=c] by auto
 then have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" using `c = (H \<Rightarrow>* G)` by auto
 ultimately have "Modal M Ms :# \<Phi>"
     proof-
     have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" by fact
     moreover
     {assume "H = \<Empt>"
      then have "\<Phi> = \<Gamma> \<oplus> Modal M Ms" using `\<Phi> + H = \<Gamma> \<oplus> Modal M Ms` by auto
      then have "Modal M Ms :# \<Phi>" by auto
     }
     moreover
     {assume "\<exists> A. H = \<LM>A\<RM>"
      then obtain T where "H = \<LM>T\<RM>" by auto
      then have "\<Phi> \<oplus> T = \<Gamma> \<oplus> Modal M Ms" using `\<Phi> + H = \<Gamma> \<oplus> Modal M Ms` by auto
      then have "set_mset (\<Phi> \<oplus> T) = set_mset (\<Gamma> \<oplus> Modal M Ms)" by auto
      then have "set_mset \<Phi> \<union> {T} = set_mset \<Gamma> \<union> {Modal M Ms}" by auto
      moreover from `H = \<LM>T\<RM>` and `\<LM>Modal M Ms\<RM> \<noteq> H` have "Modal M Ms \<noteq> T" by auto
      ultimately have "Modal M Ms \<in> set_mset \<Phi>" by auto
      then have "Modal M Ms :# \<Phi>" by auto
     }
     ultimately show "Modal M Ms :# \<Phi>" by blast
     qed
 then have "\<exists> \<Phi>1. \<Phi> = \<Phi>1 \<oplus> Modal M Ms" 
      by (rule_tac x="\<Phi> \<ominus> Modal M Ms" in exI) (auto simp add:multiset_eq_iff)
 then obtain \<Phi>1 where "S = (\<Phi>1 \<oplus> Modal M Ms \<Rightarrow>* \<Psi>)" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` by auto
 have "Ps = map (extend S) ps" using ext and extendRule_def[where forms=S and R=r] and `r = (ps,c)` by auto
 then have "\<forall> p \<in> set Ps. (\<exists> p'. p = extend S p')" using ex_map_conv[where ys=Ps and f="extend S"] by auto
 then have "\<forall> p \<in> set Ps. (Modal M Ms :# antec p)" 
      using `Modal M Ms :# \<Phi>` and `S = (\<Phi> \<Rightarrow>* \<Psi>)` apply (auto simp add:Ball_def) 
      by (drule_tac x=x in spec) (auto simp add:extend_def)
 then have a1:"\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>')" using characteriseSeq
      apply (auto simp add:Ball_def) apply (drule_tac x=x in spec,simp) 
      apply (rule_tac x="antec x \<ominus> Modal M Ms" in exI,rule_tac x="succ x" in exI) 
      by (drule_tac x=x in meta_spec) (auto simp add:multiset_eq_iff)
 with all have "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>',n) \<in> derivable (ext R R2 M1 M2) \<and> 
                              p = (\<Phi>'\<oplus>Modal M Ms \<Rightarrow>* \<Psi>')"
                  by (auto simp add:Ball_def)
 then have a2: "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' m. m\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',m) \<in> derivable (ext R R2 M1 M2) \<and> 
                  p = (\<Phi>'\<oplus>Modal M Ms \<Rightarrow>* \<Psi>')"
                  using num and b' and IH 
                  apply (auto simp add:Ball_def) apply (drule_tac x=x in spec) apply simp
                  apply hypsubst_thin
                  apply (elim exE conjE) apply (drule_tac x=n in spec) apply simp
                  apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)
                  apply (simp) apply (elim exE conjE) by (rule_tac x=m' in exI) (arith)
 obtain Ps' where eq: "Ps' = map (extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')) ps" by auto
 have "length Ps = length Ps'" using `Ps' = map (extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')) ps`
                               and `Ps = map (extend S) ps` by auto
 then have "Ps' \<noteq> []" using nonempty by auto
 from `r \<in> upRules \<or> r \<in> modRules2` and `r \<in> R` have "extendRule (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') r \<in> (ext R R2 M1 M2)" by auto
 moreover have "extendRule (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') r = (Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')"
          using `S = (\<Phi>1 \<oplus> Modal M Ms \<Rightarrow>* \<Psi>)` and ext and `r = (ps,c)` and eq
          by (auto simp add:extendRule_def extend_def union_ac multiset_eq_iff)
 ultimately have "(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> (ext R R2 M1 M2)" by simp
 have c1:"\<forall> p \<in> set ps. extend S p \<in> set Ps" using `Ps = map (extend S) ps` by (simp add:Ball_def)           
 have c2:"\<forall> p \<in> set ps. extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p \<in> set Ps'" using eq by (simp add:Ball_def)
 then have eq2:"\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq
           apply (auto simp add:Ball_def extend_def) 
           apply (rule_tac x="\<Phi>1 + antec xa" in exI) apply (simp add:union_ac) 
           by (rule_tac x="\<Psi> + succ xa" in exI) (simp add: union_ac)
 have d1:"\<forall> p \<in> set Ps. \<exists> p' \<in> set ps. p = extend S p'" using `Ps = map (extend S) ps` by (auto simp add:Ball_def Bex_def)
 then have "\<forall> p \<in> set Ps. \<exists> p'. p' \<in> set Ps'" using c2 by (auto simp add:Ball_def Bex_def)
 moreover have d2: "\<forall> p \<in> set Ps'. \<exists> p' \<in> set ps. p = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p'" using eq
             by (auto simp add:Ball_def Bex_def)
 then have "\<forall> p \<in> set Ps'. \<exists> p'. p' \<in> set Ps" using c1 by (auto simp add:Ball_def Bex_def)
 have "\<forall> \<Phi>' \<Psi>'. (\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>') \<in> set Ps \<longrightarrow> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"
                proof-
                 {fix \<Phi>' \<Psi>'
                  assume "(\<Phi>' \<oplus> Modal M Ms\<Rightarrow>* \<Psi>') \<in> set Ps"  
                  then have "\<exists> p \<in> set ps. extend (\<Phi>1\<oplus> Modal M Ms \<Rightarrow>* \<Psi>) p = (\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>')"
                       using `Ps = map (extend S) ps` and `S = (\<Phi>1\<oplus> Modal M Ms \<Rightarrow>* \<Psi>)` and a1 and d1
                            apply (simp only:Ball_def Bex_def) apply (drule_tac x=" \<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>'" in spec)
                            by (drule_tac x="\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>'" in spec) (auto)
                  then obtain p where t:"p \<in> set ps \<and> (\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>') = extend (\<Phi>1\<oplus> Modal M Ms \<Rightarrow>* \<Psi>) p"
                       apply auto by (drule_tac x=p in meta_spec) (simp)
                  then obtain D B where "p = (D \<Rightarrow>* B)" by (cases p) 
                  then have "(D \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>') = extend (\<Phi>1\<oplus> Modal M Ms \<Rightarrow>* \<Psi>) (D \<Rightarrow>* B)"
                       using t by auto
                  then have ant: "\<Phi>'\<oplus> Modal M Ms = \<Phi>1\<oplus> Modal M Ms + D" and suc: "\<Psi>' = \<Psi> + B" 
                       using extend_def[where forms="\<Phi>1\<oplus> Modal M Ms \<Rightarrow>* \<Psi>" and seq="D \<Rightarrow>* B"] by auto
                  from suc have "\<Psi>' + \<Delta>' = (\<Psi> + \<Delta>') + B" by (auto simp add:union_ac)
                  moreover
                  from ant have "\<Phi>' = \<Phi>1 + D" by (auto simp add:union_ac multiset_eq_iff)
                  then have "\<Phi>' + \<Gamma>' = (\<Phi>1 + \<Gamma>') + D" by (auto simp add:union_ac)
                  ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (D \<Rightarrow>* B)" 
                       using extend_def[where forms="\<Phi>1+\<Gamma>'\<Rightarrow>*\<Psi>+\<Delta>'" and seq="D\<Rightarrow>*B"] by auto
                  moreover have "extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (D \<Rightarrow>* B) \<in> set Ps'" using `p = (D \<Rightarrow>* B)` and t and c2 by auto
                  ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'" by simp
                  }
                  thus ?thesis by blast
                qed
             moreover
             have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps' \<longrightarrow> (\<Phi>' \<oplus> Modal M Ms \<Rightarrow>* \<Psi>') \<in> set Ps"
                proof-
                  {fix \<Phi>' \<Psi>'
                  assume "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"  
                  then have "\<exists> p \<in> set ps. extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')"
                       using eq and eq2 and d2
                            apply (simp only:Ball_def Bex_def) apply (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec)
                           by (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec) (auto)
                  then obtain p where t:"p \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p"
                       apply auto by (drule_tac x=p in meta_spec) (simp)
                  then obtain D B where "p = (D \<Rightarrow>* B)" by (cases p) 
                  then have "(D \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (D \<Rightarrow>* B)"
                       using t by auto
                  then have ant: "\<Phi>' + \<Gamma>' = \<Phi>1 + \<Gamma>' + D" and suc: "\<Psi>' + \<Delta>' = \<Psi> + \<Delta>' + B" 
                       using extend_def[where forms="\<Phi>1+\<Gamma>'\<Rightarrow>*\<Psi>+\<Delta>'" and seq="D\<Rightarrow>*B"] by auto
                  from suc have "\<Psi>' + \<Delta>' = (\<Psi> + B) + \<Delta>'" by (auto simp add:union_ac)
                  then have "\<Psi>' = \<Psi> + B" by simp
                  moreover
                  from ant have "\<Phi>' + \<Gamma>' = (\<Phi>1 + D) + \<Gamma>'" by (auto simp add:union_ac)
                  then have "\<Phi>' = \<Phi>1 + D" by simp
                  then have "\<Phi>' \<oplus> Modal M Ms = (\<Phi>1 \<oplus> Modal M Ms) + D" by (auto simp add:union_ac)
                  ultimately have "(\<Phi>' \<oplus> Modal M Ms \<Rightarrow>* \<Psi>' ) = extend (\<Phi>1\<oplus> Modal M Ms \<Rightarrow>* \<Psi>) (D \<Rightarrow>* B)" 
                       using extend_def[where forms="\<Phi>1 \<oplus> Modal M Ms\<Rightarrow>*\<Psi>" and seq="D\<Rightarrow>*B"] by auto
                  moreover have "extend (\<Phi>1\<oplus>Modal M Ms  \<Rightarrow>* \<Psi>) (D \<Rightarrow>* B) \<in> set Ps" using `p = (D \<Rightarrow>* B)` and t and c1
                       and `S = (\<Phi>1 \<oplus> Modal M Ms \<Rightarrow>* \<Psi>)` by auto
                  ultimately have "(\<Phi>' \<oplus> Modal M Ms \<Rightarrow>* \<Psi>' ) \<in> set Ps" by simp
                  }
                  thus ?thesis by blast
                qed
 ultimately
 have "\<forall> \<Phi>' \<Psi>'. ((\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>' ) \<in> set Ps) = ((\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps')" by auto
 then have "\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',n) \<in> derivable (ext R R2 M1 M2)
                 \<and> p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq2 and a2
      apply (simp add:Ball_def) apply (intro allI impI) apply (drule_tac x=x in spec) apply simp
      apply (elim exE) apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)  
      by (drule_tac x="\<Phi>'\<oplus> Modal M Ms \<Rightarrow>* \<Psi>' " in spec) (simp)
 then have all:"\<forall> p \<in> set Ps'. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)" by auto
 then show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using num
      and `(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> (ext R R2 M1 M2)` and `Ps' \<noteq> []`
      and derivable.step[where r="(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" and R="(ext R R2 M1 M2)"]
      by (auto simp add:Ball_def Bex_def)
qed


(*>*)
text{*
We have two different inversion lemmata, depending on whether the rule was a modalised context rule, or some other kind of rule.  We only show the former, since the latter is much the same as earlier proofs.  The interesting cases are picked out:
*}
lemma rightInvert:
fixes \<Gamma> \<Delta> :: "('a,'b) form multiset"
assumes rules: "R1 \<subseteq> upRules \<and> R2 \<subseteq> modRules2 \<and> R3 \<subseteq> modRules2 \<and> 
                R = Ax \<union> R1 \<union> (p_e R2 M1 M2) \<union> R3 \<and>
                R' = Ax \<union> R1 \<union> R2 \<union> R3"
    and   a: "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms,n) \<in> derivable (ext R R2 M1 M2)"
    and   b: "\<forall> r' \<in> R'. rightPrincipal r' (Modal M Ms) R' \<longrightarrow> 
                         (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and  neq: "M2 \<noteq> M"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"

(*<*)
using assms
proof (induct n arbitrary: \<Gamma> \<Delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<Delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms, m) \<in> derivable (ext R R2 M1 M2) \<longrightarrow>
              (\<forall>r' \<in> R'. rightPrincipal r' (Modal M Ms) R' \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable (ext R R2 M1 M2))" 
     and a': "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms,n) \<in> derivable (ext R R2 M1 M2)" 
     and b': "\<forall> r' \<in> R'. rightPrincipal r' (Modal M Ms) R' \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms,0) \<in> derivable (ext R R2 M1 M2)" using a' by simp
     then have "([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms) \<in> ext R R2 M1 M2" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms) \<and> (r \<in> Ax)"
          using rules apply- apply (rule ext.cases [where 'a = 'a and 'b = 'b]) apply (auto simp add:extendRule_def extend_def)
          apply (rule_tac x=b in exI) apply (rule_tac x=seq in exI) apply auto apply (rule upRules.cases) apply auto
          apply (rule upRules.cases) apply auto apply (rule upRules.cases) apply auto
          apply (insert p_e_non_empty[where R=R2 and M=M1 and N=M2])
          apply (rule Ax.cases) apply auto apply (drule_tac x="[]" in meta_spec) 
          apply (drule_tac x="\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>" in meta_spec) apply auto
          apply (drule_tac x="[]" in meta_spec) apply (drule_tac x="\<LM>ff\<RM> \<Rightarrow>* \<Empt>" in meta_spec) apply auto
          apply (drule_tac x=a in meta_spec) apply (drule_tac x=b in meta_spec) apply (auto simp add:extendConc_def)
          apply (drule_tac x="[]" in meta_spec) apply (drule_tac x=b in meta_spec) apply auto
          apply (subgoal_tac "([],b) \<in> modRules2") by (rule modRules2.cases,auto)+
     then obtain r S where "extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)" and "r \<in> Ax" by auto
     then obtain i xs where "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = r \<or> r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" 
          using characteriseAx[where r=r] by auto
     moreover 
         {assume "r = ([],\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)"
          with `extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)`
               have "extend S (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
               using extendRule_def[where R="([],\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)" and forms=S] by auto
          then have "At i :# \<Gamma> \<and> At i :# \<Delta>" 
               using extendID[where S=S and i=i and \<Gamma>=\<Gamma> and \<Delta>="\<Delta> \<oplus> Modal M Ms"] by auto
          then have "At i :# \<Gamma> + \<Gamma>' \<and> At i :# \<Delta> + \<Delta>'" by auto
          then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M1 M2)" using rules
               and containID[where \<Gamma>="\<Gamma> + \<Gamma>'" and i=i and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
         }
     moreover
         {assume "r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
          with `extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)`
             have "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
             using extendRule_def[where R="([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and forms=S] by auto
          then have "ff :# \<Gamma>" 
               using extendFalsum[where S=S and \<Gamma>=\<Gamma> and \<Delta>="\<Delta> \<oplus> Modal M Ms"] by auto
          then have "ff :# \<Gamma> + \<Gamma>'" by auto
          then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M1 M2)" using rules
               and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
         }
     ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M1 M2)" by blast
     then show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using `n=0` by auto
 next
     case (Suc n')
     then have "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms,n'+1) \<in> derivable (ext R R2 M1 M2)" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms) \<in> (ext R R2 M1 M2)" and 
                          "Ps \<noteq> []" and 
                       d':"\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)"
          using characteriseLast[where C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms" and m=n' and R="ext R R2 M1 M2"] by auto
     then have "\<exists> r S. (((r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)) \<or>
                       (r \<in> p_e R2 M1 M2 \<and> extendConc S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms))) \<and> r\<in>R" by (cases) auto
     then obtain r S where ext: "((r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms))
                                \<or> (r \<in> p_e R2 M1 M2 \<and> extendConc S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms))" and "r \<in> R" by auto
     moreover
        {assume ext1: "(r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
         with `Ps \<noteq> []` have "r \<in> upRules \<or> r \<in> modRules2" and "extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)" 
               apply auto apply (cases r) 
               by (rule Ax.cases) (auto simp add:extendRule_def)
         moreover
            {assume "r \<in> upRules"
             with `r \<in> R` have "r \<in> R1" using rules [[hypsubst_thin=true]]
                  apply auto apply (insert disjoint) apply auto
                  apply (insert upRuleCharacterise) apply (rotate_tac 10) apply (drule_tac x="fst r" in meta_spec)
                  apply (rotate_tac 10) apply (drule_tac x="snd r" in meta_spec) apply simp
                  apply (elim exE) 
                  apply (insert modRule1Characterise[where Ps="fst r" and C="snd r" and R=R2 and M=M1 and N=M2])
                  apply (auto simp add:extendRule_def extend_def)
                  apply (insert singleton_add_means_equal) apply (rotate_tac 10)
                  apply (drule_tac x="Compound F Fs" in meta_spec) apply (rotate_tac 13)
                  apply (drule_tac x="M2\<cdot>\<Delta> "in meta_spec) apply (rotate_tac 13)
                  apply (drule_tac x="Modal Fa Fsa" in meta_spec) apply auto
                  apply (rotate_tac 13) apply (drule_tac x="Compound F Fs" in meta_spec) apply (rotate_tac 13)
                  apply (drule_tac x="M1\<cdot>\<Gamma>" in meta_spec) apply (rotate_tac 13)
                  apply (drule_tac x="Modal Fa Fsa" in meta_spec) by auto
             with rules have "r \<in> R'" by auto
             obtain ps c where "r = (ps,c)" by (cases r) auto
             with `r \<in> upRules` obtain T Ts where sw:"c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> 
                                                   c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
                  using upRuleCharacterise[where Ps=ps and C=c] by auto
             have "(rightPrincipal r (Modal M Ms) R') \<or> \<not>(rightPrincipal r (Modal M Ms) R')" by blast
             moreover
                {assume "rightPrincipal r (Modal M Ms) R'"
                 then have "c = (\<Empt> \<Rightarrow>* \<LM>Modal M Ms\<RM>)" using `r = (ps,c)` by (cases) auto
                 with sw and `r \<in> R'` have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
                      by auto
                }
             moreover
                {assume "\<not> rightPrincipal r (Modal M Ms) R'"
                 then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using IH and a' b' d' `Ps \<noteq> []`
                      and nonPrincipalInvertRight[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and n=n
                                                  and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and M=M and Ms=Ms and r=r and S=S
                                                  and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and n'=n' and Ps=Ps and ps=ps 
                                                  and c=c and R'=R' and ?M1.0=M1 and ?M2.0=M2]
                      and `n = Suc n'` and ext1 and rules and `r = (ps,c)` and `r \<in> R` by auto
                }
             ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by blast
            }
         moreover
(*>*)

txt{* \noindent This is the case where the last inference was a normal modal inference: *}

  {assume "r \<in> modRules2"
   obtain ps c where "r = (ps,c)" by (cases r) auto
   with `r \<in> modRules2` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>) \<or> 
            c = (\<LM> Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
            using modRule2Characterise[where Ps=ps and C=c] by auto
   moreover
     {assume "c = (\<Empt> \<Rightarrow>* \<LM> Modal T Ts \<RM>)"
      then have bb: "rightPrincipal r (Modal T Ts) R'" using `r = (ps,c)` and `r \<in> R`
      proof-  
txt{* \noindent We need to know $r \in R$ so that we can extend the active part*}
    from `c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)` and 
           `r = (ps,c)` and 
           `r \<in> R` and 
           `r \<in> modRules2`
        have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R" by auto
    with rules have "(ps,  \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> p_e R2 M1 M2 \<or>
         (ps,  \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R3" (*<*)apply auto apply (rule Ax.cases) apply auto
                 apply (subgoal_tac "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> upRules")
                                apply auto apply (rule upRules.cases)(*>*) by auto
   moreover
      {assume "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R3"
        then have "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" using rules by auto
       }
   moreover
      {assume "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> p_e R2 M1 M2"

txt{* \noindent In this case, we show that $\Delta'$ and $\Gamma'$ must be empty.  The details are generally suppressed: *}
  then obtain \<Gamma>' \<Delta>' r' 
  where aa: "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' 
            \<and> r' \<in> R2"(*<*)apply (rule p_e.cases)(*>*) by auto
  (*<*) then have "r' \<in> modRules2" using rules by auto
                              then obtain F Fs where 
                                   "snd r' = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> snd r' = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                                   using modRule2Characterise[where Ps="fst r'" and C="snd r'"] by auto
                              with aa have "(\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs) \<or>
                                            (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                                   by (auto simp add:extendRule_def extend_def)
                              moreover
                                 {assume "(\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs)"
                                  then have "M1\<cdot>\<Gamma>' = \<Empt>" and "\<LM>Modal T Ts\<RM> = M2\<cdot>\<Delta>' \<oplus> Modal F Fs" by auto(*>*) 
     then have "M1\<cdot>\<Gamma>' = \<Empt>" (*<*)and "Modal T Ts = Modal F Fs"(*>*) and "M2\<cdot>\<Delta>' = \<Empt>"
     (*<*)    using 
                                       singleton_add_means_equal[where A="Modal T Ts" and \<Gamma>="M2\<cdot>\<Delta>'" and B="Modal F Fs"]
                                       and singleton_add_means_empty[where A="Modal T Ts" and \<Gamma>="M2\<cdot>\<Delta>'" and B="Modal F Fs"] (*>*) by (auto simp add:modaliseMultiset_def)
                      (*<*)            then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' = r'" using extendRuleEmpty[where r=r'] by auto
     
   then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<in> R2" using aa by auto
                                  then have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R2" using aa by auto
                                  then have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" using rules by simp
                                 }
                              moreover
                                 {assume "(\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                                  then have "\<Empt> = M1\<cdot>\<Gamma>' \<oplus> Modal F Fs" by auto
                                  then have "(ps, \<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" by auto
                                 }
                              ultimately have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" by blast
                             }
                         ultimately have "(ps,\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>) \<in> R'" by auto
                         then show ?thesis using `r = (ps,c)` and `c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)` by auto
                         qed
                    have "Modal T Ts = Modal M Ms \<or> Modal T Ts \<noteq> Modal M Ms" by blast
                    moreover
                       {assume "Modal T Ts = Modal M Ms"
                        with bb have "rightPrincipal r (Modal M Ms) R'" by auto
                        with b' have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r)" apply- by (rule rightPrincipal.cases) auto
                        moreover from `r = (ps,c)` and `c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)` and `Modal T Ts = Modal M Ms`
                                 and `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)`
                                 have "S = (\<Gamma> \<Rightarrow>* \<Delta>)" apply (auto simp add:extendRule_def extend_def) by (cases S) auto
                        ultimately have "(\<Gamma>+\<Gamma>' \<Rightarrow>* \<Delta>+\<Delta>') \<in> set Ps" 
                             using extendContain[where r=r and ps=ps and c=c and Ps=Ps 
                                               and C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms" and S="\<Gamma> \<Rightarrow>* \<Delta>" and p="\<Gamma>'\<Rightarrow>*\<Delta>'"]
                             and `r = (ps,c)` and `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)` by (auto simp add:extend_def)
                        with d' have "\<exists> n\<le>n'. (\<Gamma>+\<Gamma>' \<Rightarrow>* \<Delta>+\<Delta>',n) \<in> derivable (ext R R2 M1 M2)" by auto
                        with `n = Suc n'` have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)"
                             apply auto apply (rule_tac x=n in exI) by arith
                       }
                    moreover
                       {assume "Modal T Ts \<noteq> Modal M Ms"
                        with bb have "\<not> rightPrincipal r (Modal M Ms) R'" apply auto apply (rule rightPrincipal.cases)
                             apply auto apply (rotate_tac 1) apply (rule rightPrincipal.cases) apply auto
                             apply (rule rightPrincipal.cases) apply auto apply (rotate_tac 1)
                             by (rule rightPrincipal.cases) auto
                        then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using IH and a' b' d' `Ps \<noteq> []`
                             and nonPrincipalInvertRight[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and n=n
                                                  and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and M=M and Ms=Ms and r=r and S=S
                                                  and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and n'=n' and Ps=Ps and ps=ps 
                                                  and c=c and R'=R' and ?M1.0=M1 and ?M2.0=M2]
                             and `n = Suc n'` and ext1 and rules and `r = (ps,c)` and `r \<in> R` by auto
                       }
                    ultimately have " \<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by blast
                   }
                moreover
                   {assume "c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
                    with `r = (ps,c)` have "\<not> rightPrincipal r (Modal M Ms) R'"
                         apply auto by (rule rightPrincipal.cases) auto
                    then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using IH and a' b' d' `Ps \<noteq> []`
                         and nonPrincipalInvertRight[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and n=n
                                                  and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and M=M and Ms=Ms and r=r and S=S
                                                  and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and n'=n' and Ps=Ps and ps=ps 
                                                  and c=c and R'=R' and ?M1.0=M1 and ?M2.0=M2]
                         and `n = Suc n'` and ext1 and rules and `r = (ps,c)` and `r \<in> R` by auto
                   }
                ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by blast
               }
            ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by blast
           }
       moreover(*>*)
txt{* \noindent  The other interesting case is where the last inference was a modalised context inference: *}

 {assume ba: "r \<in> p_e R2 M1 M2 \<and> 
         extendConc S r = (Ps,  \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
  with rules obtain F Fs \<Gamma>'' \<Delta>'' ps r' where
       ca: "r = extendRule (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'') r'" and 
       cb: "r' \<in> R2" and
     cc:  "r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
  (*<*)using modRule1Characterise[where Ps="fst r" and C="snd r" and M=M1 and N=M2 and R=R2] by auto
  obtain \<Gamma>1 \<Delta>1 where "S = (\<Gamma>1 \<Rightarrow>* \<Delta>1)" by (cases S) auto
  moreover
    {assume "r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>)"
     with ba ca `S = (\<Gamma>1 \<Rightarrow>* \<Delta>1)` have
   eq1: "(M1\<cdot>\<Gamma>'' + \<Gamma>1 \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1 \<oplus> Modal F Fs) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
            by (auto simp add:extendRule_def extend_def extendConc_def union_ac)
     (*<*)         then have eq2: "M2\<cdot>\<Delta>'' + \<Delta>1 \<oplus> Modal F Fs = \<Delta> \<oplus> Modal M Ms" by auto
                then have "set_mset (M2 \<cdot> \<Delta>'' + \<Delta>1 \<oplus> Modal F Fs) = set_mset (\<Delta> \<oplus> Modal M Ms)" by auto
                then have "set_mset (\<LM>Modal M Ms\<RM>) \<subseteq> set_mset (M2 \<cdot> \<Delta>'') \<union> set_mset \<Delta>1 \<union>  {Modal F Fs}" by auto (*>*)
  then have "Modal M Ms \<in> set_mset (M2\<cdot>\<Delta>'') \<or> 
             Modal M Ms \<in> set_mset \<Delta>1 \<or> 
             Modal M Ms = Modal F Fs"
       by auto
  moreover
     {assume "Modal M Ms \<in> set_mset (M2\<cdot>\<Delta>'')" -- "Contradiction"
     then have "Modal M Ms :# M2\<cdot>\<Delta>''" by auto
     with (*<*)modal_not_contain[where M=M and N=M2 and A=Ms and \<Gamma>=\<Delta>''] and(*>*) neq
       have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" 
       by auto
    }
 moreover
   {assume "Modal M Ms = Modal F Fs" -- "The last inference is principal"
   then have "r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal M Ms\<RM>)" 
        using `r' = (ps,\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>)` by simp
   with cb and rules have "rightPrincipal r' (Modal M Ms) R'" 
        and "r' \<in> R'" by auto
   with b have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using `r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal M Ms\<RM>)`
       by (auto simp add:Ball_def)
  (*<*)    then have "extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'') (\<Gamma>' \<Rightarrow>* \<Delta>') 
                               \<in> set (map (extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'')) ps)" by auto
                    moreover from ba and `r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal M Ms\<RM>)` and ca
                         have "Ps = map (extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'')) ps"
                         by (auto simp add:extendRule_def extendConc_def)
                    moreover have "extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'') (\<Gamma>' \<Rightarrow>* \<Delta>') = (M1\<cdot>\<Gamma>'' + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>')" 
                         by (auto simp add:extend_def) 
                    ultimately have "(M1\<cdot>\<Gamma>'' + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>') \<in> set Ps" by auto
                    with d' have "\<exists> m\<le>n'. (M1\<cdot>\<Gamma>'' + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by auto
                    then have "\<exists> m\<le>n'. (M1\<cdot>\<Gamma>'' + \<Gamma>' + \<Gamma>1 \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>' + \<Delta>1,m) \<in> derivable (ext R R2 M1 M2)"
                         using dpWeak[where \<Gamma>="M1\<cdot>\<Gamma>'' + \<Gamma>'" and \<Delta>="M2\<cdot>\<Delta>'' + \<Delta>'" and R=R and ?R2.0=R2
                                      and M=M1 and N=M2 and ?R1.0=R1 and ?R3.0=R3 and \<Gamma>'=\<Gamma>1 and \<Delta>'=\<Delta>1] 
                         and rules by auto
                    with `n = Suc n'` 
                         have ee: "\<exists> m\<le>n. (M1\<cdot>\<Gamma>'' + \<Gamma>' + \<Gamma>1 \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>' + \<Delta>1,m) \<in> derivable (ext R R2 M1 M2)"
                         apply auto apply (rule_tac x=m in exI) by arith
                    from eq1 have "M1\<cdot>\<Gamma>'' + \<Gamma>1 = \<Gamma>" by auto
                    then have "M1\<cdot>\<Gamma>'' + \<Gamma>' + \<Gamma>1 = \<Gamma> + \<Gamma>'" by (auto simp add:union_ac)
                    moreover from eq2 and `Modal M Ms = Modal F Fs` have "M2\<cdot>\<Delta>'' + \<Delta>1 = \<Delta>" 
                         using add_equal_means_equal[where \<Gamma>=" M2 \<cdot> \<Delta>'' + \<Delta>1" and \<Delta>=\<Delta> and A="Modal F Fs"]
                         by (auto simp add:union_ac)
                    then have "M2\<cdot>\<Delta>'' + \<Delta>' + \<Delta>1 = \<Delta> + \<Delta>'" by (auto simp add:union_ac) (*>*)
  ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta>+\<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
   (*<*) using ee(*>*) by auto
  }
moreover
  {assume "Modal M Ms \<in> set_mset \<Delta>1" -- "Formula is in the implicit weakening"
 (*<*)  then have "Modal M Ms :# \<Delta>1" by auto
  then have "\<exists> \<Delta>2. \<Delta>1 = \<Delta>2 \<oplus> Modal M Ms" using insert_DiffM[where x="Modal M Ms" and M="\<Delta>1"]
                         apply auto apply (rule_tac x="\<Delta>1\<ominus>Modal M Ms" in exI) by (auto simp add:union_ac)(*>*)
  then obtain \<Delta>2 where "\<Delta>1 = \<Delta>2 \<oplus> Modal M Ms" by blast (*>*)
  from ba and rules 
       have "extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r \<in> (ext R R2 M1 M2)" by auto
  moreover from ba and ca have "fst (extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r) = Ps"
           by (auto simp add:extendConc_def)
 (*<*)        ultimately have "(snd (extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r),n'+1) \<in> derivable (ext R R2 M1 M2)"
                         using d' and derivable.step[where r="extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r"
                                                     and R="ext R R2 M1 M2" and m=n'] and `Ps \<noteq> []` by auto
                    moreover from ca and `r' = (ps,\<Empt> \<Rightarrow>* \<LM>Modal F Fs \<RM>)` 
                         have "snd (extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r) = (M1\<cdot>\<Gamma>'' + (\<Gamma>1 + \<Gamma>') \<Rightarrow>* (M2\<cdot>\<Delta>'' \<oplus> Modal F Fs) + \<Delta>2 + \<Delta>')"
                         by (auto simp add:extendRule_def extendConc_def extend_def union_ac)
                    ultimately have gg: "(M1\<cdot>\<Gamma>'' + \<Gamma>1 + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>2 + \<Delta>' \<oplus> Modal F Fs,n'+1) \<in> derivable (ext R R2 M1 M2)"
                         by (auto simp add:union_ac)
                    from eq1 have "M1\<cdot>\<Gamma>'' + \<Gamma>1 = \<Gamma>" by auto
                    then have "(M1\<cdot>\<Gamma>'' + \<Gamma>1 + \<Gamma>') = \<Gamma> + \<Gamma>'" by auto
                    moreover from eq2 and `\<Delta>1 = \<Delta>2 \<oplus> Modal M Ms`
                         have "M2\<cdot>\<Delta>'' + \<Delta>2 \<oplus> Modal F Fs \<oplus> Modal M Ms = \<Delta> \<oplus> Modal M Ms" by (auto simp add:union_ac)
                    then have "M2\<cdot>\<Delta>'' + \<Delta>2 \<oplus> Modal F Fs = \<Delta>" 
                         using add_equal_means_equal[where \<Gamma>=" M2 \<cdot> \<Delta>'' + \<Delta>2 \<oplus> Modal F Fs" and \<Delta>=\<Delta> and A="Modal M Ms"]
                         by (auto simp add:union_ac)
                    then have "M2\<cdot>\<Delta>'' + \<Delta>2 + \<Delta>' \<oplus> Modal F Fs = \<Delta> + \<Delta>'" by (auto simp add:union_ac) (*>*) 
 ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable (ext R R2 M1 M2)" (*<*)using gg(*>*)   
           
           by auto
  then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" 
           using `n = Suc n'` by auto
 }
ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" 
           by blast
(*<*)  }(*>*)
txt{* \noindent The other case, where the last inference was a left inference, is more straightforward, and so is omitted. *}
 (*<*)
            moreover
               {assume "r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                with ba ca `S = (\<Gamma>1 \<Rightarrow>* \<Delta>1)` have
                     eq1: "(M1\<cdot>\<Gamma>'' + \<Gamma>1 \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Modal M Ms)"
                     by (auto simp add:extendRule_def extend_def extendConc_def union_ac)
                then have eq2: "M2\<cdot>\<Delta>'' + \<Delta>1 = \<Delta> \<oplus> Modal M Ms" by auto
                then have "set_mset (M2 \<cdot> \<Delta>'' + \<Delta>1) = set_mset (\<Delta> \<oplus> Modal M Ms)" by auto
                then have "set_mset (\<LM>Modal M Ms\<RM>) \<subseteq> set_mset (M2 \<cdot> \<Delta>'') \<union> set_mset \<Delta>1" by auto
                then have "Modal M Ms \<in> set_mset (M2\<cdot>\<Delta>'') \<or> Modal M Ms \<in> set_mset \<Delta>1"
                     by auto
                moreover
                   {assume "Modal M Ms \<in> set_mset (M2\<cdot>\<Delta>'')"
                    then have "Modal M Ms :# M2\<cdot>\<Delta>''" by auto
                    with modal_not_contain[where M=M and N=M2 and A=Ms and \<Gamma>=\<Delta>''] and neq
                         have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by auto
                   }
                moreover
                   {assume "Modal M Ms \<in> set_mset \<Delta>1"
                    then have "Modal M Ms :# \<Delta>1" by auto
                    then have "\<exists> \<Delta>2. \<Delta>1 = \<Delta>2 \<oplus> Modal M Ms" using insert_DiffM[where x="Modal M Ms" and M="\<Delta>1"]
                         apply auto apply (rule_tac x="\<Delta>1\<ominus>Modal M Ms" in exI) by (auto simp add:union_ac)
                    then obtain \<Delta>2 where "\<Delta>1 = \<Delta>2 \<oplus> Modal M Ms" by blast
                    from ba and rules have "extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r \<in> (ext R R2 M1 M2)" by auto
                    moreover from ba and ca have "fst (extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r) = Ps"
                         by (auto simp add:extendConc_def)
                    ultimately have "(snd (extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r),n'+1) \<in> derivable (ext R R2 M1 M2)"
                         using d' and derivable.step[where r="extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r"
                                                     and R="ext R R2 M1 M2" and m=n'] and `Ps \<noteq> []` by auto
                    moreover from ca and `r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)` 
                         have "snd (extendConc (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<Delta>2 + \<Delta>') r) = ((M1\<cdot>\<Gamma>'' \<oplus> Modal F Fs)+ \<Gamma>1 + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>2 + \<Delta>')"
                         by (auto simp add:extendRule_def extendConc_def extend_def union_ac)
                    ultimately have gg: "(M1\<cdot>\<Gamma>'' + \<Gamma>1 + \<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>2 + \<Delta>',n'+1) \<in> derivable (ext R R2 M1 M2)"
                         by (auto simp add:union_ac)
                    from eq1 have "M1\<cdot>\<Gamma>'' + \<Gamma>1 \<oplus> Modal F Fs  = \<Gamma>" by auto
                    then have "(M1\<cdot>\<Gamma>'' + \<Gamma>1 + \<Gamma>') \<oplus> Modal F Fs = \<Gamma> + \<Gamma>'" by (auto simp add:union_ac)
                    moreover from eq2 and `\<Delta>1 = \<Delta>2 \<oplus> Modal M Ms`
                         have "M2\<cdot>\<Delta>'' + \<Delta>2 \<oplus> Modal M Ms = \<Delta> \<oplus> Modal M Ms" by (auto simp add:union_ac)
                    then have "M2\<cdot>\<Delta>'' + \<Delta>2 = \<Delta>" 
                         using add_equal_means_equal[where \<Gamma>=" M2 \<cdot> \<Delta>'' + \<Delta>2" and \<Delta>=\<Delta> and A="Modal M Ms"]
                         by (auto simp add:union_ac)
                    then have "M2\<cdot>\<Delta>'' + \<Delta>2 + \<Delta>'  = \<Delta> + \<Delta>'" by (auto simp add:union_ac)
                    ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable (ext R R2 M1 M2)" using gg by (auto simp add:union_ac)
                    then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using `n = Suc n'`
                         by auto
                   }
                ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by blast
               }
           ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" using cc by blast
          }   
      ultimately show "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by auto
   qed
qed
       
                     

lemma leftInvert:
fixes \<Gamma> \<Delta> :: "('a,'b) form multiset"
assumes rules: "R1 \<subseteq> upRules \<and> R2 \<subseteq> modRules2 \<and> R3 \<subseteq> modRules2 \<and> R = Ax \<union> R1 \<union> p_e R2 M1 M2 \<union> R3 \<and> R' = Ax \<union> R1 \<union> R2 \<union> R3"
    and   a: "(\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>,n) \<in> derivable (ext R R2 M1 M2)"
    and   b: "\<forall> r' \<in> R'. leftPrincipal r' (Modal M Ms) R' \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and neq: "M1 \<noteq> M"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
using assms
proof (induct n arbitrary: \<Gamma> \<Delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<Delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>, m) \<in> derivable (ext R R2 M1 M2) \<longrightarrow>
              (\<forall>r' \<in> R'. leftPrincipal r' (Modal M Ms) R' \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable (ext R R2 M1 M2))" 
     and a': "(\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>,n) \<in> derivable (ext R R2 M1 M2)" 
     and b': "\<forall> r' \<in> R'. leftPrincipal r' (Modal M Ms) R' \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>,0) \<in> derivable (ext R R2 M1 M2)" using a' by simp
     then have "([],\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>) \<in> (ext R R2 M1 M2)" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>) \<and> (r \<in> Ax)"
          using rules apply- apply (rule ext.cases [where 'a = 'a and 'b = 'b]) apply (auto simp add:extendRule_def extend_def)
          apply (rule_tac x=b in exI) apply (rule_tac x=seq in exI) apply auto apply (rule upRules.cases) apply auto
          apply (rule upRules.cases) apply auto apply (rule upRules.cases) apply auto
          apply (insert p_e_non_empty[where R=R2 and M=M1 and N=M2])
          apply (rule Ax.cases) apply auto apply (drule_tac x="[]" in meta_spec) 
          apply (drule_tac x="\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>" in meta_spec) apply auto
          apply (drule_tac x="[]" in meta_spec) apply (drule_tac x="\<LM>ff\<RM> \<Rightarrow>* \<Empt>" in meta_spec) apply auto
          apply (drule_tac x=a in meta_spec) apply (drule_tac x=b in meta_spec) apply (auto simp add:extendConc_def)
          apply (drule_tac x="[]" in meta_spec) apply (drule_tac x=b in meta_spec) apply auto
          apply (subgoal_tac "([],b) \<in> modRules2") by (rule modRules2.cases,auto)+
     then obtain r S where "extendRule S r = ([],\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)" and "r \<in> Ax" by auto
     then obtain i xs where "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = r \<or> r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" 
          using characteriseAx[where r=r] by auto
     moreover 
         {assume "r = ([],\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)"
          with `extendRule S r = ([],\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)`
               have "extend S (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)"
               using extendRule_def[where R="([],\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)" and forms=S] by auto
          then have "At i :# \<Gamma> \<and> At i :# \<Delta>" 
               using extendID[where S=S and i=i and \<Gamma>="\<Gamma>\<oplus> Modal M Ms" and \<Delta>=\<Delta>] by auto
          then have "At i :# \<Gamma> + \<Gamma>' \<and> At i :# \<Delta> + \<Delta>'" by auto
          then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M1 M2)" using rules
               and containID[where \<Gamma>="\<Gamma> + \<Gamma>'" and i=i and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
         }
     moreover
         {assume "r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
          with `extendRule S r = ([],\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)`
             have "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)"
             using extendRule_def[where R="([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and forms=S] by auto
          then have "ff :# \<Gamma>" 
               using extendFalsum[where S=S and \<Gamma>="\<Gamma>\<oplus>Modal M Ms" and \<Delta>=\<Delta>] by auto
          then have "ff :# \<Gamma> + \<Gamma>'" by auto
          then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M1 M2)" using rules
               and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
         }
     ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable (ext R R2 M1 M2)" by blast
     then show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using `n=0` by auto
 next
     case (Suc n')
     then have "(\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>,n'+1) \<in> derivable (ext R R2 M1 M2)" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>) \<in> (ext R R2 M1 M2)" and 
                          "Ps \<noteq> []" and 
                       d':"\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)"
          using characteriseLast[where C="\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>" and m=n' and R="(ext R R2 M1 M2)"] by auto
     then have "\<exists> r S. (((r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)) \<or>
                       (r \<in> p_e R2 M1 M2 \<and> extendConc S r = (Ps,\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>))) \<and> r\<in>R" by (cases) auto
     then obtain r S where ext: "((r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>))
                                \<or> (r \<in> p_e R2 M1 M2 \<and> extendConc S r = (Ps,\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>))" and "r \<in> R" by auto
     moreover
        {assume ext1: "(r \<in> Ax \<or> r \<in> upRules \<or> r \<in> modRules2) \<and> extendRule S r = (Ps, \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)"
         with `Ps \<noteq> []` have "r \<in> upRules \<or> r \<in> modRules2" and "extendRule S r = (Ps,\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)" 
               apply auto apply (cases r) 
               by (rule Ax.cases) (auto simp add:extendRule_def)
         moreover
            {assume "r \<in> upRules"
             then obtain ps c where "r = (ps,c)" by (cases r) auto
             with `r \<in> upRules` obtain T Ts where sw:"c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> 
                                                   c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
                  using upRuleCharacterise[where Ps=ps and C=c] by auto
             have "(leftPrincipal r (Modal M Ms) R') \<or> \<not>(leftPrincipal r (Modal M Ms) R')" by blast
             moreover
                {assume "leftPrincipal r (Modal M Ms) R'"
                 then have "c = (\<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)" using `r = (ps,c)` by (cases) auto
                 with sw and `r \<in> upRules` and disjoint have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
                      by auto
                }
             moreover
                {assume "\<not> leftPrincipal r (Modal M Ms) R'"
                 then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using IH and a' b' d' `Ps \<noteq> []`
                      and nonPrincipalInvertLeft[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and n=n
                                                  and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and M=M and Ms=Ms and r=r and S=S
                                                  and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and n'=n' and Ps=Ps and ps=ps 
                                                  and c=c and R'=R' and ?M1.0=M1 and ?M2.0=M2]
                      and `n = Suc n'` and ext1 and rules and `r = (ps,c)` and `r \<in> R` by auto
                }
             ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by blast
            }
         moreover
            {assume "r \<in> modRules2"
             then obtain ps c where "r = (ps,c)" by (cases r) auto
             with `r \<in> modRules2` obtain T Ts where sw: "c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)
                                                         \<or> c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
                  using modRule2Characterise[where Ps=ps and C=c] by auto
             have "leftPrincipal r (Modal M Ms) R' \<or> \<not> leftPrincipal r (Modal M Ms) R'" by blast
             moreover
                {assume "leftPrincipal r (Modal M Ms) R'"
                 then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using b' and `r = (ps,c)` and `r \<in> R`
                      apply- apply (rule leftPrincipal.cases) by auto
                 then have ex:"extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" using `extendRule S r = (Ps,\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)`
                      and `r = (ps,c)` by (simp add:extendContain)
                 moreover
                    {assume "c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)"
                     then have bb: "leftPrincipal r (Modal T Ts) R'" using `r = (ps,c)` and `r \<in> R`
                       proof-
                          from `c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)` and `r = (ps,c)` and `r \<in> R` and `r \<in> modRules2`
                          have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R" by auto
                          with rules
                          have "(ps,  \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> p_e R2 M1 M2 \<or>
                                (ps,  \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R3" apply auto apply (rule Ax.cases) apply auto
                                apply (subgoal_tac "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> upRules")
                                apply auto apply (rule upRules.cases) by auto
                          moreover
                             {assume "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R3"
                              then have "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" using rules by auto
                             }
                          moreover
                             {assume "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> p_e R2 M1 M2"
                              then obtain \<Gamma>' \<Delta>' r' 
                                   where aa: "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<and> r' \<in> R2"
                                   apply (rule p_e.cases) by auto
                              then have "r' \<in> modRules2" using rules by auto
                              then obtain F Fs where 
                                   "snd r' = (\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> snd r' = (\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                                   using modRule2Characterise[where Ps="fst r'" and C="snd r'"] by auto
                              with aa have "(\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs) \<or>
                                            (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                                   by (auto simp add:extendRule_def extend_def)
                              moreover
                                 {assume "(\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>' \<oplus> Modal F Fs)"
                                  then have "\<Empt> = M2\<cdot>\<Delta>' \<oplus> Modal F Fs" by auto
                                  then have "(ps, \<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" by auto
                                 }
                              moreover
                                 {assume "(\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) = (M1\<cdot>\<Gamma>' \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>')"
                                  then have "M2\<cdot>\<Delta>' = \<Empt>" and "\<LM>Modal T Ts\<RM> = M1\<cdot>\<Gamma>' \<oplus> Modal F Fs" by auto
                                  then have "M1\<cdot>\<Gamma>' = \<Empt>" and "Modal T Ts = Modal F Fs" and "M2\<cdot>\<Delta>' = \<Empt>"
                                       using 
                                       singleton_add_means_equal[where A="Modal T Ts" and \<Gamma>="M1\<cdot>\<Gamma>'" and B="Modal F Fs"]
                                       and singleton_add_means_empty[where A="Modal T Ts" and \<Gamma>="M1\<cdot>\<Gamma>'" and B="Modal F Fs"] 
                                       by (auto simp add:modaliseMultiset_def)
                                  then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' = r'" using extendRuleEmpty[where r=r'] by auto
                                  then have "extendRule (M1\<cdot>\<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>') r' \<in> R2" using aa by auto
                                  then have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R2" using aa by auto
                                  then have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" using rules by simp
                                 }
                              ultimately have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" by blast
                             }
                         ultimately have "(ps,\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>) \<in> R'" by auto
                         then show ?thesis using `r = (ps,c)` and `c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)` by auto
                         qed
                     then have "Modal T Ts = Modal M Ms" using `leftPrincipal r (Modal M Ms) R'` apply auto
                          apply (rule leftPrincipal.cases) apply auto apply (rotate_tac 1) apply (rule leftPrincipal.cases)
                          apply auto apply (rule leftPrincipal.cases) apply auto apply (rotate_tac 1)
                          apply (rule leftPrincipal.cases) by auto
                     then have "c = (\<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)" using `c = (\<LM>Modal T Ts\<RM> \<Rightarrow>* \<Empt>)` by auto
                    }
                    moreover
                    {assume "c = (\<Empt> \<Rightarrow>* \<LM>Modal T Ts\<RM>)"
                     then have "\<not> leftPrincipal r (Modal M Ms) R'" using `r = (ps,c)` apply auto
                          by (rule leftPrincipal.cases) (auto simp add:extendRule_def extend_def)
                     with `leftPrincipal r (Modal M Ms) R'` have "c = (\<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)" by simp
                    }
                 ultimately have "c = (\<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)" using sw by blast
                 with `extendRule S r = (Ps,\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)` have "S = (\<Gamma> \<Rightarrow>* \<Delta>)"
                      using `r = (ps,c)` apply (auto simp add:extendRule_def extend_def) by (cases S) auto
                 with ex have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
                 then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
                      using `\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable (ext R R2 M1 M2)` by auto
                 then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using `n = Suc n'`
                      by (auto,rule_tac x=m in exI) (simp)
                }
             moreover
                {assume "\<not> leftPrincipal r (Modal M Ms) R'"
                 then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using IH and a' b' d' `Ps \<noteq> []`
                      and nonPrincipalInvertLeft[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and n=n
                                                  and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and M=M and Ms=Ms and r=r and S=S
                                                  and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and n'=n' and Ps=Ps and ps=ps 
                                                  and c=c and R'=R' and ?M1.0=M1 and ?M2.0=M2]
                      and `n = Suc n'` and ext1 and rules and `r = (ps,c)` and `r \<in> R` by auto
                }
             ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by blast
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by blast
        }
     moreover
        {assume ba: "r \<in> p_e R2 M1 M2 \<and> extendConc S r = (Ps,  \<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)"
           with rules obtain F Fs \<Gamma>'' \<Delta>'' ps r' where
                ca: "r = extendRule (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'') r'" and 
                cb: "r' \<in> R2" and
                cc:  "r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>) \<or> r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                using modRule1Characterise[where Ps="fst r" and C="snd r" and M=M1 and N=M2 and R=R2] by auto
            obtain \<Gamma>1 \<Delta>1 where "S = (\<Gamma>1 \<Rightarrow>* \<Delta>1)" by (cases S) auto
            moreover
               {assume "r' = (ps, \<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>)"
                with ba ca `S = (\<Gamma>1 \<Rightarrow>* \<Delta>1)` have
                     eq1: "(M1\<cdot>\<Gamma>'' + \<Gamma>1  \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1 \<oplus> Modal F Fs) = (\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)"
                     by (auto simp add:extendRule_def extend_def extendConc_def union_ac)
                then have eq2: "M1\<cdot>\<Gamma>'' + \<Gamma>1 = \<Gamma> \<oplus> Modal M Ms" by auto
                then have "set_mset (M1 \<cdot> \<Gamma>'' + \<Gamma>1) = set_mset (\<Gamma> \<oplus> Modal M Ms)" by auto
                then have "set_mset (\<LM>Modal M Ms\<RM>) \<subseteq> set_mset (M1 \<cdot> \<Gamma>'') \<union> set_mset \<Gamma>1" by auto
                then have "Modal M Ms \<in> set_mset (M1\<cdot>\<Gamma>'') \<or> Modal M Ms \<in> set_mset \<Gamma>1"
                     by auto
                moreover
                   {assume "Modal M Ms \<in> set_mset (M1\<cdot>\<Gamma>'')"
                    then have "Modal M Ms :# M1\<cdot>\<Gamma>''" by auto
                    with modal_not_contain[where M=M and N=M1 and A=Ms and \<Gamma>=\<Gamma>''] and neq
                         have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by auto
                   }
                moreover
                   {assume "Modal M Ms \<in> set_mset \<Gamma>1"
                    then have "Modal M Ms :# \<Gamma>1" by auto
                    then have "\<exists> \<Gamma>2. \<Gamma>1 = \<Gamma>2 \<oplus> Modal M Ms" using insert_DiffM[where x="Modal M Ms" and M="\<Gamma>1"]
                         apply auto apply (rule_tac x="\<Gamma>1\<ominus>Modal M Ms" in exI) by (auto simp add:union_ac)
                    then obtain \<Gamma>2 where "\<Gamma>1 = \<Gamma>2 \<oplus> Modal M Ms" by blast
                    from ba and rules have "extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r \<in> (ext R R2 M1 M2)" by auto
                    moreover from ba and ca have "fst (extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r) = Ps"
                         by (auto simp add:extendConc_def)
                    ultimately have "(snd (extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r),n'+1) \<in> derivable (ext R R2 M1 M2)"
                         using d' and derivable.step[where r="extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r"
                                                     and R="ext R R2 M1 M2" and m=n'] and `Ps \<noteq> []` by auto
                    moreover from ca and `r' = (ps,\<Empt> \<Rightarrow>* \<LM>Modal F Fs\<RM>)` 
                         have "snd (extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r) = (M1\<cdot>\<Gamma>''+ \<Gamma>2 + \<Gamma>' \<Rightarrow>* (M2\<cdot>\<Delta>'' \<oplus> Modal F Fs)+ \<Delta>1 + \<Delta>')"
                         by (auto simp add:extendRule_def extendConc_def extend_def union_ac)
                    ultimately have gg: "(M1\<cdot>\<Gamma>'' + \<Gamma>2 + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1 + \<Delta>' \<oplus> Modal F Fs,n'+1) \<in> derivable (ext R R2 M1 M2)"
                         by (auto simp add:union_ac)
                    from eq1 have "M2\<cdot>\<Delta>'' + \<Delta>1 \<oplus> Modal F Fs  = \<Delta>" by auto
                    then have "(M2\<cdot>\<Delta>'' + \<Delta>1 + \<Delta>') \<oplus> Modal F Fs = \<Delta> + \<Delta>'" by (auto simp add:union_ac)
                    moreover from eq2 and `\<Gamma>1 = \<Gamma>2 \<oplus> Modal M Ms`
                         have "M1\<cdot>\<Gamma>'' + \<Gamma>2 \<oplus> Modal M Ms = \<Gamma> \<oplus> Modal M Ms" by (auto simp add:union_ac)
                    then have "M1\<cdot>\<Gamma>'' + \<Gamma>2 = \<Gamma>" 
                         using add_equal_means_equal[where \<Gamma>=" M1 \<cdot> \<Gamma>'' + \<Gamma>2" and \<Delta>=\<Gamma> and A="Modal M Ms"]
                         by (auto simp add:union_ac)
                    then have "M1\<cdot>\<Gamma>'' + \<Gamma>2 + \<Gamma>'  = \<Gamma> + \<Gamma>'" by (auto simp add:union_ac)
                    ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable (ext R R2 M1 M2)" using gg by (auto simp add:union_ac)
                    then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using `n = Suc n'`
                         by auto
                   }
                ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by blast
               }
            moreover
               {assume "r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)"
                with ba ca `S = (\<Gamma>1 \<Rightarrow>* \<Delta>1)` have
                     eq1: "(M1\<cdot>\<Gamma>'' + \<Gamma>1 \<oplus> Modal F Fs \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1) = (\<Gamma> \<oplus> Modal M Ms \<Rightarrow>* \<Delta>)"
                     by (auto simp add:extendRule_def extend_def extendConc_def union_ac)
                then have eq2: "M1\<cdot>\<Gamma>'' + \<Gamma>1 \<oplus> Modal F Fs = \<Gamma> \<oplus> Modal M Ms" by auto
                then have "set_mset (M1 \<cdot> \<Gamma>'' + \<Gamma>1 \<oplus> Modal F Fs) = set_mset (\<Gamma> \<oplus> Modal M Ms)" by auto
                then have "set_mset (\<LM>Modal M Ms\<RM>) \<subseteq> set_mset (M1\<cdot> \<Gamma>'') \<union> set_mset \<Gamma>1 \<union>  {Modal F Fs}" by auto
                then have "Modal M Ms \<in> set_mset (M1\<cdot>\<Gamma>'') \<or> Modal M Ms \<in> set_mset \<Gamma>1 \<or> Modal M Ms = Modal F Fs"
                     by auto
                moreover
                   {assume "Modal M Ms \<in> set_mset (M1\<cdot>\<Gamma>'')"
                    then have "Modal M Ms :# M1\<cdot>\<Gamma>''" by auto
                    with modal_not_contain[where M=M and N=M1 and A=Ms and \<Gamma>=\<Gamma>''] and neq
                         have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by auto
                   }
                moreover
                   {assume "Modal M Ms = Modal F Fs"
                    then have "r' = (ps, \<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)" using `r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)` by simp
                    with cb and rules have "leftPrincipal r' (Modal M Ms) R'" and "r' \<in> R'" by auto
                    with b have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using `r' = (ps, \<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)`
                         by (auto simp add:Ball_def)
                    then have "extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'') (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (map (extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'')) ps)" by auto
                    moreover from ba and `r' = (ps, \<LM>Modal M Ms\<RM> \<Rightarrow>* \<Empt>)` and ca
                         have "Ps = map (extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'')) ps"
                         by (auto simp add:extendRule_def extendConc_def)
                    moreover have "extend (M1\<cdot>\<Gamma>'' \<Rightarrow>* M2\<cdot>\<Delta>'') (\<Gamma>' \<Rightarrow>* \<Delta>') = (M1\<cdot>\<Gamma>'' + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>')" 
                         by (auto simp add:extend_def) 
                    ultimately have "(M1\<cdot>\<Gamma>'' + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>') \<in> set Ps" by auto
                    with d' have "\<exists> m\<le>n'. (M1\<cdot>\<Gamma>'' + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by auto
                    then have "\<exists> m\<le>n'. (M1\<cdot>\<Gamma>'' + \<Gamma>' + \<Gamma>1 \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>' + \<Delta>1,m) \<in> derivable (ext R R2 M1 M2)"
                         using dpWeak[where \<Gamma>="M1\<cdot>\<Gamma>'' + \<Gamma>'" and \<Delta>="M2\<cdot>\<Delta>'' + \<Delta>'" and R=R and ?R2.0=R2
                                      and M=M1 and N=M2 and ?R1.0=R1 and ?R3.0=R3 and \<Gamma>'=\<Gamma>1 and \<Delta>'=\<Delta>1] 
                         and rules by auto
                    with `n = Suc n'` 
                         have ee: "\<exists> m\<le>n. (M1\<cdot>\<Gamma>'' + \<Gamma>' + \<Gamma>1 \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>' + \<Delta>1,m) \<in> derivable (ext R R2 M1 M2)"
                         apply auto apply (rule_tac x=m in exI) by arith
                    from eq1 have "M2\<cdot>\<Delta>'' + \<Delta>1 = \<Delta>" by auto
                    then have "M2\<cdot>\<Delta>'' + \<Delta>' + \<Delta>1 = \<Delta> + \<Delta>'" by (auto simp add:union_ac)
                    moreover from eq2 and `Modal M Ms = Modal F Fs` have "M1\<cdot>\<Gamma>'' + \<Gamma>1 = \<Gamma>" 
                         using add_equal_means_equal[where \<Gamma>=" M1 \<cdot> \<Gamma>'' + \<Gamma>1" and \<Delta>=\<Gamma> and A="Modal F Fs"]
                         by (auto simp add:union_ac)
                    then have "M1\<cdot>\<Gamma>'' + \<Gamma>' + \<Gamma>1 = \<Gamma> + \<Gamma>'" by (auto simp add:union_ac)
                    ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta>+\<Delta>',m) \<in> derivable (ext R R2 M1 M2)"
                         using ee by auto
                   }
                moreover
                   {assume "Modal M Ms \<in> set_mset \<Gamma>1"
                    then have "Modal M Ms :# \<Gamma>1" by auto
                    then have "\<exists> \<Gamma>2. \<Gamma>1 = \<Gamma>2 \<oplus> Modal M Ms" using insert_DiffM[where x="Modal M Ms" and M="\<Gamma>1"]
                         apply auto apply (rule_tac x="\<Gamma>1\<ominus>Modal M Ms" in exI) by (auto simp add:union_ac)
                    then obtain \<Gamma>2 where "\<Gamma>1 = \<Gamma>2 \<oplus> Modal M Ms" by blast
                    from ba and rules have "extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r \<in> (ext R R2 M1 M2)" by auto
                    moreover from ba and ca have "fst (extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r) = Ps"
                         by (auto simp add:extendConc_def)
                    ultimately have "(snd (extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r),n'+1) \<in> derivable (ext R R2 M1 M2)"
                         using d' and derivable.step[where r="extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r"
                                                     and R="ext R R2 M1 M2" and m=n'] and `Ps \<noteq> []` by auto
                    moreover from ca and `r' = (ps,\<LM>Modal F Fs\<RM> \<Rightarrow>* \<Empt>)` 
                         have "snd (extendConc (\<Gamma>2 + \<Gamma>' \<Rightarrow>* \<Delta>1 + \<Delta>') r) = ((M1\<cdot>\<Gamma>'' \<oplus> Modal F Fs )+ \<Gamma>2 + \<Gamma>' \<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1 + \<Delta>')"
                         by (auto simp add:extendRule_def extendConc_def extend_def union_ac)
                    ultimately have gg: "(M1\<cdot>\<Gamma>'' + \<Gamma>2 + \<Gamma>' \<oplus> Modal F Fs\<Rightarrow>* M2\<cdot>\<Delta>'' + \<Delta>1 + \<Delta>',n'+1) \<in> derivable (ext R R2 M1 M2)"
                         by (auto simp add:union_ac)
                    from eq1 have "M2\<cdot>\<Delta>'' + \<Delta>1 = \<Delta>" by auto
                    then have "(M2\<cdot>\<Delta>'' + \<Delta>1 + \<Delta>') = \<Delta> + \<Delta>'" by auto
                    moreover from eq2 and `\<Gamma>1 = \<Gamma>2 \<oplus> Modal M Ms`
                         have "M1\<cdot>\<Gamma>'' + \<Gamma>2 \<oplus> Modal F Fs \<oplus> Modal M Ms = \<Gamma> \<oplus> Modal M Ms" by (auto simp add:union_ac)
                    then have "M1\<cdot>\<Gamma>'' + \<Gamma>2 \<oplus> Modal F Fs = \<Gamma>" 
                         using add_equal_means_equal[where \<Gamma>=" M1\<cdot>\<Gamma>'' + \<Gamma>2 \<oplus> Modal F Fs" and \<Delta>=\<Gamma> and A="Modal M Ms"]
                         by (auto simp add:union_ac)
                    then have "M1\<cdot>\<Gamma>'' + \<Gamma>2 + \<Gamma>' \<oplus> Modal F Fs = \<Gamma> + \<Gamma>'" by (auto simp add:union_ac)
                    ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable (ext R R2 M1 M2)" using gg by auto
                    then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" using `n = Suc n'`
                         by auto
                   }
                ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" by blast
               }
           ultimately have "\<exists>m\<le>n. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable (ext R R2 M1 M2)" using cc by blast
           }
      ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable (ext R R2 M1 M2)" by blast
   qed
qed



datatype C = con
datatype BD = BOX ("\<box>")| DIAMOND ("\<diamond>")

type_synonym CDBD_form = "(C,BD) form"

abbreviation con_form (infixl "\<and>*" 80) where
   "p \<and>* (q :: CDBD_form) \<equiv> Compound con [p,q]"

abbreviation BOX_form ( "\<box> _" [80]80) where
   "\<box> (p:: CDBD_form)  \<equiv> Modal \<box> [p]"

abbreviation DIAMOND_form ("\<diamond> _" [80]80) where
   "\<diamond> (p :: CDBD_form) \<equiv> Modal \<diamond> [p]"

inductive_set "g3up"
where
    conL[intro]: "([\<LM> A \<RM> + \<LM> B \<RM> \<Rightarrow>* \<Empt>], \<LM> A \<and>* B \<RM> \<Rightarrow>* \<Empt>) \<in> g3up"
|   conR[intro]: "([\<Empt> \<Rightarrow>* \<LM> A \<RM>, \<Empt> \<Rightarrow>* \<LM> B \<RM>], \<Empt> \<Rightarrow>* \<LM> A \<and>* B \<RM>) \<in> g3up"

(*>*)
text{*

We guarantee no other rule has the same modal operator in the succedent of a modalised context rule using the condition $M \neq M_{2}$.  Note this lemma only allows one kind of modalised context rule.  In other words, it could not be applied to a calculus with the rules:

\[
\begin{array}{ccc}
\infer[R_{1}]{\Gamma',!\cdot\Gamma \Rightarrow \bullet A,\bullet\cdot\Delta,\Delta'}{!\cdot\Gamma \Rightarrow A,\bullet\cdot\Delta} & \ \ \ &
\infer[R_{2}]{\Gamma',\bullet\cdot\Gamma \Rightarrow \bullet A,!\cdot\Delta,\Delta'}{\bullet\cdot\Gamma \Rightarrow A,!\cdot\Delta}
\end{array}
\]
since, if $([\emptyset \Rightarrow A],\emptyset \Rightarrow \bullet A) \in \mathcal{R}$, then $R_{1} \in \textrm{p-e } \mathcal{R}\ !\ \bullet$, whereas $R_{2} \in \textrm{p-e } \mathcal{R}\ \bullet\ !$.  Similarly, we cannot have modalised context rules which have more than one modalised multiset in the antecedent or succedent of the active part.  For instance:

\[
\infer{\Gamma',!\cdot\Gamma_{1},\bullet\cdot\Gamma_{2} \Rightarrow \bullet A,!\cdot\Delta_{1},\bullet\cdot\Delta_{2},\Delta'}{!\cdot\Gamma_{1},\bullet\cdot\Gamma_{2} \Rightarrow A,!\cdot\Delta_{1},\bullet\cdot\Delta_{2}}
\]
cannot belong to any \texttt{p-e} set.  It would be a simple matter to extend the definition of \texttt{p-e} to take a \textit{set} of modal operators, however this has not been done. 

As an example, classical modal logic can be formalised.
The (modal) rules for this calculus are then given in two sets, the latter of which will be extended with $\Box\cdot\Gamma \Rightarrow \Diamond\cdot\Delta$:
*}
inductive_set "g3mod2" 
where
    diaR(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* \<LM> A \<RM>], \<Empt> \<Rightarrow>* \<LM> \<diamond> A \<RM>) \<in> g3mod2"
|   boxL(*<*)[intro](*>*): "([\<LM> A \<RM> \<Rightarrow>* \<Empt>], \<LM> \<box> A \<RM> \<Rightarrow>* \<Empt>) \<in> g3mod2"

inductive_set "g3mod1"
where
    boxR(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* \<LM>A\<RM>],\<Empt> \<Rightarrow>* \<LM> \<box> A \<RM>) \<in> g3mod1"
|   diaL(*<*)[intro](*>*): "([\<LM>A\<RM> \<Rightarrow>* \<Empt>],\<LM> \<diamond> A \<RM> \<Rightarrow>* \<Empt>) \<in> g3mod1"

(*<*)
lemma g3up_upRules:
shows "g3up \<subseteq> upRules"
proof-
{
 fix ps c
 assume "(ps,c) \<in> g3up"
 then have "(ps,c) \<in> upRules" by (induct) auto
}
thus "g3up \<subseteq> upRules" by auto
qed

lemma g3mod2_modRules2:
shows "g3mod2 \<subseteq> modRules2"
proof-
{
 fix ps c
 assume "(ps,c) \<in> g3mod2"
 then have "(ps,c) \<in> modRules2" by (induct) auto
}
thus "g3mod2 \<subseteq> modRules2" by auto
qed

lemma g3mod1_modRules2:
shows "g3mod1 \<subseteq> modRules2"
proof-
{
 fix ps c
 assume "(ps,c) \<in> g3mod1"
 then have "(ps,c) \<in> modRules2" by (induct) auto
}
thus "g3mod1 \<subseteq> modRules2" by auto
qed



lemmas g3 = g3up_upRules g3mod1_modRules2 g3mod2_modRules2




lemma principal_Ax:
shows "\<lbrakk> r \<in> Ax ; rightPrincipal r (\<box> A) R \<rbrakk> \<Longrightarrow> (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)"
by (auto simp add:nonPrincipalID)

lemma principal_g3up:
shows "\<lbrakk> r \<in> g3up ; rightPrincipal r (\<box> A) R \<rbrakk> \<Longrightarrow> (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)"
apply (subgoal_tac "r \<in> upRules") apply (auto simp add:upRules_not_right_principal_for_modal)
apply (insert g3up_upRules) by auto


lemma principal_g3mod2:
assumes "r \<in> g3mod2"
and "R = Ax \<union> g3up \<union> g3mod1 \<union> g3mod2"
and "rightPrincipal r (\<box> A) R"
shows "(\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)"
proof-
 from `r \<in> g3mod2` have "\<exists> A. r = ([\<LM>A\<RM> \<Rightarrow>* \<Empt>], \<LM>\<box> A\<RM> \<Rightarrow>* \<Empt>) \<or>
                              r = ([\<Empt> \<Rightarrow>* \<LM>A\<RM>], \<Empt> \<Rightarrow>* \<LM>\<diamond> A\<RM>)" 
      apply (cases r) by (rule g3mod2.cases) auto
 then obtain B where  "r = ([\<LM>B\<RM> \<Rightarrow>* \<Empt>], \<LM>\<box> B\<RM> \<Rightarrow>* \<Empt>) \<or>
                       r = ([\<Empt> \<Rightarrow>* \<LM>B\<RM>], \<Empt> \<Rightarrow>* \<LM>\<diamond> B\<RM>)" by blast
 then have "\<not> rightPrincipal r (\<box> A) R" using `R = Ax \<union> g3up \<union> g3mod1 \<union> g3mod2`
      apply auto apply (rule rightPrincipal.cases) apply (auto simp add:extendRule_def extend_def)
      apply (rule rightPrincipal.cases) by (auto simp add:extendRule_def extend_def)
 with `rightPrincipal r (\<box> A) R` show ?thesis by auto
qed

lemma principal_g3mod1:
assumes "r \<in> g3mod1"
and "R = Ax \<union> g3up \<union> g3mod1 \<union> g3mod2"
and "rightPrincipal r (\<box> A) R"
shows "(\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)"
proof-
 from `r \<in> g3mod1` have "\<exists> A. r = ([\<LM>A\<RM> \<Rightarrow>* \<Empt>], \<LM>\<diamond> A\<RM> \<Rightarrow>* \<Empt>) \<or>
                              r = ([\<Empt> \<Rightarrow>* \<LM>A\<RM>], \<Empt> \<Rightarrow>* \<LM>\<box> A\<RM>)" 
      apply (cases r) by (rule g3mod1.cases) auto
 then obtain B where  "r = ([\<LM>B\<RM> \<Rightarrow>* \<Empt>], \<LM>\<diamond> B\<RM> \<Rightarrow>* \<Empt>) \<or>
                       r = ([\<Empt> \<Rightarrow>* \<LM>B\<RM>], \<Empt> \<Rightarrow>* \<LM>\<box> B\<RM>)" by blast
 moreover
    {assume "r = ([\<LM>B\<RM> \<Rightarrow>* \<Empt>], \<LM>\<diamond> B\<RM> \<Rightarrow>* \<Empt>)"
     then have "\<not> rightPrincipal r (\<box> A) R" using `R = Ax \<union> g3up \<union> g3mod1 \<union> g3mod2`
          apply auto apply (rule rightPrincipal.cases) by (auto simp add:extendRule_def extend_def)
     with `rightPrincipal r (\<box> A) R` have "(\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)" by auto
    }
 moreover
    {assume "r = ([\<Empt> \<Rightarrow>* \<LM>B\<RM>], \<Empt> \<Rightarrow>* \<LM>\<box> B\<RM>)"
     then have "rightPrincipal r (\<box> B) R" using `r \<in> g3mod1` and `R = Ax \<union> g3up \<union> g3mod1 \<union> g3mod2` by auto
     with `rightPrincipal r (\<box> A) R` have "A = B" apply-
          apply (rule rightPrincipal.cases) apply auto apply (rotate_tac 1) 
          by (rule rightPrincipal.cases) auto
     with `r = ([\<Empt> \<Rightarrow>* \<LM>B\<RM>], \<Empt> \<Rightarrow>* \<LM>\<box> B\<RM>)` have "(\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)" by auto
    }
 ultimately show ?thesis by auto
qed  

lemma principal:
assumes "R' = Ax \<union> g3up \<union> g3mod1 \<union> g3mod2"
shows "\<forall> r \<in> R'. rightPrincipal r (\<box> A) R' \<longrightarrow> (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<in> set (fst r)"
using assms apply auto
apply (insert principal_Ax)[1] apply (drule_tac x="(a,b)" in meta_spec) apply auto
apply (insert principal_g3up)[1] apply (drule_tac x="(a,b)" in meta_spec) apply auto
apply (insert principal_g3mod1)[1] apply (drule_tac x="(a,b)" in meta_spec) apply auto
apply (insert principal_g3mod2) apply (drule_tac x="(a,b)" in meta_spec) by auto
(*>*)
text{*
\noindent We then show the strong admissibility of the rule:

\[
\infer{\Gamma \Rightarrow A,\Delta}{\Gamma \Rightarrow \Box A,\Delta}
\]

*}
lemma invertBoxR:
assumes "R = Ax \<union> g3up \<union> (p_e g3mod1 \<box> \<diamond>) \<union> g3mod2"
and     "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> (\<box> A),n) \<in> derivable (ext R g3mod1 \<box> \<diamond>)"
shows   "\<exists> m\<le>n. (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> A,m) \<in> derivable (ext R g3mod1 \<box> \<diamond>)"
proof-
 from assms show ?thesis
 using principal(*<*)[where R'="Ax \<union> g3up \<union> g3mod1 \<union> g3mod2" and A=A] (*>*)
 and rightInvert(*<*)[where ?R1.0="g3up" and ?R2.0="g3mod1" and ?R3.0="g3mod2" and R=R and ?M1.0=\<box> and ?M2.0=\<diamond>
                       and M=\<box> and Ms="[A]" and n=n and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and \<Gamma>'="\<Empt>" and \<Delta>'="\<LM>A\<RM>"
                       and R'="Ax \<union> g3up \<union> g3mod1 \<union> g3mod2"](*>*)
 and g3 by auto
qed

text{* \noindent where \textit{principal} is the result which fulfils the principal formula conditions given in the inversion lemma, and \textit{g3} is a result about rule sets.*}
(*<*) 
end
(*>*)
