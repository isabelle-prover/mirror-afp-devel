(*<*)
(* Author : Peter Chapman *)
(* License: LGPL *)
section "First Order Sequents" 
theory NominalSequents
imports "~~/src/HOL/Library/Multiset" Nominal
begin

atom_decl var

(*>*)
text{*
\section{First-Order Calculi \label{isafirstorder}}
To formalise first-order results we use the package \textit{Nominal Isabelle}.  The details, for the most part, are the same as in \S\ref{isadefs}.  However, we lose one important feature: that of polymorphism.

Recall we defined formulae as being indexed by a type of connectives.  We could then give abbreviations for these indexed formulae.  Unfortunately this feature (indexing by types) is not yet supported in \textit{Nominal Isabelle}.  Nested datatypes are also not supported.  Thus, strings are used for the connectives (both propositional and first-order) and lists of formulae are simulated to nest via a mutually recursive definition:

*}

nominal_datatype form = At "nat" "var list" 
                                  | Cpd0 "string" "form_list"
                                  | Cpd1 "string" "\<guillemotleft>var\<guillemotright>form" ("_ (\<nabla> [_]._)" (*<*)[100,100,100]100(*>*))
                                  | ff
and form_list = FNil
                   | FCons "form" "form_list"

(*<*)
abbreviation multiset_abbrev ("\<LM> _  \<RM>" [75]75) where
   "\<LM> A \<RM> \<equiv> {# A #}"

abbreviation multiset_empty ("\<Empt>" 75) where
  "\<Empt> \<equiv> {#}"

datatype sequent = Sequent "form multiset" "form multiset" (" (_) \<Rightarrow>* (_)" [6,6] 5)


(* We have that any step in a rule, be it a primitive rule or an instance of a rule in a derivation
   can be represented as a list of premisses and a conclusion.  We need a list since a list is finite
   by definition *)
type_synonym rule = "sequent list * sequent"

type_synonym deriv = "sequent * nat"

abbreviation
multiset_plus (infixl "\<oplus>" 80) where
   "(\<Gamma> :: form multiset) \<oplus> (A :: form) \<equiv> \<Gamma> + \<LM>A\<RM>"
abbreviation
multiset_minus (infixl "\<ominus>" 80) where
   "(\<Gamma> :: form multiset) \<ominus>  (A :: form) \<equiv> \<Gamma> - \<LM>A\<RM>" 

consts
  (* extend a sequent by adding another one.  A form of weakening.  Is this overkill by adding a sequent? *)
  extend :: "sequent \<Rightarrow> sequent \<Rightarrow> sequent"
  extendRule :: "sequent \<Rightarrow> rule \<Rightarrow> rule"

  (* Unique conclusion Property *)
  uniqueConclusion :: "rule set \<Rightarrow> bool"

  (* functions to get at components of sequents *)
primrec antec :: "sequent \<Rightarrow> form multiset" where "antec (Sequent ant suc) = ant"
primrec succ :: "sequent \<Rightarrow> form multiset" where "succ (Sequent ant suc) = suc"
primrec mset :: "sequent \<Rightarrow> form multiset" where "mset (Sequent ant suc) = ant + suc"
primrec seq_size :: "sequent \<Rightarrow> nat" where "seq_size (Sequent ant suc) = size ant + size suc"
primrec set_of_seq :: "sequent \<Rightarrow> form set" where "set_of_seq (Sequent ant suc) = set_mset (mset (Sequent ant suc))"
primrec set_of_prem :: "sequent list \<Rightarrow> form set" where
  "set_of_prem Nil = {}"
| "set_of_prem (p # ps) = set_of_seq p \<union> set_of_prem ps"

(* Extend a sequent, and then a rule by adding seq to all premisses and the conclusion *)
overloading
  extend \<equiv> extend
  extendRule \<equiv> extendRule
  uniqueConclusion \<equiv> uniqueConclusion
begin

definition extend
  where "extend forms seq \<equiv> (antec forms + antec seq) \<Rightarrow>* (succ forms + succ seq)"

definition extendRule
  where "extendRule forms R \<equiv> (map (extend forms) (fst R), extend forms (snd R))"

(* The unique conclusion property.  A set of rules has unique conclusion property if for any pair of rules,
   the conclusions being the same means the rules are the same*)
definition uniqueConclusion :: "rule set \<Rightarrow> bool"
  where "uniqueConclusion R \<equiv> \<forall> r1 \<in> R. \<forall> r2 \<in> R. (snd r1 = snd r2) \<longrightarrow> (r1 =r2)"

end

primrec sequentMinus :: "sequent \<Rightarrow> form \<Rightarrow> sequent" ("_ - _" [100,100]100) where
  "(\<Gamma> \<Rightarrow>* \<Delta>) - A = (\<Gamma> \<ominus> A \<Rightarrow>* \<Delta> \<ominus> A)"

primrec listMinus :: "sequent list \<Rightarrow> form \<Rightarrow> sequent list" (" _ - _ " [100,100]100) where
  "[] - A = []"
| "(P # Ps) - A = (P - A) # (Ps - A)"


(* The formulation of various rule sets *)

(* idRules is the set containing all identity RULES *)
inductive_set "Ax" where
   id[intro]: "([], \<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) \<in> Ax"
|  LBot[intro]: "([], \<LM>ff\<RM> \<Rightarrow>* \<Empt>) \<in> Ax"

(* upRules is the set of all rules which have a single conclusion.  This is akin to each rule having a 
   single principal formula.  We don't want rules to have no premisses, hence the restriction
   that ps \<noteq> [] *)
inductive_set "upRules" where
   I[intro]: "\<lbrakk> mset c \<equiv> \<LM> Cpd0 R Fs \<RM> ; ps \<noteq> [] \<rbrakk> \<Longrightarrow> (ps,c) \<in> upRules"
(*>*)

text{*
\noindent Formulae are quantified over a single variable at a time.  This is a restriction imposed by \textit{Nominal Isabelle}.  

There are two new \SC rule sets in addition to the propositional rule set: first-order rules without a freshness proviso and first-order rules with a freshness proviso.  Freshness provisos are particularly easy to encode in \textit{Nominal Isabelle}.  We also show that the rules with a freshness proviso form a subset of the first-order rules.  The function \texttt{set-of-prem} takes a list of premisses, and returns all the formulae in that list:
*}

(* provRules is the set of rules where we have a freshness proviso *)
inductive_set "provRules" where
  (*<*) I[intro]:(*>*) "\<lbrakk> mset c = \<LM> F \<nabla> [x].A \<RM> ; ps \<noteq> [] ; x \<sharp> set_of_prem (ps - A)\<rbrakk>
                      \<Longrightarrow> (ps,c) \<in> provRules"

(* nprovRules is the set of rules where we do not have a freshness proviso, but we have
   a first order formula *)
inductive_set "nprovRules" where
   (*<*)I[intro]:(*>*) "\<lbrakk> mset c = \<LM> F \<nabla> [x].A \<RM> ; ps \<noteq> [] \<rbrakk>
                   \<Longrightarrow> (ps,c) \<in> nprovRules"

(* provRules are a subset of nprovRules *)
lemma nprovContain:
shows "provRules \<subseteq> nprovRules"
proof-
{fix ps c
 assume "(ps,c) \<in> provRules"
 then have "(ps,c) \<in> nprovRules" by (cases) auto
}
then show ?thesis by auto
qed
(*<*)
primrec subst :: "var \<Rightarrow> var \<Rightarrow> var list \<Rightarrow> var list" ("[_;_]_" [100,100,100] 100) where
  Empt:"[z;y][] = []"
| NEmpt:"[z;y](x#ys) = (if x=y then (z#([z;y]ys)) else (x#([z;y]ys)))"

lemma subst_var_list_eqvt[eqvt]:
  fixes pi::"var prm"
  and   y::"var list"
  shows "pi\<bullet>([z;x]y) = [(pi\<bullet>z);(pi\<bullet>x)](pi\<bullet>y)"
by (induct y) (auto simp add: eqvts)
(*>*)

text{*
\noindent Substitution is defined in the usual way: *}

nominal_primrec 
    subst_form  :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> form" ("[_,_]_"(*<*) [100,100,100] 100(*>*))
and subst_forms :: "var \<Rightarrow> var \<Rightarrow> form_list \<Rightarrow> form_list" ("[_,_]_"(*<*) [100,100,100] 100(*>*))
where
   "[z,y](At P xs) = At P ([z;y]xs)"
|  "x\<sharp>(z,y) \<Longrightarrow> [z,y](F \<nabla> [x].A) = F \<nabla> [x].([z,y]A)"
|  "[z,y](Cpd0 F Fs) = Cpd0 F ([z,y]Fs)"
|  "[z,y]ff = ff"
|  "[z,y]FNil = FNil"
|  "[z,y](FCons f Fs) = FCons ([z,y]f) ([z,y]Fs)"
(*<*)
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess add: fresh_string)+
done
(*>*)

text{* \noindent Substitution is extended to multisets in the obvious way.

To formalise the condition ``no specific substitutions'', an inductive predicate is introduced.  If some formula in the multiset $\Gamma$ is a non-trivial substitution, then \texttt{multSubst} $\Gamma$:
*}

definition multSubst :: "form multiset \<Rightarrow> bool" where
multSubst_def: "multSubst \<Gamma> \<equiv> (\<exists> A \<in> (set_mset \<Gamma>). \<exists> x y B. [y,x]B = A \<and> y\<noteq>x)"

text{* 
\noindent The notation $[z;y]xs$ stands for substitution of a variable in a variable list.  The details are simple, and so are not shown.

Extending the rule sets with passive parts depends upon which kind of active part is being extended.  The active parts with freshness contexts have additional constraints upon the multisets which are added:
*}

(* We need to be careful now about how to extend a rule, since we have binding *)
inductive_set extRules :: "rule set \<Rightarrow> rule set"   (" _*" )
   for R :: "rule set"
   where
  id(*<*)[intro](*>*):   "\<lbrakk> r \<in> R ; r \<in> Ax \<rbrakk> \<Longrightarrow> extendRule S r \<in> R*"
| sc(*<*)[intro](*>*):   "\<lbrakk> r \<in> R ; r \<in> upRules \<rbrakk> \<Longrightarrow> extendRule S r \<in> R*"
| np(*<*)[intro](*>*):   "\<lbrakk> r \<in> R ; r \<in> nprovRules \<rbrakk> \<Longrightarrow> extendRule S r \<in> R*"
| p(*<*)[intro](*>*):     "\<lbrakk> (ps,c) \<in> R ; (ps,c) \<in> provRules ; mset c = \<LM> F \<nabla> [x].A \<RM> ; x \<sharp> set_of_seq S \<rbrakk>
                          \<Longrightarrow> extendRule S (ps,c) \<in> R*"

(*<*)
(* A formulation of what it means to be a principal formula for a rule.  Note that we have to build up from
   single conclusion rules.   *)

inductive leftPrincipal :: "rule \<Rightarrow> form \<Rightarrow> bool"
  where
  sc[intro]: "\<lbrakk> C = (\<LM>A\<RM> \<Rightarrow>* \<Empt>) ; A \<noteq> ff \<rbrakk>  \<Longrightarrow> 
                   leftPrincipal (Ps,C) A"


inductive rightPrincipal :: "rule \<Rightarrow> form \<Rightarrow> bool"
  where
  sc[intro]: "C = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<Longrightarrow> rightPrincipal (Ps,C) A"


(* What it means to be a derivable sequent.  Can have this as a predicate or as a set.
   The two formation rules say that the supplied premisses are derivable, and the second says
   that if all the premisses of some rule are derivable, then so is the conclusion. *)

inductive_set derivable :: "rule set \<Rightarrow> deriv set"
  for R :: "rule set"
  where
   base[intro]: "\<lbrakk>([],C) \<in> R\<rbrakk> \<Longrightarrow> (C,0) \<in> derivable R"
|  step[intro]: "\<lbrakk> r \<in> R ; (fst r)\<noteq>[] ; \<forall> p \<in> set (fst r). \<exists> n \<le> m. (p,n) \<in> derivable R \<rbrakk> 
                       \<Longrightarrow> (snd r,m + 1) \<in> derivable R"


(* Characterisation of a sequent *)
lemma characteriseSeq:
shows "\<exists> A B. (C :: sequent) = (A \<Rightarrow>* B)"
apply (rule_tac x="antec C" in exI, rule_tac x="succ C" in exI) by (cases C) (auto)


(* Helper function for later *)
lemma nonEmptySet:
shows "A \<noteq> [] \<longrightarrow> (\<exists> a. a \<in> set A)"
by (auto simp add:neq_Nil_conv)


(* Lemma which says that if we have extended an identity rule, then the propositional variable is
   contained in the extended multisets *)
lemma extendID:
assumes "extend S (\<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "At i xs :# \<Gamma> \<and> At i xs :# \<Delta>"
using assms
proof-
  from assms have "\<exists> \<Gamma>' \<Delta>'. \<Gamma> = \<Gamma>' \<oplus> At i xs \<and> \<Delta> = \<Delta>' \<oplus> At i xs" 
     using extend_def[where forms=S and seq="\<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>"]
     by (rule_tac x="antec S" in exI,rule_tac x="succ S" in exI) auto
  then show ?thesis by auto
qed


lemma extendFalsum:
assumes "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "ff :# \<Gamma>"
proof-
  from assms have "\<exists> \<Gamma>'. \<Gamma> = \<Gamma>' \<oplus> ff" 
     using extend_def[where forms=S and seq="\<LM> ff \<RM> \<Rightarrow>* \<Empt>"]
     by (rule_tac x="antec S" in exI) auto
  then show ?thesis by auto
qed



(* Lemma that says if a propositional variable is in both the antecedent and succedent of a sequent,
   then it is derivable from idscRules *)
lemma containID:
assumes a:"At i xs :# \<Gamma> \<and> At i xs :# \<Delta>"
    and b:"Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable R*"
proof-
from a have "\<Gamma> = \<Gamma> \<ominus> At i xs \<oplus> At i xs \<and> \<Delta> = \<Delta> \<ominus> At i xs \<oplus> At i xs" by auto
then have "extend ((\<Gamma> \<ominus> At i xs) \<Rightarrow>* (\<Delta> \<ominus> At i xs)) (\<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)" 
     using extend_def[where forms="\<Gamma> \<ominus> At i xs \<Rightarrow>* \<Delta> \<ominus> At i xs" and seq="\<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>"] by auto
moreover
have "([],\<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) \<in> R" using b by auto
ultimately
have "([],\<Gamma> \<Rightarrow>* \<Delta>) \<in> extRules R" 
     using extRules.id[where R=R and r="([],  \<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>)" and S="\<Gamma> \<ominus> At i xs \<Rightarrow>* \<Delta> \<ominus> At i xs"] 
       and extendRule_def[where forms="\<Gamma> \<ominus> At i xs \<Rightarrow>* \<Delta> \<ominus> At i xs" and R="([],  \<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>)"] by auto
then show ?thesis using derivable.base[where R="R*" and C="\<Gamma> \<Rightarrow>* \<Delta>"] by auto
qed

lemma containFalsum:
assumes a: "ff :# \<Gamma>"
   and  b: "Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable R*"
proof-
from a have "\<Gamma> = \<Gamma> \<ominus> ff \<oplus> ff" by auto
then have "extend (\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>) (\<LM>ff\<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
     using extend_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>" and seq="\<LM>ff\<RM> \<Rightarrow>* \<Empt>"] by auto 
moreover
have "([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>) \<in> R" using b by auto
ultimately have "([],\<Gamma> \<Rightarrow>* \<Delta>) \<in> R*"
     using extRules.id[where R=R and r="([],  \<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and S="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>"]
       and extendRule_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>" and R="([],  \<LM>ff\<RM> \<Rightarrow>* \<Empt>)"] by auto
then show ?thesis using derivable.base[where R="R*" and C="\<Gamma> \<Rightarrow>* \<Delta>"] by auto
qed 


(* Lemma which says that if r is an identity rule, then r is of the form
   ([], P \<Rightarrow>* P) *)
lemma characteriseAx:
shows "r \<in> Ax \<Longrightarrow> r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>) \<or> (\<exists> i xs. r = ([], \<LM> At i xs\<RM> \<Rightarrow>* \<LM> At i xs\<RM>))"
apply (cases r) by (rule Ax.cases) auto


(* A lemma about the last rule used in a derivation, i.e. that one exists *)
lemma characteriseLast:
assumes "(C,m+1) \<in> derivable R"
shows "\<exists> Ps. Ps \<noteq> [] \<and>
             (Ps,C) \<in> R \<and> 
             (\<forall> p \<in> set Ps. \<exists> n\<le>m. (p,n) \<in> derivable R)"
using assms
proof (cases)
  case base
  then show "\<exists> Ps. Ps \<noteq> [] \<and>
    (Ps,C) \<in> R \<and> 
    (\<forall> p \<in> set Ps. \<exists> n\<le>m. (p,n) \<in> derivable R)" using assms by simp
next
  case (step r n)
  then obtain Ps where "r = (Ps,C)" and "m=n" by (cases r) (auto)
  then have "fst r = Ps" and "snd r = C" by auto
  then show "\<exists> Ps. Ps \<noteq> [] \<and>
    (Ps,C) \<in> R \<and> 
    (\<forall> p \<in> set Ps. \<exists> n\<le>m. (p,n) \<in> derivable R)" 
    using `r \<in> R` and `m=n` and step(4,5)
    by (rule_tac x=Ps in exI) (auto)
qed



lemma propRuleCharacterise:
assumes "(Ps,C) \<in> upRules"
shows "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Cpd0 F Fs\<RM>) \<or> C = (\<LM>Cpd0 F Fs\<RM> \<Rightarrow>* \<Empt>)"
using assms
proof (cases)
  case (I F Fs)
  then obtain \<Gamma> \<Delta> where "C = (\<Gamma> \<Rightarrow>* \<Delta>)" using characteriseSeq[where C=C] by auto
  then have "(Ps,\<Gamma> \<Rightarrow>* \<Delta>) \<in> upRules" using assms by simp
  then show "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Cpd0 F Fs\<RM>) \<or> C = (\<LM>Cpd0 F Fs\<RM> \<Rightarrow>* \<Empt>)" 
    using `mset C \<equiv> \<LM>Cpd0 F Fs\<RM>` and `C = (\<Gamma> \<Rightarrow>* \<Delta>)`
      and mset.simps[where ant=\<Gamma> and suc=\<Delta>] and union_is_single[where M=\<Gamma> and N=\<Delta> and a="Cpd0 F Fs"]
    by auto
qed

lemma provRuleCharacterise:
assumes "(Ps,C) \<in> provRules"
shows "\<exists> F x A. (C = (\<Empt> \<Rightarrow>* \<LM> F \<nabla> [x].A \<RM>) \<or> C = (\<LM> F \<nabla> [x].A \<RM> \<Rightarrow>* \<Empt>)) \<and> x \<sharp> set_of_prem (Ps - A)"
using assms
proof (cases)
  case (I F x A)
  then obtain \<Gamma> \<Delta> where "C = (\<Gamma> \<Rightarrow>* \<Delta>)" using characteriseSeq[where C=C] by auto
  then have "(Ps,\<Gamma> \<Rightarrow>* \<Delta>) \<in> provRules" using assms by simp
  then show "\<exists> F x A. (C = (\<Empt> \<Rightarrow>* \<LM> F \<nabla> [x].A \<RM>) \<or> C = (\<LM> F \<nabla> [x].A \<RM> \<Rightarrow>* \<Empt>)) \<and> x \<sharp> set_of_prem (Ps - A)" 
    using `mset C = \<LM> F \<nabla> [x].A \<RM>` and `C = (\<Gamma> \<Rightarrow>* \<Delta>)` and `x \<sharp> set_of_prem (Ps - A)`
      and mset.simps[where ant=\<Gamma> and suc=\<Delta>] and union_is_single[where M=\<Gamma> and N=\<Delta> and a="F \<nabla> [x].A"]
    by auto
qed

lemma nprovRuleCharacterise:
assumes "(Ps,C) \<in> nprovRules"
shows "\<exists> F x A. C = (\<Empt> \<Rightarrow>* \<LM> F \<nabla> [x].A \<RM>) \<or> C = (\<LM> F \<nabla> [x].A \<RM> \<Rightarrow>* \<Empt>)"
using assms
proof (cases)
  case (I F x A)
  then obtain \<Gamma> \<Delta> where "C = (\<Gamma> \<Rightarrow>* \<Delta>)" using characteriseSeq[where C=C] by auto
  then have "(Ps,\<Gamma> \<Rightarrow>* \<Delta>) \<in> nprovRules" using assms by simp
  then show "\<exists> F x A. C = (\<Empt> \<Rightarrow>* \<LM> F \<nabla> [x].A \<RM>) \<or> C = (\<LM> F \<nabla> [x].A \<RM> \<Rightarrow>* \<Empt>)" 
    using `mset C = \<LM> F \<nabla> [x].A \<RM>` and `C = (\<Gamma> \<Rightarrow>* \<Delta>)`
      and mset.simps[where ant=\<Gamma> and suc=\<Delta>] and union_is_single[where M=\<Gamma> and N=\<Delta> and a="F \<nabla> [x].A"]
    by auto
qed


lemma extendEmpty:
shows "extend (\<Empt> \<Rightarrow>* \<Empt>) C = C"
apply (auto simp add:extend_def) by (cases C) auto



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

lemma finSeqSet:
fixes S :: "sequent"
shows "finite (set_of_seq S)"
proof-
obtain \<Gamma> \<Delta> where "S = (\<Gamma> \<Rightarrow>* \<Delta>)" by (cases S) auto
then show ?thesis by (auto simp add:finite_set_mset)
qed

lemma finPremSet:
fixes Ps :: "sequent list"
shows "finite (set_of_prem Ps)"
by (induct Ps) (auto simp add:finSeqSet)


lemma finSupp:
fixes A :: "form" and As :: "form_list"
shows "finite ((supp A) :: var set)" and "finite ((supp As) :: var set)"
proof (nominal_induct A and As rule:form_form_list.strong_inducts)
print_cases
case (At n xs)   
   have "finite (set xs :: var set)" by (induct xs) auto
   moreover have "set xs = (supp xs :: var set)" by (induct xs) (auto simp add:supp_list_nil supp_set_empty supp_list_cons supp_atm)
   ultimately have "finite (supp xs :: var set)" by auto
   moreover have "supp (At n xs) = supp n \<union> (supp xs :: var set)" using form.supp(1)[where ?x2.0=n and ?x1.0=xs] by auto
   then have "supp (At n xs) = (supp xs :: var set)" using supp_nat[where n=n] by force
   ultimately show ?case by auto
next
case FNil
   have "supp FNil = ({} :: var set)" using form_list.supp by auto
   then show ?case by auto
next
case (FCons F Fs)
   then show ?case using form_list.supp by auto
next
case (Cpd0 Str Fs)
   then show ?case using form.supp(2)[where ?x2.0="Str" and ?x1.0=Fs] and supp_string[where s=Str] by auto
next
case (Cpd1 F x B)
   from `finite (supp B)` have "supp ([x].B) = supp B - {x}" using abs_fun_supp[OF pt_var_inst, OF at_var_inst] by auto
   then show ?case using form.supp(3)[where ?x3.0=F and ?x1.0=x and ?x2.0=B] and supp_string[where s=F]
                   and `finite (supp B)` by force
next
case ff
   then show ?case using form.supp by auto
qed

lemma getFresh:
fixes x :: "var" and A :: "form" and S :: "sequent" and Ps :: "sequent list"
shows "\<exists> (y :: var). y \<sharp> x \<and> y \<sharp> A \<and> y \<sharp> set_of_seq S \<and> y \<sharp> set_of_prem Ps"
proof-
have "finite ({A} \<union> set_of_seq S \<union> set_of_prem Ps)" using finSeqSet and finPremSet by auto
then have "finite (supp ({A} \<union> set_of_seq S \<union> set_of_prem Ps) :: var set)"
     using finSupp(1) and supp_of_fin_sets[OF pt_var_inst, OF at_var_inst, OF fs_var_inst,
                                           where X="({A} \<union> set_of_seq S \<union> set_of_prem Ps)"] 
     by auto
then have "finite (supp ({A} \<union> set_of_seq S \<union> set_of_prem Ps) \<union> supp x :: var set)" using supp_atm by auto
then obtain y where "y \<notin> (supp ({A} \<union> set_of_seq S \<union> set_of_prem Ps) \<union> supp x :: var set)" 
     using ex_in_inf[OF at_var_inst,where A="supp ({A} \<union> set_of_seq S \<union> set_of_prem Ps) \<union> supp x"] by auto
then have "y \<notin> supp x \<and> y \<notin> supp ({A} \<union> set_of_seq S \<union> set_of_prem Ps)" by auto
then have "y \<sharp> ({A} \<union> set_of_seq S \<union> set_of_prem Ps) \<and> y \<sharp> x" using fresh_def[where a=y and x=x]
     and fresh_def[where a=y and x="{A} \<union> set_of_seq S \<union> set_of_prem Ps"] by auto
then have "y \<sharp> A \<and> y \<sharp> (set_of_seq S \<union> set_of_prem Ps) \<and> y \<sharp> x" 
     using fresh_fin_insert[OF pt_var_inst, OF at_var_inst, OF fs_var_inst,where X="set_of_seq S \<union> set_of_prem Ps" and x=A]
       and finSeqSet and finPremSet by auto
then have "y \<sharp> A \<and> y \<sharp> set_of_seq S \<and> y \<sharp> set_of_prem Ps \<and> y \<sharp> x"
     using fresh_fin_union[OF pt_var_inst,OF at_var_inst, OF fs_var_inst, where X="set_of_seq S" and Y="set_of_prem Ps"]
       and finSeqSet and finPremSet by auto
then show ?thesis by auto
qed

lemma switchAux:
fixes Xs :: "var list"
assumes "y \<sharp> Xs"
shows "[y;x]Xs = [(y,x)]\<bullet>Xs"
using assms
proof (induct Xs)
print_cases
case Nil
   then show ?case using nil_eqvt by auto
next
case (Cons a As)
   then have "y \<sharp> a \<and> y \<sharp> As" and "[y;x]As = [(y,x)]\<bullet>As" 
        using fresh_list_cons[where a=y and x=a and xs=As] by auto
   then show ?case using NEmpt[where z=y and y=x and x=a and ys= As] 
                 and cons_eqvt[where pi="[(y,x)]" and x=a and xs=As] by (perm_simp add:fresh_atm)
qed

lemma switch:
fixes A :: "form" and As :: "form_list"
shows "y \<sharp> A \<Longrightarrow> [y,x]A = [(y,x)]\<bullet>A" and "y \<sharp> As \<Longrightarrow> [y,x]As = [(y,x)]\<bullet>As"
proof (nominal_induct A and As avoiding: x y rule:form_form_list.strong_inducts)
  case (At n xs s t)
  then have "t \<sharp> xs" using form.fresh by auto
  then show ?case using perm_nat_def[where pi="[(t,s)]" and i=n] and switchAux[where y=t and Xs=xs]
    by auto
next
  case FNil
  then show ?case by auto
next
  case (FCons B Bs s t)
  then show ?case by auto
next
  case (Cpd0 Str Bs s t)
  then show ?case using Cpd0.hyps[where ba=t and b=s] and form.fresh
    and perm_string[where s="Str" and pi="[(t,s)]"] by auto
next
  case (Cpd1 F a B s t)
  then have "t \<sharp> B" using form.fresh(3)[where ?x3.0=F and ?x1.0=a and ?x2.0=B and a=t] 
    and fresh_atm[where a=a and b=t] and fresh_string[where a=t and s=F] 
    and fresh_abs_funE[OF pt_var_inst, OF at_var_inst,where x=B and b=t and a=a]
    and finSupp(1)[where A=B] by auto
  then show ?case using Cpd1(4)[where ba=t and b=s] and form.fresh and Cpd1(1,2)
    and perm_string[where pi="[(t,s)]" and s=F] and fresh_atm by perm_simp
next
  case ff
  then show ?case by auto
qed
(*>*)
    

text{*
\noindent The final clause says we can only use an $S$ which is suitable fresh.

The only lemma which is unique to first-order calculi is the Substitution Lemma.  We show the crucial step in the proof; namely that one can substitute a fresh variable into a formula and the resultant formula is unchanged.  The proof is not particularly edifying and is omitted:
*}

lemma formSubst:
shows "y \<sharp> x \<and> y \<sharp> A \<Longrightarrow> F \<nabla> [x].A = F \<nabla> [y].([y,x]A)"
(*<*)
proof-
assume "y \<sharp> x \<and> y \<sharp> A" then have "[x].A = [y].([y,x]A)" 
  using abs_fun_eq3[OF pt_var_inst, OF at_var_inst,where x="[y,x]A" and y=A and a=y and b=x]
  and switch(1)[where y=y and A=A and x=x] and fresh_atm[where a=y and b=x] by (perm_simp)
then show ?thesis using form.inject(3) by auto
qed
(*>*)

text{*
\noindent  Using the above lemma, we can change any sequent to an equivalent new sequent which does not contain certain variables.  Therefore, we can extend with any sequent:
*}

lemma extend_for_any_seq:
fixes S :: "sequent"
assumes rules: "R1 \<subseteq> upRules \<and> R2 \<subseteq> nprovRules \<and> R3 \<subseteq> provRules"
    and rules2: "R = Ax \<union> R1 \<union> R2 \<union> R3"
    and rin: "r \<in> R"
shows "extendRule S r \<in> R*"
 (*<*)
proof-
from rin and rules2 have "r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" by auto
moreover
    {assume "r \<in> Ax"
     then have "extendRule S r \<in> R*" using extRules.id[where r=r and R=R and S=S] and rin by auto
    }
moreover
    {assume "r \<in> R1"
     then have "r \<in> upRules" using rules by auto
     then have "extendRule S r \<in> R*" using extRules.sc[where r=r and R=R and S=S] and rin by auto
    }
moreover
    {assume "r \<in> R2"
     then have "r \<in> nprovRules" using rules by auto
     then have "extendRule S r \<in> R*" using extRules.np[where r=r and R=R and S=S] and rin by auto
    }
moreover

 {(*>*)
txt{* \noindent  We only show the interesting case: where the last inference had a freshness proviso: *}
  
  assume "r \<in> R3" 
  then have "r \<in> provRules" using rules by auto
  obtain ps c where "r = (ps,c)" by (cases r) auto
  then have r1: "(ps,c) \<in> R" 
          and r2: "(ps,c) \<in> provRules" using `r \<in> provRules` and rin by auto
  with `r = (ps,c)` obtain F x A 
       where "(c = ( \<Empt> \<Rightarrow>* \<LM>F \<nabla> [x].A\<RM>) \<or> 
                 c = ( \<LM>F \<nabla> [x].A\<RM> \<Rightarrow>* \<Empt>)) \<and> x \<sharp> set_of_prem ( ps - A )"
         using provRuleCharacterise(*<*)[where Ps=ps and C=c](*>*) and `r \<in> provRules` by auto
  then have "mset c = \<LM> F \<nabla> [x].A \<RM> \<and> x \<sharp> set_of_prem (ps - A)" (*<*)using mset.simps(*>*) by auto
  moreover obtain y where fr:  "y \<sharp> x \<and> 
                                  y \<sharp> A \<and> 
                                  y \<sharp> set_of_seq S \<and> 
                                 (y :: var) \<sharp> set_of_prem (ps-A)"
         using getFresh(*<*)[where x=x and A=A and S=S and Ps="ps-A"](*>*) by auto
  then have fr2: "y \<sharp> set_of_seq S" by auto 
  ultimately have "mset c = \<LM> F \<nabla> [y].([y,x]A) \<RM> \<and> y \<sharp> set_of_prem (ps - A)" 
         using formSubst and fr by auto
  then have "mset c = \<LM> F \<nabla> [y].([y,x]A) \<RM>" by auto
  then have "extendRule S (ps,c) \<in> R*" using r1 and r2 and fr2
         and extRules.p(*<*)[where ps=ps and c=c and R=R and F=F and x=y and A="[y,x]A" and S=S](*>*) by auto
  then have "extendRule S r \<in> R*" using `r = (ps,c)` by simp
   (*<*) }

ultimately show ?thesis by blast
qed


(* Constructing the rule set we will use.  It contains all axioms, but only a subset
   of the possible logical rules. *)
lemma ruleSet:
assumes "R1 \<subseteq> upRules" and "R2 \<subseteq> nprovRules" and "R3 \<subseteq> provRules"
    and "R = Ax \<union> R1 \<union> R2 \<union> R3"
    and "(Ps,C) \<in> R*"
shows "\<exists> S r. extendRule S r = (Ps,C) \<and> (r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3 \<or> r \<in> Ax)"
proof-
from `(Ps,C) \<in> R*` have "\<exists> S r. extendRule S r = (Ps,C) \<and> r \<in> R" by (cases) auto
then obtain S r where "(Ps,C) = extendRule S r" and "r \<in> R" apply auto 
                by (drule_tac x=S in meta_spec,drule_tac x=a in meta_spec, drule_tac x=b in meta_spec) auto
moreover from `r \<in> R` and `R = Ax \<union> R1 \<union> R2 \<union> R3` have "r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3 \<or> r \<in> Ax" by blast
ultimately show ?thesis by (rule_tac x=S in exI,rule_tac x=r in exI) (auto)
qed

(* Non-principal rule lemma *)
lemma nonPrincipalInvertRight:
assumes "R1 \<subseteq> upRules" and "R2 \<subseteq> nprovRules" and "R3 \<subseteq> provRules"
    and "R = Ax \<union> R1 \<union> R2 \<union> R3" and "r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" and "r = (ps,c)"
    and IH: "\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. rightPrincipal r' (F \<nabla> [x].A) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>') \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable R*)"
    and a': "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A,n) \<in> derivable R*" 
    and b': "\<forall> r' \<in> R. rightPrincipal r' (F \<nabla> [x].A) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and c': "\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>'"
    and np: "\<not> rightPrincipal r (F \<nabla> [x].A)"
    and ext: "extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)"
    and num: "n = n' + 1"
    and all: "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
    and nonempty: "Ps \<noteq> []"
shows "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
proof-
from ext obtain \<Phi> \<Psi> where "S = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases S) (auto)
from `r = (ps,c)` obtain G H where "c = (G \<Rightarrow>* H)" by (cases c) (auto)
then have "\<LM> F \<nabla> [x].A  \<RM> \<noteq> H" using `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3`
     proof-
     {assume "r \<in> R1" then have "r \<in> upRules" using `R1 \<subseteq> upRules` by auto
      with `r = (ps,c)` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM>Cpd0 T Ts\<RM>) \<or> c = (\<LM>Cpd0 T Ts\<RM> \<Rightarrow>* \<Empt>)"
            using propRuleCharacterise[where Ps=ps and C=c] by auto
      moreover
        {assume "c = (\<Empt> \<Rightarrow>* \<LM>Cpd0 T Ts\<RM>)"
         with `c = (G \<Rightarrow>* H)` have "\<LM> F \<nabla> [x].A \<RM> \<noteq> H" by auto
        }
      moreover
        {assume "c = (\<LM>Cpd0 T Ts\<RM> \<Rightarrow>* \<Empt>)"
         then have "\<LM>F \<nabla> [x].A \<RM> \<noteq> H" using `c = (G \<Rightarrow>* H)` by auto
        }
      ultimately have "\<LM> F \<nabla> [x].A \<RM> \<noteq> H" by blast
     }
     moreover
     {assume "r \<in> R2 \<or> r \<in> R3" 
      then have "r \<in> provRules \<or> r \<in> nprovRules" using `R2 \<subseteq> nprovRules` and `R3 \<subseteq> provRules` by auto
      with `r = (ps,c)` obtain T y B where "c = (\<Empt> \<Rightarrow>* \<LM> T \<nabla> [y].B \<RM>) \<or> c = (\<LM> T \<nabla> [y].B\<RM> \<Rightarrow>* \<Empt>)"
            using provRuleCharacterise[where Ps=ps and C=c]
            and nprovRuleCharacterise[where Ps=ps and C=c] by auto
      moreover
        {assume "c = (\<Empt> \<Rightarrow>* \<LM> T \<nabla> [y].B\<RM>)"
         then have "rightPrincipal r (T \<nabla> [y].B)" using `r = (ps,c)` by auto
         with `\<not> rightPrincipal r (F \<nabla> [x].A)` have "T \<nabla> [y].B \<noteq> F \<nabla> [x].A" by auto
         with `c = (G \<Rightarrow>* H)` have "\<LM> F \<nabla> [x].A \<RM> \<noteq> H" using `c = (\<Empt> \<Rightarrow>* \<LM> T \<nabla> [y].B \<RM>)` by auto
        }
      moreover
        {assume "c = (\<LM>T \<nabla> [y].B \<RM> \<Rightarrow>* \<Empt>)"
         then have "\<LM>F \<nabla> [x].A \<RM> \<noteq> H" using `c = (G \<Rightarrow>* H)` by auto
        }
      ultimately have "\<LM> F \<nabla> [x].A \<RM> \<noteq> H" by blast
     }
     ultimately show ?thesis using `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` by blast
     qed
moreover have "succ S + succ (snd r) = (\<Delta> \<oplus> F \<nabla> [x].A)" 
         using ext and extendRule_def[where forms=S and R=r]
                   and extend_def[where forms=S and seq="snd r"] by auto
then have "\<Psi> + H = \<Delta> \<oplus> F \<nabla> [x].A" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` and `r = (ps,c)` and `c = (G \<Rightarrow>* H)` by auto
moreover from `r = (ps,c)` and `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` and `R1 \<subseteq> upRules` and `R2 \<subseteq> nprovRules`
              and `R3 \<subseteq> provRules` have "(ps,c) \<in> upRules \<or> (ps,c) \<in> nprovRules \<or> (ps,c) \<in> provRules" by auto
then have "\<exists> A. c = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<or> c = (\<LM>A\<RM> \<Rightarrow>* \<Empt>)"
     using propRuleCharacterise[where Ps=ps and C=c]
       and nprovRuleCharacterise[where Ps=ps and C=c]
       and provRuleCharacterise[where Ps=ps and C=c] by auto
then have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" using `c = (G \<Rightarrow>* H)` by auto
ultimately have "F \<nabla> [x].A :# \<Psi>"
    proof-
    have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" by fact
    moreover
    {assume "H = \<Empt>"
     then have "\<Psi> = \<Delta> \<oplus> F \<nabla> [x].A" using `\<Psi> + H = \<Delta> \<oplus> F \<nabla> [x].A` by auto
     then have "F \<nabla> [x].A :# \<Psi>" by auto
    }
    moreover
    {assume "\<exists> A. H = \<LM>A\<RM>"
     then obtain T where "H = \<LM>T\<RM>" by auto
     then have "\<Psi> \<oplus> T = \<Delta> \<oplus> F \<nabla> [x].A" using `\<Psi> + H = \<Delta> \<oplus> F \<nabla> [x].A` by auto
     then have "set_mset (\<Psi> \<oplus> T) = set_mset (\<Delta> \<oplus> F \<nabla> [x].A)" by auto
     then have "set_mset \<Psi> \<union> {T} = set_mset \<Delta> \<union> {F \<nabla> [x].A}" by auto
     moreover from `H = \<LM>T\<RM>` and `\<LM>F \<nabla> [x].A\<RM> \<noteq> H` have "F \<nabla> [x].A \<noteq> T" by auto
     ultimately have "F \<nabla> [x].A \<in> set_mset \<Psi>" by auto
     then have "F \<nabla> [x].A :# \<Psi>" by auto
    }
    ultimately show "F \<nabla> [x].A :# \<Psi>" by blast
    qed
then have "\<exists> \<Psi>1. \<Psi> = \<Psi>1 \<oplus> F \<nabla> [x].A" 
     by (rule_tac x="\<Psi> \<ominus> F \<nabla> [x].A" in exI) (auto simp add:multiset_eq_iff)
then obtain \<Psi>1 where "S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A)" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` by auto
have "Ps = map (extend S) ps" 
     using `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)` and extendRule_def and `r = (ps,c)` by auto
then have "\<forall> p \<in> set Ps. (\<exists> p'. p = extend S p')" using ex_map_conv[where ys=Ps and f="extend S"] by auto
then have "\<forall> p \<in> set Ps. (F \<nabla> [x].A :# succ p)" 
     using `F \<nabla> [x].A :# \<Psi>` and `S = (\<Phi> \<Rightarrow>* \<Psi>)` apply (auto simp add:Ball_def) 
     by (drule_tac x=xa in spec) (auto simp add:extend_def)
then have a1:"\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A)" using characteriseSeq
     apply (auto simp add:Ball_def) apply (drule_tac x=xa in spec,simp) 
     apply (rule_tac x="antec xa" in exI,rule_tac x="succ xa \<ominus> F \<nabla> [x].A" in exI) 
     by (drule_tac x=xa in meta_spec) (auto simp add:multiset_eq_iff)
with all have "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A,n) \<in> derivable R* \<and> p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A)"
                 by (auto simp add:Ball_def)
then have a2: "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' m. m\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',m) \<in> derivable R* \<and> p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A)"
                 using num and b' and IH and c'
                 apply (auto simp add:Ball_def) apply (drule_tac x=xa in spec) apply simp
                 apply hypsubst_thin
                 apply (elim exE conjE) apply (drule_tac x=n in spec) apply simp
                 apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)
                 apply (simp) apply (elim exE conjE) by (rule_tac x=m' in exI) (arith)
obtain Ps' where eq: "Ps' = map (extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>')) ps" by auto
have "length Ps = length Ps'" using `Ps' = map (extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>')) ps`
                              and `Ps = map (extend S) ps` by auto
then have "Ps' \<noteq> []" using nonempty by auto
from `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` have "r \<in> R" using `R = Ax \<union> R1 \<union> R2 \<union> R3` by auto
then have "extendRule (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') r \<in> R*" using `R = Ax \<union> R1 \<union> R2 \<union> R3`
     and extend_for_any_seq[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and r=r and S="\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>'"]
     and `R1 \<subseteq> upRules` and `R2 \<subseteq> nprovRules` and `R3 \<subseteq> provRules` by auto
moreover have "extendRule (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') r = (Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')"
         using `S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A)` and `extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)`
         and `r = (ps,c)` and eq
         by (auto simp add:extendRule_def extend_def union_ac multiset_eq_iff)
ultimately have "(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*" by simp
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
have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) \<in> set Ps \<longrightarrow> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"
               proof-
                 {fix \<Phi>' \<Psi>'
                 assume "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) \<in> set Ps"  
                 then have "\<exists> p \<in> set ps. extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A) p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A)"
                      using `Ps = map (extend S) ps` and `S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A)` and a1 and d1
                           apply (simp only:Ball_def Bex_def) apply (drule_tac x=" \<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A" in spec)
                           by (drule_tac x="\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A" in spec) (auto)
                 then obtain p where t:"p \<in> set ps \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A) p"
                      apply auto by (drule_tac x=p in meta_spec) (simp)
                 then obtain D B where "p = (D \<Rightarrow>* B)" by (cases p) 
                 then have "(D \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A) (D \<Rightarrow>* B)"
                      using t by auto
                 then have ant: "\<Phi>' = \<Phi> + D" and suc: "\<Psi>' \<oplus> F \<nabla> [x].A = \<Psi>1 \<oplus> F \<nabla> [x].A + B" using extend_def by auto
                 from ant have "\<Phi>' + \<Gamma>' = (\<Phi> + \<Gamma>') + D" by (auto simp add:union_ac)
                 moreover
                 from suc have "\<Psi>' = \<Psi>1 + B" by (auto simp add:union_ac multiset_eq_iff)
                 then have "\<Psi>' + \<Delta>' = (\<Psi>1 + \<Delta>') + B" by (auto simp add:union_ac)
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (D \<Rightarrow>* B)" using extend_def by auto
                 moreover have "extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (D \<Rightarrow>* B) \<in> set Ps'" using `p = (D \<Rightarrow>* B)` and t and c2 by auto
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'" by simp
                 }
                 thus ?thesis by blast
               qed
            moreover
            have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps' \<longrightarrow> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) \<in> set Ps"
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
                 then have ant: "\<Phi>' + \<Gamma>' = \<Phi> + \<Gamma>' + D" and suc: "\<Psi>' + \<Delta>' = \<Psi>1 + \<Delta>' + B" using extend_def by auto
                 from ant have "\<Phi>' + \<Gamma>' = (\<Phi> + D) + \<Gamma>'" by (auto simp add:union_ac)
                 then have "\<Phi>' = \<Phi> + D" by simp
                 moreover
                 from suc have "\<Psi>' + \<Delta>' = (\<Psi>1 + B) + \<Delta>'" by (auto simp add:union_ac)
                 then have "\<Psi>' = \<Psi>1 + B" by simp
                 then have "\<Psi>' \<oplus> F \<nabla> [x].A = (\<Psi>1 \<oplus> F \<nabla> [x].A) + B" by (auto simp add:union_ac)
                 ultimately have "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A) (D \<Rightarrow>* B)" 
                      using extend_def by auto
                 moreover have "extend (\<Phi>  \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A) (D \<Rightarrow>* B) \<in> set Ps" using `p = (D \<Rightarrow>* B)` and t and c1
                      and `S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> F \<nabla> [x].A)` by auto
                 ultimately have "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) \<in> set Ps" by simp
                 }
                 thus ?thesis by blast
               qed
ultimately
have "\<forall> \<Phi>' \<Psi>'. ((\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A) \<in> set Ps) = ((\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps')" by auto
then have "\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',n) \<in> derivable R*
                \<and> p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq2 and a2
     apply (simp add:Ball_def) apply (intro allI impI) apply (drule_tac x=xa in spec) apply simp
     apply (elim exE) apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)  
     by (drule_tac x="\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> F \<nabla> [x].A" in spec) (simp)
then have all:"\<forall> p \<in> set Ps'. \<exists> n\<le>n'. (p,n) \<in> derivable R*" by auto
then show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using num
     and `(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*` and `Ps' \<noteq> []`
     and derivable.step[where r="(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" and R="R*"]
     by (auto simp add:Ball_def Bex_def)
qed


(* Non-principal Left *)
lemma nonPrincipalInvertLeft:
assumes "R1 \<subseteq> upRules" and "R2 \<subseteq> nprovRules" and "R3 \<subseteq> provRules"
    and "R = Ax \<union> R1 \<union> R2 \<union> R3" and "r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" and "r = (ps,c)"
    and IH: "\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. leftPrincipal r' (F \<nabla> [x].A) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>') \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable R*)"
    and a': "(\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>,n) \<in> derivable R*" 
    and b': "\<forall> r' \<in> R. leftPrincipal r' (F \<nabla> [x].A) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and c': "\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>'"
    and np: "\<not> leftPrincipal r (F \<nabla> [x].A)"
    and ext: "extendRule S r = (Ps,\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)"
    and num: "n = n' + 1"
    and all: "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
    and nonempty: "Ps \<noteq> []"
shows "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
proof-
from ext obtain \<Phi> \<Psi> where "S = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases S) (auto)
from `r = (ps,c)` obtain G H where "c = (G \<Rightarrow>* H)" by (cases c) (auto)
then have "\<LM> F \<nabla> [x].A  \<RM> \<noteq> G" using `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3`
     proof-
     {assume "r \<in> R1" then have "r \<in> upRules" using `R1 \<subseteq> upRules` by auto
      with `r = (ps,c)` obtain T Ts where "c = (\<Empt> \<Rightarrow>* \<LM>Cpd0 T Ts\<RM>) \<or> c = (\<LM>Cpd0 T Ts\<RM> \<Rightarrow>* \<Empt>)"
            using propRuleCharacterise[where Ps=ps and C=c] by auto
      moreover
        {assume "c = (\<Empt> \<Rightarrow>* \<LM>Cpd0 T Ts\<RM>)"
         with `c = (G \<Rightarrow>* H)` have "\<LM> F \<nabla> [x].A \<RM> \<noteq> G" by auto
        }
      moreover
        {assume "c = (\<LM>Cpd0 T Ts\<RM> \<Rightarrow>* \<Empt>)"
         then have "\<LM>F \<nabla> [x].A \<RM> \<noteq> G" using `c = (G \<Rightarrow>* H)` by auto
        }
      ultimately have "\<LM> F \<nabla> [x].A \<RM> \<noteq> G" by blast
     }
     moreover
     {assume "r \<in> R2 \<or> r \<in> R3" 
      then have "r \<in> provRules \<or> r \<in> nprovRules" using `R2 \<subseteq> nprovRules` and `R3 \<subseteq> provRules` by auto
      with `r = (ps,c)` obtain T y B where "c = (\<Empt> \<Rightarrow>* \<LM> T \<nabla> [y].B \<RM>) \<or> c = (\<LM> T \<nabla> [y].B\<RM> \<Rightarrow>* \<Empt>)"
            using provRuleCharacterise[where Ps=ps and C=c]
            and nprovRuleCharacterise[where Ps=ps and C=c] by auto
      moreover
        {assume "c = (\<Empt> \<Rightarrow>* \<LM> T \<nabla> [y].B\<RM>)"
         then have "\<LM>F \<nabla> [x].A \<RM> \<noteq> G" using `c = (G \<Rightarrow>* H)` by auto         
        }
      moreover
        {assume "c = (\<LM>T \<nabla> [y].B \<RM> \<Rightarrow>* \<Empt>)"
         then have "leftPrincipal r (T \<nabla> [y].B)" using `r = (ps,c)` by auto
         with `\<not> leftPrincipal r (F \<nabla> [x].A)` have "T \<nabla> [y].B \<noteq> F \<nabla> [x].A" by auto
         with `c = (G \<Rightarrow>* H)` have "\<LM> F \<nabla> [x].A \<RM> \<noteq> G" using `c = (\<LM> T \<nabla> [y].B \<RM> \<Rightarrow>* \<Empt>)` by auto
        }
      ultimately have "\<LM> F \<nabla> [x].A \<RM> \<noteq> G" by blast
     }
     ultimately show ?thesis using `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` by blast
     qed
moreover have "antec S + antec (snd r) = (\<Gamma> \<oplus> F \<nabla> [x].A)" 
         using ext and extendRule_def[where forms=S and R=r]
                   and extend_def[where forms=S and seq="snd r"] by auto
then have "\<Phi> + G = \<Gamma> \<oplus> F \<nabla> [x].A" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` and `r = (ps,c)` and `c = (G \<Rightarrow>* H)` by auto
moreover from `r = (ps,c)` and `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` and `R1 \<subseteq> upRules` and `R2 \<subseteq> nprovRules`
              and `R3 \<subseteq> provRules` have "(ps,c) \<in> upRules \<or> (ps,c) \<in> nprovRules \<or> (ps,c) \<in> provRules" by auto
then have "\<exists> A. c = (\<Empt> \<Rightarrow>* \<LM>A\<RM>) \<or> c = (\<LM>A\<RM> \<Rightarrow>* \<Empt>)"
     using propRuleCharacterise[where Ps=ps and C=c]
       and nprovRuleCharacterise[where Ps=ps and C=c]
       and provRuleCharacterise[where Ps=ps and C=c] by auto
then have "G = \<Empt> \<or> (\<exists> A. G = \<LM>A\<RM>)" using `c = (G \<Rightarrow>* H)` by auto
ultimately have "F \<nabla> [x].A :# \<Phi>"
    proof-
    have "G = \<Empt> \<or> (\<exists> A. G = \<LM>A\<RM>)" by fact
    moreover
    {assume "G = \<Empt>"
     then have "\<Phi> = \<Gamma> \<oplus> F \<nabla> [x].A" using `\<Phi> + G = \<Gamma> \<oplus> F \<nabla> [x].A` by auto
     then have "F \<nabla> [x].A :# \<Phi>" by auto
    }
    moreover
    {assume "\<exists> A. G = \<LM>A\<RM>"
     then obtain T where "G = \<LM>T\<RM>" by auto
     then have "\<Phi> \<oplus> T = \<Gamma> \<oplus> F \<nabla> [x].A" using `\<Phi> + G = \<Gamma> \<oplus> F \<nabla> [x].A` by auto
     then have "set_mset (\<Phi> \<oplus> T) = set_mset (\<Gamma> \<oplus> F \<nabla> [x].A)" by auto
     then have "set_mset \<Phi> \<union> {T} = set_mset \<Gamma> \<union> {F \<nabla> [x].A}" by auto
     moreover from `G = \<LM>T\<RM>` and `\<LM>F \<nabla> [x].A\<RM> \<noteq> G` have "F \<nabla> [x].A \<noteq> T" by auto
     ultimately have "F \<nabla> [x].A \<in> set_mset \<Phi>" by auto
     then have "F \<nabla> [x].A :# \<Phi>" by auto
    }
    ultimately show "F \<nabla> [x].A :# \<Phi>" by blast
    qed
then have "\<exists> \<Phi>1. \<Phi> = \<Phi>1 \<oplus> F \<nabla> [x].A" 
     by (rule_tac x="\<Phi> \<ominus> F \<nabla> [x].A" in exI) (auto simp add:multiset_eq_iff)
then obtain \<Phi>1 where "S = (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>)" using `S = (\<Phi> \<Rightarrow>* \<Psi>)` by auto
have "Ps = map (extend S) ps" 
     using `extendRule S r = (Ps,\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)` and extendRule_def and `r = (ps,c)` by auto
then have "\<forall> p \<in> set Ps. (\<exists> p'. p = extend S p')" using ex_map_conv[where ys=Ps and f="extend S"] by auto
then have "\<forall> p \<in> set Ps. (F \<nabla> [x].A :# antec p)" 
     using `F \<nabla> [x].A :# \<Phi>` and `S = (\<Phi> \<Rightarrow>* \<Psi>)` apply (auto simp add:Ball_def) 
     by (drule_tac x=xa in spec) (auto simp add:extend_def)
then have a1:"\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>')" using characteriseSeq
     apply (auto simp add:Ball_def) apply (drule_tac x=xa in spec,simp) 
     apply (rule_tac x="antec xa \<ominus> F \<nabla> [x].A" in exI,rule_tac x="succ xa" in exI) 
     by (drule_tac x=xa in meta_spec) (auto simp add:multiset_eq_iff)
with all have "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>',n) \<in> derivable R* \<and> p = (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>')"
                 by (auto simp add:Ball_def)
then have a2: "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' m. m\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',m) \<in> derivable R* \<and> p = (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>')"
                 using num and b' and IH and c'
                 apply (auto simp add:Ball_def) apply (drule_tac x=xa in spec) apply simp
                 apply hypsubst_thin
                 apply (elim exE conjE) apply (drule_tac x=n in spec) apply simp
                 apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)
                 apply (simp) apply (elim exE conjE) by (rule_tac x=m' in exI) (arith)
obtain Ps' where eq: "Ps' = map (extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')) ps" by auto
have "length Ps = length Ps'" using `Ps' = map (extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')) ps`
                              and `Ps = map (extend S) ps` by auto
then have "Ps' \<noteq> []" using nonempty by auto
from `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` have "r \<in> R" using `R = Ax \<union> R1 \<union> R2 \<union> R3` by auto
then have "extendRule (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') r \<in> R*" using `R = Ax \<union> R1 \<union> R2 \<union> R3`
     and extend_for_any_seq[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and r=r and S="\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>'"]
     and `R1 \<subseteq> upRules` and `R2 \<subseteq> nprovRules` and `R3 \<subseteq> provRules` by auto
moreover have "extendRule (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') r = (Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')"
         using `S = (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>)` and `extendRule S r = (Ps, \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)`
         and `r = (ps,c)` and eq
         by (auto simp add:extendRule_def extend_def union_ac multiset_eq_iff)
ultimately have "(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*" by simp
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
have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') \<in> set Ps \<longrightarrow> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"
               proof-
                 {fix \<Phi>' \<Psi>'
                 assume "(\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') \<in> set Ps"  
                 then have "\<exists> p \<in> set ps. extend (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>) p = (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>')"
                      using `Ps = map (extend S) ps` and `S = (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>)` and a1 and d1
                           apply (simp only:Ball_def Bex_def) apply (drule_tac x=" \<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>'" in spec)
                           by (drule_tac x="\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>'" in spec) (auto)
                 then obtain p where t:"p \<in> set ps \<and> (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') = extend (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>) p"
                      apply auto by (drule_tac x=p in meta_spec) (simp)
                 then obtain D B where "p = (D \<Rightarrow>* B)" by (cases p) 
                 then have "(D \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') = extend (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>) (D \<Rightarrow>* B)"
                      using t by auto
                 then have ant: "\<Phi>' \<oplus> F \<nabla> [x].A = \<Phi>1 \<oplus> F \<nabla> [x].A + D" and suc: "\<Psi>' = \<Psi> + B" using extend_def by auto
                 from suc have "\<Psi>' + \<Delta>' = (\<Psi> + \<Delta>') + B" by (auto simp add:union_ac)
                 moreover
                 from ant have "\<Phi>' = \<Phi>1 + D" by (auto simp add:union_ac multiset_eq_iff)
                 then have "\<Phi>' + \<Gamma>' = (\<Phi>1 + \<Gamma>') + D" by (auto simp add:union_ac)
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (D \<Rightarrow>* B)" using extend_def by auto
                 moreover have "extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (D \<Rightarrow>* B) \<in> set Ps'" using `p = (D \<Rightarrow>* B)` and t and c2 by auto
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'" by simp
                 }
                 thus ?thesis by blast
               qed
            moreover
            have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps' \<longrightarrow> (\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') \<in> set Ps"
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
                 then have ant: "\<Phi>' + \<Gamma>' = \<Phi>1 + \<Gamma>' + D" and suc: "\<Psi>' + \<Delta>' = \<Psi> + \<Delta>' + B" using extend_def by auto
                 from ant have "\<Phi>' + \<Gamma>' = (\<Phi>1 + D) + \<Gamma>'" by (auto simp add:union_ac)
                 then have "\<Phi>' = \<Phi>1 + D" by simp
                 then have "\<Phi>' \<oplus> F \<nabla> [x].A = (\<Phi>1 \<oplus> F \<nabla> [x].A) + D" by (auto simp add:union_ac)
                 moreover
                 from suc have "\<Psi>' + \<Delta>' = (\<Psi> + B) + \<Delta>'" by (auto simp add:union_ac)
                 then have "\<Psi>' = \<Psi> + B" by simp
                 ultimately have "(\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') = extend (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>) (D \<Rightarrow>* B)" 
                      using extend_def by auto
                 moreover have "extend (\<Phi>1 \<oplus> F \<nabla> [x].A  \<Rightarrow>* \<Psi>) (D \<Rightarrow>* B) \<in> set Ps" using `p = (D \<Rightarrow>* B)` and t and c1
                      and `S = (\<Phi>1 \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>)` by auto
                 ultimately have "(\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') \<in> set Ps" by simp
                 }
                 thus ?thesis by blast
               qed
ultimately
have "\<forall> \<Phi>' \<Psi>'. ((\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>') \<in> set Ps) = ((\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps')" by auto
then have "\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',n) \<in> derivable R*
                \<and> p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq2 and a2
     apply (simp add:Ball_def) apply (intro allI impI) apply (drule_tac x=xa in spec) apply simp
     apply (elim exE) apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)  
     by (drule_tac x="\<Phi>' \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Psi>'" in spec) (simp)
then have all:"\<forall> p \<in> set Ps'. \<exists> n\<le>n'. (p,n) \<in> derivable R*" by auto
then show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using num
     and `(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*` and `Ps' \<noteq> []`
     and derivable.step[where r="(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" and R="R*"]
     by (auto simp add:Ball_def Bex_def)
qed
(*>*)

text{*
\noindent We can then give the two inversion lemmata.  The principal case (where the last inference had a freshness proviso) for the right inversion lemma is shown:
*}
lemma rightInvert:
fixes \<Gamma> \<Delta> :: "form multiset"
assumes rules: "R1 \<subseteq> upRules \<and> R2 \<subseteq> nprovRules \<and> R3 \<subseteq> provRules \<and> R = Ax \<union> R1 \<union> R2 \<union> R3"
    and   a: "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A,n) \<in> derivable R*"
    and   b: "\<forall> r' \<in> R. rightPrincipal r' (F \<nabla> [x].A) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and   c: "\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>'"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
(*<*)
using assms
proof (induct n arbitrary: \<Gamma> \<Delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<Delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. rightPrincipal r' (F \<nabla> [x].A) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>') \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable R*)" 
     and a': "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A,n) \<in> derivable R*" 
     and b': "\<forall> r' \<in> R. rightPrincipal r' (F \<nabla> [x].A) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
     and c': "\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>'"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A,0) \<in> derivable R*" using a' by simp
     then have "([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A) \<in> R*" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A) \<and> (r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3)"
          using rules and ruleSet[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and Ps="[]" and C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A"]
           by auto
     then obtain r S where "extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)" and "r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" by auto
      moreover
      {assume "r \<in> Ax"
       then obtain i xs where "([], \<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) = r \<or> r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" 
            using characteriseAx[where r=r] by auto
       moreover 
           {assume "r = ([],\<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>)"
            with `extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)`
               have "extend S (\<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)"
               using extendRule_def[where R="([],\<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>)" and forms=S] by auto
            then have "At i xs :# \<Gamma> \<and> At i xs :# \<Delta>" 
                 using extendID[where S=S and i=i and xs=xs and \<Gamma>=\<Gamma> and \<Delta>="\<Delta> \<oplus> F \<nabla> [x].A"] by auto
            then have "At i xs :# \<Gamma> + \<Gamma>' \<and> At i xs :# \<Delta> + \<Delta>'" by auto
            then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules
                 and containID[where \<Gamma>="\<Gamma> + \<Gamma>'" and i=i and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
           }
       moreover
           {assume "r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
            with `extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)`
               have "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)"
               using extendRule_def[where R="([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and forms=S] by auto
            then have "ff :# \<Gamma>" 
                 using extendFalsum[where S=S and \<Gamma>=\<Gamma> and \<Delta>="\<Delta> \<oplus> F \<nabla> [x].A"] by auto
            then have "ff :# \<Gamma> + \<Gamma>'" by auto
            then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules
                 and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
           }
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" by blast      
      }
      moreover
      {assume "r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3"
       then have "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)"
            proof-
            obtain y z where "r = (y,z)" by (cases r)
            with `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` have "(y,z) \<in> R1 \<or> (y,z) \<in> R2 \<or> (y,z) \<in> R3" by simp
            then have "y \<noteq> []"
                 proof-
                 {assume "(y,z) \<in> R1"
                  then have "(y,z) \<in> upRules" using rules by auto
                  then have "y\<noteq>[]" by (cases) auto
                 }
                 moreover
                 {assume "(y,z) \<in> R2"
                  then have "(y,z) \<in> nprovRules" using rules by auto
                  then have "y\<noteq>[]" by (cases) auto
                 }
                 moreover
                 {assume "(y,z) \<in> R3"
                  then have "(y,z) \<in> provRules" using rules by auto
                  then have "y\<noteq>[]" by (cases) auto
                 }
                 ultimately show "y \<noteq> []" using `(y,z) \<in> R1 \<or> (y,z) \<in> R2 \<or> (y,z) \<in> R3` by blast
                 qed
            then show "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)" using `r = (y,z)`  by blast
            qed
       then obtain Ps C where "Ps \<noteq> []" and "r = (Ps,C)" by auto
       moreover from `extendRule S r = ([], \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)` have "\<exists> S. r = ([],S)"
            using extendRule_def[where forms=S and R=r] by (cases r) (auto)
       then obtain S where "r = ([],S)" by blast
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules by simp
       }
       ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using `n=0` by blast
 next
     case (Suc n')
     then have "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A,n'+1) \<in> derivable R*" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A) \<in> R*" and 
                          "Ps \<noteq> []" and 
                       d':"\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
          using characteriseLast[where C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A" and m=n' and R="R*"] by auto
     then have "\<exists> r S. (r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)"
          using rules 
            and ruleSet[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and Ps=Ps and C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A"] by auto
     then obtain r S where "r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" 
                    and e':"extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)" by auto
     moreover
        {assume "r \<in> Ax"
         then have "fst r = []" apply (cases r) by (rule Ax.cases) auto
         moreover have "fst r \<noteq> []" using `Ps \<noteq> []` and `extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)`
                            and extendRule_def[where forms=S and R=r]
                            and extend_def[where forms=S and seq="snd r"] by auto
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by simp
        }
     moreover
        {assume "r \<in> R1"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> upRules" using rules and `r \<in> R1` by auto
         then obtain T Ts where sw:"c = (\<Empt> \<Rightarrow>* \<LM> Cpd0 T Ts \<RM>) \<or> c = (\<LM> Cpd0 T Ts \<RM> \<Rightarrow>* \<Empt>)"
              using propRuleCharacterise[where Ps=ps and C=c] and `r = (ps,c)` by auto
         have "(rightPrincipal r (F \<nabla> [x].A)) \<or> \<not>(rightPrincipal r (F \<nabla> [x].A))" by blast
         moreover
            {assume "rightPrincipal r (F \<nabla> [x].A)"
             then have "c = (\<Empt> \<Rightarrow>* \<LM> F \<nabla> [x].A \<RM>)" using `r=  (ps,c)` by (cases) auto
             with sw have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by auto
            }
         moreover
            {assume "\<not> rightPrincipal r (F \<nabla> [x].A)"
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using nonPrincipalInvertRight[where r=r and F=F and x=x and A=A and ps=ps and c=c and R=R
                                                and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3
                                                and S=S and Ps=Ps and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and n=n and n'=n']
                  and `n = Suc n'` and `Ps \<noteq> []` and a' and b' and e'
                  and c' and rules and IH and `r \<in> R1` and d' and `r = (ps,c)` by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast         
        }
     moreover
        {assume "r \<in> R2"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> nprovRules" using rules and `r \<in> R2` by auto
         have "rightPrincipal r (F \<nabla> [x].A) \<or> \<not> rightPrincipal r (F \<nabla> [x].A)" by blast
         moreover
            {assume "rightPrincipal r (F \<nabla> [x].A)"
             then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using b' and `r = (ps,c)` and `r \<in> R2` and rules
                  by auto
             then have "extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" using `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)`
                  and `r = (ps,c)` by (simp add:extendContain)
             moreover from `rightPrincipal r (F \<nabla> [x].A)` have "c = (\<Empt> \<Rightarrow>* \<LM>F \<nabla> [x].A\<RM>)" 
                  using `r = (ps,c)` by (cases) auto
             with `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)` have "S = (\<Gamma> \<Rightarrow>* \<Delta>)"
                  using `r = (ps,c)` apply (auto simp add:extendRule_def extend_def) by (cases S) auto
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
             then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using `\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*` by auto
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using `n = Suc n'`
                  by (auto,rule_tac x=m in exI) (simp)
            }
         moreover
            {assume "\<not> rightPrincipal r (F \<nabla> [x].A)"
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using nonPrincipalInvertRight[where r=r and F=F and x=x and A=A and ps=ps and c=c and R=R
                                                and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3
                                                and S=S and Ps=Ps and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and n=n and n'=n']
                  and `n = Suc n'` and `Ps \<noteq> []` and a' and b' and e'
                  and c' and rules and IH and `r \<in> R2` and d' and `r = (ps,c)` by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
        }
     moreover


  {(*>*)
   
   
   assume "r \<in> R3"
   obtain ps c where "r = (ps,c)" by (cases r) auto
   then have "r \<in> provRules" using rules and `r \<in> R3` by auto
   have "rightPrincipal r (F \<nabla> [x].A) \<or> \<not> rightPrincipal r (F \<nabla> [x].A)" by blast
   moreover
      {assume "rightPrincipal r (F \<nabla> [x].A)"
       then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using(*<*) b' and(*>*) `r = (ps,c)` and `r \<in> R3` and rules
            by auto
       then have "extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" using 
           `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)`
            and `r = (ps,c)` by (simp add:extendContain)
       moreover from `rightPrincipal r (F \<nabla> [x].A)` have 
            "c = (\<Empt> \<Rightarrow>* \<LM>F \<nabla> [x].A\<RM>)" 
            using `r = (ps,c)` by (cases) auto
       with `extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> F \<nabla> [x].A)` have "S = (\<Gamma> \<Rightarrow>* \<Delta>)"
            using `r = (ps,c)` (*<*)apply (auto simp add:extendRule_def extend_def)(*>*) by (cases S) auto
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
       then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
            using `\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*` by auto
       then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" 
            using `n = Suc n'` by (*<*)(auto,rule_tac x=m in exI)(*>*) (simp)
      }
(*<*)
         moreover
            {assume "\<not> rightPrincipal r (F \<nabla> [x].A)"
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using nonPrincipalInvertRight[where r=r and F=F and x=x and A=A and ps=ps and c=c and R=R
                                                and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3
                                                and S=S and Ps=Ps and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and n=n and n'=n']
                  and `n = Suc n'` and `Ps \<noteq> []` and a' and b' and e'
                  and c' and rules and IH and `r \<in> R3` and d' and `r = (ps,c)` by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
        }
     ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
   qed
qed
(*>*)


lemma leftInvert:
fixes \<Gamma> \<Delta> :: "form multiset"
assumes rules: "R1 \<subseteq> upRules \<and> R2 \<subseteq> nprovRules \<and> R3 \<subseteq> provRules \<and> R = Ax \<union> R1 \<union> R2 \<union> R3"
    and   a: "(\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>,n) \<in> derivable R*"
    and   b: "\<forall> r' \<in> R. leftPrincipal r' (F \<nabla> [x].A) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
    and   c: "\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>'"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
(*<*)
using assms
proof (induct n arbitrary: \<Gamma> \<Delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<Delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. leftPrincipal r' (F \<nabla> [x].A) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>') \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable R*)" 
     and a': "(\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>,n) \<in> derivable R*" 
     and b': "\<forall> r' \<in> R. leftPrincipal r' (F \<nabla> [x].A) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
     and c': "\<not> multSubst \<Gamma>' \<and> \<not> multSubst \<Delta>'"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>,0) \<in> derivable R*" using a' by simp
     then have "([],\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>) \<in> R*" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>) \<and> (r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3)"
          using rules and ruleSet[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and Ps="[]" and C="\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>*\<Delta>"]
           by auto
     then obtain r S where "extendRule S r = ([],\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)" and "r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" by auto
      moreover
      {assume "r \<in> Ax"
       then obtain i xs where "r = ([],\<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>) \<or> r = ([], \<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
            using characteriseAx[where r=r] by auto
       moreover 
           {assume "r = ([],\<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>)"
            with `extendRule S r = ([],\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)`
               have "extend S (\<LM> At i xs \<RM> \<Rightarrow>* \<LM> At i xs \<RM>) = (\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)"
               using extendRule_def[where R="([],\<LM>At i xs\<RM> \<Rightarrow>* \<LM>At i xs\<RM>)" and forms=S] by auto
            then have "At i xs :# \<Gamma> \<and> At i xs :# \<Delta>" 
                 using extendID[where S=S and i=i and xs=xs and \<Gamma>="\<Gamma>\<oplus> F \<nabla> [x].A" and \<Delta>=\<Delta>] by auto
            then have "At i xs :# \<Gamma> + \<Gamma>' \<and> At i xs :# \<Delta> + \<Delta>'" by auto
            then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules
                 and containID[where \<Gamma>="\<Gamma> + \<Gamma>'" and i=i and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
           }
       moreover
           {assume "r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
            with `extendRule S r = ([],\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)`
               have "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)"
               using extendRule_def[where R="([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and forms=S] by auto
            then have "ff :# \<Gamma>" 
                 using extendFalsum[where S=S and \<Gamma>="\<Gamma>\<oplus>F \<nabla> [x].A" and \<Delta>=\<Delta>] by auto
            then have "ff :# \<Gamma> + \<Gamma>'" by auto
            then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules
                 and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
           }
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" by blast      
      }
      moreover
      {assume "r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3"
       then have "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)"
            proof-
            obtain y z where "r = (y,z)" by (cases r)
            with `r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3` have "(y,z) \<in> R1 \<or> (y,z) \<in> R2 \<or> (y,z) \<in> R3" by simp
            then have "y \<noteq> []"
                 proof-
                 {assume "(y,z) \<in> R1"
                  then have "(y,z) \<in> upRules" using rules by auto
                  then have "y\<noteq>[]" by (cases) auto
                 }
                 moreover
                 {assume "(y,z) \<in> R2"
                  then have "(y,z) \<in> nprovRules" using rules by auto
                  then have "y\<noteq>[]" by (cases) auto
                 }
                 moreover
                 {assume "(y,z) \<in> R3"
                  then have "(y,z) \<in> provRules" using rules by auto
                  then have "y\<noteq>[]" by (cases) auto
                 }
                 ultimately show "y \<noteq> []" using `(y,z) \<in> R1 \<or> (y,z) \<in> R2 \<or> (y,z) \<in> R3` by blast
                 qed
            then show "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)" using `r = (y,z)`  by blast
            qed
       then obtain Ps C where "Ps \<noteq> []" and "r = (Ps,C)" by auto
       moreover from `extendRule S r = ([], \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)` have "\<exists> S. r = ([],S)"
            using extendRule_def[where forms=S and R=r] by (cases r) (auto)
       then obtain S where "r = ([],S)" by blast
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules by simp
       }
       ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using `n=0` by blast
 next
     case (Suc n')
     then have "(\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>,n'+1) \<in> derivable R*" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>) \<in> R*" and 
                          "Ps \<noteq> []" and 
                       d':"\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
          using characteriseLast[where C="\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>" and m=n' and R="R*"] by auto
     then have "\<exists> r S. (r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3) \<and> extendRule S r = (Ps, \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)"
          using rules 
            and ruleSet[where ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3 and R=R and Ps=Ps and C="\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>"] by auto
     then obtain r S where "r \<in> Ax \<or> r \<in> R1 \<or> r \<in> R2 \<or> r \<in> R3" 
                    and e':"extendRule S r = (Ps, \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)" by auto
     moreover
        {assume "r \<in> Ax"
         then have "fst r = []" apply (cases r) by (rule Ax.cases) auto
         moreover have "fst r \<noteq> []" using `Ps \<noteq> []` and `extendRule S r = (Ps, \<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)`
                            and extendRule_def[where forms=S and R=r]
                            and extend_def[where forms=S and seq="snd r"] by auto
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by auto
        }
     moreover
        {assume "r \<in> R1"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> upRules" using rules and `r \<in> R1` by auto
         then obtain T Ts where sw:"c = (\<Empt> \<Rightarrow>* \<LM> Cpd0 T Ts \<RM>) \<or> c = (\<LM> Cpd0 T Ts \<RM> \<Rightarrow>* \<Empt>)"
              using propRuleCharacterise[where Ps=ps and C=c] and `r = (ps,c)` by auto
         have "(leftPrincipal r (F \<nabla> [x].A)) \<or> \<not>(leftPrincipal r (F \<nabla> [x].A))" by blast
         moreover
            {assume "leftPrincipal r (F \<nabla> [x].A)"
             then have "c = (\<LM> F \<nabla> [x].A \<RM> \<Rightarrow>* \<Empt>)" using `r=  (ps,c)` by (cases) auto
             with sw have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by auto
            }
         moreover
            {assume "\<not> leftPrincipal r (F \<nabla> [x].A)"
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using nonPrincipalInvertLeft[where r=r and F=F and x=x and A=A and ps=ps and c=c and R=R
                                                and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3
                                                and S=S and Ps=Ps and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and n=n and n'=n']
                  and `n = Suc n'` and `Ps \<noteq> []` and a' and b' and e'
                  and c' and rules and IH and `r \<in> R1` and d' and `r = (ps,c)` by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast         
        }
     moreover
        {assume "r \<in> R2"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> nprovRules" using rules and `r \<in> R2` by auto
         have "leftPrincipal r (F \<nabla> [x].A) \<or> \<not> leftPrincipal r (F \<nabla> [x].A)" by blast
         moreover
            {assume "leftPrincipal r (F \<nabla> [x].A)"
             then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using b' and `r = (ps,c)` and `r \<in> R2` and rules
                  by auto
             then have "extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" using `extendRule S r = (Ps,\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)`
                  and `r = (ps,c)` by (simp add:extendContain)
             moreover from `leftPrincipal r (F \<nabla> [x].A)` have "c = (\<LM>F \<nabla> [x].A\<RM> \<Rightarrow>* \<Empt>)" 
                  using `r = (ps,c)` by (cases) auto
             with `extendRule S r = (Ps,\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)` have "S = (\<Gamma> \<Rightarrow>* \<Delta>)"
                  using `r = (ps,c)` apply (auto simp add:extendRule_def extend_def) by (cases S) auto
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
             then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using `\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*` by auto
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using `n = Suc n'`
                  by (auto,rule_tac x=m in exI) (simp)
            }
         moreover
            {assume "\<not> leftPrincipal r (F \<nabla> [x].A)"
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using nonPrincipalInvertLeft[where r=r and F=F and x=x and A=A and ps=ps and c=c and R=R
                                                and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3
                                                and S=S and Ps=Ps and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and n=n and n'=n']
                  and `n = Suc n'` and `Ps \<noteq> []` and a' and b' and e'
                  and c' and rules and IH and `r \<in> R2` and d' and `r = (ps,c)` by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
        }
     moreover
        {assume "r \<in> R3"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> provRules" using rules and `r \<in> R3` by auto
         have "leftPrincipal r (F \<nabla> [x].A) \<or> \<not> leftPrincipal r (F \<nabla> [x].A)" by blast
         moreover
            {assume "leftPrincipal r (F \<nabla> [x].A)"
             then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using b' and `r = (ps,c)` and `r \<in> R3` and rules
                  by auto
             then have "extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" using `extendRule S r = (Ps,\<Gamma> \<oplus> F \<nabla> [x].A \<Rightarrow>* \<Delta>)`
                  and `r = (ps,c)` by (simp add:extendContain)
             moreover from `leftPrincipal r (F \<nabla> [x].A)` have "c = (\<LM>F \<nabla> [x].A\<RM> \<Rightarrow>* \<Empt>)" 
                  using `r = (ps,c)` by (cases) auto
             with `extendRule S r = (Ps,\<Gamma> \<oplus> F \<nabla> [x].A\<Rightarrow>* \<Delta>)` have "S = (\<Gamma> \<Rightarrow>* \<Delta>)"
                  using `r = (ps,c)` apply (auto simp add:extendRule_def extend_def) by (cases S) auto
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
             then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using `\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*` by auto
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using `n = Suc n'`
                  by (auto,rule_tac x=m in exI) (simp)
            }
         moreover
            {assume "\<not> leftPrincipal r (F \<nabla> [x].A)"
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using nonPrincipalInvertLeft[where r=r and F=F and x=x and A=A and ps=ps and c=c and R=R
                                                and \<Gamma>'=\<Gamma>' and \<Delta>'=\<Delta>' and ?R1.0=R1 and ?R2.0=R2 and ?R3.0=R3
                                                and S=S and Ps=Ps and \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and n=n and n'=n']
                  and `n = Suc n'` and `Ps \<noteq> []` and a' and b' and e'
                  and c' and rules and IH and `r \<in> R3` and d' and `r = (ps,c)` by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
        }
     ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
   qed
qed
(*>*)

text{*
\noindent In both cases, the assumption labelled $c$ captures the ``no specific substitution'' condition.  Interestingly, it is never used throughout the proof.  This highlights the difference between the object- and meta-level existential quantifiers.

Owing to the lack of indexing within datatypes, it is difficult to give an example demonstrating these results.  It would be little effort to change the theory file to accommodate type variables when they are supported in \textit{Nominal Isabelle}, at which time an example would be simple to write.  
*}
(*<*)
end
(*>*)