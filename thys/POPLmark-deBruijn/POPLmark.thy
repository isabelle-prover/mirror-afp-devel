(*  Title:      POPLmark/POPLmark.thy
    ID:         $Id: POPLmark.thy,v 1.1 2007-08-16 13:04:18 nipkow Exp $
    Author:     Stefan Berghofer, TU Muenchen, 2005
*)
(*<*)
theory POPLmark
imports Basis
begin
(*>*)

section {* Formalization of the basic calculus *}

text {*
\label{sec:basic-calculus}
In this section, we describe the formalization of the basic calculus
without records. As a main result, we prove {\it type safety}, presented
as two separate theorems, namely {\it preservation} and {\it progress}.
*}


subsection {* Types and Terms *}

text {*
The types of System \fsub{} are represented by the following datatype:
*}

datatype type =
    TVar nat
  | Top
  | Fun type type    (infixr "\<rightarrow>" 200)
  | TyAll type type  ("(3\<forall><:_./ _)" [0, 10] 10)

text {*
The subtyping and typing judgements depend on a {\it context} (or environment) @{term \<Gamma>}
containing bindings for term and type variables. A context is a list of bindings,
where the @{term i}th element @{term "\<Gamma>\<langle>i\<rangle>"} corresponds to the variable
with index @{term i}.
*}

datatype binding = VarB type | TVarB type
types env = "binding list"

text {*
In contrast to the usual presentation of type systems often found in textbooks, new
elements are added to the left of a context using the @{text Cons} operator @{text "\<Colon>"} for lists.
We write @{term is_TVarB} for the predicate that returns @{term True} when applied to
a type variable binding, function @{term type_ofB} extracts the type contained in a binding,
and @{term "mapB f"} applies @{term f} to the type contained in a binding.
*}

consts
  is_TVarB :: "binding \<Rightarrow> bool"
  type_ofB :: "binding \<Rightarrow> type"
  mapB :: "(type \<Rightarrow> type) \<Rightarrow> binding \<Rightarrow> binding"

primrec
  "is_TVarB (VarB T) = False"
  "is_TVarB (TVarB T) = True"

primrec
  "type_ofB (VarB T) = T"
  "type_ofB (TVarB T) = T"

primrec
  "mapB f (VarB T) = VarB (f T)"
  "mapB f (TVarB T) = TVarB (f T)"

text {*
The following datatype represents the terms of System \fsub{}:
*}

datatype trm =
    Var nat
  | Abs type trm   ("(3\<lambda>:_./ _)" [0, 10] 10)
  | TAbs type trm  ("(3\<lambda><:_./ _)" [0, 10] 10)
  | App trm trm    (infixl "\<bullet>" 200)
  | TApp trm type  (infixl "\<bullet>\<^isub>\<tau>" 200)


subsection {* Lifting and Substitution *}

text {*
One of the central operations of $\lambda$-calculus is {\it substitution}.
In order to avoid that free variables in a term or type get ``captured''
when substituting it for a variable occurring in the scope of a binder,
we have to increment the indices of its free variables during substitution.
This is done by the lifting functions @{text "\<up>\<^isub>\<tau> n k"} and @{text "\<up> n k"}
for types and terms, respectively, which increment the indices of all free
variables with indices @{text "\<ge> k"} by @{term n}. The lifting functions on
types and terms are defined by
*}

consts liftT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type" ("\<up>\<^isub>\<tau>")
primrec
  "\<up>\<^isub>\<tau> n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
  "\<up>\<^isub>\<tau> n k Top = Top"
  "\<up>\<^isub>\<tau> n k (T \<rightarrow> U) = \<up>\<^isub>\<tau> n k T \<rightarrow> \<up>\<^isub>\<tau> n k U"
  "\<up>\<^isub>\<tau> n k (\<forall><:T. U) = (\<forall><:\<up>\<^isub>\<tau> n k T. \<up>\<^isub>\<tau> n (k + 1) U)"

consts lift :: "nat \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm" ("\<up>")
primrec
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
  "\<up> n k (\<lambda>:T. t) = (\<lambda>:\<up>\<^isub>\<tau> n k T. \<up> n (k + 1) t)"
  "\<up> n k (\<lambda><:T. t) = (\<lambda><:\<up>\<^isub>\<tau> n k T. \<up> n (k + 1) t)"
  "\<up> n k (s \<bullet> t) = \<up> n k s \<bullet> \<up> n k t"
  "\<up> n k (t \<bullet>\<^isub>\<tau> T) = \<up> n k t \<bullet>\<^isub>\<tau> \<up>\<^isub>\<tau> n k T"

text {*
It is useful to also define an ``unlifting'' function @{text "\<down>\<^isub>\<tau> n k"} for
decrementing all free variables with indices @{text "\<ge> k"} by @{term n}.
Moreover, we need several substitution functions, denoted by
\mbox{@{text "T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>"}}, \mbox{@{text "t[k \<mapsto>\<^isub>\<tau> S]"}}, and \mbox{@{text "t[k \<mapsto> s]"}},
which substitute type variables in types, type variables in terms,
and term variables in terms, respectively. They are defined as follows:
*}

consts substTT :: "type \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("_[_ \<mapsto>\<^isub>\<tau> _]\<^isub>\<tau>" [300, 0, 0] 300)
primrec
  "(TVar i)[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> =
     (if k < i then TVar (i - 1) else if i = k then \<up>\<^isub>\<tau> k 0 S else TVar i)"
  "Top[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> = Top"
  "(T \<rightarrow> U)[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> = T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> \<rightarrow> U[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>"
  "(\<forall><:T. U)[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> = (\<forall><:T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>. U[k+1 \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>)"

consts decT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("\<down>\<^isub>\<tau>")
primrec
  "\<down>\<^isub>\<tau> 0 k T = T"
  "\<down>\<^isub>\<tau> (Suc n) k T = \<down>\<^isub>\<tau> n k (T[k \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>)"

consts subst :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm"  ("_[_ \<mapsto> _]" [300, 0, 0] 300)
primrec
  "(Var i)[k \<mapsto> s] = (if k < i then Var (i - 1) else if i = k then \<up> k 0 s else Var i)"
  "(t \<bullet> u)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet> u[k \<mapsto> s]"
  "(t \<bullet>\<^isub>\<tau> T)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet>\<^isub>\<tau> \<down>\<^isub>\<tau> 1 k T"
  "(\<lambda>:T. t)[k \<mapsto> s] = (\<lambda>:\<down>\<^isub>\<tau> 1 k T. t[k+1 \<mapsto> s])"
  "(\<lambda><:T. t)[k \<mapsto> s] = (\<lambda><:\<down>\<^isub>\<tau> 1 k T. t[k+1 \<mapsto> s])"

consts substT :: "trm \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> trm"    ("_[_ \<mapsto>\<^isub>\<tau> _]" [300, 0, 0] 300)
primrec
  "(Var i)[k \<mapsto>\<^isub>\<tau> S] = (if k < i then Var (i - 1) else Var i)"
  "(t \<bullet> u)[k \<mapsto>\<^isub>\<tau> S] = t[k \<mapsto>\<^isub>\<tau> S] \<bullet> u[k \<mapsto>\<^isub>\<tau> S]"
  "(t \<bullet>\<^isub>\<tau> T)[k \<mapsto>\<^isub>\<tau> S] = t[k \<mapsto>\<^isub>\<tau> S] \<bullet>\<^isub>\<tau> T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>"
  "(\<lambda>:T. t)[k \<mapsto>\<^isub>\<tau> S] = (\<lambda>:T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>. t[k+1 \<mapsto>\<^isub>\<tau> S])"
  "(\<lambda><:T. t)[k \<mapsto>\<^isub>\<tau> S] = (\<lambda><:T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>. t[k+1 \<mapsto>\<^isub>\<tau> S])"

text {*
Lifting and substitution extends to typing contexts as follows:
*}

consts liftE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env" ("\<up>\<^isub>e")
primrec
  "\<up>\<^isub>e n k [] = []"
  "\<up>\<^isub>e n k (B \<Colon> \<Gamma>) = mapB (\<up>\<^isub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<up>\<^isub>e n k \<Gamma>"

consts substE :: "env \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> env"  ("_[_ \<mapsto>\<^isub>\<tau> _]\<^isub>e" [300, 0, 0] 300)
primrec
  "[][k \<mapsto>\<^isub>\<tau> T]\<^isub>e = []"
  "(B \<Colon> \<Gamma>)[k \<mapsto>\<^isub>\<tau> T]\<^isub>e = mapB (\<lambda>U. U[k + \<parallel>\<Gamma>\<parallel> \<mapsto>\<^isub>\<tau> T]\<^isub>\<tau>) B \<Colon> \<Gamma>[k \<mapsto>\<^isub>\<tau> T]\<^isub>e"

consts decE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env"  ("\<down>\<^isub>e")
primrec
  "\<down>\<^isub>e 0 k \<Gamma> = \<Gamma>"
  "\<down>\<^isub>e (Suc n) k \<Gamma> = \<down>\<^isub>e n k (\<Gamma>[k \<mapsto>\<^isub>\<tau> Top]\<^isub>e)"

text {*
Note that in a context of the form @{term "B \<Colon> \<Gamma>"}, all variables in @{term B} with
indices smaller than the length of @{term \<Gamma>} refer to entries in @{term \<Gamma>} and therefore
must not be affected by substitution and lifting. This is the reason why an
additional offset @{term "\<parallel>\<Gamma>\<parallel>"} needs to be added to the index @{term k}
in the second clauses of the above functions. Some standard properties of lifting
and substitution, which can be proved by structural induction on terms and types,
are proved below. Properties of this kind are
quite standard for encodings using de Bruijn indices and can also be found in
papers by Barras and Werner \cite{Barras-Werner-JAR} and Nipkow \cite{Nipkow-JAR01}.
*}

lemma liftE_length [simp]: "\<parallel>\<up>\<^isub>e n k \<Gamma>\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma substE_length [simp]: "\<parallel>\<Gamma>[k \<mapsto>\<^isub>\<tau> U]\<^isub>e\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma liftE_nth [simp]:
  "(\<up>\<^isub>e n k \<Gamma>)\<langle>i\<rangle> = option_map (mapB (\<up>\<^isub>\<tau> n (k + \<parallel>\<Gamma>\<parallel> - i - 1))) (\<Gamma>\<langle>i\<rangle>)"
  apply (induct \<Gamma> arbitrary: i)
  apply simp
  apply simp
  apply (case_tac i)
  apply simp
  apply simp
  done

lemma substE_nth [simp]:
  "(\<Gamma>[0 \<mapsto>\<^isub>\<tau> T]\<^isub>e)\<langle>i\<rangle> = option_map (mapB (\<lambda>U. U[\<parallel>\<Gamma>\<parallel> - i - 1 \<mapsto>\<^isub>\<tau> T]\<^isub>\<tau>)) (\<Gamma>\<langle>i\<rangle>)"
  apply (induct \<Gamma> arbitrary: i)
  apply simp
  apply simp
  apply (case_tac i)
  apply simp
  apply simp
  done

lemma liftT_liftT [simp]:
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^isub>\<tau> n j (\<up>\<^isub>\<tau> m i T) = \<up>\<^isub>\<tau> (m + n) i T"
  by (induct T arbitrary: i j m n) simp_all

lemma liftT_liftT' [simp]:
  "i + m \<le> j \<Longrightarrow> \<up>\<^isub>\<tau> n j (\<up>\<^isub>\<tau> m i T) = \<up>\<^isub>\<tau> m i (\<up>\<^isub>\<tau> n (j - m) T)"
  apply (induct T arbitrary: i j m n)
  apply simp_all
  apply arith
  apply (subgoal_tac "Suc j - m = Suc (j - m)")
  apply simp
  apply arith
  done

lemma lift_size [simp]: "size (\<up>\<^isub>\<tau> n k T) = size T"
  by (induct T arbitrary: k) simp_all

lemma liftT0 [simp]: "\<up>\<^isub>\<tau> 0 i T = T"
  by (induct T arbitrary: i) simp_all

lemma lift0 [simp]: "\<And>i. \<up> 0 i t = t"
  by (induct t arbitrary: i) simp_all

theorem substT_liftT [simp]:
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^isub>\<tau> n k T)[k' \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau> = \<up>\<^isub>\<tau> (n - 1) k T"
  by (induct T arbitrary: k k') simp_all

theorem liftT_substT [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^isub>\<tau> n k (T[k' \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau>) = \<up>\<^isub>\<tau> n k T[k' + n \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  done

theorem liftT_substT' [simp]: "k' < k \<Longrightarrow>
  \<up>\<^isub>\<tau> n k (T[k' \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau>) = \<up>\<^isub>\<tau> n (k + 1) T[k' \<mapsto>\<^isub>\<tau> \<up>\<^isub>\<tau> n (k - k') U]\<^isub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  apply arith
  done

lemma liftT_substT_Top [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^isub>\<tau> n k' (T[k \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>) = \<up>\<^isub>\<tau> n (Suc k') T[k \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  apply arith
  done

lemma liftT_substT_strange:
  "\<up>\<^isub>\<tau> n k T[n + k \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau> = \<up>\<^isub>\<tau> n (Suc k) T[k \<mapsto>\<^isub>\<tau> \<up>\<^isub>\<tau> n 0 U]\<^isub>\<tau>"
  apply (induct T arbitrary: n k)
  apply simp_all
  apply (thin_tac "\<And>x. PROP ?P x")
  apply (drule_tac x=n in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply simp
  done

lemma lift_lift [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up> n' k' (\<up> n k t) = \<up> (n + n') k t"
  by (induct t arbitrary: k k') simp_all

lemma substT_substT:
  "i \<le> j \<Longrightarrow> T[Suc j \<mapsto>\<^isub>\<tau> V]\<^isub>\<tau>[i \<mapsto>\<^isub>\<tau> U[j - i \<mapsto>\<^isub>\<tau> V]\<^isub>\<tau>]\<^isub>\<tau> = T[i \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau>[j \<mapsto>\<^isub>\<tau> V]\<^isub>\<tau>"
  apply (induct T arbitrary: i j U V)
  apply (simp_all add: diff_Suc split add: nat.split)
  apply (thin_tac "\<And>x. PROP ?P x")
  apply (drule_tac x="Suc i" in meta_spec)
  apply (drule_tac x="Suc j" in meta_spec)
  apply simp
  done


subsection {* Well-formedness *}

text {*
\label{sec:wf}
The subtyping and typing judgements to be defined in \secref{sec:subtyping}
and \secref{sec:typing} may only operate on types and contexts that
are well-formed. Intuitively, a type @{term T} is well-formed with respect to a
context @{term \<Gamma>}, if all variables occurring in it are defined in @{term \<Gamma>}.
More precisely, if @{term T} contains a type variable @{term "TVar i"}, then
the @{term i}th element of @{term \<Gamma>} must exist and have the form @{term "TVarB U"}.
*}

inductive
  well_formed :: "env \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile>\<^bsub>wf\<^esub> _" [50, 50] 50)
where
  wf_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> TVar i"
| wf_Top: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> Top"
| wf_arrow: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<rightarrow> U"
| wf_all: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> (\<forall><:T. U)"

text {*
A context @{term "\<Gamma>"} is well-formed, if all types occurring in it only refer to type variables
declared ``further to the right'':
*}

inductive
  well_formedE :: "env \<Rightarrow> bool"  ("_ \<turnstile>\<^bsub>wf\<^esub>" [50] 50)
  and well_formedB :: "env \<Rightarrow> binding \<Rightarrow> bool"  ("_ \<turnstile>\<^bsub>wfB\<^esub> _" [50, 50] 50)
where
  "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B \<equiv> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> type_ofB B"
| wf_Nil: "[] \<turnstile>\<^bsub>wf\<^esub>"
| wf_Cons: "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"

text {*
The judgement @{text "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B"}, which denotes well-formedness of the binding @{term B}
with respect to context @{term \<Gamma>}, is just an abbreviation for @{text "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> type_ofB B"}.
We now present a number of properties of the well-formedness judgements that will be used
in the proofs in the following sections.
*}

inductive_cases well_formed_cases:
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> TVar i"
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> Top"
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<rightarrow> U"
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> (\<forall><:T. U)"

inductive_cases well_formedE_cases:
  "B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"

lemma wf_TVarB: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
  by (rule wf_Cons) simp_all

lemma wf_VarB: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> VarB T \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
  by (rule wf_Cons) simp_all

lemma map_is_TVarb:
  "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow>
    \<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<exists>T. \<Gamma>'\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor>"
  apply (induct \<Gamma> arbitrary: \<Gamma>' T i)
  apply simp
  apply (auto split add: nat.split_asm)
  apply (case_tac z)
  apply simp_all
  done

text {*
A type that is well-formed in a context @{term \<Gamma>} is also well-formed in another context
@{term \<Gamma>'} that contains type variable bindings at the same positions as @{term \<Gamma>}:
*}

lemma wf_equallength:
  assumes H: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T"
  shows "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile>\<^bsub>wf\<^esub> T" using H
  by (induct arbitrary: \<Gamma>') (auto intro: well_formed.intros dest: map_is_TVarb)

text {*
A well-formed context of the form @{term "\<Delta> @ B \<Colon> \<Gamma>"} remains well-formed if we replace
the binding @{term B} by another well-formed binding @{term B'}:
*}

lemma wfE_replace:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B' \<Longrightarrow> is_TVarB B' = is_TVarB B \<Longrightarrow>
    \<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
  apply (induct \<Delta>)
  apply simp
  apply (erule wf_Cons)
  apply (erule well_formedE_cases)
  apply assumption
  apply simp
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply (case_tac a)
  apply simp
  apply (rule wf_equallength)
  apply assumption
  apply simp
  apply simp
  apply (rule wf_equallength)
  apply assumption
  apply simp
  apply simp
  done

text {*
The following weakening lemmas can easily be proved by structural induction on
types and contexts:
*}

lemma wf_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T"
  shows "\<up>\<^isub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<up>\<^isub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T"
  using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ \<Gamma>" T arbitrary: \<Gamma> \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (rule wf_TVar)
  apply simp
  apply (rule impI)
  apply (rule wf_TVar)
  apply (subgoal_tac "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)")
  apply simp
  apply arith
  apply (rule wf_Top)
  apply (rule wf_arrow)
  apply simp
  apply simp
  apply (rule wf_all)
  apply simp
  apply (thin_tac "\<And>x. PROP ?P x")
  apply (drule_tac x="\<Gamma>'" in meta_spec)
  apply (drule_tac x="TVarB T \<Colon> \<Delta>" in meta_spec)
  apply simp
  done

lemma wf_weaken': "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<up>\<^isub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta>)
  apply simp_all
  apply (drule_tac B=a in wf_weaken [of "[]", simplified])
  apply simp
  done

lemma wfE_weaken: "\<Delta> @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B \<Longrightarrow> \<up>\<^isub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
  apply (induct \<Delta>)
  apply simp
  apply (rule wf_Cons)
  apply assumption+
  apply simp
  apply (rule wf_Cons)
  apply (erule well_formedE_cases)
  apply (case_tac a)
  apply simp
  apply (rule wf_weaken)
  apply assumption
  apply simp
  apply (rule wf_weaken)
  apply assumption
  apply (erule well_formedE_cases)
  apply simp
  done

text {*
Intuitively, lemma @{text wf_weaken} states that a type @{term T} which is well-formed
in a context is still well-formed in a larger context, whereas lemma @{text wfE_weaken}
states that a well-formed context remains well-formed when extended with a
well-formed binding. Owing to the encoding of variables using de Bruijn
indices, the statements of the above lemmas involve additional lifting functions.
The typing judgement, which will be described in \secref{sec:typing}, involves
the lookup of variables in a context. It has already been pointed out earlier that each
entry in a context may only depend on types declared ``further to the right''. To ensure that
a type @{term T} stored at position @{term i} in an environment @{term \<Gamma>} is valid in the full
environment, as opposed to the smaller environment consisting only of the entries in
@{term \<Gamma>} at positions greater than @{term i}, we need to increment the indices of all
free type variables in @{term T} by @{term "Suc i"}:
*}

lemma wf_liftB:
  assumes H: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
  shows "\<Gamma>\<langle>i\<rangle> = \<lfloor>VarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<up>\<^isub>\<tau> (Suc i) 0 T"
  using H
  apply (induct arbitrary: i)
  apply simp
  apply (simp split add: nat.split_asm)
  apply (frule_tac B="VarB T" in wf_weaken [of "[]", simplified])
  apply simp+
  apply (drule_tac x=nat in meta_spec)
  apply simp
  apply (frule_tac T="\<up>\<^isub>\<tau> (Suc nat) 0 T" in wf_weaken [of "[]", simplified])
  apply simp
  done

text {*
We also need lemmas stating that substitution of well-formed types preserves the well-formedness
of types and contexts:
*}

theorem wf_subst:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^isub>\<tau> U]\<^isub>e @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> U]\<^isub>\<tau>"
  apply (induct T arbitrary: \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (frule_tac T=U and B=B in wf_weaken [of "[]", simplified])
  apply simp
  apply (drule_tac \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^isub>\<tau> U]\<^isub>e" in wf_weaken')
  apply simp
  apply (rule impI conjI)+
  apply (erule well_formed_cases)
  apply (rule wf_TVar)
  apply (simp split add: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> nat - Suc 0")
  apply (subgoal_tac "nat - Suc \<parallel>\<Delta>\<parallel> = nata")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (rule impI)
  apply (erule well_formed_cases)
  apply (rule wf_TVar)
  apply simp
  apply (rule wf_Top)
  apply (erule well_formed_cases)
  apply (rule wf_arrow)
  apply simp+
  apply (erule well_formed_cases)
  apply (rule wf_all)
  apply simp
  apply (thin_tac "\<And>x. PROP ?P x")
  apply (drule_tac x="TVarB T1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  done

theorem wfE_subst: "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^isub>\<tau> U]\<^isub>e @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
  apply (induct \<Delta>)
  apply simp
  apply (erule well_formedE_cases)
  apply assumption
  apply simp
  apply (case_tac a)
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply simp
  apply (rule wf_subst)
  apply assumption+
  apply simp
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply simp
  apply (rule wf_subst)
  apply assumption+
  done


subsection {* Subtyping *}

text {*
\label{sec:subtyping}
We now come to the definition of the subtyping judgement @{text "\<Gamma> \<turnstile> T <: U"}.
*}

inductive
  subtyping :: "env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ <: _" [50, 50, 50] 50)
where
  SA_Top: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> S \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> TVar i \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: TVar i"
| SA_trans_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB U\<rfloor> \<Longrightarrow>
    \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (Suc i) 0 U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: T"
| SA_arrow: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1 \<rightarrow> T\<^isub>2"
| SA_all: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1 \<Longrightarrow> TVarB T\<^isub>1 \<Colon> \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (\<forall><:S\<^isub>1. S\<^isub>2) <: (\<forall><:T\<^isub>1. T\<^isub>2)"

text {*
The rules @{text SA_Top} and @{text SA_refl_TVar}, which appear at the leaves of
the derivation tree for a judgement @{term "\<Gamma> \<turnstile> T <: U"}, contain additional
side conditions ensuring the well-formedness of the contexts and types involved.
In order for the rule @{text SA_trans_TVar} to be applicable, the context @{term \<Gamma>}
must be of the form \mbox{@{term "\<Gamma>\<^isub>1 @ B \<Colon> \<Gamma>\<^isub>2"}}, where @{term "\<Gamma>\<^isub>1"} has the length @{term i}.
Since the indices of variables in @{term B} can only refer to variables defined in
@{term "\<Gamma>\<^isub>2"}, they have to be incremented by @{term "Suc i"} to ensure that they point
to the right variables in the larger context @{text \<Gamma>}.
*}

lemma wf_subtype_env:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^bsub>wf\<^esub>" using PQ
  by induct assumption+

lemma wf_subtype:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> P \<and> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> Q" using PQ
  by induct (auto intro: well_formed.intros elim!: wf_equallength)

lemma wf_subtypeE:
  assumes H: "\<Gamma> \<turnstile> T <: U"
  and H': "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> P"
  shows "P"
  apply (rule H')
  apply (rule wf_subtype_env)
  apply (rule H)
  apply (rule wf_subtype [OF H, THEN conjunct1])
  apply (rule wf_subtype [OF H, THEN conjunct2])
  done

text {*
By induction on the derivation of @{term "\<Gamma> \<turnstile> T <: U"}, it can easily be shown
that all types and contexts occurring in a subtyping judgement must be well-formed:
*}

lemma wf_subtype_conj:
  "\<Gamma> \<turnstile> T <: U \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<and> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<and> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U"
  by (erule wf_subtypeE) iprover

text {*
By induction on types, we can prove that the subtyping relation is reflexive:
*}

lemma subtype_refl: -- {* A.1 *}
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
  by (induct T arbitrary: \<Gamma>) (blast intro:
    subtyping.intros wf_Nil wf_TVarB elim: well_formed_cases)+

text {*
The weakening lemma for the subtyping relation is proved in two steps:
by induction on the derivation of the subtyping relation, we first prove
that inserting a single type into the context preserves subtyping:
*}

lemma subtype_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile> P <: Q"
  and wf: "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B"
  shows "\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> P <: \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> Q" using H
proof (induct \<Gamma>' \<equiv> "\<Delta> @ \<Gamma>" P Q arbitrary: \<Delta>)
  case SA_Top
  with wf show ?case
    by (auto intro: subtyping.SA_Top wfE_weaken wf_weaken)
next
  case SA_refl_TVar
  then show ?case
    by (auto intro!: subtyping.SA_refl_TVar wfE_weaken dest: wf_weaken)
next
  case (SA_trans_TVar \<Gamma>' i U T \<Delta>)
  thus ?case
  proof (cases "i < \<parallel>\<Delta>\<parallel>")
    case True
    with SA_trans_TVar
    have "(\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB (\<up>\<^isub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U)\<rfloor>"
      by simp
    moreover from True SA_trans_TVar SA_trans_TVar(3) [OF SA_trans_TVar(4)]
    have "\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>
      \<up>\<^isub>\<tau> (Suc i) 0 (\<up>\<^isub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U) <: \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar i <: \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with True show ?thesis by simp
  next
    case False
    then have "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)" by arith
    with False SA_trans_TVar have "(\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>Suc i\<rangle> = \<lfloor>TVarB U\<rfloor>"
      by simp
    moreover from False SA_trans_TVar SA_trans_TVar(3) [OF SA_trans_TVar(4)]
    have "\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (Suc (Suc i)) 0 U <: \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar (Suc i) <: \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with False show ?thesis by simp
  qed
next
  case SA_arrow
  thus ?case by simp (iprover intro: subtyping.SA_arrow)
next
  case (SA_all \<Gamma>' T\<^isub>1 S\<^isub>1 S\<^isub>2 T\<^isub>2 \<Delta>)
  with SA_all(4) [of "TVarB T\<^isub>1 \<Colon> \<Delta>"]
  show ?case by simp (iprover intro: subtyping.SA_all)
qed

text {*
All cases are trivial, except for the @{text SA_trans_TVar} case, which
requires a case distinction on whether the index of the variable is smaller
than @{term "\<parallel>\<Delta>\<parallel>"}.
The stronger result that appending a new context @{term \<Delta>} to a context
@{term \<Gamma>} preserves subtyping can be proved by induction on @{term \<Delta>},
using the previous result in the induction step:
*}

lemma subtype_weaken': -- {* A.2 *}
  "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up>\<^isub>\<tau> \<parallel>\<Delta>\<parallel> 0 P <: \<up>\<^isub>\<tau> \<parallel>\<Delta>\<parallel> 0 Q"
  apply (induct \<Delta>)
  apply simp_all
  apply (erule well_formedE_cases)
  apply simp
  apply (drule_tac B="a" and \<Gamma>="\<Delta> @ \<Gamma>" in subtype_weaken [of "[]", simplified])
  apply simp_all
  done

text {*
An unrestricted transitivity rule has the disadvantage that it can
be applied in any situation. In order to make the above definition of the
subtyping relation {\it syntax-directed}, the transitivity rule @{text "SA_trans_TVar"}
is restricted to the case where the type on the left-hand side of the @{text "<:"}
operator is a variable. However, the unrestricted transitivity rule
can be derived from this definition.
In order for the proof to go through, we have to simultaneously prove
another property called {\it narrowing}.
The two properties are proved by nested induction. The outer induction
is on the size of the type @{term Q}, whereas the two inner inductions for
proving transitivity and narrowing are on the derivation of the
subtyping judgements. The transitivity property is needed in the proof of
narrowing, which is by induction on the derivation of \mbox{@{term "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> M <: N"}}.
In the case corresponding to the rule @{text SA_trans_TVar}, we must prove
\mbox{@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> TVar i <: T"}}. The only interesting case
is the one where @{term "i = \<parallel>\<Delta>\<parallel>"}. By induction hypothesis, we know that
@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (i+1) 0 Q <: T"} and
@{term "(\<Delta> @ TVarB Q \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB Q\<rfloor>"}.
By assumption, we have @{term "\<Gamma> \<turnstile> P <: Q"} and hence 
\mbox{@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (i+1) 0 P <: \<up>\<^isub>\<tau> (i+1) 0 Q"}} by weakening.
Since @{term "\<up>\<^isub>\<tau> (i+1) 0 Q"} has the same size as @{term Q}, we can use
the transitivity property, which yields
@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (i+1) 0 P <: T"}. The claim then follows
easily by an application of @{text SA_trans_TVar}.
*}

lemma subtype_trans: -- {* A.3 *}
  "\<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
  using wf_measure_size
proof (induct Q arbitrary: \<Gamma> S T \<Delta> P M N rule: wf_induct_rule)
  case (less Q)
  {
    fix \<Gamma> S T Q'
    assume "\<Gamma> \<turnstile> S <: Q'"
    then have "\<Gamma> \<turnstile> Q' <: T \<Longrightarrow> size Q = size Q' \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    proof (induct arbitrary: T)
      case SA_Top
      from SA_Top(3) show ?case
	by cases (auto intro: subtyping.SA_Top SA_Top)
    next
      case SA_refl_TVar show ?case .
    next
      case SA_trans_TVar
      thus ?case by (auto intro: subtyping.SA_trans_TVar)
    next
      case (SA_arrow \<Gamma> T\<^isub>1 S\<^isub>1 S\<^isub>2 T\<^isub>2)
      note SA_arrow' = SA_arrow
      from SA_arrow(5) show ?case
      proof cases
	case SA_Top
	with SA_arrow show ?thesis
	  by (auto intro: subtyping.SA_Top wf_arrow elim: wf_subtypeE)
      next
	case (SA_arrow \<Gamma>' T\<^isub>1' S\<^isub>1' S\<^isub>2' T\<^isub>2')
	from SA_arrow SA_arrow' have "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1' \<rightarrow> T\<^isub>2'"
	  by (auto intro!: subtyping.SA_arrow intro: less(1) [of "S\<^isub>1'"] less(1) [of "S\<^isub>2'"])
	with SA_arrow show ?thesis by simp
      qed simp_all
    next
      case (SA_all \<Gamma> T\<^isub>1 S\<^isub>1 S\<^isub>2 T\<^isub>2)
      note SA_all' = SA_all
      from SA_all(5) show ?case
      proof cases
	case SA_Top
	with SA_all show ?thesis by (auto intro!:
	  subtyping.SA_Top wf_all intro: wf_equallength elim: wf_subtypeE)
      next
	case (SA_all \<Gamma>' T\<^isub>1' S\<^isub>1' S\<^isub>2' T\<^isub>2')
	from SA_all SA_all' have "\<Gamma> \<turnstile> T\<^isub>1' <: S\<^isub>1"
	  by - (rule less(1), simp_all)
	moreover from SA_all SA_all' have "TVarB T\<^isub>1' \<Colon> \<Gamma> \<turnstile> S\<^isub>2 <: S\<^isub>2'"
	  by - (rule less(2) [of _ "[]", simplified], simp_all)
	with SA_all SA_all' have "TVarB T\<^isub>1' \<Colon> \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2'"
	  by - (rule less(1), simp_all)
	ultimately have "\<Gamma> \<turnstile> (\<forall><:S\<^isub>1. S\<^isub>2) <: (\<forall><:T\<^isub>1'. T\<^isub>2')"
	  by (rule subtyping.SA_all)
	with SA_all show ?thesis by simp
      qed simp_all
    qed
  }
  note tr = this
  {
    case 1
    thus ?case using refl by (rule tr)
  next
    case 2
    from 2(1) show "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
    proof (induct \<Gamma>' \<equiv> "\<Delta> @ TVarB Q \<Colon> \<Gamma>" M N arbitrary: \<Delta>)
      case SA_Top
      with 2 show ?case by (auto intro!: subtyping.SA_Top
	intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case SA_refl_TVar
      with 2 show ?case by (auto intro!: subtyping.SA_refl_TVar
	intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case (SA_trans_TVar \<Gamma>' i U T)
      show ?case
      proof (cases "i < \<parallel>\<Delta>\<parallel>")
	case True
	with SA_trans_TVar show ?thesis
	  by (auto intro!: subtyping.SA_trans_TVar)
      next
	case False
	note False' = False
	show ?thesis
	proof (cases "i = \<parallel>\<Delta>\<parallel>")
	  case True
	  from SA_trans_TVar have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"
	    by (auto elim!: wf_subtypeE)
	  with `\<Gamma> \<turnstile> P <: Q`
	  have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile> \<up>\<^isub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 P <: \<up>\<^isub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 Q"
	    by (rule subtype_weaken')
	  with SA_trans_TVar True False have "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (Suc \<parallel>\<Delta>\<parallel>) 0 P <: T"
	    by - (rule tr, simp+)
	  with True and False and SA_trans_TVar show ?thesis
	    by (auto intro!: subtyping.SA_trans_TVar)
	next
	  case False
	  with False' have "i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel> - 1)" by arith
	  with False False' SA_trans_TVar show ?thesis
	    by - (rule subtyping.SA_trans_TVar, simp+)
	qed
      qed
    next
      case SA_arrow
      thus ?case by (auto intro!: subtyping.SA_arrow)
    next
      case (SA_all \<Gamma> T\<^isub>1 S\<^isub>1 S\<^isub>2 T\<^isub>2)
      thus ?case by (auto intro: subtyping.SA_all
	SA_all(4) [of "TVarB T\<^isub>1 \<Colon> \<Delta>", simplified SA_all(5), simplified])
    qed
  }
qed

text {*
In the proof of the preservation theorem presented in \secref{sec:evaluation},
we will also need a substitution theorem, which is proved by
induction on the subtyping derivation:
*}

lemma substT_subtype: -- {* A.10 *}
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> S <: T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta>[0 \<mapsto>\<^isub>\<tau> P]\<^isub>e @ \<Gamma> \<turnstile> S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> P]\<^isub>\<tau> <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> P]\<^isub>\<tau>"
  using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ TVarB Q \<Colon> \<Gamma>" S T arbitrary: \<Delta>)
  apply simp_all
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule wf_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule impI conjI)+
  apply (rule subtype_refl)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule_tac T=P and \<Delta>="\<Delta>[0 \<mapsto>\<^isub>\<tau> P]\<^isub>e" in wf_weaken')
  apply simp
  apply (rule conjI impI)+
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply (rule impI)
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply (rule conjI impI)+
  apply (drule_tac x=\<Delta> in meta_spec)
  apply simp
  apply (drule_tac \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^isub>\<tau> P]\<^isub>e" in subtype_weaken')
  apply (erule wf_subtypeE)+
  apply assumption
  apply simp
  apply (rule subtype_trans(1))
  apply assumption+
  apply (rule conjI impI)+
  apply (rule SA_trans_TVar)
  apply (simp split add: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (drule_tac x=\<Delta> in meta_spec)
  apply simp
  apply (rule impI)
  apply (rule SA_trans_TVar)
  apply (simp split add: nat.split_asm)
  apply (drule_tac x=\<Delta> in meta_spec)
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply (rule SA_arrow)
  apply simp+
  apply (rule SA_all)
  apply simp
  apply (thin_tac "\<And>x. PROP ?P x")
  apply (drule_tac x="TVarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  done

lemma subst_subtype:
  assumes H: "\<Delta> @ VarB V \<Colon> \<Gamma> \<turnstile> T <: U"
  shows "\<down>\<^isub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> \<down>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T <: \<down>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> U"
  using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ VarB V \<Colon> \<Gamma>" T U arbitrary: \<Delta>)
  apply simp_all
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (rule wf_subst)
  apply assumption
  apply (rule wf_Top)
  apply (rule impI conjI)+
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)+
  apply (rule conjI impI)+
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule impI)
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule conjI impI)+
  apply simp
  apply (rule conjI impI)+
  apply (simp split add: nat.split_asm)
  apply (rule SA_trans_TVar)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (drule_tac x=\<Delta> in meta_spec)
  apply simp
  apply (rule impI)
  apply (rule SA_trans_TVar)
  apply simp
  apply (subgoal_tac "0 < \<parallel>\<Delta>\<parallel>")
  apply simp
  apply arith
  apply (rule SA_arrow)
  apply simp+
  apply (rule SA_all)
  apply simp
  apply (thin_tac "\<And>x. PROP ?P x")
  apply (drule_tac x="TVarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  done


subsection {* Typing *}

text {*
\label{sec:typing}
We are now ready to give a definition of the typing judgement @{text "\<Gamma> \<turnstile> t : T"}.
*}

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"    ("_ \<turnstile> _ : _" [50, 50, 50] 50)
where
  T_Var: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma>\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor> \<Longrightarrow> T = \<up>\<^isub>\<tau> (Suc i) 0 U \<Longrightarrow> \<Gamma> \<turnstile> Var i : T"
| T_Abs: "VarB T\<^isub>1 \<Colon> \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>:T\<^isub>1. t\<^isub>2) : T\<^isub>1 \<rightarrow> \<down>\<^isub>\<tau> 1 0 T\<^isub>2"
| T_App: "\<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1\<^isub>1 \<rightarrow> T\<^isub>1\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>1\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> t\<^isub>1 \<bullet> t\<^isub>2 : T\<^isub>1\<^isub>2"
| T_TAbs: "TVarB T\<^isub>1 \<Colon> \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda><:T\<^isub>1. t\<^isub>2) : (\<forall><:T\<^isub>1. T\<^isub>2)"
| T_TApp: "\<Gamma> \<turnstile> t\<^isub>1 : (\<forall><:T\<^isub>1\<^isub>1. T\<^isub>1\<^isub>2) \<Longrightarrow> \<Gamma> \<turnstile> T\<^isub>2 <: T\<^isub>1\<^isub>1 \<Longrightarrow>
    \<Gamma> \<turnstile> t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 : T\<^isub>1\<^isub>2[0 \<mapsto>\<^isub>\<tau> T\<^isub>2]\<^isub>\<tau>"
| T_Sub: "\<Gamma> \<turnstile> t : S \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> t : T"

text {*
Note that in the rule @{text T_Var}, the indices of the type @{term U} looked up in
the context @{term \<Gamma>} need to be incremented in order for the type to be well-formed
with respect to @{term \<Gamma>}. In the rule @{text T_Abs}, the type @{term "T\<^isub>2"} of the
abstraction body @{term "t\<^isub>2"} may not contain the variable with index @{text 0},
since it is a term variable. To compensate for the disappearance of the context
element @{term "VarB T\<^isub>1"} in the conclusion of thy typing rule, the indices of all
free type variables in @{term "T\<^isub>2"} have to be decremented by @{text 1}.
*}

theorem wf_typeE1:
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile>\<^bsub>wf\<^esub>" using H
  by induct (blast elim: well_formedE_cases)+

theorem wf_typeE2:
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T" using H
  apply induct
  apply simp
  apply (rule wf_liftB)
  apply assumption+
  apply (drule wf_typeE1)+
  apply (erule well_formedE_cases)+
  apply (rule wf_arrow)
  apply simp
  apply simp
  apply (rule wf_subst [of "[]", simplified])
  apply assumption
  apply (rule wf_Top)
  apply (erule well_formed_cases)
  apply assumption
  apply (rule wf_all)
  apply (drule wf_typeE1)
  apply (erule well_formedE_cases)
  apply simp  
  apply assumption
  apply (erule well_formed_cases)
  apply (rule wf_subst [of "[]", simplified])
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  done

text {*
Like for the subtyping judgement, we can again prove that all types and contexts
involved in a typing judgement are well-formed:
*}
lemma wf_type_conj: "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<and> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T"
  by (frule wf_typeE1, drule wf_typeE2) iprover

text {*
The narrowing theorem for the typing judgement states that replacing the type
of a variable in the context by a subtype preserves typability:
*}

lemma narrow_type: -- {* A.7 *}
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> t : T"
  using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T arbitrary: \<Delta>)
  apply simp_all
  apply (rule T_Var)
  apply (erule wfE_replace)
  apply (erule wf_subtypeE)
  apply simp+
  apply (case_tac "i < \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (case_tac "i = \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (simp split add: nat.split nat.split_asm)+
  apply (rule T_Abs [simplified])
  apply (drule_tac x="VarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^isub>1\<^isub>1=T\<^isub>1\<^isub>1 in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^isub>1\<^isub>1=T\<^isub>1\<^isub>1 in T_TApp)
  apply simp
  apply (rule subtype_trans(2))
  apply assumption+
  apply (rule_tac S=S in T_Sub)
  apply simp
  apply (rule subtype_trans(2))
  apply assumption+
  done

lemma subtype_refl':
  assumes t: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> T <: T"
proof (rule subtype_refl)
  from t show "\<Gamma> \<turnstile>\<^bsub>wf\<^esub>" by (rule wf_typeE1)
  from t show "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T" by (rule wf_typeE2)
qed

lemma Abs_type: -- {* A.13(1) *}
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t = (\<lambda>:S. s) \<Longrightarrow> \<Gamma> \<turnstile> T <: U \<rightarrow> U' \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      \<Gamma> \<turnstile> \<down>\<^isub>\<tau> 1 0 S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct arbitrary: U U' S s P, simp_all)
  case goal1
  from goal1(4)
  show ?case
    apply cases
    apply simp_all
    apply (rule goal1(5))
    apply simp
    apply assumption
    apply simp
    done
next
  case goal2
  show ?case
    apply (rule goal2(2))
    apply (rule conjI)
    apply (rule refl)+
    apply (rule subtype_trans(1))
    apply assumption+
    done
qed

lemma Abs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda>:S. s) : U \<rightarrow> U'"
  and R: "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
    \<Gamma> \<turnstile> \<down>\<^isub>\<tau> 1 0 S' <: U' \<Longrightarrow> P"
  shows "P" using H refl subtype_refl' [OF H]
  by (rule Abs_type) (rule R)

lemma TAbs_type: -- {* A.13(2) *}
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t = (\<lambda><:S. s) \<Longrightarrow> \<Gamma> \<turnstile> T <: (\<forall><:U. U') \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct arbitrary: U U' S s P, simp_all)
  case goal1
  from goal1(4)
  show ?case
    apply cases
    apply simp_all
    apply (rule goal1(5))
    apply simp
    apply (insert goal1(1))
    apply (erule narrow_type [of "[]", simplified])
    apply simp_all
    done
next
  case goal2
  show ?case
    apply (rule goal2(2))
    apply (rule conjI)
    apply (rule refl)+
    apply (rule subtype_trans(1))
    apply assumption+
    done
qed

lemma TAbs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda><:S. s) : (\<forall><:U. U')"
  and R: "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
    TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P"
  shows "P" using H refl subtype_refl' [OF H]
  by (rule TAbs_type) (rule R)

lemma T_eq: "\<Gamma> \<turnstile> t : T \<Longrightarrow> T = T' \<Longrightarrow> \<Gamma> \<turnstile> t : T'" by simp

text {*
The weakening theorem states that inserting a binding @{term B}
does not affect typing:
*}

lemma type_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B \<Longrightarrow>
    \<up>\<^isub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up> 1 \<parallel>\<Delta>\<parallel> t : \<up>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T" using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ \<Gamma>" t T arbitrary: \<Gamma> \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_weaken)
  apply simp+
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_weaken)
  apply assumption
  apply (subgoal_tac "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)")
  apply simp
  apply arith
  apply (rule refl)
  apply (rule T_Abs [THEN T_eq])
  apply (drule_tac x=\<Gamma>' in meta_spec)
  apply (drule_tac x="VarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply simp
  apply (rule_tac T\<^isub>1\<^isub>1="\<up>\<^isub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T\<^isub>1\<^isub>1" in T_App)
  apply simp
  apply simp
  apply (rule T_TAbs)
  apply (drule_tac x=\<Gamma>' in meta_spec)
  apply (drule_tac x="TVarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (drule_tac x=\<Gamma>' in meta_spec)
  apply (drule_tac x=\<Delta> in meta_spec)
  apply simp
  apply (erule_tac T_TApp [THEN T_eq])
  apply (drule subtype_weaken)
  apply simp+
  apply (case_tac \<Delta>)
  apply (simp add: liftT_substT_strange [of _ 0, simplified])+
  apply (rule_tac S="\<up>\<^isub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S" in T_Sub)
  apply simp
  apply (drule subtype_weaken)
  apply simp+
  done

text {*
We can strengthen this result, so as to mean that concatenating a new context
@{term \<Delta>} to the context @{term \<Gamma>} preserves typing:
*}

lemma type_weaken': -- {* A.5(6) *}
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up> \<parallel>\<Delta>\<parallel> 0 t : \<up>\<^isub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta>)
  apply simp
  apply simp
  apply (erule well_formedE_cases)
  apply simp
  apply (drule_tac B=a in type_weaken [of "[]", simplified])
  apply simp+
  done

text {*
This property is proved by structural induction on the context @{term \<Delta>},
using the previous result in the induction step. In the proof of the preservation
theorem, we will need two substitution theorems for term and type variables,
both of which are proved by induction on the typing derivation.
Since term and type variables are stored in the same context, we again have to
decrement the free type variables in @{term \<Delta>} and @{term T} by @{text 1}
in the substitution rule for term variables in order to compensate for the
disappearance of the variable.
*}

theorem subst_type: -- {* A.8 *}
  assumes H: "\<Delta> @ VarB U \<Colon> \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> u : U \<Longrightarrow>
    \<down>\<^isub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto> u] : \<down>\<^isub>\<tau> 1 \<parallel>\<Delta>\<parallel> T" using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ VarB U \<Colon> \<Gamma>" t T arbitrary: \<Delta>)
  apply simp
  apply (rule conjI)
  apply (rule impI)
  apply simp
  apply (drule_tac \<Delta>="\<Delta>[0 \<mapsto>\<^isub>\<tau> Top]\<^isub>e" in type_weaken')
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply simp
  apply (rule impI conjI)+
  apply (simp split add: nat.split_asm)
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply simp
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply simp
  apply (drule_tac x="VarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply (rule T_Abs [THEN T_eq])
  apply simp
  apply (simp add: substT_substT [symmetric])
  apply simp
  apply (rule_tac T\<^isub>1\<^isub>1="T\<^isub>1\<^isub>1[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>" in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply simp
  apply (drule_tac x=\<Delta> in meta_spec)
  apply (rule T_TApp [THEN T_eq])
  apply simp
  apply (rule subst_subtype [simplified])
  apply assumption
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac S="S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>" in T_Sub)
  apply simp
  apply simp
  apply (rule subst_subtype [simplified])
  apply assumption
  done

theorem substT_type:
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow>
    \<Delta>[0 \<mapsto>\<^isub>\<tau> P]\<^isub>e @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> P] : T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> P]\<^isub>\<tau>" using H
  apply (induct \<Gamma>' \<equiv> "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T arbitrary: \<Delta>)
  apply simp_all
  apply (rule impI conjI)+
  apply simp
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply (simp split add: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (case_tac "i = \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply simp
  apply (subgoal_tac "i < \<parallel>\<Delta>\<parallel>")
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (rule T_Abs [THEN T_eq])
  apply (drule_tac x="VarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac T\<^isub>1\<^isub>1="T\<^isub>1\<^isub>1[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> P]\<^isub>\<tau>" in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^isub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (drule_tac x=\<Delta> in meta_spec)
  apply (rule T_TApp [THEN T_eq])
  apply simp
  apply (rule substT_subtype)
  apply assumption
  apply assumption
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac S="S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^isub>\<tau> P]\<^isub>\<tau>" in T_Sub)
  apply simp
  apply (rule substT_subtype)
  apply assumption
  apply assumption
  done


subsection {* Evaluation *}

text {*
\label{sec:evaluation}
For the formalization of the evaluation strategy, it is useful to first define
a set of {\it canonical values} that are not evaluated any further. The canonical
values of call-by-value \fsub{} are exactly the abstractions over term and type variables:
*}

inductive_set
  "value" :: "trm set"
where
  Abs: "(\<lambda>:T. t) \<in> value"
| TAbs: "(\<lambda><:T. t) \<in> value"

text {*
The notion of a @{term value} is now used in the defintion of the evaluation
relation \mbox{@{text "t \<longmapsto> t'"}}. There are several ways for defining this evaluation
relation: Aydemir et al.\ \cite{PoplMark} advocate the use of {\it evaluation
contexts} that allow to separate the description of the ``immediate'' reduction rules,
i.e.\ $\beta$-reduction, from the description of the context in which these reductions
may occur in. The rationale behind this approach is to keep the formalization more modular.
We will take a closer look at this style of presentation in section
\secref{sec:evaluation-ctxt}. For the rest of this section, we will use a different
approach: both the ``immediate'' reductions and the reduction context are described
within the same inductive definition, where the context is described by additional
congruence rules.
*}

inductive
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool"  (infixl "\<longmapsto>" 50)
where
  E_Abs: "v\<^isub>2 \<in> value \<Longrightarrow> (\<lambda>:T\<^isub>1\<^isub>1. t\<^isub>1\<^isub>2) \<bullet> v\<^isub>2 \<longmapsto> t\<^isub>1\<^isub>2[0 \<mapsto> v\<^isub>2]"
| E_TAbs: "(\<lambda><:T\<^isub>1\<^isub>1. t\<^isub>1\<^isub>2) \<bullet>\<^isub>\<tau> T\<^isub>2 \<longmapsto> t\<^isub>1\<^isub>2[0 \<mapsto>\<^isub>\<tau> T\<^isub>2]"
| E_App1: "t \<longmapsto> t' \<Longrightarrow> t \<bullet> u \<longmapsto> t' \<bullet> u"
| E_App2: "v \<in> value \<Longrightarrow> t \<longmapsto> t' \<Longrightarrow> v \<bullet> t \<longmapsto> v \<bullet> t'"
| E_TApp: "t \<longmapsto> t' \<Longrightarrow> t \<bullet>\<^isub>\<tau> T \<longmapsto> t' \<bullet>\<^isub>\<tau> T"

text {*
Here, the rules @{text E_Abs} and @{text E_TAbs} describe the ``immediate'' reductions,
whereas @{text E_App1}, @{text E_App2}, and @{text E_TApp} are additional congruence
rules describing reductions in a context. The most important theorems of this section
are the {\it preservation} theorem, stating that the reduction of a well-typed term
does not change its type, and the {\it progress} theorem, stating that reduction of
a well-typed term does not ``get stuck'' -- in other words, every well-typed, closed
term @{term t} is either a value, or there is a term @{term t'} to which @{term t}
can be reduced. The preservation theorem
is proved by induction on the derivation of @{term "\<Gamma> \<turnstile> t : T"}, followed by a case
distinction on the last rule used in the derivation of @{term "t \<longmapsto> t'"}.
*}

theorem preservation: -- {* A.20 *}
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t \<longmapsto> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : T" using H
proof (induct arbitrary: t')
  case (T_Var \<Gamma> i U T t')
  have "Var i \<longmapsto> t'" .
  thus ?case by cases simp_all
next
  case (T_Abs T\<^isub>1 \<Gamma> t\<^isub>2 T\<^isub>2 t')
  have "(\<lambda>:T\<^isub>1. t\<^isub>2) \<longmapsto> t'" .
  thus ?case by cases simp_all
next
  case (T_App \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 t\<^isub>2 t')
  have "t\<^isub>1 \<bullet> t\<^isub>2 \<longmapsto> t'" .
  thus ?case
  proof cases
    case (E_Abs v\<^isub>2 T\<^isub>1\<^isub>1' t\<^isub>1\<^isub>2)
    with T_App have "\<Gamma> \<turnstile> (\<lambda>:T\<^isub>1\<^isub>1'. t\<^isub>1\<^isub>2) : T\<^isub>1\<^isub>1 \<rightarrow> T\<^isub>1\<^isub>2" by simp
    then obtain S'
      where T\<^isub>1\<^isub>1: "\<Gamma> \<turnstile> T\<^isub>1\<^isub>1 <: T\<^isub>1\<^isub>1'"
      and t\<^isub>1\<^isub>2: "VarB T\<^isub>1\<^isub>1' \<Colon> \<Gamma> \<turnstile> t\<^isub>1\<^isub>2 : S'"
      and S': "\<Gamma> \<turnstile> S'[0 \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau> <: T\<^isub>1\<^isub>2" by (rule Abs_type' [simplified]) blast
    have "\<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>1\<^isub>1" .
    hence "\<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>1\<^isub>1'" using T\<^isub>1\<^isub>1 by (rule T_Sub)
    with t\<^isub>1\<^isub>2 have "\<Gamma> \<turnstile> t\<^isub>1\<^isub>2[0 \<mapsto> t\<^isub>2] : S'[0 \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>"
      by (rule subst_type [where \<Delta>="[]", simplified])
    hence "\<Gamma> \<turnstile> t\<^isub>1\<^isub>2[0 \<mapsto> t\<^isub>2] : T\<^isub>1\<^isub>2" using S' by (rule T_Sub)
    with E_Abs show ?thesis by simp
  next
    case (E_App1 t''' t'' u)
    hence "t\<^isub>1 \<longmapsto> t''" by simp
    hence "\<Gamma> \<turnstile> t'' : T\<^isub>1\<^isub>1 \<rightarrow> T\<^isub>1\<^isub>2" by (rule T_App)
    hence "\<Gamma> \<turnstile> t'' \<bullet> t\<^isub>2 : T\<^isub>1\<^isub>2"
      by (rule typing.T_App)
    with E_App1 show ?thesis by simp
  next
    case (E_App2 v t''' t'')
    hence "t\<^isub>2 \<longmapsto> t''" by simp
    hence "\<Gamma> \<turnstile> t'' : T\<^isub>1\<^isub>1" by (rule T_App)
    with T_App(1) have "\<Gamma> \<turnstile> t\<^isub>1 \<bullet> t'' : T\<^isub>1\<^isub>2"
      by (rule typing.T_App)
    with E_App2 show ?thesis by simp
  qed simp_all
next
  case (T_TAbs T\<^isub>1 \<Gamma> t\<^isub>2 T\<^isub>2 t')
  have "(\<lambda><:T\<^isub>1. t\<^isub>2) \<longmapsto> t'" .
  thus ?case by cases simp_all
next
  case (T_TApp \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 T\<^isub>2 t')
  have "t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 \<longmapsto> t'" .
  thus ?case
  proof cases
    case (E_TAbs T\<^isub>1\<^isub>1' t\<^isub>1\<^isub>2 T\<^isub>2')
    with T_TApp have "\<Gamma> \<turnstile> (\<lambda><:T\<^isub>1\<^isub>1'. t\<^isub>1\<^isub>2) : (\<forall><:T\<^isub>1\<^isub>1. T\<^isub>1\<^isub>2)" by simp
    then obtain S'
      where "TVarB T\<^isub>1\<^isub>1 \<Colon> \<Gamma> \<turnstile> t\<^isub>1\<^isub>2 : S'"
      and "TVarB T\<^isub>1\<^isub>1 \<Colon> \<Gamma> \<turnstile> S' <: T\<^isub>1\<^isub>2" by (rule TAbs_type') blast
    hence "TVarB T\<^isub>1\<^isub>1 \<Colon> \<Gamma> \<turnstile> t\<^isub>1\<^isub>2 : T\<^isub>1\<^isub>2" by (rule T_Sub)
    hence "\<Gamma> \<turnstile> t\<^isub>1\<^isub>2[0 \<mapsto>\<^isub>\<tau> T\<^isub>2] : T\<^isub>1\<^isub>2[0 \<mapsto>\<^isub>\<tau> T\<^isub>2]\<^isub>\<tau>" using T_TApp(3)
      by (rule substT_type [where \<Delta>="[]", simplified])
    with E_TAbs show ?thesis by simp
  next
    case (E_TApp t''' t'' T)
    hence "t\<^isub>1 \<longmapsto> t''" by simp
    hence "\<Gamma> \<turnstile> t'' : (\<forall><:T\<^isub>1\<^isub>1. T\<^isub>1\<^isub>2)" by (rule T_TApp)
    hence "\<Gamma> \<turnstile> t'' \<bullet>\<^isub>\<tau> T\<^isub>2 : T\<^isub>1\<^isub>2[0 \<mapsto>\<^isub>\<tau> T\<^isub>2]\<^isub>\<tau>"
      by (rule typing.T_TApp)
    with E_TApp show ?thesis by simp
  qed simp_all
next
  case (T_Sub \<Gamma> t S T t')
  have "t \<longmapsto> t'" .
  hence "\<Gamma> \<turnstile> t' : S" by (rule T_Sub)
  moreover have "\<Gamma> \<turnstile> S <: T" .
  ultimately show ?case by (rule typing.T_Sub)
qed

text {*
The progress theorem is also proved by induction on the derivation of
@{term "[] \<turnstile> t : T"}. In the induction steps, we need the following two lemmas
about {\it canonical forms}
stating that closed values of types @{term "T\<^isub>1 \<rightarrow> T\<^isub>2"} and @{term "\<forall><:T\<^isub>1. T\<^isub>2"}
must be abstractions over term and type variables, respectively.
*}

lemma Fun_canonical: -- {* A.14(1) *}
  assumes ty: "[] \<turnstile> v : T\<^isub>1 \<rightarrow> T\<^isub>2"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda>:S. t)" using ty
proof (induct \<Gamma> \<equiv> "[]::env" v T \<equiv> "T\<^isub>1 \<rightarrow> T\<^isub>2" arbitrary: T\<^isub>1 T\<^isub>2)
  case T_Abs
  show ?case by iprover
next
  case (T_App \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 t\<^isub>2 T\<^isub>1 T\<^isub>2)
  have "t\<^isub>1 \<bullet> t\<^isub>2 \<in> value" .
  thus ?case by cases simp_all
next
  case (T_TApp \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 T\<^isub>2 T\<^isub>1 T\<^isub>2')
  have "t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 \<in> value" .
  thus ?case by cases simp_all
next
  case (T_Sub \<Gamma> t S T T\<^isub>1 T\<^isub>2)
  hence "\<Gamma> \<turnstile> S <: T\<^isub>1 \<rightarrow> T\<^isub>2" by simp
  then obtain S\<^isub>1 S\<^isub>2 where S: "S = S\<^isub>1 \<rightarrow> S\<^isub>2"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
qed simp_all

lemma TyAll_canonical: -- {* A.14(3) *}
  assumes ty: "[] \<turnstile> v : (\<forall><:T\<^isub>1. T\<^isub>2)"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda><:S. t)" using ty
proof (induct \<Gamma> \<equiv> "[]::env" v T \<equiv> "\<forall><:T\<^isub>1. T\<^isub>2" arbitrary: T\<^isub>1 T\<^isub>2)
  case (T_App \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 t\<^isub>2 T\<^isub>1 T\<^isub>2)
  have "t\<^isub>1 \<bullet> t\<^isub>2 \<in> value" .
  thus ?case by cases simp_all
next
  case T_TAbs
  show ?case by iprover
next
  case (T_TApp \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 T\<^isub>2 T\<^isub>1 T\<^isub>2')
  have "t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 \<in> value" .
  thus ?case by cases simp_all
next
  case (T_Sub \<Gamma> t S T T\<^isub>1 T\<^isub>2)
  hence "\<Gamma> \<turnstile> S <: (\<forall><:T\<^isub>1. T\<^isub>2)" by simp
  then obtain S\<^isub>1 S\<^isub>2 where S: "S = (\<forall><:S\<^isub>1. S\<^isub>2)"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
qed simp_all

theorem progress:
  assumes ty: "[] \<turnstile> t : T"
  shows "t \<in> value \<or> (\<exists>t'. t \<longmapsto> t')" using ty
proof (induct \<Gamma> \<equiv> "[]::env" t T)
  case T_Var
  thus ?case by simp
next
  case T_Abs
  from value.Abs show ?case ..
next
  case (T_App \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 t\<^isub>2)
  hence "t\<^isub>1 \<in> value \<or> (\<exists>t'. t\<^isub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^isub>1_val: "t\<^isub>1 \<in> value"
    with T_App obtain t S where t\<^isub>1: "t\<^isub>1 = (\<lambda>:S. t)"
      by (auto dest!: Fun_canonical)
    from T_App have "t\<^isub>2 \<in> value \<or> (\<exists>t'. t\<^isub>2 \<longmapsto> t')" by simp
    thus ?thesis
    proof
      assume "t\<^isub>2 \<in> value"
      with t\<^isub>1 have "t\<^isub>1 \<bullet> t\<^isub>2 \<longmapsto> t[0 \<mapsto> t\<^isub>2]"
	by simp (rule eval.intros)
      thus ?thesis by iprover
    next
      assume "\<exists>t'. t\<^isub>2 \<longmapsto> t'"
      then obtain t' where "t\<^isub>2 \<longmapsto> t'" by iprover
      with t\<^isub>1_val have "t\<^isub>1 \<bullet> t\<^isub>2 \<longmapsto> t\<^isub>1 \<bullet> t'" by (rule eval.intros)
      thus ?thesis by iprover
    qed
  next
    assume "\<exists>t'. t\<^isub>1 \<longmapsto> t'"
    then obtain t' where "t\<^isub>1 \<longmapsto> t'" ..
    hence "t\<^isub>1 \<bullet> t\<^isub>2 \<longmapsto> t' \<bullet> t\<^isub>2" by (rule eval.intros)
    thus ?thesis by iprover
  qed
next
  case T_TAbs
  from value.TAbs show ?case ..
next
  case (T_TApp \<Gamma> t\<^isub>1 T\<^isub>1\<^isub>1 T\<^isub>1\<^isub>2 T\<^isub>2)
  hence "t\<^isub>1 \<in> value \<or> (\<exists>t'. t\<^isub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume "t\<^isub>1 \<in> value"
    with T_TApp obtain t S where "t\<^isub>1 = (\<lambda><:S. t)"
      by (auto dest!: TyAll_canonical)
    hence "t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 \<longmapsto> t[0 \<mapsto>\<^isub>\<tau> T\<^isub>2]" by simp (rule eval.intros)
    thus ?thesis by iprover
  next
    assume "\<exists>t'. t\<^isub>1 \<longmapsto> t'"
    then obtain t' where "t\<^isub>1 \<longmapsto> t'" ..
    hence "t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 \<longmapsto> t' \<bullet>\<^isub>\<tau> T\<^isub>2" by (rule eval.intros)
    thus ?thesis by iprover
  qed
next
  case T_Sub
  show ?case by (rule T_Sub)
qed

(*<*)
end
(*>*)
