(*  Title:      JinjaThreads/J/DefAss.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Definite assignment} *}

theory DefAss imports 
  Expr
  Cset
begin

subsection "Hypersets"

types 'a hyperset = "'a set option"

definition hyperUn :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<squnion>" 65)
where
  "A \<squnion> B  \<equiv>  case A of None \<Rightarrow> None
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> None | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<union> B\<rfloor>)"

definition hyperInt :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<sqinter>" 70)
where
  "A \<sqinter> B  \<equiv>  case A of None \<Rightarrow> B
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> \<lfloor>A\<rfloor> | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<inter> B\<rfloor>)"

definition hyperDiff1 :: "'a hyperset \<Rightarrow> 'a \<Rightarrow> 'a hyperset"   (infixl "\<ominus>" 65)
where
  "A \<ominus> a  \<equiv>  case A of None \<Rightarrow> None | \<lfloor>A\<rfloor> \<Rightarrow> \<lfloor>A - {a}\<rfloor>"

definition hyper_isin :: "'a \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<in>\<in>" 50)
where
 "a \<in>\<in> A  \<equiv>  case A of None \<Rightarrow> True | \<lfloor>A\<rfloor> \<Rightarrow> a \<in> A"

definition hyper_subset :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<sqsubseteq>" 50)
where
  "A \<sqsubseteq> B  \<equiv>  case B of None \<Rightarrow> True
                 | \<lfloor>B\<rfloor> \<Rightarrow> (case A of None \<Rightarrow> False | \<lfloor>A\<rfloor> \<Rightarrow> A \<subseteq> B)"

definition hyperRestrict :: "'a hyperset \<Rightarrow> 'a set \<Rightarrow> 'a hyperset" (infixl "\<exclamdown>" 65)
where
  "A \<exclamdown> B \<equiv> case A of None \<Rightarrow> None
                   | \<lfloor>A'\<rfloor> \<Rightarrow> \<lfloor>A' \<inter> B\<rfloor>"

lemmas hyperset_defs =
 hyperUn_def hyperInt_def hyperDiff1_def hyper_isin_def hyper_subset_def hyperRestrict_def

lemma [simp]: "\<lfloor>{}\<rfloor> \<squnion> A = A  \<and>  A \<squnion> \<lfloor>{}\<rfloor> = A"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "\<lfloor>A\<rfloor> \<squnion> \<lfloor>B\<rfloor> = \<lfloor>A \<union> B\<rfloor> \<and> \<lfloor>A\<rfloor> \<ominus> a = \<lfloor>A - {a}\<rfloor>"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "None \<squnion> A = None \<and> A \<squnion> None = None"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "a \<in>\<in> None \<and> None \<ominus> a = None"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma hyperUn_assoc: "(A \<squnion> B) \<squnion> C = A \<squnion> (B \<squnion> C)"
(*<*)by(simp add:hyperset_defs Un_assoc)(*>*)

lemma hyper_insert_comm: "A \<squnion> \<lfloor>{a}\<rfloor> = \<lfloor>{a}\<rfloor> \<squnion> A \<and> A \<squnion> (\<lfloor>{a}\<rfloor> \<squnion> B) = \<lfloor>{a}\<rfloor> \<squnion> (A \<squnion> B)"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "None \<exclamdown> B = None"
by(simp add: hyperRestrict_def)

lemma [simp]: "\<lfloor>A\<rfloor> \<exclamdown> B = \<lfloor>A \<inter> B\<rfloor>"
by(simp add: hyperRestrict_def)

lemma sqSub_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<exclamdown> B \<sqsubseteq> A' \<exclamdown> B"
by(auto simp add: hyperset_defs)

lemma sqSub_mem_lem [elim]: "\<lbrakk> A \<sqsubseteq> A'; a \<in>\<in> A \<rbrakk> \<Longrightarrow> a \<in>\<in> A'"
by(auto simp add: hyperset_defs)

lemma [iff]: "A \<sqsubseteq> None"
by(auto simp add: hyperset_defs)

lemma [simp]: "A \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma [iff]: "\<lfloor>A\<rfloor> \<sqsubseteq> \<lfloor>B\<rfloor> \<longleftrightarrow> A \<subseteq> B"
by(auto simp add: hyperset_defs)

lemma sqUn_lem2: "A \<sqsubseteq> A' \<Longrightarrow> B \<squnion> A \<sqsubseteq> B \<squnion> A'"
by(simp add:hyperset_defs) blast

lemma sqSub_trans [trans, intro]: "\<lbrakk> A \<sqsubseteq> B; B \<sqsubseteq> C \<rbrakk> \<Longrightarrow> A \<sqsubseteq> C"
by(auto simp add: hyperset_defs)

lemma hyperUn_comm: "A \<squnion> B = B \<squnion> A"
by(auto simp add: hyperset_defs)

lemma hyperUn_leftComm: "A \<squnion> (B \<squnion> C) = B \<squnion> (A \<squnion> C)"
by(auto simp add: hyperset_defs)

lemmas hyperUn_ac = hyperUn_comm hyperUn_leftComm hyperUn_assoc

lemma [simp]: "\<lfloor>{}\<rfloor> \<squnion> B = B"
by(auto)

lemma [simp]: "A \<exclamdown> B \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma [simp]: "\<lfloor>{}\<rfloor> \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma [simp]: "A \<exclamdown> B \<exclamdown> C = A \<exclamdown> (B \<inter> C)"
by(auto simp add: hyperRestrict_def)

lemma restrict_lem: "C \<subseteq> D \<Longrightarrow> A \<squnion> B \<exclamdown> C \<sqsubseteq> B \<squnion> (A \<exclamdown> D)"
by(auto simp add: hyperset_defs)

lemma restrict_lem2: "A \<subseteq> B \<Longrightarrow> C \<exclamdown> A \<sqsubseteq> C \<exclamdown> B"
by(auto simp add: hyperRestrict_def)

lemma restrict_lem3: "D \<subseteq> E \<Longrightarrow> A \<squnion> (B \<squnion> C) \<exclamdown> D \<sqsubseteq> B \<squnion> (C \<squnion> (A \<exclamdown> E))"
by(auto simp add: hyperset_defs)

lemma sqInt_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<sqinter> B \<sqsubseteq> A' \<sqinter> B"
by(auto simp add: hyperset_defs)

subsection "Definite assignment"

primrec \<A>  :: "('a,'b) exp \<Rightarrow> 'a hyperset"
  and \<A>s :: "('a,'b) exp list \<Rightarrow> 'a hyperset"
where
  "\<A> (new C) = \<lfloor>{}\<rfloor>"
| "\<A> (newA T\<lfloor>e\<rceil>) = \<A> e"
| "\<A> (Cast C e) = \<A> e"
| "\<A> (e instanceof T) = \<A> e"
| "\<A> (Val v) = \<lfloor>{}\<rfloor>"
| "\<A> (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = \<A> e\<^isub>1 \<squnion> \<A> e\<^isub>2"
| "\<A> (Var V) = \<lfloor>{}\<rfloor>"
| "\<A> (LAss V e) = \<lfloor>{V}\<rfloor> \<squnion> \<A> e"
| "\<A> (a\<lfloor>i\<rceil>) = \<A> a \<squnion> \<A> i"
| "\<A> (a\<lfloor>i\<rceil> := e) = \<A> a \<squnion> \<A> i \<squnion> \<A> e"
| "\<A> (a\<bullet>length) = \<A> a"
| "\<A> (e\<bullet>F{D}) = \<A> e"
| "\<A> (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) = \<A> e\<^isub>1 \<squnion> \<A> e\<^isub>2"
| "\<A> (e\<bullet>M(es)) = \<A> e \<squnion> \<A>s es"
| "\<A> ({V:T=vo; e}) = \<A> e \<ominus> V"
| "\<A> (sync\<^bsub>V\<^esub> (o') e) = \<A> o' \<squnion> \<A> e"
| "\<A> (insync\<^bsub>V\<^esub> (a) e) = \<A> e"
| "\<A> (e\<^isub>1;;e\<^isub>2) = \<A> e\<^isub>1 \<squnion> \<A> e\<^isub>2"
| "\<A> (if (e) e\<^isub>1 else e\<^isub>2) =  \<A> e \<squnion> (\<A> e\<^isub>1 \<sqinter> \<A> e\<^isub>2)"
| "\<A> (while (b) e) = \<A> b"
| "\<A> (throw e) = None"
| "\<A> (try e\<^isub>1 catch(C V) e\<^isub>2) = \<A> e\<^isub>1 \<sqinter> (\<A> e\<^isub>2 \<ominus> V)"

| "\<A>s ([]) = \<lfloor>{}\<rfloor>"
| "\<A>s (e#es) = \<A> e \<squnion> \<A>s es"

primrec \<D>  :: "('a,'b) exp \<Rightarrow> 'a hyperset \<Rightarrow> bool"
  and \<D>s :: "('a,'b) exp list \<Rightarrow> 'a hyperset \<Rightarrow> bool"
where
  "\<D> (new C) A = True"
| "\<D> (newA T\<lfloor>e\<rceil>) A = \<D> e A"
| "\<D> (Cast C e) A = \<D> e A"
| "\<D> (e instanceof T) = \<D> e"
| "\<D> (Val v) A = True"
| "\<D> (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e\<^isub>1))"
| "\<D> (Var V) A = (V \<in>\<in> A)"
| "\<D> (LAss V e) A = \<D> e A"
| "\<D> (a\<lfloor>i\<rceil>) A = (\<D> a A \<and> \<D> i (A \<squnion> \<A> a))"
| "\<D> (a\<lfloor>i\<rceil> := e) A = (\<D> a A \<and> \<D> i (A \<squnion> \<A> a) \<and> \<D> e (A \<squnion> \<A> a \<squnion> \<A> i))"
| "\<D> (a\<bullet>length) A = \<D> a A"
| "\<D> (e\<bullet>F{D}) A = \<D> e A"
| "\<D> (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e\<^isub>1))"
| "\<D> (e\<bullet>M(es)) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"
| "\<D> ({V:T=vo; e}) A = (if vo = None then \<D> e (A \<ominus> V) else \<D> e (A \<squnion> \<lfloor>{V}\<rfloor>))"
| "\<D> (sync\<^bsub>V\<^esub> (o') e) A = (\<D> o' A \<and> \<D> e (A \<squnion> \<A> o'))"
| "\<D> (insync\<^bsub>V\<^esub> (a) e) A = \<D> e A"
| "\<D> (e\<^isub>1;;e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e\<^isub>1))"
| "\<D> (if (e) e\<^isub>1 else e\<^isub>2) A = (\<D> e A \<and> \<D> e\<^isub>1 (A \<squnion> \<A> e) \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e))"
| "\<D> (while (e) c) A = (\<D> e A \<and> \<D> c (A \<squnion> \<A> e))"
| "\<D> (throw e) A = \<D> e A"
| "\<D> (try e\<^isub>1 catch(C V) e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<lfloor>{V}\<rfloor>))"

| "\<D>s ([]) A = True"
| "\<D>s (e#es) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"

lemma As_map_Val[simp]: "\<A>s (map Val vs) = \<lfloor>{}\<rfloor>"
(*<*)by (induct vs) simp_all(*>*)

lemma As_append [simp]: "\<A>s (xs @ ys) = (\<A>s xs) \<squnion> (\<A>s ys)"
by(induct xs, auto simp add: hyperset_defs)

lemma Ds_map_Val[simp]: "\<D>s (map Val vs) A"
(*<*)by (induct vs) simp_all(*>*)

lemma D_append[iff]: "\<And>A. \<D>s (es @ es') A = (\<D>s es A \<and> \<D>s es' (A \<squnion> \<A>s es))"
(*<*)by (induct es type:list) (auto simp:hyperUn_assoc)(*>*)


lemma fixes e :: "('a,'b) exp" and es :: "('a,'b) exp list"
  shows A_fv: "\<And>A. \<A> e = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fv e"
  and  "\<And>A. \<A>s es = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fvs es"
apply(induct e and es)
apply (simp_all add:hyperset_defs)
apply fast+
done


lemma sqUn_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<squnion> B \<sqsubseteq> A' \<squnion> B"
(*<*)by(simp add:hyperset_defs) blast(*>*)

lemma diff_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<ominus> b \<sqsubseteq> A' \<ominus> b"
(*<*)by(simp add:hyperset_defs) blast(*>*)

(* This order of the premises avoids looping of the simplifier *)
lemma D_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D> e A \<Longrightarrow> \<D> (e::('a,'b) exp) A'"
  and Ds_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A \<Longrightarrow> \<D>s (es::('a,'b) exp list) A'"
(*<*)
apply(induct e and es)
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply (fastsimp simp add:hyperset_defs)
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply(clarsimp split: split_if_asm) apply (iprover dest:diff_lem) apply(iprover dest: sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp apply (iprover dest:sqUn_lem)
done
(*>*)

(* And this is the order of premises preferred during application: *)
lemma D_mono': "\<D> e A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D> e A'"
and Ds_mono': "\<D>s es A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A'"
(*<*)by(blast intro:D_mono, blast intro:Ds_mono)(*>*)

declare hyperUn_comm [simp]
declare hyperUn_leftComm [simp]

lemma fixes e :: "('a,'b) exp"
  and es :: "('a,'b) exp list"
  shows D_fv: "\<D> e A \<Longrightarrow> \<D> e (A \<exclamdown> (fv e))"
  and Ds_fvs: "\<D>s es A \<Longrightarrow> \<D>s es (A \<exclamdown> (fvs es))"
proof(induct e and es arbitrary: A and A)
  case Var thus ?case by(simp add: hyperset_defs)
next
  case Block thus ?case
    by(fastsimp simp add: hyperset_defs simp del: hyperRestrict_def intro: D_mono')
next
  case Synchronized thus ?case by(fastsimp simp add: hyperset_defs simp del: hyperRestrict_def intro: D_mono')
next
  case InSynchronized thus ?case by(fastsimp simp add: hyperset_defs simp del: hyperRestrict_def intro: D_mono')
next
  case TryCatch thus ?case by(fastsimp simp add: hyperset_defs simp del: hyperRestrict_def intro: D_mono')
qed (simp_all, (blast intro: D_mono' Ds_mono' restrict_lem2 restrict_lem restrict_lem3)+)

subsection {* Code generation *}

lemma [code_pred_intro]:
  "hyper_isin x None"
  "A x ==> hyper_isin x (Some A)"
by(auto simp add: hyper_isin_def mem_def)

code_pred hyper_isin
by(simp add: hyper_isin_def mem_def)

text {* Lifting @{term "\<A>"} and @{term "\<D>"} to @{typ "'a Cset.set"} *}

types 'a hyperset_code = "'a Cset.set option"

definition hyperUn_code :: "'a hyperset_code \<Rightarrow> 'a hyperset_code \<Rightarrow> 'a hyperset_code"   (infixl "\<squnion>\<^isub>f" 65)
where
  "A \<squnion>\<^isub>f B  \<equiv>  case A of None \<Rightarrow> None
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> None | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>sup A B\<rfloor>)"

definition hyperInt_code :: "'a hyperset_code \<Rightarrow> 'a hyperset_code \<Rightarrow> 'a hyperset_code"   (infixl "\<sqinter>\<^isub>f" 70)
where
  "A \<sqinter>\<^isub>f B  \<equiv>  case A of None \<Rightarrow> B
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> \<lfloor>A\<rfloor> | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>inf A B\<rfloor>)"

definition hyperDiff1_code :: "'a hyperset_code \<Rightarrow> 'a \<Rightarrow> 'a hyperset_code"   (infixl "\<ominus>\<^isub>f" 65)
where
  "A \<ominus>\<^isub>f a  \<equiv>  case A of None \<Rightarrow> None | \<lfloor>A\<rfloor> \<Rightarrow> \<lfloor>Cset.remove a A\<rfloor>"

definition hyper_isin_code :: "'a \<Rightarrow> 'a hyperset_code \<Rightarrow> bool"   (infix "\<in>\<in>\<^isub>f" 50)
where
  "a \<in>\<in>\<^isub>f A  \<equiv>  case A of None \<Rightarrow> True | \<lfloor>A\<rfloor> \<Rightarrow> Cset.member A a"

definition hyper_subset_code :: "'a hyperset_code \<Rightarrow> 'a hyperset_code \<Rightarrow> bool"   (infix "\<sqsubseteq>\<^isub>f" 50)
where
  "A \<sqsubseteq>\<^isub>f B  \<equiv>  case B of None \<Rightarrow> True
                 | \<lfloor>B\<rfloor> \<Rightarrow> (case A of None \<Rightarrow> False | \<lfloor>A\<rfloor> \<Rightarrow> (Cset.forall (Cset.member B) A))"

primrec \<A>_code :: "('a,'b) exp \<Rightarrow> 'a hyperset_code"
  and \<A>s_code :: "('a,'b) exp list \<Rightarrow> 'a hyperset_code"
where
  "\<A>_code (new C) = \<lfloor>bot\<rfloor>"
| "\<A>_code (newA T\<lfloor>e\<rceil>) = \<A>_code e"
| "\<A>_code (Cast C e) = \<A>_code e"
| "\<A>_code (e instanceof T) = \<A>_code e"
| "\<A>_code (Val v) = \<lfloor>bot\<rfloor>"
| "\<A>_code (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = \<A>_code e\<^isub>1 \<squnion>\<^isub>f \<A>_code e\<^isub>2"
| "\<A>_code (Var V) = \<lfloor>bot\<rfloor>"
| "\<A>_code (LAss V e) = \<lfloor>Cset.insert V bot\<rfloor> \<squnion>\<^isub>f \<A>_code e"
| "\<A>_code (a\<lfloor>i\<rceil>) = \<A>_code a \<squnion>\<^isub>f \<A>_code i"
| "\<A>_code (a\<lfloor>i\<rceil> := e) = \<A>_code a \<squnion>\<^isub>f \<A>_code i \<squnion>\<^isub>f \<A>_code e"
| "\<A>_code (a\<bullet>length) = \<A>_code a"
| "\<A>_code (e\<bullet>F{D}) = \<A>_code e"
| "\<A>_code (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) = \<A>_code e\<^isub>1 \<squnion>\<^isub>f \<A>_code e\<^isub>2"
| "\<A>_code (e\<bullet>M(es)) = \<A>_code e \<squnion>\<^isub>f \<A>s_code es"
| "\<A>_code ({V:T=vo; e}) = \<A>_code e \<ominus>\<^isub>f V"
| "\<A>_code (sync\<^bsub>V\<^esub> (o') e) = \<A>_code o' \<squnion>\<^isub>f \<A>_code e"
| "\<A>_code (insync\<^bsub>V\<^esub> (a) e) = \<A>_code e"
| "\<A>_code (e\<^isub>1;;e\<^isub>2) = \<A>_code e\<^isub>1 \<squnion>\<^isub>f \<A>_code e\<^isub>2"
| "\<A>_code (if (e) e\<^isub>1 else e\<^isub>2) =  \<A>_code e \<squnion>\<^isub>f (\<A>_code e\<^isub>1 \<sqinter>\<^isub>f \<A>_code e\<^isub>2)"
| "\<A>_code (while (b) e) = \<A>_code b"
| "\<A>_code (throw e) = None"
| "\<A>_code (try e\<^isub>1 catch(C V) e\<^isub>2) = \<A>_code e\<^isub>1 \<sqinter>\<^isub>f (\<A>_code e\<^isub>2 \<ominus>\<^isub>f V)"

| "\<A>s_code ([]) = \<lfloor>bot\<rfloor>"
| "\<A>s_code (e#es) = \<A>_code e \<squnion>\<^isub>f \<A>s_code es"

primrec \<D>_code :: "('a,'b) exp \<Rightarrow> 'a hyperset_code \<Rightarrow> bool"
  and \<D>s_code :: "('a,'b) exp list \<Rightarrow> 'a hyperset_code \<Rightarrow> bool"
where
  "\<D>_code (new C) A = True"
| "\<D>_code (newA T\<lfloor>e\<rceil>) A = \<D>_code e A"
| "\<D>_code (Cast C e) A = \<D>_code e A"
| "\<D>_code (e instanceof T) A = \<D>_code e A"
| "\<D>_code (Val v) A = True"
| "\<D>_code (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) A = (\<D>_code e\<^isub>1 A \<and> \<D>_code e\<^isub>2 (A \<squnion>\<^isub>f \<A>_code e\<^isub>1))"
| "\<D>_code (Var V) A = (V \<in>\<in>\<^isub>f A)"
| "\<D>_code (LAss V e) A = \<D>_code e A"
| "\<D>_code (a\<lfloor>i\<rceil>) A = (\<D>_code a A \<and> \<D>_code i (A \<squnion>\<^isub>f \<A>_code a))"
| "\<D>_code (a\<lfloor>i\<rceil> := e) A = (\<D>_code a A \<and> \<D>_code i (A \<squnion>\<^isub>f \<A>_code a) \<and> \<D>_code e (A \<squnion>\<^isub>f \<A>_code a \<squnion>\<^isub>f \<A>_code i))"
| "\<D>_code (a\<bullet>length) A = \<D>_code a A"
| "\<D>_code (e\<bullet>F{D}) A = \<D>_code e A"
| "\<D>_code (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) A = (\<D>_code e\<^isub>1 A \<and> \<D>_code e\<^isub>2 (A \<squnion>\<^isub>f \<A>_code e\<^isub>1))"
| "\<D>_code (e\<bullet>M(es)) A = (\<D>_code e A \<and> \<D>s_code es (A \<squnion>\<^isub>f \<A>_code e))"
| "\<D>_code ({V:T=vo; e}) A = (if vo = None then \<D>_code e (A \<ominus>\<^isub>f V) else \<D>_code e (A \<squnion>\<^isub>f \<lfloor>Cset.insert V bot\<rfloor>))"
| "\<D>_code (sync\<^bsub>V\<^esub> (o') e) A = (\<D>_code o' A \<and> \<D>_code e (A \<squnion>\<^isub>f \<A>_code o'))"
| "\<D>_code (insync\<^bsub>V\<^esub> (a) e) A = \<D>_code e A"
| "\<D>_code (e\<^isub>1;;e\<^isub>2) A = (\<D>_code e\<^isub>1 A \<and> \<D>_code e\<^isub>2 (A \<squnion>\<^isub>f \<A>_code e\<^isub>1))"
| "\<D>_code (if (e) e\<^isub>1 else e\<^isub>2) A =
  (\<D>_code e A \<and> \<D>_code e\<^isub>1 (A \<squnion>\<^isub>f \<A>_code e) \<and> \<D>_code e\<^isub>2 (A \<squnion>\<^isub>f \<A>_code e))"
| "\<D>_code (while (e) c) A = (\<D>_code e A \<and> \<D>_code c (A \<squnion>\<^isub>f \<A>_code e))"
| "\<D>_code (throw e) A = \<D>_code e A"
| "\<D>_code (try e\<^isub>1 catch(C V) e\<^isub>2) A = (\<D>_code e\<^isub>1 A \<and> \<D>_code e\<^isub>2 (A \<squnion>\<^isub>f \<lfloor>Cset.insert V bot\<rfloor>))"

| "\<D>s_code ([]) A = True"
| "\<D>s_code (e#es) A = (\<D>_code e A \<and> \<D>s_code es (A \<squnion>\<^isub>f \<A>_code e))"

primrec hyperCset :: "'a hyperset \<Rightarrow> 'a hyperset_code"
where "hyperCset None = None"
| "hyperCset \<lfloor>A\<rfloor> = \<lfloor>Cset A\<rfloor>"

lemma hyperCset_inject [simp]: "hyperCset A = hyperCset B \<longleftrightarrow> A = B"
by(cases A)(case_tac [!] B, auto)

lemma hyperUn_code_hyperCset [simp]: "hyperCset A \<squnion>\<^isub>f hyperCset B = hyperCset (A \<squnion> B)"
by(simp add: hyperUn_code_def hyperUn_def)

lemma hyperInt_code_hyperCset [simp]: "hyperCset A \<sqinter>\<^isub>f hyperCset B = hyperCset (A \<sqinter> B)"
by(simp add: hyperInt_code_def hyperInt_def)

lemma hyper_isin_code_hyperCset [simp]: "(a \<in>\<in>\<^isub>f hyperCset A) = (a \<in>\<in> A)"
by(simp add: hyper_isin_code_def hyper_isin_def mem_def)

lemma hyperDiff1_code_hyperCset [simp]: "(hyperCset A) \<ominus>\<^isub>f a = hyperCset (A \<ominus> a)"
by(simp add: hyperDiff1_code_def hyperDiff1_def)

lemma fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows  \<A>_code_conv_\<A>: "\<A>_code e = hyperCset (\<A> e)"
  and \<A>s_code_conv_\<A>s: "\<A>s_code es = hyperCset (\<A>s es)"
apply(induct e and es)
apply auto
apply(simp add: hyperUn_code_def hyperUn_def)
done

lemma fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows  \<D>_code_conv_\<D>: "\<D>_code e (hyperCset A) = \<D> e A"
  and \<D>s_code_conv_\<D>s: "\<D>s_code es (hyperCset A) = \<D>s es A"
apply(induct e and es arbitrary: A and A)
apply(simp_all add: \<A>_code_conv_\<A> \<A>s_code_conv_\<A>s hyperCset.simps[symmetric] del: hyperCset.simps)
done

end
