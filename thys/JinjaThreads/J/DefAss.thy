(*  Title:      Jinja/DefAss.thy
    ID:         $Id: DefAss.thy,v 1.3 2008-04-23 08:43:36 alochbihler Exp $
    Author:     Tobias Nipkow, Andreas Lochbihler
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Definite assignment} *}

theory DefAss imports Expr begin

subsection "Hypersets"

types 'a hyperset = "'a set option"

constdefs
  hyperUn :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<squnion>" 65)
  "A \<squnion> B  \<equiv>  case A of None \<Rightarrow> None
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> None | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<union> B\<rfloor>)"

  hyperInt :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<sqinter>" 70)
  "A \<sqinter> B  \<equiv>  case A of None \<Rightarrow> B
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> \<lfloor>A\<rfloor> | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<inter> B\<rfloor>)"

  hyperDiff1 :: "'a hyperset \<Rightarrow> 'a \<Rightarrow> 'a hyperset"   (infixl "\<ominus>" 65)
  "A \<ominus> a  \<equiv>  case A of None \<Rightarrow> None | \<lfloor>A\<rfloor> \<Rightarrow> \<lfloor>A - {a}\<rfloor>"

 hyper_isin :: "'a \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<in>\<in>" 50)
 "a \<in>\<in> A  \<equiv>  case A of None \<Rightarrow> True | \<lfloor>A\<rfloor> \<Rightarrow> a \<in> A"

  hyper_subset :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<sqsubseteq>" 50)
  "A \<sqsubseteq> B  \<equiv>  case B of None \<Rightarrow> True
                 | \<lfloor>B\<rfloor> \<Rightarrow> (case A of None \<Rightarrow> False | \<lfloor>A\<rfloor> \<Rightarrow> A \<subseteq> B)"

lemmas hyperset_defs =
 hyperUn_def hyperInt_def hyperDiff1_def hyper_isin_def hyper_subset_def

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


subsection "Definite assignment"

consts
 \<A>  :: "'a exp \<Rightarrow> 'a hyperset"
 \<A>s :: "'a exp list \<Rightarrow> 'a hyperset"
 \<D>  :: "'a exp \<Rightarrow> 'a hyperset \<Rightarrow> bool"
 \<D>s :: "'a exp list \<Rightarrow> 'a hyperset \<Rightarrow> bool"

primrec
"\<A> (new C) = \<lfloor>{}\<rfloor>"
"\<A> (newA T\<lfloor>e\<rceil>) = \<A> e"
"\<A> (Cast C e) = \<A> e"
"\<A> (Val v) = \<lfloor>{}\<rfloor>"
"\<A> (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = \<A> e\<^isub>1 \<squnion> \<A> e\<^isub>2"
"\<A> (Var V) = \<lfloor>{}\<rfloor>"
"\<A> (LAss V e) = \<lfloor>{V}\<rfloor> \<squnion> \<A> e"
"\<A> (a\<lfloor>i\<rceil>) = \<A> a \<squnion> \<A> i"
"\<A> (a\<lfloor>i\<rceil> := e) = \<A> a \<squnion> \<A> i \<squnion> \<A> e"
"\<A> (e\<bullet>F{D}) = \<A> e"
"\<A> (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) = \<A> e\<^isub>1 \<squnion> \<A> e\<^isub>2"
"\<A> (e\<bullet>M(es)) = \<A> e \<squnion> \<A>s es"
"\<A> ({V:T; e}) = \<A> e \<ominus> V"
"\<A> (sync(o') e) = \<A> o' \<squnion> \<A> e"
"\<A> (insync(a) e) = \<A> e"
"\<A> (e\<^isub>1;;e\<^isub>2) = \<A> e\<^isub>1 \<squnion> \<A> e\<^isub>2"
"\<A> (if (e) e\<^isub>1 else e\<^isub>2) =  \<A> e \<squnion> (\<A> e\<^isub>1 \<sqinter> \<A> e\<^isub>2)"
"\<A> (while (b) e) = \<A> b"
"\<A> (throw e) = None"
"\<A> (try e\<^isub>1 catch(C V) e\<^isub>2) = \<A> e\<^isub>1 \<sqinter> (\<A> e\<^isub>2 \<ominus> V)"

"\<A>s ([]) = \<lfloor>{}\<rfloor>"
"\<A>s (e#es) = \<A> e \<squnion> \<A>s es"

primrec
"\<D> (new C) A = True"
"\<D> (newA T\<lfloor>e\<rceil>) A = \<D> e A"
"\<D> (Cast C e) A = \<D> e A"
"\<D> (Val v) A = True"
"\<D> (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e\<^isub>1))"
"\<D> (Var V) A = (V \<in>\<in> A)"
"\<D> (LAss V e) A = \<D> e A"
"\<D> (a\<lfloor>i\<rceil>) A = (\<D> a A \<and> \<D> i (A \<squnion> \<A> a))"
"\<D> (a\<lfloor>i\<rceil> := e) A = (\<D> a A \<and> \<D> i (A \<squnion> \<A> a) \<and> \<D> e (A \<squnion> \<A> a \<squnion> \<A> i))"
"\<D> (e\<bullet>F{D}) A = \<D> e A"
"\<D> (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e\<^isub>1))"
"\<D> (e\<bullet>M(es)) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"
"\<D> ({V:T; e}) A = \<D> e (A \<ominus> V)"
"\<D> (sync(o') e) A = (\<D> o' A \<and> \<D> e (A \<squnion> \<A> o'))"
"\<D> (insync(a) e) A = \<D> e A"
"\<D> (e\<^isub>1;;e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e\<^isub>1))"
"\<D> (if (e) e\<^isub>1 else e\<^isub>2) A =
  (\<D> e A \<and> \<D> e\<^isub>1 (A \<squnion> \<A> e) \<and> \<D> e\<^isub>2 (A \<squnion> \<A> e))"
"\<D> (while (e) c) A = (\<D> e A \<and> \<D> c (A \<squnion> \<A> e))"
"\<D> (throw e) A = \<D> e A"
"\<D> (try e\<^isub>1 catch(C V) e\<^isub>2) A = (\<D> e\<^isub>1 A \<and> \<D> e\<^isub>2 (A \<squnion> \<lfloor>{V}\<rfloor>))"

"\<D>s ([]) A = True"
"\<D>s (e#es) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"

lemma As_map_Val[simp]: "\<A>s (map Val vs) = \<lfloor>{}\<rfloor>"
(*<*)by (induct vs) simp_all(*>*)

lemma As_append [simp]: "\<A>s (xs @ ys) = (\<A>s xs) \<squnion> (\<A>s ys)"
by(induct xs, auto simp add: hyperset_defs)

lemma Ds_map_Val[simp]: "\<D>s (map Val vs) A"
(*<*)by (induct vs) simp_all(*>*)

lemma D_append[iff]: "\<And>A. \<D>s (es @ es') A = (\<D>s es A \<and> \<D>s es' (A \<squnion> \<A>s es))"
(*<*)by (induct es type:list) (auto simp:hyperUn_assoc)(*>*)


lemma A_fv: "\<And>A. \<A> e = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fv e"
and  "\<And>A. \<A>s es = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fvs es"
(*<*)
apply(induct e and es)
apply (simp_all add:hyperset_defs)
apply blast+
done
(*>*)


lemma sqUn_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<squnion> B \<sqsubseteq> A' \<squnion> B"
(*<*)by(simp add:hyperset_defs) blast(*>*)

lemma diff_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<ominus> b \<sqsubseteq> A' \<ominus> b"
(*<*)by(simp add:hyperset_defs) blast(*>*)

(* This order of the premises avoids looping of the simplifier *)
lemma D_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D> e A \<Longrightarrow> \<D> (e::'a exp) A'"
and Ds_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A \<Longrightarrow> \<D>s (es::'a exp list) A'"
(*<*)
apply(induct e and es)
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
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:diff_lem)
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

end
