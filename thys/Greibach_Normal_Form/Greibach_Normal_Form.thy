(* Authors: Alexander Haberl, Tobias Nipkow, Akihisa Yamada *)

theory Greibach_Normal_Form
imports
  "Context_Free_Grammar.Context_Free_Grammar"
  "Context_Free_Grammar.Epsilon_Elimination"
  "Context_Free_Grammar.Replace_Terminals"
  Fresh_Identifiers.Fresh_Nat
begin

(* Import of additional theories undoes this deletion in \<open>Context_Free_Grammar\<close>: *)
declare relpowp.simps(2)[simp del] 

lemma set_fold_union: "set (fold List.union xss ys) = \<Union>(set ` set xss) \<union> set ys"
  apply (induction xss arbitrary: ys)
  by auto

lemma distinct_fold_union: "distinct (fold List.union xss ys) \<longleftrightarrow> distinct ys"
  by (induction xss arbitrary: ys; simp)

text \<open>Lemmas for @{const Option.these}:\<close>

lemma these_eq_Collect: "Option.these X = {x. Some x \<in> X}"
  by (auto simp: in_these_eq)

lemma these_image: "Option.these (f ` X) = {y. \<exists>x \<in> X. f x = Some y}"
  by (force simp: these_eq_Collect image_def)

lemma these_eq_image_Diff: "Option.these X = the ` (X - {None})"
  by (auto simp: Option.these_def)

lemma inj_on_theI: "None \<notin> X \<Longrightarrow> inj_on the X"
  apply (auto intro!:inj_onI)
  by (metis option.exhaust_sel)

lemma finite_these: "finite (Option.these X) \<longleftrightarrow> finite X"
  by (auto simp: these_eq_image_Diff finite_image_iff inj_on_theI)

lemma finite_image_filter: "finite (Option.image_filter f X) \<longleftrightarrow> finite (f ` X)"
  by (auto simp: Option.image_filter_eq finite_these)

section \<open>Definition of Greibach Normal Forms\<close>

text \<open>This theory formalizes a method to transform a set of productions into 
Greibach Normal Form (GNF) \<^cite>\<open>Greibach\<close>.
A grammar is in GNF iff the rhss of each production is a terminal followed by nonterminals.\<close>

definition GNF where
"GNF P = (\<forall>(A,\<alpha>) \<in> P. \<exists>a Bs. \<alpha> = Tm a # map Nt Bs)"

abbreviation gnf where
"gnf P \<equiv> GNF (set P)"

lemma GNF_I: "(\<And>A \<alpha>. (A,\<alpha>) \<in> P \<Longrightarrow> \<exists>a Bs. \<alpha> = Tm a # map Nt Bs) \<Longrightarrow> GNF P"
  by (auto simp: GNF_def)

lemma GNF_Un: "GNF (P \<union> Q) \<longleftrightarrow> GNF P \<and> GNF Q"
  by (auto simp: GNF_def ball_Un)

text \<open>We first concentrate on the essential property of the GNF:
every production starts with a \<open>Tm\<close>; the tail of a rhs can contain further terminals.
We call such grammars are \emph{head GNF}, and formalize as \<open>GNF_hd\<close> below.
This more liberal definition of GNF is also found elsewhere \cite{BlumK99}.
\<close>
definition GNF_hd :: "('n,'t)Prods \<Rightarrow> bool" where 
"GNF_hd P = (\<forall>(A, w) \<in> P. \<exists>t v. w = Tm t # v)"

abbreviation gnf_hd :: "('n,'t)prods \<Rightarrow> bool" where 
"gnf_hd P \<equiv> GNF_hd (set P)"

section \<open>Transformation to Head GNF\<close>

text \<open>The algorithm to obtain head GNF consists of two phases:

  \<^item> \<open>Solve_tri\<close> converts the productions into a \<open>Triangular\<close> form, where Nt \<open>Ai\<close> does not 
  depend on Nts \<open>Ai, \<dots>, An\<close>. This involves the elimination of left-recursion and is the heart
  of the algorithm.

  \<^item> \<open>Expand_tri_rec\<close> expands the triangular form by substituting in:
  Due to triangular form, \<open>A0\<close> productions satisfy \<open>GNF_hd\<close> and we can substitute
  them into the heads of the remaining productions. Now all \<open>A1\<close> productions satisfy \<open>GNF_hd\<close>,
  and we continue until all productions satisfy \<open>GNF_hd\<close>.

This is essentially the algorithm given by Hopcroft and Ullman \cite{HopcroftU79},
except that we can drop the conversion to Chomsky Normal Form because of our more liberal \<open>GNF_hd\<close>.
\<close>
text \<open>Depend on: \<open>A\<close> depends on \<open>B\<close> if there is a rule \<open>A \<rightarrow> B w\<close>:\<close>
definition dep_on :: "('n,'t) Prods \<Rightarrow> 'n \<Rightarrow> 'n set" where
"dep_on P A = {B. \<exists>w. (A, Nt B # w) \<in> P}"

definition Subst_hd :: "('n,'t)Prods \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"Subst_hd P X = P - X \<union> {(A,v@w) | A v w. \<exists>B. (B,v) \<in> P \<and> (A, Nt B # w) \<in> X}"

lemma Subst_hd_image_filter: "Subst_hd P X = P - X \<union>
  Option.image_filter
 (\<lambda>((A, Nt B # \<alpha>), (B',\<beta>)) \<Rightarrow> if B = B' then Some (A,\<beta>@\<alpha>) else None | _ \<Rightarrow> None)
 (X \<times> P)"
  apply (unfold Subst_hd_def)
  apply (rule arg_cong[where f = "\<lambda>x. P - X \<union> x"])
  apply (auto simp add: Option.image_filter_eq these_image
      prod.case_distrib[of "\<lambda>x. x = _"]
      list.case_distrib[of "\<lambda>x. x = _"]
      sym.case_distrib[of "\<lambda>x. x = _"]
      if_distrib[of "\<lambda>x. x = _"] cong: prod.case_cong list.case_cong sym.case_cong)
   apply (force)
  apply (auto split: list.splits sym.splits)
  done

lemma finite_Subst_hd: "finite P \<Longrightarrow> finite X \<Longrightarrow> finite (Subst_hd P X)"
  by (auto simp: Subst_hd_image_filter finite_image_filter)

definition subst_hd :: "('n,'t)prods \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"subst_hd ps xs = minus_list_set ps xs @
  List.map_filter (\<lambda>((A,Nt B # \<alpha>),(B',\<beta>)) \<Rightarrow>
  if B = B' then Some (A,\<beta>@\<alpha>) else None | _ \<Rightarrow> None) (List.product xs ps)"

lemma set_subst_hd: "set (subst_hd ps xs) = Subst_hd (set ps) (set xs)"
  by (simp add: subst_hd_def image_filter_set_eq[symmetric] Subst_hd_image_filter)

text \<open>Expand head: Replace all rules \<open>A \<rightarrow> B w\<close> where \<open>B \<in> Ss\<close>
(\<open>Ss\<close> = solved Nts in \<open>Triangular\<close> form)
by \<open>A \<rightarrow> v w\<close> where \<open>B \<rightarrow> v\<close>. Starting from the end of \<open>Ss\<close>.\<close>
fun Expand_hd_rec :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"Expand_hd_rec A [] P = P" |
"Expand_hd_rec A (S#Ss) P =
 (let P' = Expand_hd_rec A Ss P;
      X = {r \<in> P'. \<exists>w. r = (A, Nt S # w)}
  in Subst_hd P' X)"

fun expand_hd_rec :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"expand_hd_rec A [] ps = ps" |
"expand_hd_rec A (B#Bs) ps =
 (let ps' = expand_hd_rec A Bs ps;
      xs = filter (\<lambda>(A', Nt B' # w) \<Rightarrow> A' = A \<and> B' = B | _ \<Rightarrow> False) ps'
  in subst_hd ps' xs)"

lemma set_expand_hd_rec: "set (expand_hd_rec A Bs ps) = Expand_hd_rec A Bs (set ps)"
proof (induction Bs arbitrary: ps)
  case Nil
  then show ?case by simp
next
  case (Cons B Bs)
  have 1: "{r \<in> P'. \<exists>w. r = (A, Nt B # w)} = Set.filter (\<lambda>(A', Nt B' # w) \<Rightarrow> A' = A \<and> B' = B | _ \<Rightarrow> False) P'"
    for P'
    apply (auto)
    by (simp_all split: list.splits sym.splits)
  show ?case by (simp add:Let_def 1 set_subst_hd Cons)
qed

declare Expand_hd_rec.simps(1)[code]
lemma Expand_hd_rec_Cons_code[code]: "Expand_hd_rec A (S#Ss) P =
 (let R' = Expand_hd_rec A Ss P;
      X = {w \<in> Rhss R' A. w \<noteq> [] \<and> hd w = Nt S};
      Y = (\<Union>(B,v) \<in> R'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(A,v @ tl w)})
  in R' - ({A} \<times> X) \<union> Y)"
by(simp add: Rhss_def Let_def neq_Nil_conv Ball_def hd_append Subst_hd_def split: if_splits, safe, force+)

text \<open>Remove left-recursions: Remove left-recursive rules \<open>A \<rightarrow> A w\<close>:\<close>
definition Rm_lrec ::  "'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"Rm_lrec A P = P - {(A,Nt A # v)|v. True}"

lemma Rm_lrec_code[code]:
  "Rm_lrec A P = {Aw \<in> P. let (A',w) = Aw in A' \<noteq> A \<or> w = [] \<or> hd w \<noteq> Nt A}"
by(auto simp add: Rm_lrec_def neq_Nil_conv)

definition rm_lrec :: "'n \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
"rm_lrec A ps = filter (\<lambda>(A', Nt A'' # \<alpha>) \<Rightarrow> A' \<noteq> A \<or> A'' \<noteq> A | _ \<Rightarrow> True) ps"

lemma set_rm_lrec: "set (rm_lrec A ps) = Rm_lrec A (set ps)"
  by (auto simp: rm_lrec_def Rm_lrec_def split: list.splits sym.splits)

text \<open>Make right-recursion of left-recursion: Conversion from left-recursion to right-recursion:
Split \<open>A\<close>-rules into \<open>A \<rightarrow> u\<close> and \<open>A \<rightarrow> A v\<close>.
Keep \<open>A \<rightarrow> u\<close> but replace \<open>A \<rightarrow> A v\<close> by \<open>A \<rightarrow> u A'\<close>, \<open>A' \<rightarrow> v\<close>, \<open>A' \<rightarrow> v A'\<close>.

The then part of the if statement is only an optimisation, so that we do not introduce the 
\<open>A \<rightarrow> u A'\<close> rules if we do not introduce any \<open>A'\<close> rules, but the function also works, if we always 
enter the else part.\<close>
definition Rrec_of_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"Rrec_of_lrec A A' P =
  (let V = {v. (A,Nt A # v) \<in> P \<and> v \<noteq> []};
       U = {u. (A,u) \<in> P \<and> (\<nexists>v. u = Nt A # v) }
  in if V = {} then {A}\<times>U
     else {A}\<times>U \<union> {(A, u @ [Nt A'])|u. u\<in>U} \<union> {A'}\<times>V \<union> {(A', v @ [Nt A']) |v. v\<in>V})"

lemma Rrec_of_lrec_code[code]: "Rrec_of_lrec A A' P =
  (let RA = Rhss P A;
       V = tl ` {w \<in> RA. w \<noteq> [] \<and> hd w = Nt A \<and> tl w \<noteq> []};
       U = {u \<in> RA. u = [] \<or> hd u \<noteq> Nt A }
  in if V = {} then {A}\<times>U
     else {A}\<times>U \<union> {(A, u @ [Nt A'])|u. u\<in>U} \<union> {A'}\<times>V \<union> {(A', v @ [Nt A']) |v. v\<in>V})"
proof -
  let ?RA = "Rhss P A"
  let ?Vc = "tl ` {w \<in> ?RA. w \<noteq> [] \<and> hd w = Nt A \<and> tl w \<noteq> []}"
  let ?Uc = "{u \<in> ?RA. u = [] \<or> hd u \<noteq> Nt A }"

  let ?V = "{v. (A,Nt A # v) \<in> P \<and> v \<noteq> []}"
  let ?U = "{u. (A,u) \<in> P \<and> \<not>(\<exists>v. u = Nt A # v) }"

  have 1: "?V = ?Vc" by (auto simp add: Rhss_def neq_Nil_conv image_def)
  moreover have 2: "?U = ?Uc" by (auto simp add: Rhss_def neq_Nil_conv)

  ultimately show ?thesis
    unfolding Rrec_of_lrec_def Let_def by presburger 

qed

definition rrec_of_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"rrec_of_lrec A A' ps =
  (let vs = [v. (B, Nt C # v) \<leftarrow> ps, B = A \<and> C = A \<and> v \<noteq> []];
       us = [u. (B,u) \<leftarrow> ps, B = A \<and> (case u of Nt C # w \<Rightarrow> C \<noteq> A | _ \<Rightarrow> True) ]
  in if vs = [] then [(A,u). u \<leftarrow> us]
     else [(A,u). u \<leftarrow> us] @
     [(A, u @ [Nt A']). u \<leftarrow> us] @
     [(A', v). v \<leftarrow> vs] @
     [(A', v @ [Nt A']). v \<leftarrow> vs])"

lemma set_rrec_of_lrec: "set (rrec_of_lrec A A' ps) = Rrec_of_lrec A A' (set ps)"
proof-
  define vs where "vs = [v. (B, Nt C # v) \<leftarrow> ps, B = A \<and> C = A \<and> v \<noteq> []]"
  define us where "us = [u. (B,u) \<leftarrow> ps, B = A \<and> (case u of Nt C # w \<Rightarrow> C \<noteq> A | _ \<Rightarrow> True) ]"
  have 1: "{v. (A,Nt A # v) \<in> (set ps) \<and> v \<noteq> []} = set vs"
    by (auto simp: vs_def)
  have 2: "{u. (A,u) \<in> set ps \<and> (\<nexists>v. u = Nt A # v) } = set us"
    apply (auto split: list.splits sym.splits simp: neq_Nil_conv us_def)
    apply (metis sym.exhaust)
    by (metis neq_Nil_conv sym.exhaust)
  show ?thesis
    apply (unfold Rrec_of_lrec_def 1 2)
    apply (unfold rrec_of_lrec_def)
    apply (fold vs_def us_def)
    by (auto simp add: Let_def)
qed

text \<open>Solve left-recursions: Solves the left-recursion of Nt \<open>A\<close> by replacing it with a 
right-recursion on a fresh Nt \<open>A'\<close>. The fresh Nt \<open>A'\<close> is also given as a parameter.\<close>
definition Solve_lrec :: "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"Solve_lrec A A' P = Rm_lrec A P \<union> Rrec_of_lrec A A' P"

lemmas Solve_lrec_defs = Solve_lrec_def Rm_lrec_def Rrec_of_lrec_def Let_def Nts_def

definition solve_lrec :: "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"solve_lrec A A' P = rm_lrec A P @ rrec_of_lrec A A' P"

lemma set_solve_lrec: "set (solve_lrec A A' ps) = Solve_lrec A A' (set ps)"
  by (simp add: solve_lrec_def Solve_lrec_def set_rm_lrec set_rrec_of_lrec)

text \<open>Solve Triangular: Put \<open>R\<close> into Triangular form wrt \<open>As\<close> (using the new Nts \<open>As'\<close>).
In each step \<open>A#As\<close>, first the remaining Nts in \<open>As\<close> are solved, then \<open>A\<close> is solved.
This should mean that in the result of the outermost \<open>Expand_hd_rec A As\<close>, \<open>A\<close> only depends on \<open>A\<close>.
Then the \<open>A\<close> rules in the result of \<open>Solve_lrec A A'\<close> are already in GNF. More precisely:
the result should be in \<open>Triangular\<close> form.\<close>
fun Solve_tri :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) Prods \<Rightarrow> ('a, 'b) Prods" where
"Solve_tri (A#As) (A'#As') P = Solve_lrec A A' (Expand_hd_rec A As (Solve_tri As As' P))" |
"Solve_tri _ _ P = P"

fun solve_tri :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) prods \<Rightarrow> ('a, 'b) prods" where
"solve_tri (A#As) (A'#As') ps = solve_lrec A A' (expand_hd_rec A As (solve_tri As As' ps))" |
"solve_tri _ _ ps = ps"

lemma set_solve_tri: "set (solve_tri As As' ps) = Solve_tri As As' (set ps)"
  by (induction rule: solve_tri.induct, simp_all add: set_solve_lrec set_expand_hd_rec)

text \<open>Triangular form wrt \<open>[A1,\<dots>,An]\<close> means that \<open>Ai\<close> must not depend on \<open>Ai, \<dots>, An\<close>.
In particular: \<open>A0\<close> does not depend on any \<open>Ai\<close>, its rules are already in GNF.
Therefore one can convert a \<open>Triangular\<close> form into GNF by backwards substitution:
The rules for \<open>Ai\<close> are used to expand the heads of all \<open>A(i+1),\<dots>,An\<close> rules,
starting with \<open>A0\<close>.\<close>
fun Triangular :: "'n list \<Rightarrow> ('n \<times> ('n, 't) sym list) set \<Rightarrow> bool" where
"Triangular [] P = True" |
"Triangular (A#As) P = (dep_on P A \<inter> ({A} \<union> set As) = {} \<and> Triangular As P)"

text \<open>Remove self loops: Removes all productions of the form \<open>A \<rightarrow> A\<close>.\<close>
definition Rm_self_loops :: "('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
  "Rm_self_loops P = {(A,\<alpha>)\<in>P. \<alpha> \<noteq> [Nt A]}"

text \<open>Expand triangular: Expands all head-Nts of productions with a Lhs in \<open>As\<close> 
(\<open>Triangular (rev As)\<close>). In each step \<open>A#As\<close> first all Nts in \<open>As\<close> are expanded, then every rule 
\<open>A \<rightarrow> B w\<close> is expanded if \<open>B \<in> set As\<close>. If the productions were in \<open>Triangular\<close> form wrt \<open>rev As\<close> 
then \<open>Ai\<close> only depends on \<open>A(i+1), \<dots>, An\<close> which have already been expanded in the first part
of the step and are in GNF. Then the all \<open>A\<close>-productions are also is in GNF after expansion.\<close>

fun Expand_tri :: "'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"Expand_tri [] P = P" |
"Expand_tri (A#As) P =
 (let P' = Expand_tri As P;
      X = {r \<in> P'. \<exists>w B. r = (A, Nt B # w) \<and> B \<in> set As}
  in Subst_hd P' X)"

fun expand_tri :: "'n list \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"expand_tri [] P = P" |
"expand_tri (A#As) P =
 (let P' = expand_tri As P;
      X = filter (\<lambda>(A',Nt B # \<alpha>) \<Rightarrow> A' = A \<and> B \<in> set As | _ \<Rightarrow> False) P'
  in subst_hd P' X)"

lemma set_expand_tri: "set (expand_tri As P) = Expand_tri As (set P)"
proof-
  have 1: "(\<exists>w B. r = (A, Nt B # w) \<and> B \<in> X) =
  (case r of (A',Nt B # \<alpha>) \<Rightarrow> A' = A \<and> B \<in> X | _ \<Rightarrow> False)" for r A X
    apply (auto simp: neq_Nil_conv split: list.splits sym.splits)
    apply (metis destTm.cases)
    by (metis sym.exhaust)
  show ?thesis
    by (induction rule: expand_tri.induct, simp_all add: set_subst_hd Let_def 1 )
qed

declare Expand_tri.simps(1)[code]
lemma Expand_tri_Cons_code[code]: "Expand_tri (S#Ss) R =
 (let P' = Expand_tri Ss R;
      X = {w \<in> Rhss P' S. w \<noteq> [] \<and> hd w \<in> Nt ` set Ss};
      Y = (\<Union>(B,v) \<in> P'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(S,v @ tl w)})
  in P' - ({S} \<times> X) \<union> Y)"
by(simp add: Let_def Rhss_def neq_Nil_conv Ball_def Subst_hd_def, safe, force+)

text \<open>The main function \<open>GNF_hd_of\<close> converts into \<open>GNF_hd\<close>:\<close>
definition GNF_hd_of :: "'n::fresh list \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"GNF_hd_of As P =
 (let As' = freshs (set As) As
  in Expand_tri (As' @ rev As) (Solve_tri As As' (Eps_elim P)))"

definition gnf_hd_of :: "('n::fresh,'t)prods \<Rightarrow> ('n,'t)prods" where
"gnf_hd_of P =
 (let As = nts P; As' = freshs (set As) As
  in expand_tri (As' @ rev As) (solve_tri As As' (eps_elim P)))"

lemma set_gnf_hd_of: "set (gnf_hd_of P) = GNF_hd_of (nts P) (set P)"
  by (simp add: GNF_hd_of_def gnf_hd_of_def set_expand_tri set_solve_tri set_eps_elim Let_def)

section \<open>Some Basic Lemmas\<close>

subsection \<open>\<open>Eps_free\<close> preservation\<close>

lemma Eps_free_Expand_hd_rec: "Eps_free R \<Longrightarrow> Eps_free (Expand_hd_rec A Ss R)"
  by (induction A Ss R rule: Expand_hd_rec.induct)
    (auto simp add: Eps_free_def Let_def Subst_hd_def)

lemma Eps_free_Solve_lrec: "Eps_free R \<Longrightarrow> Eps_free (Solve_lrec A A' R)"
  unfolding Solve_lrec_defs Eps_free_def by (auto)

lemma Eps_free_Solve_tri: "Eps_free R \<Longrightarrow> Eps_free (Solve_tri As As' R)"
  by (induction As As' R rule: Solve_tri.induct) 
    (auto simp add: Eps_free_Solve_lrec Eps_free_Expand_hd_rec)

lemma Eps_free_Expand_tri: "Eps_free R \<Longrightarrow> Eps_free (Expand_tri As R)"
  by (induction As R rule: Expand_tri.induct) (auto simp add: Let_def Eps_free_def Subst_hd_def)


subsection \<open>Lemmas about \<open>Nts\<close> and \<open>dep_on\<close>\<close>

lemma dep_on_Un[simp]: "dep_on (R \<union> S) A = dep_on R A \<union> dep_on S A"
  by(auto simp add: dep_on_def)

lemma dep_on_empty[simp]: "dep_on {} A = {}"
  by (simp add: dep_on_def)

lemma dep_on_insert: "dep_on (insert (A,w) P) A' =
  (if A = A' then case w of Nt B # w' \<Rightarrow> {B} | _ \<Rightarrow> {} else {}) \<union> dep_on P A'"
  by (auto simp: dep_on_def split: list.splits sym.splits)

lemma Expand_hd_rec_preserves_neq: "B \<noteq> A \<Longrightarrow> (B,w) \<in> Expand_hd_rec A Ss R \<longleftrightarrow> (B,w) \<in> R"
  by(induction A Ss R rule: Expand_hd_rec.induct) (auto simp add: Let_def Subst_hd_def)

text \<open>Let \<open>R\<close> be epsilon-free and in \<open>Triangular\<close> form wrt \<open>Bs\<close>.
After \<open>Expand_hd_rec A Bs R\<close>, \<open>A\<close> depends only on what \<open>A\<close> depended on before or
what one of the \<open>B \<in> Bs\<close> depends on, but \<open>A\<close> does not depend on the \<open>Bs\<close>:\<close>
lemma dep_on_Expand_hd_rec:
  "\<lbrakk> Eps_free R; Triangular Bs R; distinct Bs; A \<notin> set Bs \<rbrakk>
  \<Longrightarrow> dep_on (Expand_hd_rec A Bs R) A \<subseteq> (dep_on R A \<union> (\<Union>B\<in>set Bs. dep_on R B)) - set Bs"
proof(induction A Bs R rule: Expand_hd_rec.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A B Bs R)
  then show ?case
    by(fastforce simp add: Let_def dep_on_def Cons_eq_append_conv Eps_free_Expand_hd_rec Eps_free_Nil 
        Subst_hd_def Expand_hd_rec_preserves_neq set_eq_iff)
qed

lemma Expand_hd_rec_id: "dep_on P A \<inter> set As = {} \<Longrightarrow> Expand_hd_rec A As P = P"
  by (induction As, auto simp: dep_on_def Subst_hd_def)

lemma dep_on_subs_Nts: "dep_on R A \<subseteq> Nts R"
  by (auto simp add: Nts_def dep_on_def)

section \<open>Transformations and Symbols\<close>

lemma Lhss_Subst_hd: "Lhss (Subst_hd P X) \<subseteq> Lhss P \<union> Lhss X"
  by (auto simp: Lhss_def Subst_hd_def)

lemma Rhs_Nts_Subst_hd: "Rhs_Nts (Subst_hd P X) \<subseteq> Rhs_Nts P \<union> Rhs_Nts X"
  by (auto simp: Subst_hd_def Rhs_Nts_def Nts_syms_def split: prod.splits)

lemma Nts_Subst_hd: "Nts (Subst_hd P X) \<subseteq> Nts P \<union> Nts X"
  using Un_mono[OF Lhss_Subst_hd Rhs_Nts_Subst_hd]
  by (simp add: Nts_Lhss_Rhs_Nts ac_simps)

lemma Tms_Subst_hd: "Tms (Subst_hd P X) \<subseteq> Tms P \<union> Tms X"
  by (auto simp: Subst_hd_def Tms_def Tms_syms_def split: prod.splits)

lemma Lhss_Expand_hd_rec: "Lhss (Expand_hd_rec A Ss P) \<subseteq> Lhss P"
  and Tms_Expand_hd_rec: "Tms (Expand_hd_rec A Ss P) \<subseteq> Tms P"
  and Rhs_Nts_Expand_hd_rec: "Rhs_Nts (Expand_hd_rec A Ss P) \<subseteq> Rhs_Nts P"
proof (atomize(full), induction Ss arbitrary: P)
  case Nil
  show ?case by simp
next
  case (Cons S Ss)
  define P' where "P' = Expand_hd_rec A Ss P"
  define X where "X = {r \<in> P'. \<exists>w. r = (A, Nt S # w)}"
  have "Lhss X \<subseteq> Lhss P'" and "Tms X \<subseteq> Tms P'" and "Rhs_Nts X \<subseteq> Rhs_Nts P'"
    by (auto simp: X_def Lhss_def Tms_def Tms_syms_def Rhs_Nts_def Nts_syms_def)
  moreover from Cons
  have "Lhss P' \<subseteq> Lhss P" and "Tms P' \<subseteq> Tms P" and "Rhs_Nts P' \<subseteq> Rhs_Nts P" by (auto simp: P'_def)
  ultimately show ?case
    by (auto simp flip: P'_def X_def dest!: subsetD[OF Lhss_Subst_hd] subsetD[OF Tms_Subst_hd] subsetD[OF Rhs_Nts_Subst_hd])
qed

lemma Nts_Expand_hd_rec: "Nts (Expand_hd_rec A Ss P) \<subseteq> Nts P"
  using Un_mono[OF Lhss_Expand_hd_rec Rhs_Nts_Expand_hd_rec]
  by (simp add: Nts_Lhss_Rhs_Nts ac_simps)

lemma Tms_Solve_lrec: "Tms (Solve_lrec A A' P) \<subseteq> Tms P"
  by (auto simp: Tms_def Tms_syms_def Solve_lrec_defs)

lemma Lhss_Solve_lrec: "Lhss (Solve_lrec A A' P) \<subseteq> Lhss P \<union> {A'}"
  by (auto simp: Lhss_def Solve_lrec_defs)

lemma Rhs_Nts_Solve_lrec: "Rhs_Nts (Solve_lrec A A' P) \<subseteq> Rhs_Nts P \<union> {A'}"
  by (auto simp: Rhs_Nts_def Solve_lrec_defs)

lemma Nts_Solve_lrec: "Nts (Solve_lrec A A' P) \<subseteq> Nts P \<union> {A'}"
  using Lhss_Solve_lrec[of A A' P] Rhs_Nts_Solve_lrec[of A A' P]
  by (auto simp: Nts_Lhss_Rhs_Nts)

lemma Lhss_Solve_tri: "Lhss (Solve_tri As As' P) \<subseteq> Lhss P \<union> set As'"
  and Tms_Solve_tri: "Tms (Solve_tri As As' P) \<subseteq> Tms P"
  and Rhs_Nts_Solve_tri: "Rhs_Nts (Solve_tri As As' P) \<subseteq> Rhs_Nts P \<union> set As'"
  apply (induction rule: Solve_tri.induct)
  by (auto dest!:
      subsetD[OF Lhss_Solve_lrec] subsetD[OF Lhss_Expand_hd_rec]
      subsetD[OF Tms_Solve_lrec] subsetD[OF Tms_Expand_hd_rec]
      subsetD[OF Rhs_Nts_Solve_lrec] subsetD[OF Rhs_Nts_Expand_hd_rec])

lemma Nts_Solve_tri: "Nts (Solve_tri As As' P) \<subseteq> Nts P \<union> set As'"
  using Lhss_Solve_tri[of As As' P] Rhs_Nts_Solve_tri[of As As' P]
  by (auto simp: Nts_Lhss_Rhs_Nts)

lemma Lhss_Expand_tri: "Lhss (Expand_tri As P) \<subseteq> Lhss P"
  and Tms_Expand_tri: "Tms (Expand_tri As P) \<subseteq> Tms P"
  and Rhs_Nts_Expand_tri: "Rhs_Nts (Expand_tri As P) \<subseteq> Rhs_Nts P"
proof (atomize(full), induction As)
  case Nil
  show ?case by simp
next
  case (Cons A As)
  define P' where "P' = Expand_tri As P"
  define X where "X = {r \<in> P'. \<exists>w B. r = (A, Nt B # w) \<and> B \<in> set As}"
  from Cons have 1: "Lhss P' \<subseteq> Lhss P" "Tms P' \<subseteq> Tms P" "Rhs_Nts P' \<subseteq> Rhs_Nts P"
    by (auto simp: P'_def)
  have 2: "Lhss X \<subseteq> Lhss P'" "Tms X \<subseteq> Tms P'" "Rhs_Nts X \<subseteq> Rhs_Nts P'"
    by (auto simp: X_def Lhss_def Tms_def Rhs_Nts_def)
  show ?case
    by (auto simp flip: P'_def X_def
        dest!: subsetD[OF Lhss_Subst_hd] subsetD[OF Tms_Subst_hd] subsetD[OF Rhs_Nts_Subst_hd]
        1[THEN subsetD] 2[THEN subsetD])
qed

lemma Nts_Expand_tri: "Nts (Expand_tri As P) \<subseteq> Nts P"
  using Lhss_Expand_tri[of As P] Rhs_Nts_Expand_tri[of As P]
  by (auto simp: Nts_Lhss_Rhs_Nts)

lemma Lhss_GNF_hd_of: "Lhss (GNF_hd_of As P) \<subseteq> Lhss P \<union> set (freshs (set As) As)"
  by (auto simp: GNF_hd_of_def Let_def
      dest!: subsetD[OF Lhss_Expand_tri] subsetD[OF Lhss_Solve_tri] subsetD[OF Lhss_Eps_elim])

lemma Rhs_Nts_GNF_hd_of: "Rhs_Nts (GNF_hd_of As P) \<subseteq> Rhs_Nts P \<union> set (freshs (set As) As)"
  by (auto simp: GNF_hd_of_def Let_def
      dest!: subsetD[OF Rhs_Nts_Expand_tri] subsetD[OF Rhs_Nts_Solve_tri] subsetD[OF Rhs_Nts_Eps_elim])

lemma Tms_GNF_hd_of: "Tms (GNF_hd_of As P) \<subseteq> Tms P"
  by (auto simp: GNF_hd_of_def Let_def
      dest!: subsetD[OF Tms_Expand_tri] subsetD[OF Tms_Solve_tri] subsetD[OF Tms_Eps_elim])

lemma Nts_GNF_hd_of: "Nts (GNF_hd_of As P) \<subseteq> Nts P \<union> set (freshs (set As) As)"
  using Lhss_GNF_hd_of[of As P] Rhs_Nts_GNF_hd_of[of As P]
  by (auto simp: Nts_Lhss_Rhs_Nts)

subsection \<open>Lemmas about \<open>Triangular\<close>\<close>

lemma tri_Snoc_impl_tri: "Triangular (As @ [A]) R \<Longrightarrow> Triangular As R"
  by (induction As R rule: Triangular.induct, auto)

text \<open>If two parts of the productions are \<open>Triangular\<close> and no Nts from the first part depend on 
      ones of the second they are also \<open>Triangular\<close> when put together.\<close>
lemma Triangular_append: 
  "\<lbrakk>Triangular As R; Triangular Bs R; \<forall>A\<in>set As. dep_on R A \<inter> set Bs = {}\<rbrakk> 
   \<Longrightarrow> Triangular (As@Bs) R"
  by (induction As) auto


section \<open>Function \<open>Solve_tri\<close>: Remove Left-Recursion and Convert into Triangular Form\<close>

subsection \<open>Basic Lemmas\<close>

text \<open>Mostly about rule inclusions in \<open>Solve_lrec\<close>.\<close>

lemma Solve_lrec_rule_simp1: "A \<noteq> B \<Longrightarrow> A \<noteq> B' \<Longrightarrow> (A, w) \<in> Solve_lrec B B' R \<longleftrightarrow> (A, w) \<in> R"
  unfolding Solve_lrec_defs by (auto)

lemma Solve_lrec_rule_simp3: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> Eps_free R 
  \<Longrightarrow> (A, [Nt A']) \<notin> Solve_lrec A A' R"
  unfolding Solve_lrec_defs by (auto simp: Eps_free_def)

lemma Solve_lrec_rule_simp7: "A' \<noteq> A \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> (A', Nt A' # w) \<notin> Solve_lrec A A' R"
unfolding Solve_lrec_defs by(auto simp: neq_Nil_conv split: prod.splits)

lemma Solve_lrec_rule_simp8: "A' \<notin> Nts R \<Longrightarrow> B \<noteq> A' \<Longrightarrow> B \<noteq> A 
  \<Longrightarrow> (B, Nt A' # w) \<notin> Solve_lrec A A' R"
unfolding Solve_lrec_defs by (auto split: prod.splits)

lemma dep_on_Expand_hd_rec_simp2: "B \<noteq> A \<Longrightarrow> dep_on (Expand_hd_rec A As R) B = dep_on R B"
  by (auto simp add: dep_on_def Expand_hd_rec_preserves_neq)

lemma dep_on_Solve_lrec_simp2: "A \<noteq> B \<Longrightarrow> A' \<noteq> B \<Longrightarrow> dep_on (Solve_lrec A A' R) B = dep_on R B"
unfolding Solve_lrec_defs dep_on_def by (auto)

lemma Solve_lrec_id: "A \<notin> dep_on P A \<Longrightarrow> Solve_lrec A A' P = P"
  by (auto simp: Solve_lrec_defs dep_on_def)

lemma Solve_tri_id:
  "\<lbrakk>Triangular As P; length As' = length As\<rbrakk> \<Longrightarrow> Solve_tri As As' P = P"
  by (induction rule: Solve_tri.induct, simp_all add: Expand_hd_rec_id Solve_lrec_id)


subsection \<open>Triangular Form\<close>

text
\<open>\<open>Expand_hd_rec\<close> preserves \<open>Triangular\<close>, if it does not expand a Nt considered in \<open>Triangular\<close>.\<close>
lemma Triangular_Expand_hd_rec: "\<lbrakk>A \<notin> set As; Triangular As R\<rbrakk> \<Longrightarrow> Triangular As (Expand_hd_rec A Bs R)"
  by (induction As) (auto simp add: dep_on_Expand_hd_rec_simp2)

text \<open>Solving a Nt not considered by \<open>Triangular\<close> preserves the \<open>Triangular\<close> property.\<close>
lemma Triangular_Solve_lrec: "\<lbrakk>A \<notin> set As; A' \<notin> set As; Triangular As R\<rbrakk> 
  \<Longrightarrow> Triangular As (Solve_lrec A A' R)"
proof(induction As)
  case Nil
  then show ?case by simp
next
  case (Cons a As)
  have "Triangular (a # As) (Solve_lrec A A' R) = 
    (dep_on (Solve_lrec A A' R) a \<inter> ({a} \<union> set As) = {} \<and> Triangular As (Solve_lrec A A' R))"
    by simp
  also have "... = (dep_on (Solve_lrec A A' R) a \<inter> ({a} \<union> set As) = {})" using Cons by auto
  also have "... = (dep_on R a \<inter> ({a} \<union> set As) = {})" using Cons dep_on_Solve_lrec_simp2
    by (metis list.set_intros(1))
  then show ?case using Cons by auto
qed

text \<open>Solving more Nts does not remove the \<open>Triangular\<close> property of previously solved Nts.\<close>
lemma part_Triangular_induct_step: 
  "\<lbrakk>Eps_free R; distinct ((A#As)@(A'#As')); Triangular As (Solve_tri As As' R)\<rbrakk> 
  \<Longrightarrow> Triangular As (Solve_tri (A#As) (A'#As') R)"
  by (cases "As = []")
    (auto simp add: Triangular_Expand_hd_rec Triangular_Solve_lrec)

text \<open>Couple of small lemmas about \<open>dep_on\<close> and the solving of left-recursion.\<close>
lemma Rm_lrec_rem_own_dep: "A \<notin> dep_on (Rm_lrec A R) A"
  by (auto simp add: dep_on_def Rm_lrec_def)

lemma Rrec_of_lrec_has_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (Rrec_of_lrec A A' R) A"
  by (auto simp add: dep_on_def Rrec_of_lrec_def Let_def Cons_eq_append_conv)

lemma Solve_lrec_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (Solve_lrec A A' R) A"
  by (auto simp add: Solve_lrec_def Rm_lrec_rem_own_dep Rrec_of_lrec_has_no_own_dep)

lemma Solve_lrec_no_new_own_dep: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> A' \<notin> dep_on (Solve_lrec A A' R) A'"
  by (auto simp add: dep_on_def Solve_lrec_rule_simp7)  
  
lemma dep_on_rem_lrec_simp: "dep_on (Rm_lrec A R) A = dep_on R A - {A}"
  by (auto simp add: dep_on_def Rm_lrec_def)

lemma dep_on_Rrec_of_lrec_simp:
  "Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> dep_on (Rrec_of_lrec A A' R) A = dep_on R A - {A}"
  using Eps_freeE_Cons[of R A "[]"]
  by (auto simp add: dep_on_def Rrec_of_lrec_def Let_def Cons_eq_append_conv)

lemma dep_on_Solve_lrec_simp: 
  "\<lbrakk>Eps_free R; A \<noteq> A'\<rbrakk> \<Longrightarrow> dep_on (Solve_lrec A A' R) A = dep_on R A - {A}"
  by (simp add: dep_on_rem_lrec_simp dep_on_Rrec_of_lrec_simp Solve_lrec_def)

lemma dep_on_Solve_tri_simp: "B \<notin> set As \<Longrightarrow> B \<notin> set As'
  \<Longrightarrow> dep_on (Solve_tri As As' R) B = dep_on R B"
proof (induction As As' R rule: Solve_tri.induct)
  case *: (1 A As A' As' R)
  have "dep_on (Solve_tri (A#As) (A'#As') R) B = dep_on (Expand_hd_rec A As (Solve_tri As As' R)) B" 
    using * by (auto simp add: dep_on_Solve_lrec_simp2)
  then show ?case using * by (auto simp add: dep_on_Expand_hd_rec_simp2)
qed auto

text \<open>Induction step for showing that \<open>Solve_tri\<close> removes dependencies of previously solved Nts.\<close>
lemma Triangular_dep_on_induct_step: 
  assumes "Eps_free R" "distinct ((A#As)@A'#As')" "Triangular As (Solve_tri As As' R)"
  shows "dep_on (Solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {}"
proof(cases "As = []")
  case True
  with assms Solve_lrec_no_own_dep show ?thesis by fastforce
next
  case False
  have "Eps_free (Solve_tri As As' R)"
    using assms Eps_free_Solve_tri by auto
  then have test: "X \<in> set As \<Longrightarrow> X \<notin> dep_on (Expand_hd_rec A As (Solve_tri As As' R)) A" for X
    using assms dep_on_Expand_hd_rec
    by (metis distinct.simps(2) distinct_append insert_Diff subset_Diff_insert)

  have A: "Triangular As (Solve_tri (A # As) (A' # As') R)" 
    using part_Triangular_induct_step assms by metis

  have "dep_on (Solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) 
        = (dep_on (Expand_hd_rec A As (Solve_tri As As' R)) A - {A}) \<inter> ({A} \<union> set  As)"
    using assms by (simp add: dep_on_Solve_lrec_simp Eps_free_Solve_tri Eps_free_Expand_hd_rec)
  also have "... = dep_on (Expand_hd_rec A As (Solve_tri As As' R)) A \<inter> set As"
    using assms by auto
  also have "... = {}" using test by fastforce
  finally show ?thesis by auto
qed

theorem Triangular_Solve_tri_orig:
  "\<lbrakk> Eps_free P; length As \<le> length As'; distinct(As @ As')\<rbrakk>
  \<Longrightarrow> Triangular As (Solve_tri As As' P)"
proof(induction As As' P rule: Solve_tri.induct)
  case *: (1 A As A' As' R)
  then have "length As \<le> length As' \<and> distinct (As @ As')" by auto
  then have A: "Triangular As (Solve_tri (A # As) (A' # As') R)" 
    using part_Triangular_induct_step * by metis
  have "(dep_on (Solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {})"
    using Triangular_dep_on_induct_step * 
    by (metis \<open>length As \<le> length As' \<and> distinct (As @ As')\<close>) 
  then show ?case using A by simp
qed auto

lemma dep_on_Solve_tri_Nts_R: 
  "\<lbrakk>Eps_free R; B \<in> set As; distinct (As @ As'); set As' \<inter> Nts R = {}; length As \<le> length As'\<rbrakk>
    \<Longrightarrow> dep_on (Solve_tri As As' R) B \<subseteq> Nts R"
proof (induction As As' R arbitrary: B rule: Solve_tri.induct)
  case *: (1 A As A' As' R)
  then have F1: "dep_on (Solve_tri As As' R) B \<subseteq> Nts R"
    by (cases "B = A") (simp_all add: dep_on_Solve_tri_simp dep_on_subs_Nts)
  then have F2: "dep_on (Expand_hd_rec A As (Solve_tri As As' R)) B \<subseteq> Nts R"
  proof (cases "B = A")
    case True
    have "Triangular As (Solve_tri As As' R)" using * by (auto simp add: Triangular_Solve_tri_orig)
    then have "dep_on (Expand_hd_rec A As (Solve_tri As As' R)) B \<subseteq> dep_on (Solve_tri As As' R) B 
       \<union> \<Union> (dep_on (Solve_tri As As' R) ` set As) - set As"
      using * True by (auto simp add: dep_on_Expand_hd_rec Eps_free_Solve_tri)
    also have "... \<subseteq> Nts R" using * F1 by auto
    finally show ?thesis.
  next
    case False
    then show ?thesis using F1 by (auto simp add: dep_on_Expand_hd_rec_simp2)
  qed
  then have "dep_on (Solve_lrec A A' (Expand_hd_rec A As (Solve_tri As As' R))) B \<subseteq> Nts R"
  proof (cases "B = A")
    case True
    then show ?thesis 
      using * F2 by (auto simp add: dep_on_Solve_lrec_simp Eps_free_Solve_tri Eps_free_Expand_hd_rec)
  next
    case False
    have "B \<noteq> A'" using * by auto
    then show ?thesis using * F2 False by (simp add: dep_on_Solve_lrec_simp2)
  qed
  then show ?case by simp
qed auto

lemma Triangular_unused_Nts: "set As \<inter> Nts R = {} \<Longrightarrow> Triangular As R"
proof (induction As)
  case Nil
  then show ?case by auto
next
  case (Cons a As)
  have "dep_on R a \<subseteq> Nts R" by (simp add: dep_on_subs_Nts)
  then have "dep_on R a \<inter> (set As  \<union> {a}) = {}" using Cons by auto
  then show ?case using Cons by auto
qed

text \<open>The newly added Nts in \<open>Solve_lrec\<close> are in \<open>Triangular\<close> form wrt \<open>rev As'\<close>.\<close>
lemma Triangular_Solve_tri_new: 
  "\<lbrakk>set As' \<inter> Nts R = {}; distinct (As @ As')\<rbrakk> 
   \<Longrightarrow> Triangular (rev As') (Solve_tri As As' R)"
proof (induction As As' R rule: Solve_tri.induct)
  case *: (1 A As A' As' R)
  then have "Triangular (rev As') (Solve_tri As As' R)" by simp
  then have "Triangular (rev As') (Expand_hd_rec A As (Solve_tri As As' R))"
    using * by (auto simp add: Triangular_Expand_hd_rec)
  then have F1: "Triangular (rev As') (Solve_tri (A#As) (A'#As') R)"
    using * by (auto simp add: Triangular_Solve_lrec)
  have "Nts (Solve_tri As As' R) \<subseteq> Nts R \<union> set As'" using * by (auto simp add: Nts_Solve_tri)
  then have F_nts: "Nts (Expand_hd_rec A As (Solve_tri As As' R)) \<subseteq> Nts R \<union> set As'"
    using Nts_Expand_hd_rec[of A As "(Solve_tri As As' R)"] by auto
  then have "A' \<notin> dep_on (Solve_lrec A A' (Expand_hd_rec A As (Solve_tri As As' R))) A'" 
    using * Solve_lrec_no_new_own_dep[of A A'] by auto
  then have F2: "Triangular [A'] (Solve_tri (A#As) (A'#As') R)" by auto
  have "\<forall>a\<in>set As'. dep_on (Solve_tri (A#As) (A'#As') R) a \<inter> set [A'] = {}"
  proof
    fix a
    assume "a \<in> set As'"
    then have "A' \<notin> Nts (Expand_hd_rec A As (Solve_tri As As' R)) \<and> a \<noteq> A" using F_nts * by auto
    then show "dep_on (Solve_tri (A#As) (A'#As') R) a \<inter> set [A'] = {}" 
      using * Solve_lrec_rule_simp8[of A' "(Expand_hd_rec A As (Solve_tri As As' R))" a A] 
            Solve_lrec_rule_simp7[of A'] 
      by (cases "a = A'") (auto simp add: dep_on_def)
  qed
    
  then have "Triangular (rev (A'#As')) (Solve_tri (A#As) (A'#As') R)" 
    using F1 F2 by (auto simp add: Triangular_append)
  then show ?case by auto
qed (auto simp add:Triangular_unused_Nts)

text \<open>The entire set of productions is in \<open>Triangular\<close> form after \<open>Solve_tri\<close> wrt \<open>As@(rev As')\<close>.\<close>
theorem Triangular_Solve_tri:
  assumes "Eps_free P" "length As \<le> length As'" "distinct(As @ As')" "Nts P \<subseteq> set As" 
    shows "Triangular (As@(rev As')) (Solve_tri As As' P)"
proof -
  from assms have 1: "Triangular As (Solve_tri As As' P)" by (auto simp add: Triangular_Solve_tri_orig)
  have "set As' \<inter> Nts P = {}" using assms by auto
  then have 2: "Triangular (rev As') (Solve_tri As As' P)" 
    using assms by (auto simp add: Triangular_Solve_tri_new)
  have "set As' \<inter> Nts P = {}" using assms by auto
  then have "\<forall>A\<in>set As. dep_on (Solve_tri As As' P) A \<subseteq> Nts P" 
    using assms by (auto simp add: dep_on_Solve_tri_Nts_R)
  then have "\<forall>A\<in>set As. dep_on (Solve_tri As As' P) A \<inter> set As' = {}" using assms by auto
  then show ?thesis using 1 2 by (auto simp add: Triangular_append)
qed


subsection \<open>\<open>Solve_lrec\<close> Preserves Language\<close>

subsubsection \<open>@{prop "Lang (Solve_lrec B B' R) A \<supseteq> Lang R A"}\<close>

text \<open>Restricted to productions with one lhs (\<open>A\<close>), and no \<open>A \<rightarrow> A\<close> productions
      if there is a derivation from \<open>u\<close> to \<open>A # v\<close> then \<open>u\<close> must start with Nt \<open>A\<close>.\<close>
lemma lrec_lemma1: 
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "Rm_self_loops S \<turnstile> u \<Rightarrow>l(n) Nt A#v"
  shows "\<exists>u'. u = Nt A # u'"
proof (rule ccontr)
  assume neg: "\<nexists>u'. u = Nt A # u'"
  show "False"
  proof (cases "u = []")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then show ?thesis
    proof (cases "\<exists>t. hd u = Tm t")
      case True
      then show ?thesis using assms neg
        by (metis (no_types, lifting) False deriveln_Tm_Cons hd_Cons_tl list.inject)
    next
      case False
      then have "\<exists>B u'. u = Nt B # u' \<and> B \<noteq> A" using assms neg
        by (metis deriveln_from_empty list.sel(1) neq_Nil_conv sym.exhaust)
      then obtain B u' where B_not_A: "u = Nt B # u' \<and> B \<noteq> A" by blast
      then have "\<exists>w. (B, w) \<in> Rm_self_loops S" using assms neg
        by (metis (no_types, lifting) derivels_Nt_Cons relpowp_imp_rtranclp)
      then obtain w where elem: "(B, w) \<in> Rm_self_loops S" by blast
      have "(B, w) \<notin> Rm_self_loops S" using B_not_A assms by (auto simp add: Rm_self_loops_def)
      then show ?thesis using elem by simp
    qed
  qed
qed


text \<open>Restricted to productions with one lhs (\<open>A\<close>), and no \<open>A \<rightarrow> A\<close> productions
      if there is a derivation from \<open>u\<close> to \<open>A # v\<close> then \<open>u\<close> must start with Nt \<open>A\<close> and there 
      exists a prefix of \<open>A # v\<close> s.t. a left-derivation from \<open>[Nt A]\<close> to that prefix exists.\<close>
lemma  lrec_lemma2:
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "Eps_free R"
  shows "Rm_self_loops S \<turnstile> u \<Rightarrow>l(n) Nt A#v \<Longrightarrow> 
    \<exists>u' v'. u = Nt A # u' \<and> v = v' @ u' \<and> (Rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v'"
proof (induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "\<exists>u'. u = Nt A # u'" using lrec_lemma1[of S] Suc assms by auto
  then obtain u' where u'_prop: "u = Nt A # u'" by blast
  then have "\<exists>w. (A,w) \<in> (Rm_self_loops S) \<and> (Rm_self_loops S) \<turnstile> w @ u' \<Rightarrow>l(n) Nt A # v" 
    using Suc by (auto simp add: deriveln_Nt_Cons split: prod.split)
  then obtain w where w_prop: 
    "(A,w) \<in> (Rm_self_loops S) \<and> (Rm_self_loops S) \<turnstile> w @ u' \<Rightarrow>l(n) Nt A # v" 
    by blast
  then have "\<exists>u'' v''. w @ u' = Nt A # u'' \<and>  v = v'' @ u'' \<and> 
    (Rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v''" 
    using Suc.IH Suc by auto
  then obtain u'' v'' where u''_prop: "w @ u' = Nt A # u'' \<and>  v = v'' @ u''" and
    ln_derive: "(Rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v''"
    by blast
  have "w \<noteq> [] \<and> w \<noteq> [Nt A]" 
    using Suc w_prop assms by (auto simp add: Eps_free_Nil Rm_self_loops_def split: prod.splits)
  then have "\<exists>u1. u1 \<noteq> [] \<and> w = Nt A # u1 \<and> u'' = u1 @ u'" 
    using u''_prop by (metis Cons_eq_append_conv)
  then obtain u1 where u1_prop: "u1 \<noteq> [] \<and> w = Nt A # u1 \<and> u'' = u1 @ u'" by blast
  then have 1: "u = Nt A # u' \<and> v = (v'' @ u1) @ u'" using u'_prop u''_prop by auto
  
  have 2: "(Rm_self_loops S) \<turnstile> [Nt A] @ u1 \<Rightarrow>l(n) Nt A # v'' @ u1" 
    using ln_derive deriveln_append
    by fastforce
  have "(Rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l [Nt A] @ u1" 
    using w_prop u''_prop u1_prop
    by (simp add: derivel_Nt_Cons)
  then have "(Rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(Suc n) Nt A # v'' @ u1" 
    using ln_derive
    by (meson 2 relpowp_Suc_I2)
  then show ?case using 1 by blast
qed

text \<open>Restricted to productions with one lhs (\<open>A\<close>), and no \<open>A \<rightarrow> A\<close> productions
  if there is a left-derivation from \<open>[Nt A]\<close> to \<open>A # u\<close> then there exists a derivation
  from \<open>[Nt A']\<close> to \<open>u@[Nt A]\<close> and if \<open>u \<noteq> []\<close> also to \<open>u\<close> in \<open>Solve_lrec A A' R\<close>.\<close>
lemma lrec_lemma3: 
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "Eps_free R"
  shows "Rm_self_loops S \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u
  \<Longrightarrow> Solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(n) u @ [Nt A'] \<and> 
      (u \<noteq> [] \<longrightarrow> Solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(n) u)"
proof(induction n arbitrary: u)
  case 0
  then show ?case by (simp)
next
  case (Suc n)
  then have "\<exists>w. (A,w) \<in> Rm_self_loops S \<and> Rm_self_loops S \<turnstile> w \<Rightarrow>l(n) Nt A # u"
    by (auto simp add: deriveln_Nt_Cons split: prod.splits)
  then obtain w where w_prop1: "(A,w) \<in> (Rm_self_loops S) \<and> (Rm_self_loops S) \<turnstile> w \<Rightarrow>l(n) Nt A#u"
    by blast
  then have "\<exists>w' u'. w = Nt A # w' \<and> u = u' @ w' \<and> (Rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u'"
    using lrec_lemma2[of S] Suc assms by auto
  then obtain w' u' where w_prop2: "w = Nt A # w' \<and> u = u' @ w'" and
    ln_derive: "Rm_self_loops S \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u'" by blast
  then have "w' \<noteq> []" using w_prop1 Suc by (auto simp add: Rm_self_loops_def)
  have "(A, w) \<in> S" using Suc.prems(1) w_prop1 by (auto simp add: Rm_self_loops_def)
  then have prod_in_Solve_lrec: "(A', w' @ [Nt A']) \<in> Solve_lrec A A' S"
    using w_prop2 \<open>w' \<noteq> []\<close> unfolding Solve_lrec_defs by (auto)

  have 1: "Solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(n) u' @ [Nt A']" using Suc.IH Suc ln_derive by auto
  then have 2: "Solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(Suc n) u' @ w' @ [Nt A']"
    using prod_in_Solve_lrec by (simp add: derive_prepend derive_singleton relpowp_Suc_I)

  have "(A', w') \<in> Solve_lrec A A' S" using w_prop2 \<open>w' \<noteq> []\<close> \<open>(A, w) \<in> S\<close>
    unfolding Solve_lrec_defs by (auto)
  then have "Solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(Suc n) u' @ w'" 
    using 1 by (simp add: derive_prepend derive_singleton relpowp_Suc_I)
  then show ?case using w_prop2 2 by simp
qed


text \<open>A left derivation from \<open>p\<close> (\<open>hd p = Nt A\<close>) to \<open>q\<close> (\<open>hd q \<noteq> Nt A\<close>) can be split into 
  a left-recursive part, only using left-recursive productions \<open>A \<rightarrow> A # w\<close>, 
  one left derivation step consuming Nt \<open>A\<close> using some rule \<open>A \<rightarrow> B # v\<close> where \<open>B \<noteq> Nt A\<close>
  and a left-derivation comprising the rest of the derivation.\<close>
lemma lrec_decomp: 
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "Eps_free R"
  shows "\<lbrakk> hd p = Nt A; hd q \<noteq> Nt A; R \<turnstile> p \<Rightarrow>l(n) q \<rbrakk>
  \<Longrightarrow> \<exists>u w m k. S \<turnstile> p \<Rightarrow>l(m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w \<and> hd w \<noteq> Nt A \<and>
       R \<turnstile> w \<Rightarrow>l(k) q \<and> n = m + k + 1"
proof (induction n arbitrary: p)
  case 0
  then have pq_not_Nil: "p \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil assms
    by simp

  have "p = q" using 0 by auto
  then show ?case using pq_not_Nil 0 by auto
next
  case (Suc n)
  then have pq_not_Nil: "p \<noteq> [] \<and> q \<noteq> []"
    using Eps_free_deriveln_Nil assms by fastforce

  have ex_p': "\<exists>p'. p = Nt A # p'" using pq_not_Nil Suc
    by (metis hd_Cons_tl)
  then obtain p' where P: "p = Nt A # p'" by blast
  have "\<nexists>q'. q = Nt A # q'" using pq_not_Nil Suc
    by fastforce

  then have "\<exists>w. (A,w) \<in> R \<and> R \<turnstile> w @ p' \<Rightarrow>l(n) q" using Suc P by (auto simp add: deriveln_Nt_Cons)
  then obtain w where w_prop: "(A,w) \<in> R \<and> R \<turnstile> w @ p' \<Rightarrow>l(n) q" by blast
  then have prod_in_S: "(A, w) \<in> S" using Suc assms by auto

  show ?case
  proof (cases "\<exists>w'. w = Nt A # w'")
    case True
    then obtain w' where "w = Nt A # w'" by blast
    then have "\<exists>u w'' m k. S \<turnstile> w @ p' \<Rightarrow>l(m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w'' \<and>
       hd w'' \<noteq> Nt A \<and> R \<turnstile> w'' \<Rightarrow>l(k) q \<and> n = m + k + 1"
      using Suc.IH Suc.prems w_prop by auto
    then obtain u w'' m k where propo: "S \<turnstile> w @ p' \<Rightarrow>l(m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w'' \<and> 
       hd w'' \<noteq> Nt A \<and> R \<turnstile> w'' \<Rightarrow>l(k) q \<and> n = m + k + 1"
      by blast
    then have "S \<turnstile> Nt A # p' \<Rightarrow>l(Suc m) Nt A # u" 
      using prod_in_S P by (meson derivel_Nt_Cons relpowp_Suc_I2)
  
    then have "S \<turnstile> p \<Rightarrow>l(Suc m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w'' \<and>
       hd w'' \<noteq> Nt A \<and> R \<turnstile> w'' \<Rightarrow>l(k) q \<and> Suc n = Suc m + k + 1" 
      using P propo by auto
    then show ?thesis by blast
  next
    case False
    then have "w \<noteq> [] \<and> hd w \<noteq> Nt A" using Suc w_prop assms
      by (metis Eps_free_Nil list.collapse)
    then have "S \<turnstile> p \<Rightarrow>l(0) Nt A # p' \<and> S \<turnstile> Nt A # p' \<Rightarrow>l w @ p' \<and> hd (w @ p') \<noteq> Nt A \<and> 
         R \<turnstile> w @ p' \<Rightarrow>l(n) q \<and> Suc n = 0 + n + 1"
        using P w_prop prod_in_S by (auto simp add: derivel_Nt_Cons)
    then show ?thesis by blast
  qed
qed

text \<open>Every derivation resulting in a word has a derivation in \<open>Solve_lrec B B' R\<close>.\<close>
lemma tm_derive_impl_Solve_lrec_derive:
  assumes "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R"
  shows "\<lbrakk> p \<noteq> []; R \<turnstile> p \<Rightarrow>(n) map Tm q\<rbrakk> \<Longrightarrow> Solve_lrec B B' R \<turnstile> p \<Rightarrow>* map Tm q"
proof (induction n arbitrary: p q rule: nat_less_induct)
  case (1 n)
  then show ?case
  proof (cases "Solve_lrec B B' R = R - {(B, [Nt B])}")
    case True
    have 2: "Rm_self_loops R \<subseteq> R - {(B, [Nt B])}" by (auto simp add: Rm_self_loops_def)
    have "Rm_self_loops R \<turnstile> p \<Rightarrow>* map Tm q" 
      using  "1.prems"(2) 
      by (auto simp: Rm_self_loops_def no_self_loops_derives relpowp_imp_rtranclp)
    then show ?thesis 
      using 2 by (simp add: True derives_mono)
  next
    case Solve_lrec_not_R: False
    then show ?thesis
    proof (cases "Nts_syms p = {}")
      case True
      then obtain pt where "p = map Tm pt" using Nts_syms_empty_iff by blast
      then have "map Tm q = p"
        using deriven_from_TmsD "1.prems"(2) by blast
      then show ?thesis by simp
    next
      case False
      then have "\<exists>C pt p2. p = map Tm pt @ Nt C # p2" using non_word_has_first_Nt[of p] by auto
      then obtain C pt p2 where P: "p = map Tm pt @ Nt C # p2" by blast
      then have "R \<turnstile> map Tm pt @ Nt C # p2 \<Rightarrow>l(n) map Tm q" 
        using "1.prems" by (simp add: deriveln_iff_deriven)
      then have "\<exists>q2. map Tm q = map Tm pt @ q2 \<and> R \<turnstile> Nt C # p2 \<Rightarrow>l(n) q2"
        by (simp add: deriveln_map_Tm_append[of "n" R "pt" "Nt C # p2" "map Tm q"])
      then obtain q2 where P1: "map Tm q = map Tm pt @ q2 \<and> R \<turnstile> Nt C # p2 \<Rightarrow>l(n) q2" by blast
      then have "n \<noteq> 0"
        by (metis False P Nts_syms_map_Tm relpowp_0_E)
      then have "\<exists>m. n = Suc m"
        by (meson old.nat.exhaust)
      then obtain m where n_Suc: "n = Suc m" by blast
      have "\<exists>q2t. q2 = map Tm q2t"
        by (metis P1 append_eq_map_conv)
      then obtain q2t where q2_tms: "q2 = map Tm q2t" by blast
      then show ?thesis
      proof (cases "C = B")
        case True
        then have n_derive: "R \<turnstile> Nt B # p2 \<Rightarrow>(n) q2" using P1
          by (simp add: deriveln_imp_deriven)
        have "\<nexists>v2. q2 = Nt B #v2 \<and> R \<turnstile> p2 \<Rightarrow>(n) v2" using q2_tms by auto
        then have "\<exists>n1 n2 w v1 v2. n = Suc (n1 + n2) \<and> q2 = v1 @ v2 \<and>
            (B,w) \<in> R \<and> R \<turnstile> w \<Rightarrow>(n1) v1 \<and> R \<turnstile> p2 \<Rightarrow>(n2) v2" using n_derive deriven_Cons_decomp
          by (smt (verit) sym.inject(1))
        then obtain n1 n2 w v1 v2 where decomp: "n = Suc (n1 + n2) \<and> q2 = v1 @ v2 \<and>
            (B,w) \<in> R \<and> R \<turnstile> w \<Rightarrow>(n1) v1 \<and> R \<turnstile> p2 \<Rightarrow>(n2) v2" by blast
        then have derive_from_singleton: "R \<turnstile> [Nt B] \<Rightarrow>(Suc n1) v1"
          using deriven_Suc_decomp_left by force
  
        have "v1 \<noteq> []"
          using assms(1) Eps_free_deriven_Nil derive_from_singleton by auto
        then have "\<exists>v1t. v1 = map Tm v1t"
          using decomp append_eq_map_conv q2_tms by blast
        then obtain v1t where v1_tms: "v1 = map Tm v1t" by blast
        then have v1_hd: "hd v1 \<noteq> Nt B"
          by (metis Nil_is_map_conv \<open>v1 \<noteq> []\<close> hd_map sym.distinct(1))
  
        have deriveln_from_singleton: "R \<turnstile> [Nt B] \<Rightarrow>l(Suc n1) v1" using v1_tms derive_from_singleton
          by (simp add: deriveln_iff_deriven)
  
        text \<open>This is the interesting bit where we use other lemmas to prove that we can replace a 
              specific part of the derivation which is a left-recursion by a right-recursion in the 
              new productions.\<close>
        let ?S = "{x. (\<exists>v. x = (B, v) \<and> x \<in> R)}"
        have "\<exists>u w m k. ?S \<turnstile> [Nt B] \<Rightarrow>l(m) Nt B # u \<and> ?S \<turnstile> Nt B # u \<Rightarrow>l w \<and> 
           hd w \<noteq> Nt B \<and> R \<turnstile> w \<Rightarrow>l(k) v1 \<and> Suc n1 = m + k + 1"
          using deriveln_from_singleton v1_hd assms lrec_decomp[of ?S B R "[Nt B]" v1 "Suc n1"] by auto
        then obtain u w2 m2 k where l_decomp: "?S \<turnstile> [Nt B] \<Rightarrow>l(m2) Nt B # u \<and> ?S \<turnstile> Nt B # u \<Rightarrow>l w2 
            \<and> hd w2 \<noteq> Nt B \<and> R \<turnstile> w2 \<Rightarrow>l(k) v1 \<and> Suc n1 = m2 + k + 1" 
          by blast
        then have "\<exists>w2'. (B,w2') \<in> ?S \<and> w2 = w2' @ u" by (simp add: derivel_Nt_Cons)
        then obtain w2' where w2'_prod: "(B,w2') \<in> ?S \<and> w2 = w2' @ u" by blast
        then have w2'_props: "w2' \<noteq> [] \<and> hd w2' \<noteq> Nt B"
          by (metis (mono_tags, lifting) assms(1) Eps_free_Nil l_decomp 
              hd_append mem_Collect_eq)
  
        have Solve_lrec_subset: "Solve_lrec B B' ?S \<subseteq> Solve_lrec B B' R" 
          unfolding Solve_lrec_defs by (auto)
  
        have "Solve_lrec B B' ?S \<turnstile> [Nt B] \<Rightarrow>* w2"
          proof(cases "u = []")
            case True
            have "(B, w2') \<in> Solve_lrec B B' ?S"
              using  w2'_props w2'_prod unfolding Solve_lrec_defs by (auto)
            then show ?thesis
              by (simp add: True bu_prod derives_if_bu w2'_prod)
          next
            case False
            have solved_prod: "(B, w2' @ [Nt B']) \<in> Solve_lrec B B' ?S"
              using w2'_props w2'_prod Solve_lrec_not_R unfolding Solve_lrec_defs by (auto)
            have "Rm_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l* Nt B # u"
              apply (unfold Rm_self_loops_def no_self_loops_derivels)
              using l_decomp by (auto simp: relpowp_imp_rtranclp)
            then have "\<exists>ln. Rm_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l(ln) Nt B # u"
              by (simp add: rtranclp_power)
            then obtain ln where "Rm_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l(ln) Nt B # u" by blast
            then have "(Solve_lrec B B' ?S) \<turnstile> [Nt B'] \<Rightarrow>(ln) u"
              using lrec_lemma3[of ?S B R ln u] assms False by auto
            then have rrec_derive: "(Solve_lrec B B' ?S) \<turnstile> w2' @ [Nt B'] \<Rightarrow>(ln) w2' @ u"
              by (simp add: deriven_prepend)
            have "(Solve_lrec B B' ?S) \<turnstile> [Nt B] \<Rightarrow> w2' @ [Nt B']"
              using solved_prod by (simp add: derive_singleton)
            then have "(Solve_lrec B B' ?S) \<turnstile> [Nt B] \<Rightarrow>* w2' @ u"
              using rrec_derive by (simp add: converse_rtranclp_into_rtranclp relpowp_imp_rtranclp)
            then show ?thesis using w2'_prod by auto
          qed
          then have 2: "Solve_lrec B B' R \<turnstile> [Nt B] \<Rightarrow>* w2"
            using Solve_lrec_subset by (simp add: derives_mono)
  
        text \<open>From here on all the smaller derivations are concatenated after applying the IH.\<close>
        have fact2: "R \<turnstile> w2 \<Rightarrow>l(k) v1 \<and> Suc n1 = m2 + k + 1" using l_decomp by auto
        then have "k < n"
          using decomp by linarith
        then have 3: "Solve_lrec B B' R \<turnstile> w2 \<Rightarrow>* v1" using "1.IH" v1_tms fact2
          by (metis deriveln_iff_deriven derives_from_empty relpowp_imp_rtranclp)
  
        have 4: "Solve_lrec B B' R \<turnstile> [Nt B] \<Rightarrow>* v1" using 2 3
          by auto
  
        have "\<exists>v2t. v2 = map Tm v2t" using decomp append_eq_map_conv q2_tms by blast
        then obtain v2t where v2_tms: "v2 = map Tm v2t" by blast
        have "n2 < n" using decomp by auto
        then have 5: "Solve_lrec B B' R \<turnstile> p2 \<Rightarrow>* v2" using "1.IH" decomp v2_tms
          by (metis derives_from_empty relpowp_imp_rtranclp)
  
        have "Solve_lrec B B' R \<turnstile> Nt B # p2 \<Rightarrow>* q2" using 4 5 decomp
          by (metis append_Cons append_Nil derives_append_decomp)
        then show ?thesis
          by (simp add: P P1 True derives_prepend)
      next
        case C_not_B: False
        then have "\<exists>w. (C, w) \<in> R \<and> R \<turnstile> w @ p2 \<Rightarrow>l(m) q2"
          by (metis P1 derivel_Nt_Cons relpowp_Suc_D2 n_Suc)
        then obtain w where P2: "(C, w) \<in> R \<and> R \<turnstile> w @ p2 \<Rightarrow>l(m) q2" by blast
        then have rule_in_Solve_lrec: "(C, w) \<in> (Solve_lrec B B' R)" 
          using C_not_B by (auto simp add: Solve_lrec_def Rm_lrec_def)
        have derivem: "R \<turnstile> w @ p2 \<Rightarrow>(m) q2" using q2_tms P2 by (auto simp add: deriveln_iff_deriven)
        have "w @ p2 \<noteq> []"
          using assms(1) Eps_free_Nil P2 by fastforce
        then have "(Solve_lrec B B' R) \<turnstile> w @ p2 \<Rightarrow>* q2" using "1.IH" q2_tms n_Suc derivem
          by auto
        then have "(Solve_lrec B B' R) \<turnstile> Nt C # p2 \<Rightarrow>* q2" 
          using rule_in_Solve_lrec by (auto simp add: derives_Cons_rule)
        then show ?thesis
          by (simp add: P P1 derives_prepend)
      qed
    qed
  qed
qed

corollary Lang_incl_Lang_Solve_lrec: 
  "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> Lang R A \<subseteq> Lang (Solve_lrec B B' R) A"
by(auto simp: Lang_def intro: tm_derive_impl_Solve_lrec_derive dest: rtranclp_imp_relpowp)


subsubsection \<open>\<^prop>\<open>Lang (Solve_lrec B B' R) A \<subseteq> Lang R A\<close>\<close>

text \<open>Restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>)
      if there is a right-derivation from \<open>u\<close> to \<open>v @ [Nt A']\<close> then u ends in Nt \<open>A'\<close>.\<close>
lemma rrec_lemma1: 
  assumes "S = {x. \<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> Solve_lrec A A' R}" "S \<turnstile> u \<Rightarrow>r(n) v @ [Nt A']"
  shows "\<exists>u'. u = u' @ [Nt A']"
proof (rule ccontr)
  assume neg: "\<nexists>u'. u = u' @ [Nt A']"
  show "False"
  proof (cases "u = []")
    case True
    then show ?thesis using assms derivern_imp_deriven by fastforce
  next
    case u_not_Nil: False
    then show ?thesis
    proof (cases "\<exists>t. last u = Tm t")
      case True
      then show ?thesis using assms neg
        by (metis (lifting) u_not_Nil append_butlast_last_id derivern_snoc_Tm last_snoc)
    next
      case False
      then have "\<exists>B u'. u = u' @ [Nt B] \<and> B \<noteq> A'" using assms neg u_not_Nil
        by (metis append_butlast_last_id sym.exhaust)
      then obtain B u' where B_not_A': "u = u' @ [Nt B] \<and> B \<noteq> A'" by blast
      then have "\<exists>w. (B, w) \<in> S" using assms neg
        by (metis (lifting) derivers_snoc_Nt relpowp_imp_rtranclp)
      then obtain w where elem: "(B, w) \<in> S" by blast
      have "(B, w) \<notin> S" using B_not_A' assms by auto
      then show ?thesis using elem by simp
    qed
  qed
qed

text \<open>\<open>Solve_lrec\<close> does not add productions of the form \<open>A' \<rightarrow> Nt A'\<close>.\<close>
lemma Solve_lrec_no_self_loop: "Eps_free R \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> (A', [Nt A']) \<notin> Solve_lrec A A' R"
unfolding Solve_lrec_defs by (auto)

text \<open>Restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>) if there is a 
      right-derivation from \<open>u\<close> to \<open>v @ [Nt A']\<close> then u ends in Nt \<open>A'\<close> and there exists a suffix 
      of \<open>v @ [Nt A']\<close> s.t. there is a right-derivation from \<open>[Nt A']\<close> to that suffix.\<close>
lemma rrec_lemma2:
assumes "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> Solve_lrec A A' R)}" "Eps_free R" "A' \<notin> Nts R"
shows "S \<turnstile> u \<Rightarrow>r(n) v @ [Nt A']
  \<Longrightarrow> \<exists>u' v'. u = u' @ [Nt A'] \<and> v = u' @ v' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v' @ [Nt A']"
proof (induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "\<exists>u'. u = u' @ [Nt A']" using rrec_lemma1[of S] Suc.prems assms by auto
  then obtain u' where u'_prop: "u = u' @ [Nt A']" by blast
  then have "\<exists>w. (A',w) \<in> S \<and> S \<turnstile> u' @ w \<Rightarrow>r(n) v @ [Nt A']"
    using Suc by (auto simp add: derivern_snoc_Nt)
  then obtain w where w_prop: "(A',w) \<in> S \<and> S \<turnstile> u' @ w \<Rightarrow>r(n) v @ [Nt A']" by blast
  then have "\<exists>u'' v''. u' @ w = u'' @ [Nt A'] \<and>  v = u'' @ v'' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v'' @ [Nt A']"
    using Suc.IH Suc by auto
  then obtain u'' v'' where u''_prop: "u' @ w = u'' @ [Nt A'] \<and>  v = u'' @ v'' \<and>
     S \<turnstile> [Nt A'] \<Rightarrow>r(n) v'' @ [Nt A']"
    by blast
  have "w \<noteq> [] \<and> w \<noteq> [Nt A']" 
    using Suc.IH assms w_prop Solve_lrec_no_self_loop by fastforce
  then have "\<exists>u1. u1 \<noteq> [] \<and> w = u1 @ [Nt A'] \<and> u'' = u' @ u1" 
    using u''_prop
    by (metis (no_types, opaque_lifting) append.left_neutral append1_eq_conv 
        append_assoc rev_exhaust)
  then obtain u1 where u1_prop: "u1 \<noteq> [] \<and> w = u1 @ [Nt A'] \<and> u'' = u' @ u1" by blast
  then have 1: "u = u' @ [Nt A'] \<and> v = u' @ (u1 @ v'')" using u'_prop u''_prop by auto
  
  have 2: "S \<turnstile> u1 @ [Nt A'] \<Rightarrow>r(n) u1 @ v'' @ [Nt A']" using u''_prop derivern_prepend
    by fastforce
  have "S \<turnstile> [Nt A'] \<Rightarrow>r u1 @ [Nt A']" using w_prop u''_prop u1_prop
    by (simp add: deriver_singleton)
  then have "S \<turnstile> [Nt A'] \<Rightarrow>r(Suc n) u1 @ v'' @ [Nt A']" using u''_prop
    by (meson 2 relpowp_Suc_I2)
  then show ?case using 1
    by auto
qed

text \<open>Restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>)
      if there is a restricted right-derivation in \<open>Solve_lrec\<close> from \<open>[Nt A']\<close> to \<open>u @ [Nt A']\<close> 
      then there exists a derivation in \<open>R\<close> from \<open>[Nt A]\<close> to \<open>A # u\<close>.\<close>
lemma rrec_lemma3: 
  assumes "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> Solve_lrec A A' R)}" "Eps_free R"
    "A' \<notin> Nts R" "A \<noteq> A'"
  shows "S \<turnstile> [Nt A'] \<Rightarrow>r(n) u @ [Nt A'] \<Longrightarrow> R \<turnstile> [Nt A] \<Rightarrow>(n) Nt A # u"
proof(induction n arbitrary: u)
  case 0
  then show ?case by (simp)
next
  case (Suc n)
  then have "\<exists>w. (A',w) \<in> S \<and> S \<turnstile> w \<Rightarrow>r(n) u @ [Nt A']"
    by (auto simp add: derivern_singleton split: prod.splits)
  then obtain w where w_prop1: "(A',w) \<in> S \<and> S \<turnstile> w \<Rightarrow>r(n) u @ [Nt A']" by blast
  then have "\<exists>u' v'. w = u' @ [Nt A'] \<and> u = u' @ v' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v' @ [Nt A']"
    using rrec_lemma2[of S] assms by auto
  then obtain u' v' where u'v'_prop: "w = u' @ [Nt A'] \<and> u = u' @ v' 
     \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v' @ [Nt A']" 
    by blast
  then have 1: "R \<turnstile> [Nt A] \<Rightarrow>(n) Nt A # v'" using Suc.IH by auto

  have "(A', u' @ [Nt A']) \<in> Solve_lrec A A' R \<longrightarrow> (A, Nt A # u') \<in> R"
    using assms unfolding Solve_lrec_defs by (auto)
  then have "(A, Nt A # u') \<in> R" using u'v'_prop assms(1) w_prop1 by auto

  then have "R \<turnstile> [Nt A] \<Rightarrow> Nt A # u'"
    by (simp add: derive_singleton)
  then have "R \<turnstile> [Nt A] @ v' \<Rightarrow> Nt A # u' @ v'"
    by (metis Cons_eq_appendI derive_append)
  then have "R \<turnstile> [Nt A] \<Rightarrow>(Suc n) Nt A # (u' @ v')" using 1
    by (simp add: relpowp_Suc_I)
  then show ?case using u'v'_prop by simp
qed


text \<open>A right derivation from \<open>p@[Nt A']\<close> to \<open>q\<close> (\<open>last q \<noteq> Nt A'\<close>) can be split into a 
  right-recursive part, only using right-recursive productions with Nt \<open>A'\<close>, 
  one right derivation step consuming Nt \<open>A'\<close> using some rule \<open>A' \<rightarrow> as@[Nt B]\<close> where \<open>Nt B \<noteq> Nt A'\<close>
  and a right-derivation comprising the rest of the derivation.\<close>
lemma rrec_decomp: 
  assumes "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> Solve_lrec A A' R)}" "Eps_free R"
    "A \<noteq> A'" "A' \<notin> Nts R"
  shows "\<lbrakk>A' \<notin> Nts_syms p; last q \<noteq> Nt A'; Solve_lrec A A' R \<turnstile> p @ [Nt A'] \<Rightarrow>r(n) q\<rbrakk>
  \<Longrightarrow> \<exists>u w m k. S \<turnstile> p @ [Nt A'] \<Rightarrow>r(m) u @ [Nt A'] 
       \<and> Solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w \<and> A' \<notin> Nts_syms w 
       \<and> Solve_lrec A A' R \<turnstile> w \<Rightarrow>r(k) q \<and> n = m + k + 1"
proof (induction n arbitrary: p)
  case 0
  then have pq_not_Nil: "p @ [Nt A'] \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil
    by auto

  have "p = q" using 0 by auto
  then show ?case using pq_not_Nil 0 by auto
next
  case (Suc n)
  have pq_not_Nil: "p @ [Nt A'] \<noteq> [] \<and> q \<noteq> []"
    using assms Suc.prems Eps_free_deriven_Nil Eps_free_Solve_lrec derivern_imp_deriven
    by (metis (no_types, lifting) snoc_eq_iff_butlast)

  have "\<nexists>q'. q = q' @ [Nt A']" using pq_not_Nil Suc.prems
    by fastforce

  then have "\<exists>w. (A',w) \<in> (Solve_lrec A A' R) \<and> (Solve_lrec A A' R) \<turnstile> p @ w \<Rightarrow>r(n) q"
    using Suc.prems by (auto simp add: derivern_snoc_Nt)
  then obtain w where w_prop: "(A',w) \<in> (Solve_lrec A A' R) \<and> Solve_lrec A A' R \<turnstile> p @ w \<Rightarrow>r(n) q"
    by blast

  show ?case
  proof (cases "(A', w) \<in> S")
    case True
    then have "\<exists>w'. w = w' @ [Nt A']"
      by (simp add: assms(1))
    then obtain w' where w_decomp: "w = w' @ [Nt A']" by blast
    then have "A' \<notin> Nts_syms (p @ w')" using assms Suc.prems True
      unfolding Solve_lrec_defs by (auto split: if_splits)
    then have "\<exists>u w'' m k. S \<turnstile> p @ w \<Rightarrow>r(m) u @ [Nt A'] \<and> Solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' 
       \<and> A' \<notin> Nts_syms w'' \<and> Solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> n = m + k + 1"
      using Suc.IH Suc.prems w_prop w_decomp by (metis (lifting) append_assoc)
    then obtain u w'' m k where propo: 
      "S \<turnstile> p @ w \<Rightarrow>r(m) u @ [Nt A'] \<and> Solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' \<and> A' \<notin> Nts_syms w'' 
       \<and> Solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> n = m + k + 1" 
      by blast
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(Suc m) u @ [Nt A']" using True
      by (meson deriver_snoc_Nt relpowp_Suc_I2)
  
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(Suc m) u @ [Nt A'] \<and> Solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w''
       \<and> A' \<notin> Nts_syms w'' \<and> Solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> Suc n = Suc m + k + 1"
      using propo by auto
    then show ?thesis by blast
  next
    case False
    then have "last w \<noteq> Nt A'" using assms
      by (metis (mono_tags, lifting) Eps_freeE_Cons Eps_free_Solve_lrec
          append_butlast_last_id list.distinct(1) mem_Collect_eq w_prop)
    then have "A' \<notin> Nts_syms w" using assms w_prop
      unfolding Solve_lrec_defs by (auto split: if_splits)
    then have "w \<noteq> [] \<and> A' \<notin> Nts_syms w" using assms w_prop False
      by (metis (mono_tags, lifting) Eps_free_Nil Eps_free_Solve_lrec)
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(0) p @ [Nt A'] \<and> Solve_lrec A A' R \<turnstile> p @ [Nt A'] \<Rightarrow>r p @ w 
       \<and> A' \<notin> Nts_syms (p @ w) \<and> Solve_lrec A A' R \<turnstile> p @ w \<Rightarrow>r(n) q \<and> Suc n = 0 + n + 1"
      using w_prop Suc.prems by (auto simp add: deriver_snoc_Nt)
    then show ?thesis by blast
  qed
qed

text \<open>Every word derived by \<open>Solve_lrec B B' R\<close> can be derived by \<open>R\<close>.\<close>
lemma tm_Solve_lrec_derive_impl_derive:
  assumes "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R"
  shows "\<lbrakk> p \<noteq> []; B' \<notin> Nts_syms p; (Solve_lrec B B' R) \<turnstile> p \<Rightarrow>(n) map Tm q\<rbrakk> \<Longrightarrow> R \<turnstile> p \<Rightarrow>* map Tm q"
proof (induction arbitrary: p q rule: nat_less_induct)
  case (1 n)
  let ?R' = "(Solve_lrec B B' R)"
  show ?case
  proof (cases "Nts_syms p = {}")
    case True
    then show ?thesis
      using "1.prems"(3) deriven_from_TmsD derives_from_Tms_iff
      by (metis Nts_syms_empty_iff)
  next
    case False
    from non_word_has_last_Nt[OF this] have "\<exists>C pt p2. p = p2 @ [Nt C] @ map Tm pt" by blast
    then obtain C pt p2 where p_decomp: "p = p2 @ [Nt C] @ map Tm pt" by blast
    then have "\<exists>pt' At w k m. ?R' \<turnstile> p2 \<Rightarrow>(k) map Tm pt' \<and> ?R' \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (C, w) \<in> ?R' 
       \<and> q = pt' @ At @ pt \<and> n = Suc(k + m)"
      using "1.prems" word_decomp1[of n ?R' p2 C pt q] by auto
    then obtain pt' At w k m 
      where P: "?R' \<turnstile> p2 \<Rightarrow>(k) map Tm pt' \<and> ?R' \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (C, w) \<in> ?R' 
       \<and> q = pt' @ At @ pt \<and> n = Suc(k + m)" 
      by blast
    then have pre1: "m < n" by auto

    have "B' \<notin> Nts_syms p2 \<and> k < n" using P "1.prems" p_decomp by auto
    then have p2_not_Nil_derive: "p2 \<noteq> [] \<longrightarrow> R \<turnstile> p2 \<Rightarrow>* map Tm pt'" using 1 P by blast

    have "p2 = [] \<longrightarrow> map Tm pt' = []" using P
      by auto
    then have p2_derive: "R \<turnstile> p2 \<Rightarrow>* map Tm pt'" using p2_not_Nil_derive by auto

    have "R \<turnstile> [Nt C] \<Rightarrow>* map Tm At"
    proof(cases "C = B")
      case C_is_B: True
      then show ?thesis
      proof (cases "last w = Nt B'")
        case True
        let ?S = "{x. (\<exists>v. x = (B', v @ [Nt B']) \<and> x \<in> Solve_lrec B B' R)}"

        have "\<exists>w1. w = w1 @ [Nt B']" using True
          by (metis assms(1) Eps_free_Nil Eps_free_Solve_lrec P append_butlast_last_id)
        then obtain w1 where w_decomp: "w = w1 @ [Nt B']" by blast
        then have "\<exists>w1' b k1 m1. ?R' \<turnstile> w1 \<Rightarrow>(k1) w1' \<and> ?R' \<turnstile> [Nt B'] \<Rightarrow>(m1) b \<and> map Tm At = w1' @ b 
           \<and> m = k1 + m1"
          using P deriven_append_decomp by blast
        then obtain w1' b k1 m1 
          where w_derive_decomp: "?R' \<turnstile> w1 \<Rightarrow>(k1) w1' \<and> ?R' \<turnstile> [Nt B'] \<Rightarrow>(m1) b 
           \<and> map Tm At = w1' @ b \<and> m = k1 + m1" 
          by blast
        then have "\<exists>w1t bt. w1' = map Tm w1t \<and> b = map Tm bt"
          by (meson map_eq_append_conv)
        then obtain w1t bt where tms: "w1' = map Tm w1t \<and> b = map Tm bt" by blast

        have pre1: "k1 < n \<and> m1 < n" using w_derive_decomp P by auto
        have pre2: "w1 \<noteq> []" using w_decomp C_is_B P assms by (auto simp add: Solve_lrec_rule_simp3)
        have Bw1_in_R: "(B, w1) \<in> R"
          using w_decomp P C_is_B assms
          unfolding Solve_lrec_defs by (auto split: if_splits)

        then have pre3: "B' \<notin> Nts_syms w1" using assms by (auto simp add: Nts_def)

        have "R \<turnstile> w1 \<Rightarrow>* map Tm w1t" using pre1 pre2 pre3 w_derive_decomp "1.IH" tms by blast
        then have w1'_derive: "R \<turnstile> [Nt B] \<Rightarrow>* w1'" using Bw1_in_R tms
          by (simp add: derives_Cons_rule)

        have "last [Nt B'] = Nt B' \<and> last (map Tm bt) \<noteq> Nt B'" 
          by (metis assms(1) Eps_free_deriven_Nil Eps_free_Solve_lrec last_ConsL last_map
              list.map_disc_iff not_Cons_self2 sym.distinct(1) tms w_derive_decomp)
        then have "\<exists>u v m2 k2. ?S \<turnstile> [Nt B'] \<Rightarrow>r(m2) u @ [Nt B'] \<and> ?R' \<turnstile> u @ [Nt B'] \<Rightarrow>r v 
           \<and> B' \<notin> Nts_syms v \<and> ?R' \<turnstile> v \<Rightarrow>r(k2) map Tm bt \<and> m1 = m2 + k2 + 1"
          using rrec_decomp[of ?S B' B R "[]" "map Tm bt" m1] w_derive_decomp assms "1.prems" tms
          by (simp add: derivern_iff_deriven)
        then obtain u v m2 k2 
          where rec_decomp: "?S \<turnstile> [Nt B'] \<Rightarrow>r(m2) u @ [Nt B'] \<and> ?R' \<turnstile> u @ [Nt B'] \<Rightarrow>r v 
           \<and> B' \<notin> Nts_syms v \<and> ?R' \<turnstile> v \<Rightarrow>r(k2) map Tm bt \<and> m1 = m2 + k2 + 1"
          by blast
        then have Bu_derive: "R \<turnstile> [Nt B] \<Rightarrow>(m2) Nt B # u"
          using assms rrec_lemma3 by fastforce

        have "\<exists>v'. (B', v') \<in> ?R' \<and> v = u @ v'" using rec_decomp
          by (simp add: deriver_snoc_Nt)
        then obtain v' where v_decomp: "(B', v') \<in> ?R' \<and> v = u @ v'" by blast
        then have "(B, Nt B # v') \<in> R"
          using assms rec_decomp unfolding Solve_lrec_defs by (auto split: if_splits)
        then have "R \<turnstile> [Nt B] \<Rightarrow> Nt B # v'"
          by (simp add: derive_singleton)
        then have "R \<turnstile> [Nt B] @ v' \<Rightarrow>* Nt B # u @ v'"
          by (metis Bu_derive append_Cons derives_append rtranclp_power)
        then have Buv'_derive: "R \<turnstile> [Nt B] \<Rightarrow>* Nt B # u @ v'"
          using \<open>R \<turnstile> [Nt B] \<Rightarrow> Nt B # v'\<close> by force

        have pre2: "k2 < n" using rec_decomp pre1 by auto
        have "v \<noteq> []" using rec_decomp
          by (metis (lifting) assms(1) Eps_free_deriven_Nil Eps_free_Solve_lrec tms
              deriven_from_TmsD derivern_imp_deriven list.simps(8) not_Cons_self2 w_derive_decomp)
        then have "R \<turnstile> v \<Rightarrow>* map Tm bt"
          using "1.IH" 1 pre2 rec_decomp
          by (auto simp add: derivern_iff_deriven)
        then have "R \<turnstile> [Nt B] \<Rightarrow>* Nt B # map Tm bt" using Buv'_derive v_decomp
          by (meson derives_Cons rtranclp_trans)
        then have "R \<turnstile> [Nt B] \<Rightarrow>* [Nt B] @ map Tm bt" by auto
        then have "R \<turnstile> [Nt B] \<Rightarrow>* w1' @ map Tm bt" using w1'_derive derives_append
          by (metis rtranclp_trans)
        then show ?thesis using tms w_derive_decomp C_is_B by auto
      next
        case False
        have pre2: "w \<noteq> []" using P assms(1)
          by (meson Eps_free_Nil Eps_free_Solve_lrec)
        then have 2: "(C, w) \<in> R" 
          using P False "1.prems" p_decomp C_is_B
          unfolding Solve_lrec_defs by (auto split: if_splits)

        then have pre3: "B' \<notin> Nts_syms w" using P assms(3) by (auto simp add: Nts_def)

        have "R \<turnstile> w \<Rightarrow>* map Tm At" using "1.IH" assms pre1 pre2 pre3 P by blast
        then show ?thesis using 2
          by (meson bu_prod derives_bu_iff rtranclp_trans)
      qed
    next
      case False
      then have 2: "(C, w) \<in> R" 
        using P "1.prems"(2) p_decomp
        by (auto simp add: Solve_lrec_rule_simp1)
      then have pre2: "B' \<notin> Nts_syms w" using P assms(3) by (auto simp add: Nts_def)
      have pre3: "w \<noteq> []" using assms(1) 2 by (auto simp add: Eps_free_def)

      have "R \<turnstile> w \<Rightarrow>* map Tm At" using "1.IH" pre1 pre2 pre3 P by blast
      then show ?thesis using 2
        by (meson bu_prod derives_bu_iff rtranclp_trans)
    qed

    then show ?thesis using p2_derive
      by (metis P derives_append derives_append_decomp map_append p_decomp)
  qed
qed

corollary Lang_Solve_lrec_incl_Lang:
  assumes "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R" "A \<noteq> B'"
  shows "Lang (Solve_lrec B B' R) A \<subseteq> Lang R A"
proof
  fix w
  assume "w \<in> Lang (Solve_lrec B B' R) A"
  then have "Solve_lrec B B' R \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by (simp add: Lang_def)
  then have "\<exists>n. Solve_lrec B B' R \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w"
    by (simp add: rtranclp_power)
  then obtain n where "(Solve_lrec B B' R) \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w" by blast
  then have "R \<turnstile> [Nt A] \<Rightarrow>* map Tm w" using tm_Solve_lrec_derive_impl_derive[of R] assms by auto
  then show "w \<in> Lang R A" by (simp add: Lang_def)
qed

corollary Solve_lrec_Lang: 
  "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R; A \<noteq> B'\<rbrakk> \<Longrightarrow> Lang (Solve_lrec B B' R) A = Lang R A"
  using Lang_Solve_lrec_incl_Lang Lang_incl_Lang_Solve_lrec by fastforce


subsection \<open>\<open>Expand_hd_rec\<close> Preserves Language\<close>

text \<open>Every rhs of an \<open>Expand_hd_rec P\<close> production is derivable by \<open>P\<close>.\<close>
lemma Expand_hd_rec_is_deriveable: "(A, w) \<in> Expand_hd_rec B As P \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* w"
proof (induction B As P arbitrary: A w rule: Expand_hd_rec.induct)
  case (1 B R)
  then show ?case
    by (simp add: bu_prod derives_if_bu)
next
  case (2 B S Ss R)
  then show ?case
  proof (cases "B = A")
    case True
    then have Aw_or_ACv: "(A, w) \<in> Expand_hd_rec A Ss R \<or> (\<exists>C v. (A, Nt C # v) \<in> Expand_hd_rec A Ss R)"
      using 2 by (auto simp add: Let_def Subst_hd_def)
    then show ?thesis
    proof (cases "(A, w) \<in> Expand_hd_rec A Ss R")
      case True
      then show ?thesis using 2 True by (auto simp add: Let_def Subst_hd_def)
    next
      case False
      then have "\<exists> v wv. w = v @ wv \<and> (A, Nt S#wv) \<in> Expand_hd_rec A Ss R \<and> (S, v) \<in> Expand_hd_rec A Ss R"
        using 2 True by (auto simp add: Let_def Subst_hd_def)
      then obtain v wv 
        where P: "w = v @ wv \<and> (A, Nt S # wv) \<in> Expand_hd_rec A Ss R \<and> (S, v) \<in> Expand_hd_rec A Ss R"
        by blast
      then have tr: "R \<turnstile> [Nt A] \<Rightarrow>* [Nt S] @ wv" using 2 True by simp
      have "R \<turnstile> [Nt S] \<Rightarrow>* v" using 2 True P by simp
      then show ?thesis using P tr derives_append
        by (metis rtranclp_trans)
    qed
  next
    case False
    then show ?thesis using 2 by (auto simp add: Let_def Subst_hd_def)
  qed
qed


lemma Expand_hd_rec_incl1: "Lang (Expand_hd_rec B As P) A \<subseteq> Lang P A"
by (meson DersD DersI Lang_subset_if_Ders_subset derives_simul_rules Expand_hd_rec_is_deriveable subsetI)

text \<open>This lemma expects a set of quadruples \<open>(A, a1, B, a2)\<close>. Each quadruple encodes a specific Nt
  in a specific rule \<open>A \<rightarrow> a1 @ Nt B # a2\<close> (this encodes Nt \<open>B\<close>) which should be expanded, 
  by replacing the Nt with every rule for that Nt and then removing the original rule.
  This expansion contains the original productions Language.\<close>
lemma exp_includes_Lang: 
  assumes S_props: "\<forall>x \<in> S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> R"
  shows "Lang R A 
      \<subseteq> Lang (R - {x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> S } 
                \<union> {x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> S \<and> (B,v) \<in> R}) A"
proof
  fix x
  assume x_Lang: "x \<in> Lang R A" 
  let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> S }"
  let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> S \<and> (B,v) \<in> R}"
  let ?subst = "R - ?S' \<union> ?E"
  have S'_sub: "?S' \<subseteq> R" using S_props by auto
  have "(N, ts) \<in> ?S' \<Longrightarrow> \<exists>B. B \<in> Nts_syms ts" for N ts by fastforce
  then have terminal_prods_stay: "(N, ts) \<in> R \<Longrightarrow> Nts_syms ts = {} \<Longrightarrow> (N, ts) \<in> ?subst" for N ts
    by auto

  have "R \<turnstile> p \<Rightarrow>(n) map Tm x \<Longrightarrow> ?subst \<turnstile> p \<Rightarrow>* map Tm x" for p n
  proof (induction n arbitrary: p x rule: nat_less_induct)
    case (1 n)
    then show ?case
    proof (cases "\<exists>pt. p = map Tm pt")
      case True
      then obtain pt where "p = map Tm pt" by blast
      then show ?thesis using "1.prems" deriven_from_TmsD derives_from_Tms_iff by blast
    next
      case False
      then have "\<exists>uu V ww. p = uu @ Nt V # ww"
        by (smt (verit, best) "1.prems" deriven_Suc_decomp_left relpowp_E)
      then obtain uu V ww where p_eq: "p = uu @ Nt V # ww" by blast
      then have "\<not> R \<turnstile> p \<Rightarrow>(0) map Tm x"
        using False by auto
      then have "\<exists>m. n = Suc m"
        using "1.prems" old.nat.exhaust by blast
      then obtain m where n_Suc: "n = Suc m" by blast
      then have "\<exists>v. (V, v) \<in> R \<and> R \<turnstile> uu @ v @ ww \<Rightarrow>(m) map Tm x" 
        using 1 p_eq by (auto simp add: deriven_start_sent)
      then obtain v where start_deriven: "(V, v) \<in> R \<and> R \<turnstile> uu @ v @ ww \<Rightarrow>(m) map Tm x" by blast
      then show ?thesis
      proof (cases "(V, v) \<in> ?S'")
        case True
        then have "\<exists>a1 B a2. v = a1 @ Nt B # a2 \<and> (V, a1, B, a2) \<in> S" by blast
        then obtain a1 B a2 where v_eq: "v = a1 @ Nt B # a2 \<and> (V, a1, B, a2) \<in> S" by blast
        then have m_deriven: "R \<turnstile> (uu @ a1) @ Nt B # (a2 @ ww) \<Rightarrow>(m) map Tm x" 
          using start_deriven by auto
        then have "\<not> R \<turnstile> (uu @ a1) @ Nt B # (a2 @ ww) \<Rightarrow>(0) map Tm x"
          by (metis (mono_tags, lifting) append.left_neutral append_Cons derive.intros insertI1 
              not_derive_from_Tms relpowp.simps(1))
        then have "\<exists>k. m = Suc k"
          using m_deriven "1.prems" old.nat.exhaust by blast
        then obtain k where m_Suc: "m = Suc k" by blast
        then have "\<exists>b. (B, b) \<in> R \<and> R \<turnstile> (uu @ a1) @ b @ (a2 @ ww) \<Rightarrow>(k) map Tm x"
          using m_deriven deriven_start_sent[where ?u = "uu@a1" and ?w = "a2 @ ww"] 
          by (auto simp add: m_Suc)
        then obtain b 
          where second_deriven: "(B, b) \<in> R \<and> R \<turnstile> (uu @ a1) @ b @ (a2 @ ww) \<Rightarrow>(k) map Tm x" 
          by blast
        then have expd_rule_subst: "(V, a1 @ b @ a2) \<in> ?subst" using v_eq by auto
        have "k < n" using n_Suc m_Suc by auto
        then have subst_derives: "?subst \<turnstile> uu @ a1 @ b @ a2 @ ww \<Rightarrow>* map Tm x" 
          using 1 second_deriven by (auto)
        have "?subst \<turnstile> [Nt V] \<Rightarrow>* a1 @ b @ a2" using expd_rule_subst
          by (meson derive_singleton r_into_rtranclp)
        then have "?subst \<turnstile> [Nt V] @ ww \<Rightarrow>* a1 @ b @ a2 @ ww" 
          using derives_append[of ?subst "[Nt V]" "a1 @ b @ a2"] 
          by simp
        then have "?subst \<turnstile> Nt V # ww \<Rightarrow>* a1 @ b @ a2 @ ww"
          by simp
        then have "?subst \<turnstile> uu @ Nt V # ww \<Rightarrow>* uu @ a1 @ b @ a2 @ ww" 
          using derives_prepend[of ?subst "[Nt V] @ ww"] 
          by simp
        then show ?thesis using subst_derives by (auto simp add: p_eq v_eq)
      next
        case False
        then have Vv_subst: "(V,v) \<in> ?subst" using S_props start_deriven by auto
        then have "?subst \<turnstile> uu @ v @ ww \<Rightarrow>* map Tm x" using 1 start_deriven n_Suc by auto
        then show ?thesis using Vv_subst derives_append_decomp
          by (metis (no_types, lifting) derives_Cons_rule p_eq)
      qed
    qed
  qed

  then have "R \<turnstile> p \<Rightarrow>* map Tm x \<Longrightarrow> ?subst \<turnstile> p \<Rightarrow>* map Tm x" for p
    by (meson rtranclp_power)

  then show "x \<in> Lang ?subst A" using x_Lang by (auto simp add: Lang_def)
qed

lemma Expand_hd_rec_incl2: "Lang (Expand_hd_rec B As P) A \<supseteq> Lang P A"
proof (induction B As P rule: Expand_hd_rec.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 C H Ss R)
  let ?R' = "Expand_hd_rec C Ss R"
  let ?X = "{r \<in> ?R'. \<exists>w. r = (C, Nt H # w)}"
  have "Expand_hd_rec C (H # Ss) R = Subst_hd ?R' ?X" by (auto simp: Let_def)

  let ?S = "{x. \<exists>A w. x = (A, [], H, w) \<and> (A, Nt H # w) \<in> ?X}"
  let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
  let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> ?R'}"

  have S'_eq_X: "?S' = ?X" by fastforce
  have E_eq_Y: "?E = {(A,v@w) | A v w. \<exists>B. (B,v) \<in> ?R' \<and> (A, Nt B # w) \<in> ?X}" by fastforce

  have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> ?R'" by fastforce
  then have Lang_sub: "Lang ?R' A \<subseteq> Lang (?R' - ?S' \<union> ?E) A"
    using exp_includes_Lang[of ?S] by auto

  have "Lang R A \<subseteq> Lang ?R' A" using 2 by simp
  also have "... \<subseteq> Lang (?R' - ?S' \<union> ?E) A" using Lang_sub by simp
  also have "... \<subseteq> Lang (Subst_hd ?R' ?X) A" using S'_eq_X E_eq_Y by (simp add: Subst_hd_def)
  finally show ?case by (simp add: Let_def)
qed

theorem Expand_hd_rec_Lang: "Lang (Expand_hd_rec B As P) A = Lang P A"
  using Expand_hd_rec_incl1[of B As P A] Expand_hd_rec_incl2[of P A B As] by auto

subsection \<open>\<open>Solve_tri\<close> Preserves Language\<close>
    
lemma Lang_Solve_tri: 
  "\<lbrakk> Eps_free P; length As \<le> length As'; distinct(As @ As'); Nts P \<inter> set As' = {}; A \<notin> set As'\<rbrakk>
   \<Longrightarrow> Lang (Solve_tri As As' P) A = Lang P A"
proof (induction As As' P rule: Solve_tri.induct)
  case *: (1 Aa As A' As' R)
  then have e_free1: "Eps_free (Expand_hd_rec Aa As (Solve_tri As As' R))"
    by (simp add: Eps_free_Expand_hd_rec Eps_free_Solve_tri)
  have "length As \<le> length As'" using * by simp
  then have "Nts (Expand_hd_rec Aa As (Solve_tri As As' R)) \<subseteq> Nts R \<union> set As'"
    using * Nts_Expand_hd_rec Nts_Solve_tri
    by (metis subset_trans)
  then have nts1: " A' \<notin> Nts (Expand_hd_rec Aa As (Solve_tri As As' R))"
    using * Nts_Expand_hd_rec Nts_Solve_tri by auto
  
  have "Lang (Solve_tri (Aa # As) (A' # As') R) A 
        = Lang (Solve_lrec Aa A' (Expand_hd_rec Aa As (Solve_tri As As' R))) A"
    by simp
  also have "... = Lang (Expand_hd_rec Aa As (Solve_tri As As' R)) A"
    using nts1 e_free1 * Solve_lrec_Lang[of "Expand_hd_rec Aa As (Solve_tri As As' R)" Aa A' A]
    by (simp)
  also have "... = Lang (Solve_tri As As' R) A" by (simp add: Expand_hd_rec_Lang)
  finally show ?case using * by (auto)
qed auto


section \<open>Function \<open>Expand_hd_rec\<close>: Convert Triangular Form into GNF\<close>
  
subsection \<open>\<open>Expand_hd_rec\<close>: Result is in \<open>GNF_hd\<close>\<close>
  
lemma dep_on_helper: "dep_on R A = {} \<Longrightarrow> (A, w) \<in> R \<Longrightarrow> w = [] \<or> (\<exists>T wt. w = Tm T # wt)"
  using neq_Nil_conv[of w] by (simp add: dep_on_def) (metis sym.exhaust)

lemma GNF_hd_iff_dep_on:
  assumes "Eps_free P"
  shows "GNF_hd P \<longleftrightarrow> (\<forall>A \<in> Nts P. dep_on P A = {})" (is "?L=?R")
proof
  assume ?L
  then show ?R by (auto simp add: GNF_hd_def dep_on_def)
next
  assume assm: ?R
  have 1: "\<forall>(B, w) \<in> P. \<exists>T wt. w = Tm T # wt \<or> w = []"
  proof
    fix x
    assume "x \<in> P"
    then have "case x of (B, w) \<Rightarrow> dep_on P B = {}" using assm by (auto simp add: Nts_def)
    then show "case x of (B, w) \<Rightarrow> \<exists>T wt. w = Tm T # wt \<or> w = []"
      using \<open>x \<in> P\<close> dep_on_helper by fastforce
  qed
  have 2: "\<forall>(B, w) \<in> P. w \<noteq> []" using assms assm by (auto simp add: Eps_free_def)
  have "\<forall>(B, w) \<in> P. \<exists>T wt. w = Tm T # wt" using 1 2 by auto
  then show "GNF_hd P" by (auto simp add: GNF_hd_def)
qed

lemma Expand_tri_simp1: "A \<notin> set As \<Longrightarrow> (A,w) \<in> Expand_tri As P \<longleftrightarrow> (A,w) \<in> P"
  by (induction As P rule: Expand_tri.induct) (auto simp add: Let_def Subst_hd_def)

text \<open>If none of the expanded Nts depend on \<open>A\<close> then any rule depending on \<open>A\<close> in \<open>Expand_tri As R\<close>
      must already have been in \<open>R\<close>.\<close>
lemma helper_Expand_tri2: 
  "\<lbrakk>Eps_free R; A \<notin> set As; \<forall>C \<in> set As. A \<notin> (dep_on R C); B \<noteq> A; (B, Nt A # w) \<in> Expand_tri As R\<rbrakk>
    \<Longrightarrow> (B, Nt A # w) \<in> R"
proof (induction As R arbitrary: B w rule: Expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  have "(B, Nt A # w) \<in> Expand_tri Ss R"
  proof (cases "B = S")
    case B_is_S: True
    let ?R' = "Expand_tri Ss R"
    let ?X = "{(Al,Bw) \<in> ?R'. Al=S \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set (Ss))}"
    let ?Y = "{(S,v@w) |v w. \<exists>B. (S, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
    have "(B, Nt A # w) \<notin> ?X" using 2 by auto
    then have 3: "(B, Nt A # w) \<in> ?R' \<or> (B, Nt A # w) \<in> ?Y" using 2
      by (auto simp add: Let_def Subst_hd_def)
    then show ?thesis
    proof (cases "(B, Nt A # w) \<in> ?R'")
      case True
      then show ?thesis by simp
    next
      case False
      then have "(B, Nt A # w) \<in> ?Y" using 3 by simp
      then have "\<exists>v wa Ba. Nt A # w = v @ wa \<and> (S, Nt Ba # wa) \<in> Expand_tri Ss R \<and> Ba \<in> set Ss 
         \<and> (Ba, v) \<in> Expand_tri Ss R"
        by (auto simp add: Let_def)
      then obtain v wa Ba 
        where P: "Nt A # w = v @ wa \<and> (S, Nt Ba # wa) \<in> Expand_tri Ss R \<and> Ba \<in> set Ss 
                  \<and> (Ba, v) \<in> Expand_tri Ss R" 
        by blast
      have "Eps_free (Expand_tri Ss R)" using 2 by (auto simp add: Eps_free_Expand_tri)
      then have "v \<noteq> []" using P by (auto simp add: Eps_free_def)
      then have v_hd: "hd v = Nt A" using P by (metis hd_append list.sel(1))
      then have "\<exists>va. v = Nt A # va"
        by (metis \<open>v \<noteq> []\<close> list.collapse)
      then obtain va where P2: "v = Nt A # va" by blast
      then have "(Ba, v) \<in> R" using 2 P
        by (metis list.set_intros(2))
      then have "A \<in> dep_on R Ba" using v_hd P2 by (auto simp add: dep_on_def)
      then show ?thesis using 2 P by auto
    qed
  next
    case False
    then show ?thesis using 2 by (auto simp add: Let_def Subst_hd_def)
  qed

  then show ?case using 2 by auto
qed 

text \<open>In a Triangular form no Nts depend on the last Nt in the list.\<close>
lemma Triangular_snoc_dep_on: "Triangular (As@[A]) R \<Longrightarrow> \<forall>C \<in> set As. A \<notin> (dep_on R C)"
  by (induction As) auto

lemma Triangular_helper1: "Triangular As R \<Longrightarrow> A \<in> set As \<Longrightarrow> A \<notin> dep_on R A"
  by (induction As) auto

lemma dep_on_Expand_tri: 
  "\<lbrakk>Eps_free R; Triangular (rev As) R; distinct As; A \<in> set As\<rbrakk> 
   \<Longrightarrow> dep_on (Expand_tri As R) A \<inter> set As = {}"
proof(induction As R arbitrary: A rule: Expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  then have Eps_free_exp_Ss: "Eps_free (Expand_tri Ss R)"
    by (simp add: Eps_free_Expand_tri)
  have dep_on_fact: "\<forall>C \<in> set Ss. S \<notin> (dep_on R C)" 
    using 2 by (auto simp add: Triangular_snoc_dep_on)
  then show ?case
  proof (cases "A = S")
    case True
    have F1: "(S, Nt S # w) \<notin> Expand_tri Ss R" for w
    proof(rule ccontr)
      assume "\<not>((S, Nt S # w) \<notin> Expand_tri Ss R)"
      then have "(S, Nt S # w) \<in> R" using 2 by (auto simp add: Expand_tri_simp1)
      then have N: "S \<in> dep_on R A" using True by (auto simp add: dep_on_def)
      have "S \<notin> dep_on R A" using 2 True by (auto simp add: Triangular_helper1)
      then show "False" using N by simp
    qed

    have F2: "(S, Nt S # w) \<notin> Expand_tri (S#Ss) R" for w
    proof
      assume "(S, Nt S # w) \<in> Expand_tri (S#Ss) R"
      then have "\<exists>v wa B. Nt S # w = v @ wa \<and> B \<in> set Ss \<and> (S, Nt B # wa) \<in> Expand_tri Ss R 
         \<and> (B, v) \<in> Expand_tri Ss R"
        using 2 F1 by (auto simp add: Let_def Subst_hd_def)
      then obtain v wa B 
        where v_wa_B_P: "Nt S # w = v @ wa \<and> B \<in> set Ss \<and> (S, Nt B # wa) \<in> Expand_tri Ss R 
         \<and> (B, v) \<in> Expand_tri Ss R" 
        by blast
      then have "v \<noteq> [] \<and> (\<exists>va. v = Nt S # va)" using Eps_free_exp_Ss
        by (metis Eps_free_Nil append_eq_Cons_conv)
      then obtain va where vP: "v \<noteq> [] \<and> v = Nt S # va" by blast
      then have "(B, v) \<in> R" 
        using v_wa_B_P 2 dep_on_fact helper_Expand_tri2[of R S Ss B] True by auto
      then have "S \<in> dep_on R B" using vP by (auto simp add: dep_on_def)
      then show "False" using dep_on_fact v_wa_B_P by auto
    qed

    have "(S, Nt x # w) \<notin> Expand_tri (S#Ss) R" if asm: "x \<in> set Ss" for x w
    proof
      assume assm: "(S, Nt x # w) \<in> Expand_tri (S # Ss) R"
      then have "\<exists>v wa B. Nt x # w = v @ wa \<and> (S, Nt B # wa) \<in> Expand_tri Ss R \<and> B \<in> set Ss 
         \<and> (B, v) \<in> Expand_tri Ss R"
        using 2 asm by (auto simp add: Let_def Subst_hd_def)
      then obtain v wa B 
        where v_wa_B_P:"Nt x # w = v @ wa \<and> (S, Nt B # wa) \<in> Expand_tri Ss R \<and> B \<in> set Ss 
         \<and> (B, v) \<in> Expand_tri Ss R" 
        by blast
      then have dep_on_IH: "dep_on (Expand_tri Ss R) B \<inter> set Ss = {}" 
        using 2 by (auto simp add: tri_Snoc_impl_tri)
      have "v \<noteq> [] \<and> (\<exists>va. v = Nt x # va)" using Eps_free_exp_Ss v_wa_B_P
        by (metis Eps_free_Nil append_eq_Cons_conv)
      then obtain va where vP: "v \<noteq> [] \<and> v = Nt x # va" by blast
      then have "x \<in> dep_on (Expand_tri Ss R) B" using v_wa_B_P by (auto simp add: dep_on_def)
      then show "False" using dep_on_IH v_wa_B_P asm assm by auto
    qed

    then show ?thesis using 2 True F2 by (auto simp add: Let_def dep_on_def)
  next
    case False
    have "(A, Nt S # w) \<notin> Expand_tri Ss R" for w
    proof
      assume "(A, Nt S # w) \<in> Expand_tri Ss R"
      then have "(A, Nt S # w) \<in> R" using 2 helper_Expand_tri2 dep_on_fact
        by (metis False distinct.simps(2))
      then have F: "S \<in> dep_on R A" by (auto simp add: dep_on_def)
      have "S \<notin> dep_on R A" using dep_on_fact False 2 by auto
      then show "False" using F by simp
    qed
    then show ?thesis using 2 False by (auto simp add: tri_Snoc_impl_tri Let_def dep_on_def Subst_hd_def)
  qed
qed

text \<open>If the entire \<open>Triangular\<close> form is expanded, the result is in GNF:\<close>
theorem GNF_hd_Expand_tri: 
  assumes "Eps_free R" "Triangular (rev As) R" "distinct As" "Nts R \<subseteq> set As"
  shows "GNF_hd (Expand_tri As R)"
by (metis Eps_free_Expand_tri GNF_hd_iff_dep_on Int_absorb2 Nts_Expand_tri assms dep_on_Expand_tri
      dep_on_subs_Nts subset_trans subsetD)

text \<open>Any set of productions can be transformed into GNF via \<open>Expand_tri (Solve_tri)\<close>.\<close>
theorem GNF_hd_Expand_Solve_tri:
  assumes assms: "Eps_free R" "distinct (As @ As')" "Nts R \<subseteq> set As" "length As \<le> length As'"
  shows "GNF_hd (Expand_tri (As' @ rev As) (Solve_tri As As' R))"
proof -
  from assms have tri: "Triangular (As @ rev As') (Solve_tri As As' R)"
    by (simp add: Int_commute Triangular_Solve_tri)
  have "Nts (Solve_tri As As' R) \<subseteq> set As \<union> set As'" using assms Nts_Solve_tri by fastforce 
  then show ?thesis 
    using GNF_hd_Expand_tri[of "(Solve_tri As As' R)" "(As' @ rev As)"] assms tri 
    by (auto simp add: Eps_free_Solve_tri)
qed


subsection \<open>\<open>Expand_tri\<close> Preserves Language\<close>

text \<open>Similar to the proof of Language equivalence of \<open>Expand_hd_rec\<close>.\<close>

text \<open>All productions in \<open>Expand_tri As P\<close> are derivable by \<open>P\<close>.\<close>
lemma Expand_tri_prods_deirvable: "(B, bs) \<in> Expand_tri As P \<Longrightarrow> P \<turnstile> [Nt B] \<Rightarrow>* bs"
proof (induction As P arbitrary: B bs rule: Expand_tri.induct)
  case (1 R)
  then show ?case
    by (simp add: bu_prod derives_if_bu)
next
  case (2 A As R)
  then show ?case
  proof (cases "B \<in> set (A#As)")
    case True
    then show ?thesis 
    proof (cases "B = A")
      case True
      then have "\<exists>C cw v.(bs = cw@v \<and> (B, Nt C#v) \<in> (Expand_tri As R) \<and> (C,cw) \<in> (Expand_tri As R)) 
          \<or> (B, bs) \<in> (Expand_tri As R)"
        using 2 by (auto simp add: Let_def Subst_hd_def)
      then obtain C cw v 
        where "(bs = cw @ v \<and> (B, Nt C # v) \<in> (Expand_tri As R) \<and> (C, cw) \<in> (Expand_tri As R)) 
         \<or> (B, bs) \<in> (Expand_tri As R)" 
        by blast
      then have "(bs = cw @ v \<and> R \<turnstile> [Nt B] \<Rightarrow>* [Nt C] @ v \<and> R \<turnstile> [Nt C] \<Rightarrow>* cw) \<or> R \<turnstile> [Nt B] \<Rightarrow>* bs"
        using "2.IH" by auto       
      then show ?thesis by (meson derives_append rtranclp_trans)
    next
      case False
      then have "(B, bs) \<in> (Expand_tri As R)" using 2 by (auto simp add: Let_def Subst_hd_def)
      then show ?thesis using "2.IH" by (simp add: bu_prod derives_if_bu)
    qed
  next
    case False
    then have "(B, bs) \<in> R" using 2 by (auto simp: Expand_tri_simp1 simp del: Expand_tri.simps)
    then show ?thesis by (simp add: bu_prod derives_if_bu)
  qed
qed

text \<open>Language Preservation:\<close>
lemma Expand_tri_Lang: "Lang (Expand_tri As P) A = Lang P A"
proof
  have "(B, bs) \<in> (Expand_tri As P) \<Longrightarrow> P \<turnstile> [Nt B] \<Rightarrow>* bs" for B bs
    by (simp add: Expand_tri_prods_deirvable)
  then have "Expand_tri As P \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm x" for x
    using derives_simul_rules by blast
  then show "Lang (Expand_tri As P) A \<subseteq> Lang P A"  by(auto simp add: Lang_def)
next
  show "Lang P A \<subseteq> Lang (Expand_tri As P) A"
  proof (induction As P rule: Expand_tri.induct)
    case (1 R)
    then show ?case by simp
  next
    case (2 D Ds R)
    let ?R' = "Expand_tri Ds R"
    let ?X = "{r \<in> ?R'. (\<exists>w B. r = (D, Nt B # w) \<and> B \<in> set (Ds))}"
    let ?Y = "{(D,v@w) | v w. \<exists>B. (B,v) \<in> ?R' \<and> (D, Nt B # w) \<in> ?X}"
    have F1: "Expand_tri (D#Ds) R = ?R' - ?X \<union> ?Y" by (auto simp: Let_def Subst_hd_def)

    let ?S = "{x. \<exists>A w H. x = (A, [], H, w) \<and> (A, Nt H # w) \<in> ?X}"
    let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
    let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> ?R'}"
  
    have S'_eq_X: "?S' = ?X" by fastforce
    have E_eq_Y: "?E = ?Y" by fastforce

    have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> ?R'" by fastforce
    have "Lang R A \<subseteq> Lang (Expand_tri Ds R) A" using 2 by simp
    also have "... \<subseteq> Lang (?R' - ?S' \<union> ?E) A"
      using exp_includes_Lang[of ?S] by auto
    also have "... = Lang (Expand_tri (D#Ds) R) A" using S'_eq_X E_eq_Y F1 by fastforce
    finally show ?case.
  qed
qed

section \<open>Function @{const GNF_hd_of}: Conversion to @{const GNF_hd}\<close>

text \<open>All epsilon-free grammars can be put into GNF while preserving their language.\<close>
text \<open>Putting the productions into GNF via \<open>Expand_tri (Solve_tri)\<close> preserves the language.\<close>
lemma Lang_Expand_Solve_tri: 
  assumes "Eps_free P" "length As \<le> length As'" "distinct (As @ As')" "Nts P \<inter> set As' = {}" "A \<notin> set As'"
  shows "Lang (Expand_tri (As' @ rev As) (Solve_tri As As' P)) A = Lang P A"
using Lang_Solve_tri[OF assms] Expand_tri_Lang[of "(As' @ rev As)"] by blast

text \<open>Any grammar can be brought into head GNF.\<close>

theorem GNF_hd_GNF_hd_of: "distinct As \<Longrightarrow> Nts P \<subseteq> set As \<Longrightarrow> GNF_hd (GNF_hd_of As P)"
unfolding GNF_hd_of_def Let_def
  apply (rule GNF_hd_Expand_Solve_tri[OF Eps_free_Eps_elim])
  using Nts_Eps_elim[of P]
  by(simp_all add: freshs_distinct freshs_disj length_freshs)

corollary gnf_hd_gnf_hd_of: "gnf_hd (gnf_hd_of ps)"
unfolding set_gnf_hd_of
apply (rule GNF_hd_GNF_hd_of)
by (simp_all add: set_nts distinct_nts)

lemma distinct_app_freshs: "\<lbrakk> distinct As; As' = freshs (set As) As \<rbrakk> \<Longrightarrow>
   distinct (As @ As')"
using freshs_disj[of "set As" As]
by (auto simp: distinct_nts freshs_distinct)

text \<open>\<open>GNF_hd_of\<close> preserves the language (modulo \<open>[]\<close>):\<close>
theorem Lang_GNF_hd_of: "distinct As \<Longrightarrow> Nts P \<subseteq> set As \<Longrightarrow> A \<in> set As \<Longrightarrow> Lang (GNF_hd_of As P) A = Lang P A - {[]}"
unfolding GNF_hd_of_def Let_def
apply(rule Lang_Expand_Solve_tri[OF Eps_free_Eps_elim, simplified Lang_Eps_elim])
   apply (simp add: length_freshs)
  apply (rule distinct_app_freshs;simp_all)
 apply (metis (no_types, lifting) ext Int_assoc Int_empty_right Nts_Eps_elim
    distinct_app_freshs distinct_append inf.orderE)
apply (meson List.finite_set disjoint_iff freshs_disj subsetD)
done

corollary lang_gnf_hd_of: "A \<in> set (nts ps) \<Longrightarrow> lang (gnf_hd_of ps) A = lang ps A - {[]}"
  unfolding set_gnf_hd_of
  apply (rule Lang_GNF_hd_of)
  by (auto simp: set_nts distinct_nts)

text \<open>Two simple examples:\<close>

lemma "gnf_hd_of [(0, [Nt(0::nat), Tm (1::int)])] = [(1, [Tm 1]), (1, [Tm 1, Nt 1])]"
  by eval

lemma "gnf_hd_of [(0, [Nt(0::nat), Tm (1::int)]), (0, [Tm 2]), (8, []), (9, [Nt 8])] =
  [(0, [Tm 2]), (0, [Tm 2]), (0, [Tm 2, Nt 1]), (1, [Tm 1]), (1, [Tm 1, Nt 1])]"
  by eval

text \<open>Example 4.10 \cite{HopcroftU79}:
 \<open>P0\<close> is the input; \<open>P1\<close> is the result after Step 1; \<open>P3\<close> is the result after Step 2 and 3.\<close>

lemma
  "let
     P0 =
       [(1::int, [Nt 2, Nt 3]), (2,[Nt 3, Nt 1]), (2, [Tm (1::int)]), (3,[Nt 1, Nt 2]), (3,[Tm 0])];
     P1 =
       [(1, [Nt 2, Nt 3]), (2, [Nt 3, Nt 1]), (2, [Tm 1]),
        (3, [Tm 1, Nt 3, Nt 2, Nt 4]), (3, [Tm 0, Nt 4]), (3, [Tm 1, Nt 3, Nt 2]), (3, [Tm 0]),
        (4, [Nt 1, Nt 3, Nt 2]), (4, [Nt 1, Nt 3, Nt 2, Nt 4])];
     P2 =
       [(1, [Tm 1, Nt 3, Nt 2, Nt 4, Nt 1, Nt 3]), (1, [Tm 1, Nt 3, Nt 2, Nt 1, Nt 3]),
        (1, [Tm 0, Nt 4, Nt 1, Nt 3]), (1, [Tm 0, Nt 1, Nt 3]), (1, [Tm 1, Nt 3]),
        (2, [Tm 1, Nt 3, Nt 2, Nt 4, Nt 1]), (2, [Tm 1, Nt 3, Nt 2, Nt 1]),
        (2, [Tm 0, Nt 4, Nt 1]), (2, [Tm 0, Nt 1]), (2, [Tm 1]),
        (3, [Tm 1, Nt 3, Nt 2, Nt 4]), (3, [Tm 1, Nt 3, Nt 2]),
        (3, [Tm 0, Nt 4]), (3, [Tm 0]),
        (4, [Tm 1, Nt 3, Nt 2, Nt 4, Nt 1, Nt 3, Nt 3, Nt 2, Nt 4]), (4, [Tm 1, Nt 3, Nt 2, Nt 4, Nt 1, Nt 3, Nt 3, Nt 2]),
        (4, [Tm 0, Nt 4, Nt 1, Nt 3, Nt 3, Nt 2, Nt 4]), (4, [Tm 0, Nt 4, Nt 1, Nt 3, Nt 3, Nt 2]),
        (4, [Tm 1, Nt 3, Nt 3, Nt 2, Nt 4]), (4, [Tm 1, Nt 3, Nt 3, Nt 2]),
        (4, [Tm 1, Nt 3, Nt 2, Nt 1, Nt 3, Nt 3, Nt 2, Nt 4]), (4, [Tm 1, Nt 3, Nt 2, Nt 1, Nt 3, Nt 3, Nt 2]),
        (4, [Tm 0, Nt 1, Nt 3, Nt 3, Nt 2, Nt 4]), (4, [Tm 0, Nt 1, Nt 3, Nt 3, Nt 2])]
   in
     Solve_tri [3,2,1] [4,5,6] (set P0) = set P1 \<and> Expand_tri [4,1,2,3] (set P1) = set P2"
by eval

section \<open>Full Greibach Normal Form\<close>

text \<open>One can easily convert head GNF into full GNF by replacing tail terminals
by fresh nonterminals.\<close>

definition Bad_Tms_GNF :: "('n,'t) Prods \<Rightarrow> 't set" where
  "Bad_Tms_GNF P = \<Union>{Tms_syms \<alpha> | \<alpha>. \<exists>A x. (A,x#\<alpha>) \<in> P}"

definition bad_tms_gnf :: "('n,'t) prods \<Rightarrow> 't list" where
  "bad_tms_gnf P = fold List.union [tms_syms \<alpha>. (A,x#\<alpha>) \<leftarrow> P] []"

lemma set_bad_tms_gnf: "set (bad_tms_gnf P) = Bad_Tms_GNF (set P)"
  by (force simp: Bad_Tms_GNF_def bad_tms_gnf_def set_fold_union image_Collect set_tms_syms)

lemma distinct_bad_tms_gnf: "distinct (bad_tms_gnf P)"
  by (simp add: bad_tms_gnf_def distinct_fold_union)

lemma GNF_Replace_Tm_tl:
  assumes P: "GNF_hd P" and Pf: "Bad_Tms_GNF P \<subseteq> dom f"
  shows "GNF (Replace_Tm_tl f P)"
  apply (unfold Replace_Tm_tl_def Replace_Tm_def set_append GNF_Un)
proof (intro conjI GNF_I)
  fix A \<alpha>' assume "(A,\<alpha>') \<in> {(A, replace_Tm_tl_syms f \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P}"
  then obtain \<alpha> where AP: "(A,\<alpha>) \<in> P" and \<alpha>': "\<alpha>' = replace_Tm_tl_syms f \<alpha>" by auto
  from AP P obtain a \<beta> where [simp]: "\<alpha> = Tm a # \<beta>" by (auto simp: GNF_hd_def)
  from \<alpha>' have [simp]: "\<alpha>' = Tm a # map (replace_Tm_sym f) \<beta>" by (auto simp: replace_Tm_tl_syms_def)
  define Bs where "Bs \<equiv> [case x of Nt B \<Rightarrow> B | Tm b \<Rightarrow> the (f b). x \<leftarrow> \<beta>]"
  from Pf AP have "Tms_syms \<beta> \<subseteq> dom f" by (force simp: Bad_Tms_GNF_def)
  then have "map (replace_Tm_sym f) \<beta> = map Nt Bs"
    by (unfold Bs_def, induction \<beta>, auto simp: replace_Tm_sym_simps split: sym.splits option.splits)
  with \<alpha>' have "\<alpha>' = Tm a # map Nt Bs" by simp
  then show "\<exists>a Bs. \<alpha>' = Tm a # map Nt Bs" by blast
qed (auto simp: Replace_Tm_new_def)

definition GNF_of :: "'n list \<Rightarrow> 't list \<Rightarrow> ('n::fresh0,'t)Prods \<Rightarrow> ('n,'t)Prods" where
[code_unfold]: "GNF_of As as P =
 (let As' = freshs (set As) As;
      P' = Expand_tri (As' @ rev As) (Solve_tri As As' (Eps_elim P))
  in Replace_Tm_tl (fresh_map (set As \<union> set As') as) P')"

value "GNF_of [1,2,3] [0,1] {
(1::nat, [Nt 2, Nt 3]),
(2,[Nt 3, Nt 1]), (2, [Tm (1::int)]),
(3,[Nt 1, Nt 2]), (3,[Tm 0])}"

definition gnf_of :: "('n::fresh0,'t)prods \<Rightarrow> ('n,'t)prods" where
"gnf_of P =
 (let As = nts P;
      As' = freshs (set As) As;
      P' = expand_tri (As' @ rev As) (solve_tri As As' (eps_elim P));
      f = fresh_assoc (set As \<union> set As') (bad_tms_gnf P')
  in replace_Tm_tl f P')"

lemma set_gnf_of: "set (gnf_of P) = GNF_of (nts P) (bad_tms_gnf (gnf_hd_of P)) (set P)"
  by (simp add: gnf_of_def GNF_of_def Let_def set_replace_Tm_tl set_expand_tri
      set_solve_tri set_eps_elim distinct_fold_union map_fst_fresh_assoc distinct_bad_tms_gnf
      map_of_fresh_assoc gnf_hd_of_def)

lemma GNF_of_via_GNF_hd_of:
  "GNF_of As as P =
  (let As' = freshs (set As) As;
       f = fresh_map (set As \<union> set As') as
   in Replace_Tm_tl f (GNF_hd_of As P))"
  by (auto simp: GNF_of_def GNF_hd_of_def Let_def)

theorem GNF_GNF_of:
  assumes As: "distinct As" and PAs: "Nts P \<subseteq> set As"
    and Pas: "Bad_Tms_GNF (GNF_hd_of As P) \<subseteq> set as"
  shows "GNF (GNF_of As as P)"
  apply (unfold GNF_of_via_GNF_hd_of Let_def)
  apply (rule GNF_Replace_Tm_tl)
  using GNF_hd_GNF_hd_of[OF As PAs] Pas
  by (simp_all add: dom_fresh_map)

theorem Lang_GNF_of:
  assumes As: "distinct As" and PAs: "Nts P \<subseteq> set As"
    and Pas: "Bad_Tms_GNF (GNF_hd_of As P) \<subseteq> set as"
    and AAs: "A \<in> set As"
  shows "Lang (GNF_of As as P) A = Lang P A - {[]}"
proof-
  define As' where "As' = freshs (set As) As"
  define f where "f = fresh_map (set As \<union> set As') as"
  show ?thesis
    apply (unfold GNF_of_via_GNF_hd_of Let_def)
    apply (fold As'_def)
    apply (fold f_def)
    apply (fold Lang_GNF_hd_of[OF As PAs AAs])
  proof (rule Lang_Replace_Tm_tl[OF _ _ ])
    show "inj_on f (dom f)"
      apply (unfold f_def dom_fresh_map)
      apply (rule fresh_map_inj_on)
      by simp
    from fresh_map_disj[of "set As \<union> set As'" as, simplified, folded f_def]
      Nts_GNF_hd_of[of As P, folded As'_def] AAs PAs
    show "A \<notin> ran f" and "ran f \<inter> Nts (GNF_hd_of As P) = {}" by auto
  qed
qed

corollary gnf_gnf_of: "gnf (gnf_of P)"
  apply (unfold set_gnf_of)
  apply (rule GNF_GNF_of)
  using distinct_nts by (auto simp: set_nts set_bad_tms_gnf set_gnf_hd_of)

theorem lang_gnf_of:
  assumes A: "A \<in> set (nts P)"
  shows "lang (gnf_of P) A = lang P A - {[]}"
  apply (unfold set_gnf_of)
  apply (rule Lang_GNF_of)
  using distinct_nts A by (auto simp: set_nts set_bad_tms_gnf set_gnf_hd_of)

value "remdups (gnf_of [
(1::nat, [Nt 2, Nt 3]),
(2,[Nt 3, Nt 1]), (2, [Tm (1::int)]),
(3,[Nt 1, Nt 2]), (3,[Tm 0])])"



section \<open>Complexity\<close>

text \<open>Our method has exponential complexity, which we demonstrate below.
Alternative polynomial methods are described in the literature \cite{BlumK99}.

We start with an informal proof that the blowup of the whole method can be as bad
as $2^{n^2}$, where $n$ is the number of non terminals, and the starting grammar has $4n$ productions.

Consider this grammar, where \<open>a\<close> and \<open>b\<close> are terminals and we use nested alternatives in the obvious way:

\<open>A0 \<rightarrow> A1 (a | b) | A2 (a | b) | ... | An (a | b) | a | b\<close>

\<open>A(i+1) \<rightarrow> Ai (a | b)\<close>

Expanding all alternatives makes this a grammar of size $4n$.

When converting this grammar into Triangular form, starting with \<open>A0\<close>, we find that \<open>A0\<close> remains the
same after \<open>Expand_hd_rec\<close>, and \<open>Solve_lrec\<close> introduces a new additional production for every \<open>A0\<close> production,
which we will ignore to simplify things:

Then every \<open>Expand_hd_rec\<close> step yields for \<open>Ai\<close> these number of productions:

  (1) \<open>2^(i+1)\<close> productions with rhs \<open>Ak (a | b)^(i+1)\<close> for every \<open>k \<in> [i+1, n]\<close>,

  (2) \<open>2^(i+1)\<close> productions with rhs \<open>(a | b)^(i+1)\<close>,

  (3) \<open>2^(i+1)\<close> productions with rhs \<open>Ai (a | b)^(i+1)\<close>.

Note that \<open>(a | b)^(i+1)\<close> represents all words of length \<open>i+1\<close> over \<open>{a,b}\<close>.
Solving the left recursion again introduces a new additional production for every production of form (1) and (2),
which we will again ignore for simplicity. 
The productions of (3) get removed by \<open>Solve_lrec\<close>.
We will not consider the productions of the newly introduced nonterminals.

In the Triangular form, every \<open>Ai\<close> has at least \<open>2^(i+1)\<close> productions starting with terminals (2)
and \<open>2^(i+1)\<close> productions with rhs starting with \<open>Ak\<close> for every \<open>k \<in> [i+1, n]\<close>.

When expanding the Triangular form starting from \<open>An\<close>, which has at least the \<open>2^(i+1)\<close> productions from (2),
we observe that the number of productions of \<open>Ai\<close> (denoted by \<open>#Ai\<close>) is  \<open>#Ai \<ge> 2^(i+1) * #A(i+1)\<close> 
(Only considering the productions of the form \<open>A(i+1) (a | b)^(i+1)\<close>).
This yields that \<open>#Ai \<ge> 2^(i+1) * 2^((i+2) + ... + (n+1)) = 2^((i+1) + (i+2) + ... (n+1))\<close>.
Thus \<open>#A0 \<ge> 2^(1 + 2 + ... + n + (n+1)) = 2^((n+1)*(n+2)/2)\<close>.

Below we prove formally that \<open>Expand_tri\<close> can cause exponential blowup.\<close>

text \<open>Bad grammar: Constructs a grammar which leads to a exponential blowup when expanded 
      by \<open>Expand_tri\<close>:\<close>
fun bad_grammar :: "nat \<Rightarrow> (nat,bool) prods" where
 "bad_grammar 0 = [(0, [Tm False]), (0, [Tm True])]"
|"bad_grammar (Suc n) = [(Suc n, Nt n # [Tm False]), (Suc n, Nt n # [Tm True])] @ bad_grammar n"


value "nts (bad_grammar 4)"

lemma bad_gram_simp1: "n < m \<Longrightarrow> (m,w) \<notin> set (bad_grammar n)"
  by (induction n rule: bad_grammar.induct) auto

lemma Expand_tri_insert_simp: 
  "B \<notin> set As \<Longrightarrow> Expand_tri As (insert (B,w) R) = insert (B,w) (Expand_tri As R)"
  apply (induction As R rule: Expand_tri.induct)
   apply (auto simp add: Let_def Subst_hd_def)apply auto done

lemma Expand_tri_bad_grammar_simp1: 
  "Expand_tri (rev [0..<Suc n]) (set (bad_grammar (Suc n))) =
   {(Suc n, Nt n # [Tm False]), (Suc n, Nt n # [Tm True])} \<union>
   Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))"
proof (induction n)
  case 0
  then show ?case by (auto simp: Subst_hd_def)
next
  case (Suc n)
  have 1: "rev [0..< Suc (Suc n)] = Suc n # rev [0..<Suc n]" by simp
  define S where "S \<equiv> Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))"
  show ?case
    unfolding 1
    apply (simp del: upt_Suc bad_grammar.simps(2)
        add: bad_grammar.simps(2)[of "Suc n"] Expand_tri_insert_simp Suc
        S_def[symmetric] Subst_hd_def)
    by auto (* takes time *)
qed

lemma finite_Expand_tri: "finite R \<Longrightarrow> finite (Expand_tri As R)"
proof (induction As R rule: Expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  let ?S = "{(A, v @ w) |A v w. \<exists>B. (B, v) \<in> Expand_tri Ss R \<and> (A, Nt B # w) \<in> Expand_tri Ss R \<and> A = S \<and> B \<in> set Ss}"
  let ?f = "\<lambda>((A,w),(B,v)). (A, v @ (tl w))"
  have "?S \<subseteq> ?f ` (Expand_tri Ss R \<times> Expand_tri Ss R)"
  proof
    fix x
    assume "x \<in> ?S"
    then have "\<exists>S v B w. (S,Nt B # w) \<in> Expand_tri Ss R \<and> (B,v) \<in> Expand_tri Ss R \<and> x = (S, v @ w)" 
      by blast
    then obtain S v B w 
      where P: "(S, Nt B # w) \<in> Expand_tri Ss R \<and> (B, v) \<in> Expand_tri Ss R \<and> x = (S, v @ w)"
      by blast
    then have 1: "((S, Nt B # w), (B ,v)) \<in> ((Expand_tri Ss R) \<times> (Expand_tri Ss R))" by auto
    have "?f ((S, Nt B # w), (B ,v)) = (S, v @ w)" by auto
    then have "(S, v @ w) \<in> ?f ` ((Expand_tri Ss R) \<times> (Expand_tri Ss R))" using 1 by force
    then show "x \<in> ?f ` ((Expand_tri Ss R) \<times> (Expand_tri Ss R))" using P by simp
  qed
  then have "finite ?S"
    by (meson "2.IH" "2.prems" finite_SigmaI finite_surj)
  with 2 show ?case by (auto simp add: Let_def Subst_hd_def)
qed

text \<open>The last Nt expanded by \<open>Expand_tri\<close> has an exponential number of productions.\<close>

lemma bad_gram_last_expanded_card:
  "card ({v. (n, v) \<in> Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))}) = 2 ^ Suc n" 
proof(induction n)
  case 0
  have 4: "{v. v = [Tm False] \<or> v = [Tm True]} = {[Tm False], [Tm True]}" by auto
  show ?case by (auto simp: 4 Subst_hd_def)
next
  case (Suc n)
  have 1: "rev [0..<Suc (Suc n)] = Suc n # rev [0..<Suc n]" by simp
  note upt_Suc[simp del]
  let ?R = "Expand_tri (rev [0..<Suc (Suc n)]) (set (bad_grammar (Suc n)))"
  let ?S = "{v. (Suc n, v) \<in> ?R}"
  let ?Rn = "Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))"
  let ?Sn = "{v. (n, v) \<in> ?Rn}"
  
  let ?R' = "Expand_tri (rev [0..<Suc n]) (set (bad_grammar (Suc n)))"
  let ?X = "{(Al,Bw) \<in> ?R'. Al=Suc n \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<le> n)}"
  let ?Y = "{(Suc n, v@w) |v w. \<exists>B. (Suc n, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"


  have 4: "(Suc n, Bw) \<in> ?R' \<longleftrightarrow> (Suc n, Bw) \<in> set (bad_grammar (Suc n))" for Bw
    by (simp add: Expand_tri_simp1)
  have "?X = {(Al,Bw) \<in> set (bad_grammar (Suc n)). Al = Suc n \<and> (\<exists>w B. Bw = Nt B#w \<and> B \<le> n)}"
    by (auto simp add: Expand_tri_simp1)
  also have "... = {(Suc n, Nt n # [Tm False]), (Suc n, Nt n # [Tm True])}" 
    by (auto simp: bad_gram_simp1)
  finally have 5: "?X = \<dots>".
  then have cons5: "?X = {(Suc n, Nt n # [Tm False]), (Suc n, Nt n # [Tm True])}" by simp

  have 6: "?R' = {(Suc n, [Nt n, Tm False]), (Suc n, [Nt n, Tm True])} \<union> Expand_tri (rev[0..<Suc n]) (set (bad_grammar n))"
    using Expand_tri_bad_grammar_simp1
    by simp
  have 8: "(Suc n, w) \<notin> Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))" for w 
    by (simp add: bad_gram_simp1 Expand_tri_simp1)
  then have 7: "{(Suc n, [Nt n, Tm False]), (Suc n, [Nt n, Tm True])} \<inter> Expand_tri (rev [0..<Suc n]) (set (bad_grammar n)) = {}"
    by auto

  have "?R' - ?X = Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))" using 7 6 5 by simp
  have S_from_Y: "?S = {v. (Suc n, v) \<in> ?Y}"
    by (auto simp: 1 Let_def Expand_tri_simp1 bad_gram_simp1 Expand_tri_insert_simp Subst_hd_def)

  note bad_grammar.simps(2)[simp del]
  have Y_decomp: "?Y = {(Suc n, v @ [Tm False]) | v. (n,v) \<in> ?R'} \<union> {(Suc n, v @ [Tm True]) | v. (n,v) \<in> ?R'}"
    (is "?Y = ?Z")
  proof
    show "?Y \<subseteq> ?Z"
    proof
      fix x
      assume assm: "x \<in> ?Y"
      then have "\<exists>v w. x = (Suc n, v @ w) \<and> (\<exists>B. (Suc n, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R')" by blast
      then obtain v w where P: "x = (Suc n, v @ w) \<and> (\<exists>B. (Suc n, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R')" by blast
      then have cfact:"(Suc n, Nt n # w) \<in> ?X \<and> (n,v) \<in> ?R'" using cons5 
        by (metis (no_types, lifting) Pair_inject insert_iff list.inject singletonD sym.inject(1))
      then have "w = [Tm False] \<or> w = [Tm True]" using cons5
        by (metis (no_types, lifting) empty_iff insertE list.inject prod.inject)
      then show "x \<in> ?Z" using P cfact by auto
    qed
  next
    show "?Z \<subseteq> ?Y" 
      using cons5 by auto
  qed
  
  from Y_decomp have S_decomp: "?S = {v@[Tm False] | v. (n,v) \<in> ?R'} \<union> {v@[Tm True] | v. (n,v) \<in> ?R'}"
    using S_from_Y by auto

  have cardCvR: "card {v. (n, v) \<in> ?R'} = 2 ^ Suc n" using Suc 6 by auto
  have "bij_betw (\<lambda>x. x@[Tm False]) {v. (n, v) \<in> ?R'} {v@[Tm False] | v. (n, v) \<in> ?R'}"
    by (auto simp add: bij_betw_def inj_on_def)
  then have cardS1: "card {v@[Tm False] | v. (n, v) \<in> ?R'} = 2 ^ Suc n"
    using cardCvR by (auto simp add: bij_betw_same_card)
  have "bij_betw (\<lambda>x. x@[Tm True]) {v. (n, v) \<in> ?R'} {v@[Tm True] | v. (n,v) \<in> ?R'}"
    by (auto simp add: bij_betw_def inj_on_def)
  then have cardS2: "card {v@[Tm True] | v. (n,v) \<in> ?R'} = 2 ^ Suc n" 
    using cardCvR by (auto simp add: bij_betw_same_card)

  have fin_R': "finite ?R'" using finite_set finite_Expand_tri by blast
  let ?f1 = "\<lambda>(C,v). v@[Tm False]"
  have "{v@[Tm False] | v. (n,v) \<in> ?R'} \<subseteq> ?f1 ` ?R'" by auto
  then have fin1: "finite {v@[Tm False] | v. (n,v) \<in> ?R'}"
    using fin_R' by (meson finite_SigmaI finite_surj)
  let ?f2 = "\<lambda>(C,v). v@[Tm True]"
  have "{v@[Tm True] | v. (n,v) \<in> ?R'} \<subseteq> ?f2 ` ?R'" by auto
  then have fin2: "finite {v@[Tm True] | v. (n,v) \<in> ?R'}"
    using fin_R' by (meson finite_SigmaI finite_surj)

  have fin_sets: "finite {v@[Tm False] | v. (n,v) \<in> ?R'} \<and> finite {v@[Tm True] | v. (n,v) \<in> ?R'}"
    using fin1 fin2 by simp

  have "{v@[Tm False] | v. (n,v) \<in> ?R'} \<inter> {v@[Tm True] | v. (n,v) \<in> ?R'} = {}" by auto
  then have "card ?S = 2^(Suc n) + 2^(Suc n)"
    using S_decomp cardS1 cardS2 fin_sets 
    by (auto simp add: card_Un_disjoint)
  then show ?case by auto
qed

text \<open>The productions resulting from \<open>Expand_tri (bad_grammar)\<close> have at least exponential size.\<close>
theorem Expand_tri_blowup:
  "card (Expand_tri (rev [0..<Suc n]) (set (bad_grammar n))) \<ge> 2^(Suc n)"
(is "card ?R \<ge> _")
proof -
  have fin: "finite ?R"
    using finite_set finite_Expand_tri by blast
  have "{v. (n,v) \<in> ?R} \<subseteq> snd ` ?R" by (force simp del: upt_Suc simp: image_def)
  from fin card_mono[OF _ this, unfolded bad_gram_last_expanded_card]
    card_image_le[OF fin, of snd]
  show ?thesis by (auto simp del: upt_Suc)
qed

(* Attempt to prove gnf_hd_of (bad_grammar n). Aborted because nts cannot be ordered properly. *)
lemma in_dep_on_bad_grammar: "n \<in> dep_on (set (bad_grammar m)) l \<longleftrightarrow> l = Suc n \<and> n < m"
  by (induction m, auto simp: dep_on_insert)

lemma Triangular_bad_grammar: "Triangular [m..<n] (set (bad_grammar l))"
proof (induction "n-m" arbitrary: n m)
  case 0
  then show ?case by (auto simp: dep_on_def)
next
  case (Suc d)
  then have 1: "[m..<n] = m # [Suc m..<n]" by (simp add: upt_conv_Cons)
  from Suc have "d = n - Suc m" by simp
  from Suc(1)[OF this]
  show ?case by (auto simp add: 1 in_dep_on_bad_grammar)
qed

lemma Solve_tri_bad_grammar:
  "length As' = Suc n \<Longrightarrow> Solve_tri [0..<Suc n] As' (set (bad_grammar l)) = set (bad_grammar l)"
  apply (rule Solve_tri_id[OF Triangular_bad_grammar]) by simp

end
