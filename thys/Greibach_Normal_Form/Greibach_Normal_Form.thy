(* Authors: Alexander Haberl, Tobias Nipkow, Akihisa Yamada *)

theory Greibach_Normal_Form
imports
  "Context_Free_Grammar.Context_Free_Grammar"
  "Context_Free_Grammar.Epsilon_Elimination"
  Fresh_Identifiers.Fresh_Nat
begin

(* Import of additional theories undoes this deletion in \<open>Context_Free_Grammar\<close>: *)
declare relpowp.simps(2)[simp del] 

text \<open>This theory formalizes a method to transform a set of productions into 
Greibach Normal Form (GNF) \<^cite>\<open>Greibach\<close>. We concentrate on the essential property of the GNF:
every production starts with a \<open>Tm\<close>; the tail of a rhs can contain further terminals.
This is formalized as \<open>GNF_hd\<close> below. This more liberal definition of GNF is also found elsewhere
\cite{BlumK99}.

The algorithm consists of two phases:

  \<^item> \<open>solve_tri\<close> converts the productions into a \<open>triangular\<close> form, where Nt \<open>Ai\<close> does not 
  depend on Nts \<open>Ai, \<dots>, An\<close>. This involves the elimination of left-recursion and is the heart
  of the algorithm.

  \<^item> \<open>expand_tri\<close> expands the triangular form by substituting in:
  Due to triangular form, \<open>A0\<close> productions satisfy \<open>GNF_hd\<close> and we can substitute
  them into the heads of the remaining productions. Now all \<open>A1\<close> productions satisfy \<open>GNF_hd\<close>,
  and we continue until all productions satisfy \<open>GNF_hd\<close>.

This is essentially the algorithm given by Hopcroft and Ullman \cite{HopcroftU79},
except that we can drop the conversion to Chomsky Normal Form because of our more liberal \<open>GNF_hd\<close>.
\<close>


section \<open>Function Definitions\<close>

text \<open>Depend on: \<open>A\<close> depends on \<open>B\<close> if there is a rule \<open>A \<rightarrow> B w\<close>:\<close>
definition dep_on :: "('n,'t) Prods \<Rightarrow> 'n \<Rightarrow> 'n set" where
"dep_on R A = {B. \<exists>w. (A,Nt B # w) \<in> R}"

text \<open>GNF property: All productions start with a terminal.\<close>
definition GNF_hd :: "('n,'t)Prods \<Rightarrow> bool" where 
"GNF_hd R = (\<forall>(A, w) \<in> R. \<exists>t. hd w = Tm t)"

text \<open>GNF property expressed via \<open>dep_on\<close>:\<close>
definition GNF_hd_dep_on :: "('n,'t)Prods \<Rightarrow> bool" where
"GNF_hd_dep_on R = (\<forall>A \<in> Nts R. dep_on R A = {})"

abbreviation lrec_Prods :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 'n set \<Rightarrow> ('n,'t)Prods" where
"lrec_Prods R A S \<equiv> {(A',Bw) \<in> R. A'=A \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> S)}"

abbreviation subst_hd :: "('n,'t)Prods \<Rightarrow> ('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods" where
"subst_hd R X A \<equiv>  {(A,v@w) |v w. \<exists>B. (A,Nt B # w) \<in> X \<and> (B,v) \<in> R}"

text \<open>Expand head: Replace all rules \<open>A \<rightarrow> B w\<close> where \<open>B \<in> Ss\<close>
(\<open>Ss\<close> = solved Nts in \<open>triangular\<close> form)
by \<open>A \<rightarrow> v w\<close> where \<open>B \<rightarrow> v\<close>. Starting from the end of \<open>Ss\<close>.\<close>
fun expand_hd :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"expand_hd A [] R = R" |
"expand_hd A (S#Ss) R =
 (let R' = expand_hd A Ss R;
      X = lrec_Prods R' A {S};
      Y = subst_hd R' X A
  in R' - X \<union> Y)"

lemma Rhss_code[code]: "Rhss P A = snd ` {Aw \<in> P. fst Aw = A}"
by(auto simp add: Rhss_def image_iff)

declare expand_hd.simps(1)[code]
lemma expand_hd_Cons_code[code]: "expand_hd A (S#Ss) R =
 (let R' = expand_hd A Ss R;
      X = {w \<in> Rhss R' A. w \<noteq> [] \<and> hd w = Nt S};
      Y = (\<Union>(B,v) \<in> R'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(A,v @ tl w)})
  in R' - ({A} \<times> X) \<union> Y)"
by(simp add: Rhss_def Let_def neq_Nil_conv Ball_def hd_append split: if_splits, safe, force+)

text \<open>Remove left-recursions: Remove left-recursive rules \<open>A \<rightarrow> A w\<close>:\<close>
definition rm_lrec ::  "'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"rm_lrec A R = R - {(A,Nt A # v)|v. True}"

lemma rm_lrec_code[code]:
  "rm_lrec A R = {Aw \<in> R. let (A',w) = Aw in A' \<noteq> A \<or> w = [] \<or> hd w \<noteq> Nt A}"
by(auto simp add: rm_lrec_def neq_Nil_conv)

text \<open>Make right-recursion of left-recursion: Conversion from left-recursion to right-recursion:
Split \<open>A\<close>-rules into \<open>A \<rightarrow> u\<close> and \<open>A \<rightarrow> A v\<close>.
Keep \<open>A \<rightarrow> u\<close> but replace \<open>A \<rightarrow> A v\<close> by \<open>A \<rightarrow> u A'\<close>, \<open>A' \<rightarrow> v\<close>, \<open>A' \<rightarrow> v A'\<close>.

The then part of the if statement is only an optimisation, so that we do not introduce the 
\<open>A \<rightarrow> u A'\<close> rules if we do not introduce any \<open>A'\<close> rules, but the function also works, if we always 
enter the else part.\<close>
definition rrec_of_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"rrec_of_lrec A A' R =
  (let V = {v. (A,Nt A # v) \<in> R \<and> v \<noteq> []};
       U = {u. (A,u) \<in> R \<and> \<not>(\<exists>v. u = Nt A # v) }
  in if V = {} then R - {(A, [Nt A])} else ({A} \<times> U) \<union> (\<Union>u\<in>U. {(A,u@[Nt A'])}) \<union> ({A'} \<times> V) \<union> (\<Union>v\<in>V. {(A',v @ [Nt A'])}))"

lemma rrec_of_lrec_code[code]: "rrec_of_lrec A A' R =
  (let RA = Rhss R A;
       V = tl ` {w \<in> RA. w \<noteq> [] \<and> hd w = Nt A \<and> tl w \<noteq> []};
       U = {u \<in> RA. u = [] \<or> hd u \<noteq> Nt A }
  in if V = {} then R - {(A, [Nt A])} else ({A} \<times> U) \<union> (\<Union>u\<in>U. {(A,u@[Nt A'])}) \<union> ({A'} \<times> V) \<union> (\<Union>v\<in>V. {(A',v @ [Nt A'])}))"
proof -
  let ?RA = "Rhss R A"
  let ?Vc = "tl ` {w \<in> ?RA. w \<noteq> [] \<and> hd w = Nt A \<and> tl w \<noteq> []}"
  let ?Uc = "{u \<in> ?RA. u = [] \<or> hd u \<noteq> Nt A }"

  let ?V = "{v. (A,Nt A # v) \<in> R \<and> v \<noteq> []}"
  let ?U = "{u. (A,u) \<in> R \<and> \<not>(\<exists>v. u = Nt A # v) }"

  have 1: "?V = ?Vc" by (auto simp add: Rhss_def neq_Nil_conv image_def)
  moreover have 2: "?U = ?Uc" by (auto simp add: Rhss_def neq_Nil_conv)

  ultimately show ?thesis
    unfolding rrec_of_lrec_def Let_def by presburger
qed

text \<open>Solve left-recursions: Solves the left-recursion of Nt \<open>A\<close> by replacing it with a 
right-recursion on a fresh Nt \<open>A'\<close>. The fresh Nt \<open>A'\<close> is also given as a parameter.\<close>
definition solve_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"solve_lrec A A' R = rm_lrec A R \<union> rrec_of_lrec A A' R"

lemmas solve_lrec_defs = solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def

text \<open>Solve triangular: Put \<open>R\<close> into triangular form wrt \<open>As\<close> (using the new Nts \<open>As'\<close>).
In each step \<open>A#As\<close>, first the remaining Nts in \<open>As\<close> are solved, then \<open>A\<close> is solved.
This should mean that in the result of the outermost \<open>expand_hd A As\<close>, \<open>A\<close> only depends on \<open>A\<close>.
Then the \<open>A\<close> rules in the result of \<open>solve_lrec A A'\<close> are already in GNF. More precisely:
the result should be in \<open>triangular\<close> form.\<close>
fun solve_tri :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) Prods \<Rightarrow> ('a, 'b) Prods" where
"solve_tri [] _ R = R" |
"solve_tri (A#As) (A'#As') R = solve_lrec A A' (expand_hd A As (solve_tri As As' R))"

text \<open>Triangular form wrt \<open>[A1,\<dots>,An]\<close> means that \<open>Ai\<close> must not depend on \<open>Ai, \<dots>, An\<close>.
In particular: \<open>A0\<close> does not depend on any \<open>Ai\<close>, its rules are already in GNF.
Therefore one can convert a \<open>triangular\<close> form into GNF by backwards substitution:
The rules for \<open>Ai\<close> are used to expand the heads of all \<open>A(i+1),\<dots>,An\<close> rules,
starting with \<open>A0\<close>.\<close>
fun triangular :: "'n list \<Rightarrow> ('n \<times> ('n, 't) sym list) set \<Rightarrow> bool" where
"triangular [] R = True" |
"triangular (A#As) R = (dep_on R A \<inter> ({A} \<union> set As) = {} \<and> triangular As R)"

text \<open>Remove self loops: Removes all productions of the form \<open>A \<rightarrow> A\<close>.\<close>
definition rm_self_loops :: "('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
  "rm_self_loops P = P - {x\<in>P. \<exists>A. x = (A, [Nt A])}"

text \<open>Expand triangular: Expands all head-Nts of productions with a Lhs in \<open>As\<close> 
(\<open>triangular (rev As)\<close>). In each step \<open>A#As\<close> first all Nts in \<open>As\<close> are expanded, then every rule 
\<open>A \<rightarrow> B w\<close> is expanded if \<open>B \<in> set As\<close>. If the productions were in \<open>triangular\<close> form wrt \<open>rev As\<close> 
then \<open>Ai\<close> only depends on \<open>A(i+1), \<dots>, An\<close> which have already been expanded in the first part
of the step and are in GNF. Then the all \<open>A\<close>-productions are also is in GNF after expansion.\<close>
fun expand_tri :: "'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"expand_tri [] R = R" |
"expand_tri (A#As) R =
 (let R' = expand_tri As R;
      X = lrec_Prods R' A (set As);
      Y = subst_hd R' X A
  in R' - X \<union> Y)"

declare expand_tri.simps(1)[code]
lemma expand_tri_Cons_code[code]: "expand_tri (S#Ss) R =
 (let R' = expand_tri Ss R;
      X = {w \<in> Rhss R' S. w \<noteq> [] \<and> hd w \<in> Nt ` (set Ss)};
      Y = (\<Union>(B,v) \<in> R'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(S,v @ tl w)})
  in R' - ({S} \<times> X) \<union> Y)"
by(simp add: Let_def Rhss_def neq_Nil_conv Ball_def, safe, force+)

text \<open>The main function \<open>gnf_hd\<close> converts into \<open>GNF_hd\<close>:\<close>
definition gnf_hd :: "('n::fresh,'t)prods \<Rightarrow> ('n,'t)Prods" where
"gnf_hd ps =
  (let As = nts_prods_list ps;
       ps' = eps_elim ps;
       As' = freshs (set As) As
   in expand_tri (As' @ rev As) (solve_tri As As' (set ps')))"

section \<open>Some Basic Lemmas\<close>

subsection \<open>\<open>Eps_free\<close> preservation\<close>

lemma Eps_free_expand_hd: "Eps_free R \<Longrightarrow> Eps_free (expand_hd A Ss R)"
  by (induction A Ss R rule: expand_hd.induct)
    (auto simp add: Eps_free_def Let_def)

lemma Eps_free_solve_lrec: "Eps_free R \<Longrightarrow> Eps_free (solve_lrec A A' R)"
  unfolding solve_lrec_defs Eps_free_def by (auto)

lemma Eps_free_solve_tri: "Eps_free R \<Longrightarrow> length As \<le> length As' \<Longrightarrow> Eps_free (solve_tri As As' R)"
  by (induction As As' R rule: solve_tri.induct) 
    (auto simp add: Eps_free_solve_lrec Eps_free_expand_hd)

lemma Eps_free_expand_tri: "Eps_free R \<Longrightarrow> Eps_free (expand_tri As R)"
  by (induction As R rule: expand_tri.induct) (auto simp add: Let_def Eps_free_def)


subsection \<open>Lemmas about \<open>Nts\<close> and \<open>dep_on\<close>\<close>

lemma dep_on_Un[simp]: "dep_on (R \<union> S) A = dep_on R A \<union> dep_on S A"
  by(auto simp add: dep_on_def)

lemma expand_hd_preserves_neq: "B \<noteq> A \<Longrightarrow> (B,w) \<in> expand_hd A Ss R \<longleftrightarrow> (B,w) \<in> R"
  by(induction A Ss R rule: expand_hd.induct) (auto simp add: Let_def)

text \<open>Let \<open>R\<close> be epsilon-free and in \<open>triangular\<close> form wrt \<open>Bs\<close>.
After \<open>expand_hd A Bs R\<close>, \<open>A\<close> depends only on what \<open>A\<close> depended on before or
what one of the \<open>B \<in> Bs\<close> depends on, but \<open>A\<close> does not depend on the \<open>Bs\<close>:\<close>
lemma dep_on_expand_hd:
  "\<lbrakk> Eps_free R; triangular Bs R; distinct Bs; A \<notin> set Bs \<rbrakk>
  \<Longrightarrow> dep_on (expand_hd A Bs R) A \<subseteq> (dep_on R A \<union> (\<Union>B\<in>set Bs. dep_on R B)) - set Bs"
proof(induction A Bs R rule: expand_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A B Bs R)
  then show ?case
    by(fastforce simp add: Let_def dep_on_def Cons_eq_append_conv Eps_free_expand_hd Eps_free_Nil 
        expand_hd_preserves_neq set_eq_iff)
qed

lemma dep_on_subs_Nts: "dep_on R A \<subseteq> Nts R"
  by (auto simp add: Nts_def dep_on_def)

lemma Nts_expand_hd_sub: "Nts (expand_hd A As R) \<subseteq> Nts R"
proof (induction A As R rule: expand_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A S Ss R)
  let ?R' = "expand_hd A Ss R"
  let ?X = "{(Al, Bw). (Al, Bw) \<in> ?R' \<and> Al = A \<and> (\<exists>w. Bw = Nt S # w)}"
  let ?Y = "{(A, v @ w) |v w. (A, Nt S # w) \<in> ?R' \<and> (S, v) \<in> ?R'}"

  have lhs_sub: "Lhss ?Y \<subseteq> Lhss ?R'" by (auto simp add: Lhss_def)

  have "B \<notin> Rhs_Nts ?R' \<longrightarrow> B \<notin> Rhs_Nts ?Y" for B 
    by (fastforce simp add: Rhs_Nts_def split: prod.splits)
  then have "B \<in> Rhs_Nts ?Y \<longrightarrow> B \<in> Rhs_Nts ?R'" for B by blast
  then have rhs_sub: "Rhs_Nts ?Y \<subseteq> Rhs_Nts ?R'" by auto

  have "Nts ?Y \<subseteq> Nts ?R'" using lhs_sub rhs_sub by (auto simp add: Nts_Lhss_Rhs_Nts)
  then have "Nts ?Y \<subseteq> Nts R" using 2 by auto
  then show ?case using Nts_mono[of "?R' - ?X"] 2 by (auto simp add: Let_def Nts_Un)
qed
  
lemma Nts_solve_lrec_sub: "Nts (solve_lrec A A' R) \<subseteq> Nts R \<union> {A'}"
proof -
  have 1: "Nts (rm_lrec A R) \<subseteq> Nts R" 
    by (auto simp add: Nts_mono rm_lrec_def)

  have 2: "Lhss (rrec_of_lrec A A' R) \<subseteq> Lhss R \<union> {A'}" 
    by (auto simp add: rrec_of_lrec_def Let_def Lhss_def)
  have 3: "Rhs_Nts (rrec_of_lrec A A' R) \<subseteq> Rhs_Nts R \<union> {A'}" 
    by (auto simp add: rrec_of_lrec_def Let_def Rhs_Nts_def)

  have "Nts (rrec_of_lrec A A' R) \<subseteq> Nts R \<union> {A'}" using 2 3 by (auto simp add: Nts_Lhss_Rhs_Nts)
  then show ?thesis using 1 by (auto simp add: solve_lrec_def Nts_Un)
qed

lemma Nts_solve_tri_sub: "length As \<le> length As' \<Longrightarrow> Nts (solve_tri As As' R) \<subseteq> Nts R \<union> set As'"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  have "Nts (solve_tri (A # As) (A' # As') R) = 
        Nts (solve_lrec A A' (expand_hd A As (solve_tri As As' R)))" by simp
  also have "... \<subseteq> Nts (expand_hd A As (solve_tri As As' R)) \<union> {A'}"
    using Nts_solve_lrec_sub[of A A' "expand_hd A As (solve_tri As As' R)"] by simp
  also have "... \<subseteq> Nts (solve_tri As As' R) \<union> {A'}" 
    using Nts_expand_hd_sub[of A As "solve_tri As As' R"] by auto
  finally show ?case using 2 by auto
next
  case (3 v va c)
  then show ?case by simp
qed

subsection \<open>Lemmas about \<open>triangular\<close>\<close>

lemma tri_Snoc_impl_tri: "triangular (As @ [A]) R \<Longrightarrow> triangular As R"
proof(induction As R rule: triangular.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 A As R)
  then show ?case by simp
qed

text \<open>If two parts of the productions are \<open>triangular\<close> and no Nts from the first part depend on 
      ones of the second they are also \<open>triangular\<close> when put together.\<close>
lemma triangular_append: 
  "\<lbrakk>triangular As R; triangular Bs R; \<forall>A\<in>set As. dep_on R A \<inter> set Bs = {}\<rbrakk> 
   \<Longrightarrow> triangular (As@Bs) R"
  by (induction As) auto


section \<open>Function \<open>solve_tri\<close>: Remove Left-Recursion and Convert into Triangular Form\<close>

subsection \<open>Basic Lemmas\<close>

text \<open>Mostly about rule inclusions in \<open>solve_lrec\<close>.\<close>

lemma solve_lrec_rule_simp1: "A \<noteq> B \<Longrightarrow> A \<noteq> B' \<Longrightarrow> (A, w) \<in> solve_lrec B B' R \<longleftrightarrow> (A, w) \<in> R"
  unfolding solve_lrec_defs by (auto)

lemma solve_lrec_rule_simp3: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> Eps_free R 
  \<Longrightarrow> (A, [Nt A']) \<notin> solve_lrec A A' R"
  unfolding solve_lrec_defs by (auto simp: Eps_free_def)

lemma solve_lrec_rule_simp7: "A' \<noteq> A \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> (A', Nt A' # w) \<notin> solve_lrec A A' R"
unfolding solve_lrec_defs by(auto simp: neq_Nil_conv split: prod.splits)

lemma solve_lrec_rule_simp8: "A' \<notin> Nts R \<Longrightarrow> B \<noteq> A' \<Longrightarrow> B \<noteq> A 
  \<Longrightarrow> (B, Nt A' # w) \<notin> solve_lrec A A' R"
unfolding solve_lrec_defs by (auto split: prod.splits)

lemma dep_on_expand_hd_simp2: "B \<noteq> A \<Longrightarrow> dep_on (expand_hd A As R) B = dep_on R B"
  by (auto simp add: dep_on_def expand_hd_preserves_neq)

lemma dep_on_solve_lrec_simp2: "A \<noteq> B \<Longrightarrow> A' \<noteq> B \<Longrightarrow> dep_on (solve_lrec A A' R) B = dep_on R B"
unfolding solve_lrec_defs dep_on_def by (auto)


subsection \<open>Triangular Form\<close>

text
\<open>\<open>expand_hd\<close> preserves \<open>triangular\<close>, if it does not expand a Nt considered in \<open>triangular\<close>.\<close>
lemma triangular_expand_hd: "\<lbrakk>A \<notin> set As; triangular As R\<rbrakk> \<Longrightarrow> triangular As (expand_hd A Bs R)"
  by (induction As) (auto simp add: dep_on_expand_hd_simp2)

text \<open>Solving a Nt not considered by \<open>triangular\<close> preserves the \<open>triangular\<close> property.\<close>
lemma triangular_solve_lrec: "\<lbrakk>A \<notin> set As; A' \<notin> set As; triangular As R\<rbrakk> 
  \<Longrightarrow> triangular As (solve_lrec A A' R)"
proof(induction As)
  case Nil
  then show ?case by simp
next
  case (Cons a As)
  have "triangular (a # As) (solve_lrec A A' R) = 
    (dep_on (solve_lrec A A' R) a \<inter> ({a} \<union> set As) = {} \<and> triangular As (solve_lrec A A' R))"
    by simp
  also have "... = (dep_on (solve_lrec A A' R) a \<inter> ({a} \<union> set As) = {})" using Cons by auto
  also have "... = (dep_on R a \<inter> ({a} \<union> set As) = {})" using Cons dep_on_solve_lrec_simp2
    by (metis list.set_intros(1))
  then show ?case using Cons by auto
qed

text \<open>Solving more Nts does not remove the \<open>triangular\<close> property of previously solved Nts.\<close>
lemma part_triangular_induct_step: 
  "\<lbrakk>Eps_free R; distinct ((A#As)@(A'#As')); triangular As (solve_tri As As' R)\<rbrakk> 
  \<Longrightarrow> triangular As (solve_tri (A#As) (A'#As') R)"
  by (cases "As = []")
    (auto simp add: triangular_expand_hd triangular_solve_lrec)

text \<open>Couple of small lemmas about \<open>dep_on\<close> and the solving of left-recursion.\<close>
lemma rm_lrec_rem_own_dep: "A \<notin> dep_on (rm_lrec A R) A"
  by (auto simp add: dep_on_def rm_lrec_def)

lemma rrec_of_lrec_has_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (rrec_of_lrec A A' R) A"
  by (auto simp add: dep_on_def rrec_of_lrec_def Let_def Cons_eq_append_conv)

lemma solve_lrec_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (solve_lrec A A' R) A"
  by (auto simp add: solve_lrec_def rm_lrec_rem_own_dep rrec_of_lrec_has_no_own_dep)

lemma solve_lrec_no_new_own_dep: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> A' \<notin> dep_on (solve_lrec A A' R) A'"
  by (auto simp add: dep_on_def solve_lrec_rule_simp7)  
  
lemma dep_on_rem_lrec_simp: "dep_on (rm_lrec A R) A = dep_on R A - {A}"
  by (auto simp add: dep_on_def rm_lrec_def)

lemma dep_on_rrec_of_lrec_simp:
  "Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> dep_on (rrec_of_lrec A A' R) A = dep_on R A - {A}"
  using Eps_freeE_Cons[of R A "[]"]
  by (auto simp add: dep_on_def rrec_of_lrec_def Let_def Cons_eq_append_conv)

lemma dep_on_solve_lrec_simp: 
  "\<lbrakk>Eps_free R; A \<noteq> A'\<rbrakk> \<Longrightarrow> dep_on (solve_lrec A A' R) A = dep_on R A - {A}"
  by (simp add: dep_on_rem_lrec_simp dep_on_rrec_of_lrec_simp solve_lrec_def)

lemma dep_on_solve_tri_simp: "B \<notin> set As \<Longrightarrow> B \<notin> set As' \<Longrightarrow> length As \<le> length As' 
  \<Longrightarrow> dep_on (solve_tri As As' R) B = dep_on R B"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  have "dep_on (solve_tri (A#As) (A'#As') R) B = dep_on (expand_hd A As (solve_tri As As' R)) B" 
    using 2 by (auto simp add: dep_on_solve_lrec_simp2)
  then show ?case using 2 by (auto simp add: dep_on_expand_hd_simp2)
next
  case (3 v va c)
  then show ?case by simp
qed

text \<open>Induction step for showing that \<open>solve_tri\<close> removes dependencies of previously solved Nts.\<close>
lemma triangular_dep_on_induct_step: 
  assumes "Eps_free R" "length As \<le> length As'" "distinct ((A#As)@A'#As')" "triangular As (solve_tri As As' R)"
  shows "dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {}"
proof(cases "As = []")
  case True
  with assms solve_lrec_no_own_dep show ?thesis by fastforce
next
  case False
  have "Eps_free (solve_tri As As' R)"
    using assms Eps_free_solve_tri by auto
  then have test: "X \<in> set As \<Longrightarrow> X \<notin> dep_on (expand_hd A As (solve_tri As As' R)) A" for X
    using assms dep_on_expand_hd
    by (metis distinct.simps(2) distinct_append insert_Diff subset_Diff_insert)

  have A: "triangular As (solve_tri (A # As) (A' # As') R)" 
    using part_triangular_induct_step assms by metis

  have "dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) 
        = (dep_on (expand_hd A As (solve_tri As As' R)) A - {A}) \<inter> ({A} \<union> set  As)"
    using assms by (simp add: dep_on_solve_lrec_simp Eps_free_solve_tri Eps_free_expand_hd)
  also have "... = dep_on (expand_hd A As (solve_tri As As' R)) A \<inter> set As"
    using assms by auto
  also have "... = {}" using test by fastforce
  finally show ?thesis by auto
qed

theorem triangular_solve_tri:  "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As')\<rbrakk>
  \<Longrightarrow> triangular As (solve_tri As As' R)"
proof(induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  then have "length As \<le> length As' \<and> distinct (As @ As')" by auto
  then have A: "triangular As (solve_tri (A # As) (A' # As') R)" 
    using part_triangular_induct_step 2 "2.IH" by metis

  have "(dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {})"
    using triangular_dep_on_induct_step 2 
    by (metis \<open>length As \<le> length As' \<and> distinct (As @ As')\<close>) 
  then show ?case using A by simp
next
  case (3 v va c)
  then show ?case by simp
qed

lemma dep_on_solve_tri_Nts_R: 
  "\<lbrakk>Eps_free R; B \<in> set As; distinct (As @ As'); set As' \<inter> Nts R = {}; length As \<le> length As'\<rbrakk>
    \<Longrightarrow> dep_on (solve_tri As As' R) B \<subseteq> Nts R"
proof (induction As As' R arbitrary: B rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by (simp add: dep_on_subs_Nts)
next
  case (2 A As A' As' R)
  then have F1: "dep_on (solve_tri As As' R) B \<subseteq> Nts R"
    by (cases "B = A") (simp_all add: dep_on_solve_tri_simp dep_on_subs_Nts)
  then have F2: "dep_on (expand_hd A As (solve_tri As As' R)) B \<subseteq> Nts R"
  proof (cases "B = A")
    case True
    have "triangular As (solve_tri As As' R)" using 2 by (auto simp add: triangular_solve_tri)
    then have "dep_on (expand_hd A As (solve_tri As As' R)) B \<subseteq> dep_on (solve_tri As As' R) B 
       \<union> \<Union> (dep_on (solve_tri As As' R) ` set As) - set As"
      using 2 True by (auto simp add: dep_on_expand_hd Eps_free_solve_tri)
    also have "... \<subseteq> Nts R" using "2.IH" 2 F1 by auto
    finally show ?thesis.
  next
    case False
    then show ?thesis using F1 by (auto simp add: dep_on_expand_hd_simp2)
  qed
  then have "dep_on (solve_lrec A A' (expand_hd A As (solve_tri As As' R))) B \<subseteq> Nts R"
  proof (cases "B = A")
    case True
    then show ?thesis 
      using 2 F2 by (auto simp add: dep_on_solve_lrec_simp Eps_free_solve_tri Eps_free_expand_hd)
  next
    case False
    have "B \<noteq> A'" using 2 by auto
    then show ?thesis using 2 F2 False by (simp add: dep_on_solve_lrec_simp2)
  qed
  then show ?case by simp
next
  case (3 v va c)
  then show ?case by simp
qed

lemma triangular_unused_Nts: "set As \<inter> Nts R = {} \<Longrightarrow> triangular As R"
proof (induction As)
  case Nil
  then show ?case by auto
next
  case (Cons a As)
  have "dep_on R a \<subseteq> Nts R" by (simp add: dep_on_subs_Nts)
  then have "dep_on R a \<inter> (set As  \<union> {a}) = {}" using Cons by auto
  then show ?case using Cons by auto
qed

text \<open>The newly added Nts in \<open>solve_lrec\<close> are in \<open>triangular\<close> form wrt \<open>rev As'\<close>.\<close>
lemma triangular_rev_As'_solve_tri: 
  "\<lbrakk>set As' \<inter> Nts R = {}; distinct (As @ As'); length As \<le> length As'\<rbrakk> 
   \<Longrightarrow> triangular (rev As') (solve_tri As As' R)"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by (auto simp add: triangular_unused_Nts)
next
  case (2 A As A' As' R)
  then have "triangular (rev As') (solve_tri As As' R)" by simp
  then have "triangular (rev As') (expand_hd A As (solve_tri As As' R))"
    using 2 by (auto simp add: triangular_expand_hd)
  then have F1: "triangular (rev As') (solve_tri (A#As) (A'#As') R)"
    using 2 by (auto simp add: triangular_solve_lrec)
  have "Nts (solve_tri As As' R) \<subseteq> Nts R \<union> set As'" using 2 by (auto simp add: Nts_solve_tri_sub)
  then have F_nts: "Nts (expand_hd A As (solve_tri As As' R)) \<subseteq> Nts R \<union> set As'"
    using Nts_expand_hd_sub[of A As "(solve_tri As As' R)"] by auto
  then have "A' \<notin> dep_on (solve_lrec A A' (expand_hd A As (solve_tri As As' R))) A'" 
    using 2 solve_lrec_no_new_own_dep[of A A'] by auto
  then have F2: "triangular [A'] (solve_tri (A#As) (A'#As') R)" by auto
  have "\<forall>a\<in>set As'. dep_on (solve_tri (A#As) (A'#As') R) a \<inter> set [A'] = {}"
  proof
    fix a
    assume "a \<in> set As'"
    then have "A' \<notin> Nts (expand_hd A As (solve_tri As As' R)) \<and> a \<noteq> A" using F_nts 2 by auto
    then show "dep_on (solve_tri (A#As) (A'#As') R) a \<inter> set [A'] = {}" 
      using 2 solve_lrec_rule_simp8[of A' "(expand_hd A As (solve_tri As As' R))" a A] 
            solve_lrec_rule_simp7[of A'] 
      by (cases "a = A'") (auto simp add: dep_on_def)
  qed
    
  then have "triangular (rev (A'#As')) (solve_tri (A#As) (A'#As') R)" 
    using F1 F2 by (auto simp add: triangular_append)
  then show ?case by auto
next
  case (3 v va c)
  then show ?case by auto
qed

text \<open>The entire set of productions is in \<open>triangular\<close> form after \<open>solve_tri\<close> wrt \<open>As@(rev As')\<close>.\<close>
theorem triangular_As_As'_solve_tri:
  assumes "Eps_free R" "length As \<le> length As'" "distinct(As @ As')" "Nts R \<subseteq> set As" 
    shows "triangular (As@(rev As')) (solve_tri As As' R)"
proof -
  from assms have 1: "triangular As (solve_tri As As' R)" by (auto simp add: triangular_solve_tri)
  have "set As' \<inter> Nts R = {}" using assms by auto
  then have 2: "triangular (rev As') (solve_tri As As' R)" 
    using assms by (auto simp add: triangular_rev_As'_solve_tri)
  have "set As' \<inter> Nts R = {}" using assms by auto
  then have "\<forall>A\<in>set As. dep_on (solve_tri As As' R) A \<subseteq> Nts R" 
    using assms by (auto simp add: dep_on_solve_tri_Nts_R)
  then have "\<forall>A\<in>set As. dep_on (solve_tri As As' R) A \<inter> set As' = {}" using assms by auto
  then show ?thesis using 1 2 by (auto simp add: triangular_append)
qed


subsection \<open>\<open>solve_lrec\<close> Preserves Language\<close>

subsubsection \<open>@{prop "Lang (solve_lrec B B' R) A \<supseteq> Lang R A"}\<close>

text \<open>If there exists a derivation from \<open>u\<close> to \<open>v\<close> then there exists one which does not use
  productions of the form \<open>A \<rightarrow> A\<close>.\<close>
lemma rm_self_loops_derivels: assumes "P \<turnstile> u \<Rightarrow>l(n) v" shows "rm_self_loops P \<turnstile> u \<Rightarrow>l* v"
proof -
  have "rm_self_loops P = {p\<in>P. \<not>(\<exists>A. p = (A,[Nt A]))}" unfolding rm_self_loops_def by auto
  with no_self_loops_derivels[of n P u v] assms show ?thesis by simp
qed

text \<open>Restricted to productions with one lhs (\<open>A\<close>), and no \<open>A \<rightarrow> A\<close> productions
      if there is a derivation from \<open>u\<close> to \<open>A # v\<close> then \<open>u\<close> must start with Nt \<open>A\<close>.\<close>
lemma lrec_lemma1: 
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "rm_self_loops S \<turnstile> u \<Rightarrow>l(n) Nt A#v"
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
      then have "\<exists>w. (B, w) \<in> rm_self_loops S" using assms neg
        by (metis (no_types, lifting) derivels_Nt_Cons relpowp_imp_rtranclp)
      then obtain w where elem: "(B, w) \<in> rm_self_loops S" by blast
      have "(B, w) \<notin> rm_self_loops S" using B_not_A assms by (auto simp add: rm_self_loops_def)
      then show ?thesis using elem by simp
    qed
  qed
qed


text \<open>Restricted to productions with one lhs (\<open>A\<close>), and no \<open>A \<rightarrow> A\<close> productions
      if there is a derivation from \<open>u\<close> to \<open>A # v\<close> then \<open>u\<close> must start with Nt \<open>A\<close> and there 
      exists a prefix of \<open>A # v\<close> s.t. a left-derivation from \<open>[Nt A]\<close> to that prefix exists.\<close>
lemma  lrec_lemma2:
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "Eps_free R"
  shows "rm_self_loops S \<turnstile> u \<Rightarrow>l(n) Nt A#v \<Longrightarrow> 
    \<exists>u' v'. u = Nt A # u' \<and> v = v' @ u' \<and> (rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v'"
proof (induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "\<exists>u'. u = Nt A # u'" using lrec_lemma1[of S] Suc assms by auto
  then obtain u' where u'_prop: "u = Nt A # u'" by blast
  then have "\<exists>w. (A,w) \<in> (rm_self_loops S) \<and> (rm_self_loops S) \<turnstile> w @ u' \<Rightarrow>l(n) Nt A # v" 
    using Suc by (auto simp add: deriveln_Nt_Cons split: prod.split)
  then obtain w where w_prop: 
    "(A,w) \<in> (rm_self_loops S) \<and> (rm_self_loops S) \<turnstile> w @ u' \<Rightarrow>l(n) Nt A # v" 
    by blast
  then have "\<exists>u'' v''. w @ u' = Nt A # u'' \<and>  v = v'' @ u'' \<and> 
    (rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v''" 
    using Suc.IH Suc by auto
  then obtain u'' v'' where u''_prop: "w @ u' = Nt A # u'' \<and>  v = v'' @ u''" and
    ln_derive: "(rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v''"
    by blast
  have "w \<noteq> [] \<and> w \<noteq> [Nt A]" 
    using Suc w_prop assms by (auto simp add: Eps_free_Nil rm_self_loops_def split: prod.splits)
  then have "\<exists>u1. u1 \<noteq> [] \<and> w = Nt A # u1 \<and> u'' = u1 @ u'" 
    using u''_prop by (metis Cons_eq_append_conv)
  then obtain u1 where u1_prop: "u1 \<noteq> [] \<and> w = Nt A # u1 \<and> u'' = u1 @ u'" by blast
  then have 1: "u = Nt A # u' \<and> v = (v'' @ u1) @ u'" using u'_prop u''_prop by auto
  
  have 2: "(rm_self_loops S) \<turnstile> [Nt A] @ u1 \<Rightarrow>l(n) Nt A # v'' @ u1" 
    using ln_derive deriveln_append
    by fastforce
  have "(rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l [Nt A] @ u1" 
    using w_prop u''_prop u1_prop
    by (simp add: derivel_Nt_Cons)
  then have "(rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(Suc n) Nt A # v'' @ u1" 
    using ln_derive
    by (meson 2 relpowp_Suc_I2)
  then show ?case using 1 by blast
qed

text \<open>Restricted to productions with one lhs (\<open>A\<close>), and no \<open>A \<rightarrow> A\<close> productions
  if there is a left-derivation from \<open>[Nt A]\<close> to \<open>A # u\<close> then there exists a derivation
  from \<open>[Nt A']\<close> to \<open>u@[Nt A]\<close> and if \<open>u \<noteq> []\<close> also to \<open>u\<close> in \<open>solve_lrec A A' R\<close>.\<close>
lemma lrec_lemma3: 
  assumes "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}" "Eps_free R"
  shows "rm_self_loops S \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u
  \<Longrightarrow> solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(n) u @ [Nt A'] \<and> 
      (u \<noteq> [] \<longrightarrow> solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(n) u)"
proof(induction n arbitrary: u)
  case 0
  then show ?case by (simp)
next
  case (Suc n)
  then have "\<exists>w. (A,w) \<in> rm_self_loops S \<and> rm_self_loops S \<turnstile> w \<Rightarrow>l(n) Nt A # u"
    by (auto simp add: deriveln_Nt_Cons split: prod.splits)
  then obtain w where w_prop1: "(A,w) \<in> (rm_self_loops S) \<and> (rm_self_loops S) \<turnstile> w \<Rightarrow>l(n) Nt A#u"
    by blast
  then have "\<exists>w' u'. w = Nt A # w' \<and> u = u' @ w' \<and> (rm_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u'"
    using lrec_lemma2[of S] Suc assms by auto
  then obtain w' u' where w_prop2: "w = Nt A # w' \<and> u = u' @ w'" and
    ln_derive: "rm_self_loops S \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u'" by blast
  then have "w' \<noteq> []" using w_prop1 Suc by (auto simp add: rm_self_loops_def)
  have "(A, w) \<in> S" using Suc.prems(1) w_prop1 by (auto simp add: rm_self_loops_def)
  then have prod_in_solve_lrec: "(A', w' @ [Nt A']) \<in> solve_lrec A A' S"
    using w_prop2 \<open>w' \<noteq> []\<close> unfolding solve_lrec_defs by (auto)

  have 1: "solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(n) u' @ [Nt A']" using Suc.IH Suc ln_derive by auto
  then have 2: "solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(Suc n) u' @ w' @ [Nt A']"
    using prod_in_solve_lrec by (simp add: derive_prepend derive_singleton relpowp_Suc_I)

  have "(A', w') \<in> solve_lrec A A' S" using w_prop2 \<open>w' \<noteq> []\<close> \<open>(A, w) \<in> S\<close>
    unfolding solve_lrec_defs by (auto)
  then have "solve_lrec A A' S \<turnstile> [Nt A'] \<Rightarrow>(Suc n) u' @ w'" 
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

text \<open>Every derivation resulting in a word has a derivation in \<open>solve_lrec B B' R\<close>.\<close>
lemma tm_derive_impl_solve_lrec_derive:
  assumes "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R"
  shows "\<lbrakk> p \<noteq> []; R \<turnstile> p \<Rightarrow>(n) map Tm q\<rbrakk> \<Longrightarrow> solve_lrec B B' R \<turnstile> p \<Rightarrow>* map Tm q"
proof (induction n arbitrary: p q rule: nat_less_induct)
  case (1 n)
  then show ?case
  proof (cases "solve_lrec B B' R = R - {(B, [Nt B])}")
    case True
    have 2: "rm_self_loops R \<subseteq> R - {(B, [Nt B])}" by (auto simp add: rm_self_loops_def)
    have "rm_self_loops R \<turnstile> p \<Rightarrow>* map Tm q" 
      using rm_self_loops_derivels "1.prems"(2) deriveln_iff_deriven derivels_imp_derives 
      by blast
    then show ?thesis 
      using 2 by (simp add: True derives_mono)
  next
    case solve_lrec_not_R: False
    then show ?thesis
    proof (cases "nts_syms p = {}")
      case True
      then obtain pt where "p = map Tm pt" using nts_syms_empty_iff by blast
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
        by (metis False P nts_syms_map_Tm relpowp_0_E)
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
  
        have solve_lrec_subset: "solve_lrec B B' ?S \<subseteq> solve_lrec B B' R" 
          unfolding solve_lrec_defs by (auto)
  
        have "solve_lrec B B' ?S \<turnstile> [Nt B] \<Rightarrow>* w2"
          proof(cases "u = []")
            case True
            have "(B, w2') \<in> solve_lrec B B' ?S"
              using  w2'_props w2'_prod unfolding solve_lrec_defs by (auto)
            then show ?thesis
              by (simp add: True bu_prod derives_if_bu w2'_prod)
          next
            case False
            have solved_prod: "(B, w2' @ [Nt B']) \<in> solve_lrec B B' ?S"
              using w2'_props w2'_prod solve_lrec_not_R unfolding solve_lrec_defs by (auto)
            have "rm_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l* Nt B # u"
              using l_decomp rm_self_loops_derivels by auto
            then have "\<exists>ln. rm_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l(ln) Nt B # u"
              by (simp add: rtranclp_power)
            then obtain ln where "rm_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l(ln) Nt B # u" by blast
            then have "(solve_lrec B B' ?S) \<turnstile> [Nt B'] \<Rightarrow>(ln) u"
              using lrec_lemma3[of ?S B R ln u] assms False by auto
            then have rrec_derive: "(solve_lrec B B' ?S) \<turnstile> w2' @ [Nt B'] \<Rightarrow>(ln) w2' @ u"
              by (simp add: deriven_prepend)
            have "(solve_lrec B B' ?S) \<turnstile> [Nt B] \<Rightarrow> w2' @ [Nt B']"
              using solved_prod by (simp add: derive_singleton)
            then have "(solve_lrec B B' ?S) \<turnstile> [Nt B] \<Rightarrow>* w2' @ u"
              using rrec_derive by (simp add: converse_rtranclp_into_rtranclp relpowp_imp_rtranclp)
            then show ?thesis using w2'_prod by auto
          qed
          then have 2: "solve_lrec B B' R \<turnstile> [Nt B] \<Rightarrow>* w2"
            using solve_lrec_subset by (simp add: derives_mono)
  
        text \<open>From here on all the smaller derivations are concatenated after applying the IH.\<close>
        have fact2: "R \<turnstile> w2 \<Rightarrow>l(k) v1 \<and> Suc n1 = m2 + k + 1" using l_decomp by auto
        then have "k < n"
          using decomp by linarith
        then have 3: "solve_lrec B B' R \<turnstile> w2 \<Rightarrow>* v1" using "1.IH" v1_tms fact2
          by (metis deriveln_iff_deriven derives_from_empty relpowp_imp_rtranclp)
  
        have 4: "solve_lrec B B' R \<turnstile> [Nt B] \<Rightarrow>* v1" using 2 3
          by auto
  
        have "\<exists>v2t. v2 = map Tm v2t" using decomp append_eq_map_conv q2_tms by blast
        then obtain v2t where v2_tms: "v2 = map Tm v2t" by blast
        have "n2 < n" using decomp by auto
        then have 5: "solve_lrec B B' R \<turnstile> p2 \<Rightarrow>* v2" using "1.IH" decomp v2_tms
          by (metis derives_from_empty relpowp_imp_rtranclp)
  
        have "solve_lrec B B' R \<turnstile> Nt B # p2 \<Rightarrow>* q2" using 4 5 decomp
          by (metis append_Cons append_Nil derives_append_decomp)
        then show ?thesis
          by (simp add: P P1 True derives_prepend)
      next
        case C_not_B: False
        then have "\<exists>w. (C, w) \<in> R \<and> R \<turnstile> w @ p2 \<Rightarrow>l(m) q2"
          by (metis P1 derivel_Nt_Cons relpowp_Suc_D2 n_Suc)
        then obtain w where P2: "(C, w) \<in> R \<and> R \<turnstile> w @ p2 \<Rightarrow>l(m) q2" by blast
        then have rule_in_solve_lrec: "(C, w) \<in> (solve_lrec B B' R)" 
          using C_not_B by (auto simp add: solve_lrec_def rm_lrec_def)
        have derivem: "R \<turnstile> w @ p2 \<Rightarrow>(m) q2" using q2_tms P2 by (auto simp add: deriveln_iff_deriven)
        have "w @ p2 \<noteq> []"
          using assms(1) Eps_free_Nil P2 by fastforce
        then have "(solve_lrec B B' R) \<turnstile> w @ p2 \<Rightarrow>* q2" using "1.IH" q2_tms n_Suc derivem
          by auto
        then have "(solve_lrec B B' R) \<turnstile> Nt C # p2 \<Rightarrow>* q2" 
          using rule_in_solve_lrec by (auto simp add: derives_Cons_rule)
        then show ?thesis
          by (simp add: P P1 derives_prepend)
      qed
    qed
  qed
qed

corollary Lang_incl_Lang_solve_lrec: 
  "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> Lang R A \<subseteq> Lang (solve_lrec B B' R) A"
by(auto simp: Lang_def intro: tm_derive_impl_solve_lrec_derive dest: rtranclp_imp_relpowp)


subsubsection \<open>\<^prop>\<open>Lang (solve_lrec B B' R) A \<subseteq> Lang R A\<close>\<close>

text \<open>Restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>)
      if there is a right-derivation from \<open>u\<close> to \<open>v @ [Nt A']\<close> then u ends in Nt \<open>A'\<close>.\<close>
lemma rrec_lemma1: 
  assumes "S = {x. \<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R}" "S \<turnstile> u \<Rightarrow>r(n) v @ [Nt A']"
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

text \<open>\<open>solve_lrec\<close> does not add productions of the form \<open>A' \<rightarrow> Nt A'\<close>.\<close>
lemma solve_lrec_no_self_loop: "Eps_free R \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> (A', [Nt A']) \<notin> solve_lrec A A' R"
unfolding solve_lrec_defs by (auto)

text \<open>Restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>) if there is a 
      right-derivation from \<open>u\<close> to \<open>v @ [Nt A']\<close> then u ends in Nt \<open>A'\<close> and there exists a suffix 
      of \<open>v @ [Nt A']\<close> s.t. there is a right-derivation from \<open>[Nt A']\<close> to that suffix.\<close>
lemma rrec_lemma2:
assumes "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)}" "Eps_free R" "A' \<notin> Nts R"
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
    using Suc.IH assms w_prop solve_lrec_no_self_loop by fastforce
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
      if there is a restricted right-derivation in \<open>solve_lrec\<close> from \<open>[Nt A']\<close> to \<open>u @ [Nt A']\<close> 
      then there exists a derivation in \<open>R\<close> from \<open>[Nt A]\<close> to \<open>A # u\<close>.\<close>
lemma rrec_lemma3: 
  assumes "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)}" "Eps_free R"
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

  have "(A', u' @ [Nt A']) \<in> solve_lrec A A' R \<longrightarrow> (A, Nt A # u') \<in> R"
    using assms unfolding solve_lrec_defs by (auto)
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
  assumes "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)}" "Eps_free R"
    "A \<noteq> A'" "A' \<notin> Nts R"
  shows "\<lbrakk>A' \<notin> nts_syms p; last q \<noteq> Nt A'; solve_lrec A A' R \<turnstile> p @ [Nt A'] \<Rightarrow>r(n) q\<rbrakk>
  \<Longrightarrow> \<exists>u w m k. S \<turnstile> p @ [Nt A'] \<Rightarrow>r(m) u @ [Nt A'] 
       \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w \<and> A' \<notin> nts_syms w 
       \<and> solve_lrec A A' R \<turnstile> w \<Rightarrow>r(k) q \<and> n = m + k + 1"
proof (induction n arbitrary: p)
  case 0
  then have pq_not_Nil: "p @ [Nt A'] \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil
    by auto

  have "p = q" using 0 by auto
  then show ?case using pq_not_Nil 0 by auto
next
  case (Suc n)
  have pq_not_Nil: "p @ [Nt A'] \<noteq> [] \<and> q \<noteq> []"
    using assms Suc.prems Eps_free_deriven_Nil Eps_free_solve_lrec derivern_imp_deriven
    by (metis (no_types, lifting) snoc_eq_iff_butlast)

  have "\<nexists>q'. q = q' @ [Nt A']" using pq_not_Nil Suc.prems
    by fastforce

  then have "\<exists>w. (A',w) \<in> (solve_lrec A A' R) \<and> (solve_lrec A A' R) \<turnstile> p @ w \<Rightarrow>r(n) q"
    using Suc.prems by (auto simp add: derivern_snoc_Nt)
  then obtain w where w_prop: "(A',w) \<in> (solve_lrec A A' R) \<and> solve_lrec A A' R \<turnstile> p @ w \<Rightarrow>r(n) q"
    by blast

  show ?case
  proof (cases "(A', w) \<in> S")
    case True
    then have "\<exists>w'. w = w' @ [Nt A']"
      by (simp add: assms(1))
    then obtain w' where w_decomp: "w = w' @ [Nt A']" by blast
    then have "A' \<notin> nts_syms (p @ w')" using assms Suc.prems True
      unfolding solve_lrec_defs by (auto split: if_splits)
    then have "\<exists>u w'' m k. S \<turnstile> p @ w \<Rightarrow>r(m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' 
       \<and> A' \<notin> nts_syms w'' \<and> solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> n = m + k + 1"
      using Suc.IH Suc.prems w_prop w_decomp by (metis (lifting) append_assoc)
    then obtain u w'' m k where propo: 
      "S \<turnstile> p @ w \<Rightarrow>r(m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' \<and> A' \<notin> nts_syms w'' 
       \<and> solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> n = m + k + 1" 
      by blast
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(Suc m) u @ [Nt A']" using True
      by (meson deriver_snoc_Nt relpowp_Suc_I2)
  
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(Suc m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w''
       \<and> A' \<notin> nts_syms w'' \<and> solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> Suc n = Suc m + k + 1"
      using propo by auto
    then show ?thesis by blast
  next
    case False
    then have "last w \<noteq> Nt A'" using assms
      by (metis (mono_tags, lifting) Eps_freeE_Cons Eps_free_solve_lrec
          append_butlast_last_id list.distinct(1) mem_Collect_eq w_prop)
    then have "A' \<notin> nts_syms w" using assms w_prop
      unfolding solve_lrec_defs by (auto split: if_splits)
    then have "w \<noteq> [] \<and> A' \<notin> nts_syms w" using assms w_prop False
      by (metis (mono_tags, lifting) Eps_free_Nil Eps_free_solve_lrec)
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(0) p @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> p @ [Nt A'] \<Rightarrow>r p @ w 
       \<and> A' \<notin> nts_syms (p @ w) \<and> solve_lrec A A' R \<turnstile> p @ w \<Rightarrow>r(n) q \<and> Suc n = 0 + n + 1"
      using w_prop Suc.prems by (auto simp add: deriver_snoc_Nt)
    then show ?thesis by blast
  qed
qed

text \<open>Every word derived by \<open>solve_lrec B B' R\<close> can be derived by \<open>R\<close>.\<close>
lemma tm_solve_lrec_derive_impl_derive:
  assumes "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R"
  shows "\<lbrakk> p \<noteq> []; B' \<notin> nts_syms p; (solve_lrec B B' R) \<turnstile> p \<Rightarrow>(n) map Tm q\<rbrakk> \<Longrightarrow> R \<turnstile> p \<Rightarrow>* map Tm q"
proof (induction arbitrary: p q rule: nat_less_induct)
  case (1 n)
  let ?R' = "(solve_lrec B B' R)"
  show ?case
  proof (cases "nts_syms p = {}")
    case True
    then show ?thesis
      using "1.prems"(3) deriven_from_TmsD derives_from_Tms_iff
      by (metis nts_syms_empty_iff)
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

    have "B' \<notin> nts_syms p2 \<and> k < n" using P "1.prems" p_decomp by auto
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
        let ?S = "{x. (\<exists>v. x = (B', v @ [Nt B']) \<and> x \<in> solve_lrec B B' R)}"

        have "\<exists>w1. w = w1 @ [Nt B']" using True
          by (metis assms(1) Eps_free_Nil Eps_free_solve_lrec P append_butlast_last_id)
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
        have pre2: "w1 \<noteq> []" using w_decomp C_is_B P assms by (auto simp add: solve_lrec_rule_simp3)
        have Bw1_in_R: "(B, w1) \<in> R"
          using w_decomp P C_is_B assms
          unfolding solve_lrec_defs by (auto split: if_splits)

        then have pre3: "B' \<notin> nts_syms w1" using assms by (auto simp add: Nts_def)

        have "R \<turnstile> w1 \<Rightarrow>* map Tm w1t" using pre1 pre2 pre3 w_derive_decomp "1.IH" tms by blast
        then have w1'_derive: "R \<turnstile> [Nt B] \<Rightarrow>* w1'" using Bw1_in_R tms
          by (simp add: derives_Cons_rule)

        have "last [Nt B'] = Nt B' \<and> last (map Tm bt) \<noteq> Nt B'" 
          by (metis assms(1) Eps_free_deriven_Nil Eps_free_solve_lrec last_ConsL last_map
              list.map_disc_iff not_Cons_self2 sym.distinct(1) tms w_derive_decomp)
        then have "\<exists>u v m2 k2. ?S \<turnstile> [Nt B'] \<Rightarrow>r(m2) u @ [Nt B'] \<and> ?R' \<turnstile> u @ [Nt B'] \<Rightarrow>r v 
           \<and> B' \<notin> nts_syms v \<and> ?R' \<turnstile> v \<Rightarrow>r(k2) map Tm bt \<and> m1 = m2 + k2 + 1"
          using rrec_decomp[of ?S B' B R "[]" "map Tm bt" m1] w_derive_decomp assms "1.prems" tms
          by (simp add: derivern_iff_deriven)
        then obtain u v m2 k2 
          where rec_decomp: "?S \<turnstile> [Nt B'] \<Rightarrow>r(m2) u @ [Nt B'] \<and> ?R' \<turnstile> u @ [Nt B'] \<Rightarrow>r v 
           \<and> B' \<notin> nts_syms v \<and> ?R' \<turnstile> v \<Rightarrow>r(k2) map Tm bt \<and> m1 = m2 + k2 + 1"
          by blast
        then have Bu_derive: "R \<turnstile> [Nt B] \<Rightarrow>(m2) Nt B # u"
          using assms rrec_lemma3 by fastforce

        have "\<exists>v'. (B', v') \<in> ?R' \<and> v = u @ v'" using rec_decomp
          by (simp add: deriver_snoc_Nt)
        then obtain v' where v_decomp: "(B', v') \<in> ?R' \<and> v = u @ v'" by blast
        then have "(B, Nt B # v') \<in> R"
          using assms rec_decomp unfolding solve_lrec_defs by (auto split: if_splits)
        then have "R \<turnstile> [Nt B] \<Rightarrow> Nt B # v'"
          by (simp add: derive_singleton)
        then have "R \<turnstile> [Nt B] @ v' \<Rightarrow>* Nt B # u @ v'"
          by (metis Bu_derive append_Cons derives_append rtranclp_power)
        then have Buv'_derive: "R \<turnstile> [Nt B] \<Rightarrow>* Nt B # u @ v'"
          using \<open>R \<turnstile> [Nt B] \<Rightarrow> Nt B # v'\<close> by force

        have pre2: "k2 < n" using rec_decomp pre1 by auto
        have "v \<noteq> []" using rec_decomp
          by (metis (lifting) assms(1) Eps_free_deriven_Nil Eps_free_solve_lrec tms
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
          by (meson Eps_free_Nil Eps_free_solve_lrec)
        then have 2: "(C, w) \<in> R" 
          using P False "1.prems" p_decomp C_is_B
          unfolding solve_lrec_defs by (auto split: if_splits)

        then have pre3: "B' \<notin> nts_syms w" using P assms(3) by (auto simp add: Nts_def)

        have "R \<turnstile> w \<Rightarrow>* map Tm At" using "1.IH" assms pre1 pre2 pre3 P by blast
        then show ?thesis using 2
          by (meson bu_prod derives_bu_iff rtranclp_trans)
      qed
    next
      case False
      then have 2: "(C, w) \<in> R" 
        using P "1.prems"(2) p_decomp
        by (auto simp add: solve_lrec_rule_simp1)
      then have pre2: "B' \<notin> nts_syms w" using P assms(3) by (auto simp add: Nts_def)
      have pre3: "w \<noteq> []" using assms(1) 2 by (auto simp add: Eps_free_def)

      have "R \<turnstile> w \<Rightarrow>* map Tm At" using "1.IH" pre1 pre2 pre3 P by blast
      then show ?thesis using 2
        by (meson bu_prod derives_bu_iff rtranclp_trans)
    qed

    then show ?thesis using p2_derive
      by (metis P derives_append derives_append_decomp map_append p_decomp)
  qed
qed

corollary Lang_solve_lrec_incl_Lang:
  assumes "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R" "A \<noteq> B'"
  shows "Lang (solve_lrec B B' R) A \<subseteq> Lang R A"
proof
  fix w
  assume "w \<in> Lang (solve_lrec B B' R) A"
  then have "solve_lrec B B' R \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by (simp add: Lang_def)
  then have "\<exists>n. solve_lrec B B' R \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w"
    by (simp add: rtranclp_power)
  then obtain n where "(solve_lrec B B' R) \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w" by blast
  then have "R \<turnstile> [Nt A] \<Rightarrow>* map Tm w" using tm_solve_lrec_derive_impl_derive[of R] assms by auto
  then show "w \<in> Lang R A" by (simp add: Lang_def)
qed

corollary solve_lrec_Lang: 
  "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R; A \<noteq> B'\<rbrakk> \<Longrightarrow> Lang (solve_lrec B B' R) A = Lang R A"
  using Lang_solve_lrec_incl_Lang Lang_incl_Lang_solve_lrec by fastforce


subsection \<open>\<open>expand_hd\<close> Preserves Language\<close>

text \<open>Every rhs of an \<open>expand_hd R\<close> production is derivable by \<open>R\<close>.\<close>
lemma expand_hd_is_deriveable: "(A, w) \<in> expand_hd B As R \<Longrightarrow> R \<turnstile> [Nt A] \<Rightarrow>* w"
proof (induction B As R arbitrary: A w rule: expand_hd.induct)
  case (1 B R)
  then show ?case
    by (simp add: bu_prod derives_if_bu)
next
  case (2 B S Ss R)
  then show ?case
  proof (cases "B = A")
    case True
    then have Aw_or_ACv: "(A, w) \<in> expand_hd A Ss R \<or> (\<exists>C v. (A, Nt C # v) \<in> expand_hd A Ss R)"
      using 2 by (auto simp add: Let_def)
    then show ?thesis
    proof (cases "(A, w) \<in> expand_hd A Ss R")
      case True
      then show ?thesis using 2 True by (auto simp add: Let_def)
    next
      case False
      then have "\<exists> v wv. w = v @ wv \<and> (A, Nt S#wv) \<in> expand_hd A Ss R \<and> (S, v) \<in> expand_hd A Ss R"
        using 2 True by (auto simp add: Let_def)
      then obtain v wv 
        where P: "w = v @ wv \<and> (A, Nt S # wv) \<in> expand_hd A Ss R \<and> (S, v) \<in> expand_hd A Ss R"
        by blast
      then have tr: "R \<turnstile> [Nt A] \<Rightarrow>* [Nt S] @ wv" using 2 True by simp
      have "R \<turnstile> [Nt S] \<Rightarrow>* v" using 2 True P by simp
      then show ?thesis using P tr derives_append
        by (metis rtranclp_trans)
    qed
  next
    case False
    then show ?thesis using 2 by (auto simp add: Let_def)
  qed
qed


lemma expand_hd_incl1: "Lang (expand_hd B As R) A \<subseteq> Lang R A"
by (meson DersD DersI Lang_subset_if_Ders_subset derives_simul_rules expand_hd_is_deriveable subsetI)

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
  have "(N, ts) \<in> ?S' \<Longrightarrow> \<exists>B. B \<in> nts_syms ts" for N ts by fastforce
  then have terminal_prods_stay: "(N, ts) \<in> R \<Longrightarrow> nts_syms ts = {} \<Longrightarrow> (N, ts) \<in> ?subst" for N ts
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

lemma expand_hd_incl2: "Lang (expand_hd B As R) A \<supseteq> Lang R A"
proof (induction B As R rule: expand_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 C H Ss R)
  let ?R' = "expand_hd C Ss R"
  let ?X = "{(Al,Bw) \<in> ?R'. Al=C \<and> (\<exists>w. Bw = Nt H # w)}"
  let ?Y = "{(C,v@w) |v w. \<exists>B. (C,Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
  have "expand_hd C (H # Ss) R = ?R' - ?X \<union> ?Y" by (simp add: Let_def)

  let ?S = "{x. \<exists>A w. x = (A, [], H, w) \<and> (A, Nt H # w) \<in> ?X}"
  let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
  let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> ?R'}"

  have S'_eq_X: "?S' = ?X" by fastforce
  have E_eq_Y: "?E = ?Y" by fastforce

  have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> ?R'" by fastforce
  then have Lang_sub: "Lang ?R' A \<subseteq> Lang (?R' - ?S' \<union> ?E) A"
    using exp_includes_Lang[of ?S] by auto

  have "Lang R A \<subseteq> Lang ?R' A" using 2 by simp
  also have "... \<subseteq> Lang (?R' - ?S' \<union> ?E) A" using Lang_sub by simp
  also have "... \<subseteq> Lang (?R' - ?X \<union> ?Y) A" using S'_eq_X E_eq_Y by simp
  finally show ?case by (simp add: Let_def)
qed

theorem expand_hd_Lang: "Lang (expand_hd B As R) A = Lang R A"
  using expand_hd_incl1[of B As R A] expand_hd_incl2[of R A B As] by auto

subsection \<open>\<open>solve_tri\<close> Preserves Language\<close>
    
lemma solve_tri_Lang: 
  "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); Nts R \<inter> set As' = {}; A \<notin> set As'\<rbrakk>
   \<Longrightarrow> Lang (solve_tri As As' R) A = Lang R A"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 Aa As A' As' R)
  then have e_free1: "Eps_free (expand_hd Aa As (solve_tri As As' R))"
    by (simp add: Eps_free_expand_hd Eps_free_solve_tri)
  have "length As \<le> length As'" using 2 by simp
  then have "Nts (expand_hd Aa As (solve_tri As As' R)) \<subseteq> Nts R \<union> set As'"
    using 2 Nts_expand_hd_sub Nts_solve_tri_sub
    by (metis subset_trans)
  then have nts1: " A' \<notin> Nts (expand_hd Aa As (solve_tri As As' R))"
    using 2 Nts_expand_hd_sub Nts_solve_tri_sub by auto
  
  have "Lang (solve_tri (Aa # As) (A' # As') R) A 
        = Lang (solve_lrec Aa A' (expand_hd Aa As (solve_tri As As' R))) A"
    by simp
  also have "... = Lang (expand_hd Aa As (solve_tri As As' R)) A"
    using nts1 e_free1 2 solve_lrec_Lang[of "expand_hd Aa As (solve_tri As As' R)" Aa A' A]
    by (simp)
  also have "... = Lang (solve_tri As As' R) A" by (simp add: expand_hd_Lang)
  finally show ?case using 2 by (auto)
next
  case (3 v va c)
  then show ?case by simp
qed


section \<open>Function \<open>expand_hd\<close>: Convert Triangular Form into GNF\<close>
  
subsection \<open>\<open>expand_hd\<close>: Result is in \<open>GNF_hd\<close>\<close>
  
lemma dep_on_helper: "dep_on R A = {} \<Longrightarrow> (A, w) \<in> R \<Longrightarrow> w = [] \<or> (\<exists>T wt. w = Tm T # wt)"
  using neq_Nil_conv[of w] by (simp add: dep_on_def) (metis sym.exhaust)

lemma GNF_hd_iff_dep_on:
  assumes "Eps_free R"
  shows "GNF_hd R \<longleftrightarrow> (\<forall>A \<in> Nts R. dep_on R A = {})" (is "?L=?R")
proof
  assume ?L
  then show ?R by (auto simp add: GNF_hd_def dep_on_def)
next
  assume assm: ?R
  have 1: "\<forall>(B, w) \<in> R. \<exists>T wt. w = Tm T # wt \<or> w = []"
  proof
    fix x
    assume "x \<in> R"
    then have "case x of (B, w) \<Rightarrow> dep_on R B = {}" using assm by (auto simp add: Nts_def)
    then show "case x of (B, w) \<Rightarrow> \<exists>T wt. w = Tm T # wt \<or> w = []"
      using \<open>x \<in> R\<close> dep_on_helper by fastforce
  qed
  have 2: "\<forall>(B, w) \<in> R. w \<noteq> []" using assms assm by (auto simp add: Eps_free_def)
  have "\<forall>(B, w) \<in> R. \<exists>T wt. w = Tm T # wt" using 1 2 by auto
  then show "GNF_hd R" by (auto simp add: GNF_hd_def)
qed

lemma helper_expand_tri1: "A \<notin> set As \<Longrightarrow> (A, w) \<in> expand_tri As R \<Longrightarrow> (A, w) \<in> R"
  by (induction As R rule: expand_tri.induct) (auto simp add: Let_def)

text \<open>If none of the expanded Nts depend on \<open>A\<close> then any rule depending on \<open>A\<close> in \<open>expand_tri As R\<close>
      must already have been in \<open>R\<close>.\<close>
lemma helper_expand_tri2: 
  "\<lbrakk>Eps_free R; A \<notin> set As; \<forall>C \<in> set As. A \<notin> (dep_on R C); B \<noteq> A; (B, Nt A # w) \<in> expand_tri As R\<rbrakk>
    \<Longrightarrow> (B, Nt A # w) \<in> R"
proof (induction As R arbitrary: B w rule: expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  have "(B, Nt A # w) \<in> expand_tri Ss R"
  proof (cases "B = S")
    case B_is_S: True
    let ?R' = "expand_tri Ss R"
    let ?X = "{(Al,Bw) \<in> ?R'. Al=S \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set (Ss))}"
    let ?Y = "{(S,v@w) |v w. \<exists>B. (S, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
    have "(B, Nt A # w) \<notin> ?X" using 2 by auto
    then have 3: "(B, Nt A # w) \<in> ?R' \<or> (B, Nt A # w) \<in> ?Y" using 2 by (auto simp add: Let_def)
    then show ?thesis
    proof (cases "(B, Nt A # w) \<in> ?R'")
      case True
      then show ?thesis by simp
    next
      case False
      then have "(B, Nt A # w) \<in> ?Y" using 3 by simp
      then have "\<exists>v wa Ba. Nt A # w = v @ wa \<and> (S, Nt Ba # wa) \<in> expand_tri Ss R \<and> Ba \<in> set Ss 
         \<and> (Ba, v) \<in> expand_tri Ss R"
        by (auto simp add: Let_def)
      then obtain v wa Ba 
        where P: "Nt A # w = v @ wa \<and> (S, Nt Ba # wa) \<in> expand_tri Ss R \<and> Ba \<in> set Ss 
                  \<and> (Ba, v) \<in> expand_tri Ss R" 
        by blast
      have "Eps_free (expand_tri Ss R)" using 2 by (auto simp add: Eps_free_expand_tri)
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
    then show ?thesis using 2 by (auto simp add: Let_def)
  qed

  then show ?case using 2 by auto
qed 

text \<open>In a triangular form no Nts depend on the last Nt in the list.\<close>
lemma triangular_snoc_dep_on: "triangular (As@[A]) R \<Longrightarrow> \<forall>C \<in> set As. A \<notin> (dep_on R C)"
  by (induction As) auto

lemma triangular_helper1: "triangular As R \<Longrightarrow> A \<in> set As \<Longrightarrow> A \<notin> dep_on R A"
  by (induction As) auto

lemma dep_on_expand_tri: 
  "\<lbrakk>Eps_free R; triangular (rev As) R; distinct As; A \<in> set As\<rbrakk> 
   \<Longrightarrow> dep_on (expand_tri As R) A \<inter> set As = {}"
proof(induction As R arbitrary: A rule: expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  then have Eps_free_exp_Ss: "Eps_free (expand_tri Ss R)"
    by (simp add: Eps_free_expand_tri)
  have dep_on_fact: "\<forall>C \<in> set Ss. S \<notin> (dep_on R C)" 
    using 2 by (auto simp add: triangular_snoc_dep_on)
  then show ?case
  proof (cases "A = S")
    case True
    have F1: "(S, Nt S # w) \<notin> expand_tri Ss R" for w
    proof(rule ccontr)
      assume "\<not>((S, Nt S # w) \<notin> expand_tri Ss R)"
      then have "(S, Nt S # w) \<in> R" using 2 by (auto simp add: helper_expand_tri1)
      then have N: "S \<in> dep_on R A" using True by (auto simp add: dep_on_def)
      have "S \<notin> dep_on R A" using 2 True by (auto simp add: triangular_helper1)
      then show "False" using N by simp
    qed

    have F2: "(S, Nt S # w) \<notin> expand_tri (S#Ss) R" for w
    proof
      assume "(S, Nt S # w) \<in> expand_tri (S#Ss) R"
      then have "\<exists>v wa B. Nt S # w = v @ wa \<and> B \<in> set Ss \<and> (S, Nt B # wa) \<in> expand_tri Ss R 
         \<and> (B, v) \<in> expand_tri Ss R"
        using 2 F1 by (auto simp add: Let_def)
      then obtain v wa B 
        where v_wa_B_P: "Nt S # w = v @ wa \<and> B \<in> set Ss \<and> (S, Nt B # wa) \<in> expand_tri Ss R 
         \<and> (B, v) \<in> expand_tri Ss R" 
        by blast
      then have "v \<noteq> [] \<and> (\<exists>va. v = Nt S # va)" using Eps_free_exp_Ss
        by (metis Eps_free_Nil append_eq_Cons_conv)
      then obtain va where vP: "v \<noteq> [] \<and> v = Nt S # va" by blast
      then have "(B, v) \<in> R" 
        using v_wa_B_P 2 dep_on_fact helper_expand_tri2[of R S Ss B] True by auto
      then have "S \<in> dep_on R B" using vP by (auto simp add: dep_on_def)
      then show "False" using dep_on_fact v_wa_B_P by auto
    qed

    have "(S, Nt x # w) \<notin> expand_tri (S#Ss) R" if asm: "x \<in> set Ss" for x w
    proof
      assume assm: "(S, Nt x # w) \<in> expand_tri (S # Ss) R"
      then have "\<exists>v wa B. Nt x # w = v @ wa \<and> (S, Nt B # wa) \<in> expand_tri Ss R \<and> B \<in> set Ss 
         \<and> (B, v) \<in> expand_tri Ss R"
        using 2 asm by (auto simp add: Let_def)
      then obtain v wa B 
        where v_wa_B_P:"Nt x # w = v @ wa \<and> (S, Nt B # wa) \<in> expand_tri Ss R \<and> B \<in> set Ss 
         \<and> (B, v) \<in> expand_tri Ss R" 
        by blast
      then have dep_on_IH: "dep_on (expand_tri Ss R) B \<inter> set Ss = {}" 
        using 2 by (auto simp add: tri_Snoc_impl_tri)
      have "v \<noteq> [] \<and> (\<exists>va. v = Nt x # va)" using Eps_free_exp_Ss v_wa_B_P
        by (metis Eps_free_Nil append_eq_Cons_conv)
      then obtain va where vP: "v \<noteq> [] \<and> v = Nt x # va" by blast
      then have "x \<in> dep_on (expand_tri Ss R) B" using v_wa_B_P by (auto simp add: dep_on_def)
      then show "False" using dep_on_IH v_wa_B_P asm assm by auto
    qed

    then show ?thesis using 2 True F2 by (auto simp add: Let_def dep_on_def)
  next
    case False
    have "(A, Nt S # w) \<notin> expand_tri Ss R" for w
    proof
      assume "(A, Nt S # w) \<in> expand_tri Ss R"
      then have "(A, Nt S # w) \<in> R" using 2 helper_expand_tri2 dep_on_fact
        by (metis False distinct.simps(2))
      then have F: "S \<in> dep_on R A" by (auto simp add: dep_on_def)
      have "S \<notin> dep_on R A" using dep_on_fact False 2 by auto
      then show "False" using F by simp
    qed
    then show ?thesis using 2 False by (auto simp add: tri_Snoc_impl_tri Let_def dep_on_def)
  qed
qed

text \<open>Interlude: \<open>Nts\<close> of \<open>expand_tri\<close>:\<close>

lemma Lhss_expand_tri: "Lhss (expand_tri As R) \<subseteq> Lhss R"
  by (induction As R rule: expand_tri.induct) (auto simp add: Lhss_def Let_def)

lemma Rhs_Nts_expand_tri: "Rhs_Nts (expand_tri As R) \<subseteq> Rhs_Nts R"
proof (induction As R rule: expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  let ?X = "{(Al, Bw). (Al, Bw) \<in> expand_tri Ss R \<and> Al = S \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set Ss)}"
  let ?Y = "{(S,v@w)|v w. \<exists>B. (S,Nt B#w) \<in> expand_tri Ss R \<and> B \<in> set Ss \<and> (B,v) \<in> expand_tri Ss R}"
  have F1: "Rhs_Nts ?X \<subseteq> Rhs_Nts R" using 2 by (auto simp add: Rhs_Nts_def)
  have "Rhs_Nts ?Y \<subseteq> Rhs_Nts R"
  proof
    fix x
    assume "x \<in> Rhs_Nts ?Y"
    then have "\<exists>y ys. (y, ys) \<in> ?Y \<and> x \<in> nts_syms ys" by (auto simp add: Rhs_Nts_def)
    then obtain y ys where P1: "(y, ys) \<in> ?Y \<and> x \<in> nts_syms ys" by blast
    then show "x \<in> Rhs_Nts R" using P1 2 Rhs_Nts_def by fastforce
  qed
  then show ?case using F1 2 by (auto simp add: Rhs_Nts_def Let_def)
qed 

lemma Nts_expand_tri: "Nts (expand_tri As R) \<subseteq> Nts R"
  by (metis Lhss_expand_tri Nts_Lhss_Rhs_Nts Rhs_Nts_expand_tri Un_mono)

text \<open>If the entire \<open>triangular\<close> form is expanded, the result is in GNF:\<close>
theorem GNF_hd_expand_tri: 
  assumes "Eps_free R" "triangular (rev As) R" "distinct As" "Nts R \<subseteq> set As"
  shows "GNF_hd (expand_tri As R)"
by (metis Eps_free_expand_tri GNF_hd_iff_dep_on Int_absorb2 Nts_expand_tri assms dep_on_expand_tri
      dep_on_subs_Nts subset_trans subsetD)

text \<open>Any set of productions can be transformed into GNF via \<open>expand_tri (solve_tri)\<close>.\<close>
theorem GNF_of_R:
  assumes assms: "Eps_free R" "distinct (As @ As')" "Nts R \<subseteq> set As" "length As \<le> length As'"
  shows "GNF_hd (expand_tri (As' @ rev As) (solve_tri As As' R))"
proof -
  from assms have tri: "triangular (As @ rev As') (solve_tri As As' R)"
    by (simp add: Int_commute triangular_As_As'_solve_tri)
  have "Nts (solve_tri As As' R) \<subseteq> set As \<union> set As'" using assms Nts_solve_tri_sub by fastforce 
  then show ?thesis 
    using GNF_hd_expand_tri[of "(solve_tri As As' R)" "(As' @ rev As)"] assms tri 
    by (auto simp add: Eps_free_solve_tri)
qed


subsection \<open>\<open>expand_tri\<close> Preserves Language\<close>

text \<open>Similar to the proof of Language equivalence of \<open>expand_hd\<close>.\<close>

text \<open>All productions in \<open>expand_tri As R\<close> are derivable by \<open>R\<close>.\<close>
lemma expand_tri_prods_deirvable: "(B, bs) \<in> expand_tri As R \<Longrightarrow> R \<turnstile> [Nt B] \<Rightarrow>* bs"
proof (induction As R arbitrary: B bs rule: expand_tri.induct)
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
      then have "\<exists>C cw v.(bs = cw@v \<and> (B, Nt C#v) \<in> (expand_tri As R) \<and> (C,cw) \<in> (expand_tri As R)) 
          \<or> (B, bs) \<in> (expand_tri As R)"
        using 2 by (auto simp add: Let_def)
      then obtain C cw v 
        where "(bs = cw @ v \<and> (B, Nt C # v) \<in> (expand_tri As R) \<and> (C, cw) \<in> (expand_tri As R)) 
         \<or> (B, bs) \<in> (expand_tri As R)" 
        by blast
      then have "(bs = cw @ v \<and> R \<turnstile> [Nt B] \<Rightarrow>* [Nt C] @ v \<and> R \<turnstile> [Nt C] \<Rightarrow>* cw) \<or> R \<turnstile> [Nt B] \<Rightarrow>* bs"
        using "2.IH" by auto       
      then show ?thesis by (meson derives_append rtranclp_trans)
    next
      case False
      then have "(B, bs) \<in> (expand_tri As R)" using 2 by (auto simp add: Let_def)
      then show ?thesis using "2.IH" by (simp add: bu_prod derives_if_bu)
    qed
  next
    case False
    then have "(B, bs) \<in> R" using 2 by (auto simp only: helper_expand_tri1)
    then show ?thesis by (simp add: bu_prod derives_if_bu)
  qed
qed

text \<open>Language Preservation:\<close>
lemma expand_tri_Lang: "Lang (expand_tri As R) A = Lang R A"
proof
  have "(B, bs) \<in> (expand_tri As R) \<Longrightarrow> R \<turnstile> [Nt B] \<Rightarrow>* bs" for B bs
    by (simp add: expand_tri_prods_deirvable)
  then have "expand_tri As R \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<Longrightarrow> R \<turnstile> [Nt A] \<Rightarrow>* map Tm x" for x
    using derives_simul_rules by blast
  then show "Lang (expand_tri As R) A \<subseteq> Lang R A"  by(auto simp add: Lang_def)
next
  show "Lang R A \<subseteq> Lang (expand_tri As R) A"
  proof (induction As R rule: expand_tri.induct)
    case (1 R)
    then show ?case by simp
  next
    case (2 D Ds R)
    let ?R' = "expand_tri Ds R"
    let ?X = "{(Al,Bw) \<in> ?R'. Al=D \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set (Ds))}"
    let ?Y = "{(D,v@w) |v w. \<exists>B. (D, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
    have F1: "expand_tri (D#Ds) R = ?R' - ?X \<union> ?Y" by (simp add: Let_def)

    let ?S = "{x. \<exists>A w H. x = (A, [], H, w) \<and> (A, Nt H # w) \<in> ?X}"
    let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
    let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> ?R'}"
  
    have S'_eq_X: "?S' = ?X" by fastforce
    have E_eq_Y: "?E = ?Y" by fastforce

    have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> ?R'" by fastforce
    have "Lang R A \<subseteq> Lang (expand_tri Ds R) A" using 2 by simp
    also have "... \<subseteq> Lang (?R' - ?S' \<union> ?E) A"
      using exp_includes_Lang[of ?S] by auto
    also have "... = Lang (expand_tri (D#Ds) R) A" using S'_eq_X E_eq_Y F1 by fastforce
    finally show ?case.
  qed
qed

section \<open>Function \<open>gnf_hd\<close>: Conversion to \<open>GNF_hd\<close>\<close>

text \<open>All epsilon-free grammars can be put into GNF while preserving their language.\<close>
text \<open>Putting the productions into GNF via \<open>expand_tri (solve_tri)\<close> preserves the language.\<close>
lemma Lang_expand_solve_tri: 
  assumes "Eps_free R" "length As \<le> length As'" "distinct (As @ As')" "Nts R \<inter> set As' = {}" "A \<notin> set As'"
  shows "Lang (expand_tri (As' @ rev As) (solve_tri As As' R)) A = Lang R A"
using solve_tri_Lang[OF assms] expand_tri_Lang[of "(As' @ rev As)"] by blast

text \<open>Any Grammar can be brought into GNF.\<close>
theorem GNF_hd_gnf_hd: "GNF_hd (gnf_hd ps)"
unfolding gnf_hd_def Let_def
by(simp add: gnf_hd_def Let_def GNF_of_R[OF eps_free_eps_elim]
  distinct_nts_prods_list freshs_distinct finite_nts freshs_disj nts_eps_elim set_nts_prods_list length_freshs)

lemma distinct_app_freshs: "\<lbrakk> As = nts_prods_list ps; As' = freshs (set As) As \<rbrakk> \<Longrightarrow>
   distinct (As @ As')"
using freshs_disj[of "set As" As]
by (auto simp: distinct_nts_prods_list freshs_distinct)

lemma lem: "A \<notin> Nts P \<Longrightarrow> Lang P A = {}"
  by (simp add: Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts)

text \<open>\<open>gnf_hd\<close> preserves the language (modulo \<open>[]\<close>):\<close>
theorem Lang_gnf_hd: "A \<in> nts ps \<Longrightarrow> Lang (gnf_hd ps) A = lang ps A - {[]}"
unfolding gnf_hd_def Let_def
apply(rule Lang_expand_solve_tri[OF eps_free_eps_elim, simplified lang_eps_elim])
   apply (simp add: length_freshs)
  apply (metis distinct_app_freshs)
 using set_nts_prods_list distinct_app_freshs nts_eps_elim apply fastforce
apply(metis IntI empty_iff finite_nts freshs_disj set_nts_prods_list)
done

text \<open>Two simple examples:\<close>

lemma "gnf_hd [(0, [Nt(0::nat), Tm (1::int)])] = {(1, [Tm 1]), (1, [Tm 1, Nt 1])}"
  by eval

lemma "gnf_hd [(0, [Nt(0::nat), Tm (1::int)]), (0, [Tm 2]), (8, []), (9, [Nt 8])] =
  { (0, [Tm 2, Nt 1]), (0, [Tm 2]), (1, [Tm 1, Nt 1]), (1, [Tm 1]) }"
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
     solve_tri [3,2,1] [4,5,6] (set P0) = set P1 \<and> expand_tri [4,1,2,3] (set P1) = set P2"
by eval


section \<open>Complexity\<close>

text \<open>Our method has exponential complexity, which we demonstrate below.
Alternative polynomial methods are described in the literature \cite{BlumK99}.

We start with an informal proof that the blowup of the whole method can be as bad
as $2^{n^2}$, where $n$ is the number of non terminals, and the starting grammar has $4n$ productions.

Consider this grammar, where \<open>a\<close> and \<open>b\<close> are terminals and we use nested alternatives in the obvious way:

\<open>A0 \<rightarrow> A1 (a | b) | A2 (a | b) | ... | An (a | b) | a | b\<close>

\<open>A(i+1) \<rightarrow> Ai (a | b)\<close>

Expanding all alternatives makes this a grammar of size $4n$.

When converting this grammar into triangular form, starting with \<open>A0\<close>, we find that \<open>A0\<close> remains the
same after \<open>expand_hd\<close>, and \<open>solve_lrec\<close> introduces a new additional production for every \<open>A0\<close> production,
which we will ignore to simplify things:

Then every \<open>expand_hd\<close> step yields for \<open>Ai\<close> these number of productions:

  (1) \<open>2^(i+1)\<close> productions with rhs \<open>Ak (a | b)^(i+1)\<close> for every \<open>k \<in> [i+1, n]\<close>,

  (2) \<open>2^(i+1)\<close> productions with rhs \<open>(a | b)^(i+1)\<close>,

  (3) \<open>2^(i+1)\<close> productions with rhs \<open>Ai (a | b)^(i+1)\<close>.

Note that \<open>(a | b)^(i+1)\<close> represents all words of length \<open>i+1\<close> over \<open>{a,b}\<close>.
Solving the left recursion again introduces a new additional production for every production of form (1) and (2),
which we will again ignore for simplicity. 
The productions of (3) get removed by \<open>solve_lrec\<close>.
We will not consider the productions of the newly introduced nonterminals.

In the triangular form, every \<open>Ai\<close> has at least \<open>2^(i+1)\<close> productions starting with terminals (2)
and \<open>2^(i+1)\<close> productions with rhs starting with \<open>Ak\<close> for every \<open>k \<in> [i+1, n]\<close>.

When expanding the triangular form starting from \<open>An\<close>, which has at least the \<open>2^(i+1)\<close> productions from (2),
we observe that the number of productions of \<open>Ai\<close> (denoted by \<open>#Ai\<close>) is  \<open>#Ai \<ge> 2^(i+1) * #A(i+1)\<close> 
(Only considering the productions of the form \<open>A(i+1) (a | b)^(i+1)\<close>).
This yields that \<open>#Ai \<ge> 2^(i+1) * 2^((i+2) + ... + (n+1)) = 2^((i+1) + (i+2) + ... (n+1))\<close>.
Thus \<open>#A0 \<ge> 2^(1 + 2 + ... + n + (n+1)) = 2^((n+1)*(n+2)/2)\<close>.

Below we prove formally that \<open>expand_tri\<close> can cause exponential blowup.\<close>

text \<open>Bad grammar: Constructs a grammar which leads to a exponential blowup when expanded 
      by \<open>expand_tri\<close>:\<close>
fun bad_grammar :: "'n list \<Rightarrow> ('n, nat)Prods" where
 "bad_grammar [] = {}"
|"bad_grammar [A] = {(A, [Tm 0]), (A, [Tm 1])}"
|"bad_grammar (A#B#As) = {(A, Nt B # [Tm 0]), (A, Nt B # [Tm 1])} \<union> (bad_grammar (B#As))"

lemma bad_gram_simp1: "A \<notin> set As \<Longrightarrow> (A, Bs) \<notin> (bad_grammar As)"
  by (induction As rule: bad_grammar.induct) auto

lemma expand_tri_simp1: "A \<notin> set As \<Longrightarrow> (A, Bs) \<in> R \<Longrightarrow> (A, Bs) \<in> expand_tri As R"
  by (induction As R rule: expand_tri.induct) (auto simp add: Let_def)

lemma expand_tri_iff1: "A \<notin> set As \<Longrightarrow> (A, Bs) \<in> expand_tri As R \<longleftrightarrow> (A, Bs) \<in> R"
  using expand_tri_simp1 helper_expand_tri1 by auto

lemma expand_tri_insert_simp: 
  "B \<notin> set As \<Longrightarrow> expand_tri As (insert (B, Bs) R) = insert (B, Bs) (expand_tri As R)"
  by (induction As R rule: expand_tri.induct) (auto simp add: Let_def)

lemma expand_tri_bad_grammar_simp1: 
  "distinct (A#As) \<Longrightarrow> length As \<ge> 1 
   \<Longrightarrow> expand_tri As (bad_grammar (A#As)) 
       = {(A, Nt (hd As) # [Tm 0]), (A, Nt (hd As) # [Tm 1])} \<union> (expand_tri As (bad_grammar As))"
proof (induction As)
  case Nil
  then show ?case by simp
next
  case Cons1: (Cons B Bs)
  then show ?case
  proof (cases Bs)
    case Nil
    then show ?thesis by auto
  next
    case Cons2: (Cons C Cs)
    then show ?thesis using Cons1 expand_tri_insert_simp
      by (smt (verit) Un_insert_left bad_grammar.elims distinct.simps(2) insert_is_Un 
          list.distinct(1) list.inject list.sel(1))
  qed
qed

lemma finite_bad_grammar: "finite (bad_grammar As)"
  by (induction As rule: bad_grammar.induct) auto

lemma finite_expand_tri: "finite R \<Longrightarrow> finite (expand_tri As R)"
proof (induction As R rule: expand_tri.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  let ?S = "{(S,v@w)|v w. \<exists>B. (S,Nt B#w) \<in> expand_tri Ss R \<and> B \<in> set Ss \<and> (B,v) \<in> expand_tri Ss R}"
  let ?f = "\<lambda>((A,w),(B,v)). (A, v @ (tl w))"
  have "?S \<subseteq> ?f ` ((expand_tri Ss R) \<times> (expand_tri Ss R))"
  proof
    fix x
    assume "x \<in> ?S"
    then have "\<exists>S v B w. (S,Nt B # w) \<in> expand_tri Ss R \<and> (B,v) \<in> expand_tri Ss R \<and> x = (S, v @ w)" 
      by blast
    then obtain S v B w 
      where P: "(S, Nt B # w) \<in> expand_tri Ss R \<and> (B, v) \<in> expand_tri Ss R \<and> x = (S, v @ w)"
      by blast
    then have 1: "((S, Nt B # w), (B ,v)) \<in> ((expand_tri Ss R) \<times> (expand_tri Ss R))" by auto
    have "?f ((S, Nt B # w), (B ,v)) = (S, v @ w)" by auto
    then have "(S, v @ w) \<in> ?f ` ((expand_tri Ss R) \<times> (expand_tri Ss R))" using 1 by force
    then show "x \<in> ?f ` ((expand_tri Ss R) \<times> (expand_tri Ss R))" using P by simp
  qed
  then have "finite ?S"
    by (meson "2.IH" "2.prems" finite_SigmaI finite_surj)
  then show ?case using 2 by (auto simp add: Let_def)
qed

text \<open>The last Nt expanded by \<open>expand_tri\<close> has an exponential number of productions.\<close>
lemma bad_gram_last_expanded_card: 
  "\<lbrakk>distinct As; length As = n; n \<ge> 1\<rbrakk>
   \<Longrightarrow> card ({v. (hd As, v) \<in> expand_tri As (bad_grammar As)}) = 2 ^ n" 
proof(induction As arbitrary: n rule: bad_grammar.induct)
  case 1
  then show ?case by simp
next
  case (2 A)
  have 4: "{v. v = [Tm 0] \<or> v = [Tm (Suc 0)]} = {[Tm 0], [Tm 1]}" by auto
  then show ?case using 2 by (auto simp add: 4)
next
  case (3 A C As)
  let ?R' = "expand_tri (C#As) (bad_grammar (A#C#As))"
  let ?X = "{(Al,Bw) \<in> ?R'. Al=A \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set (C#As))}"
  let ?Y = "{(A,v@w) |v w. \<exists>B. (A, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"

  let ?S = "{v. (hd (A#C#As), v) \<in> expand_tri (A#C#As) (bad_grammar (A#C#As))}"

  have 4: "(A,Bw) \<in> ?R' \<longleftrightarrow> (A, Bw) \<in> (bad_grammar (A#C#As))" for Bw
    using expand_tri_iff1[of "A" "C#As" Bw] 3 by auto
  then have "?X = {(Al,Bw) \<in> (bad_grammar (A#C#As)). Al=A \<and> (\<exists>w B. Bw = Nt B#w \<and> B \<in> set (C#As))}" 
    using expand_tri_iff1 by auto
  also have "... = {(A, Nt C # [Tm 0]), (A, Nt C # [Tm 1])}" 
    using 3 by (auto simp add: bad_gram_simp1)
  finally have 5: "?X = {(A, [Nt C, Tm 0]), (A, [Nt C, Tm 1])}".
  then have cons5: "?X = {(A, Nt C # [Tm 0]), (A, Nt C # [Tm 1])}" by simp

  have 6: "?R' = {(A, [Nt C, Tm 0]), (A, [Nt C, Tm 1])} \<union> expand_tri (C#As) (bad_grammar (C#As))"
    using 3 expand_tri_bad_grammar_simp1[of A "C#As"] by auto
  have 8: "(A, as) \<notin> expand_tri (C#As) (bad_grammar (C#As))" for as 
    using "3.prems" bad_gram_simp1 expand_tri_iff1
    by (metis distinct.simps(2))
  then have 7: "{(A,[Nt C, Tm 0]), (A,[Nt C, Tm 1])} \<inter> expand_tri (C#As) (bad_grammar (C#As)) = {}"
    by auto
    
  have "?R' - ?X = expand_tri (C#As) (bad_grammar (C#As))" using 7 6 5 by auto
  then have S_from_Y: "?S = {v. (A, v) \<in> ?Y}" using 6 8 by auto

  have Y_decomp: "?Y = {(A, v @ [Tm 0]) | v. (C,v) \<in> ?R'} \<union> {(A, v @ [Tm 1]) | v. (C,v) \<in> ?R'}"
  proof
    show "?Y \<subseteq> {(A, v @ [Tm 0]) | v. (C,v) \<in> ?R'} \<union> {(A, v @ [Tm 1]) | v. (C,v) \<in> ?R'}"
    proof
      fix x
      assume assm: "x \<in> ?Y"
      then have "\<exists>v w. x = (A, v @ w) \<and> (\<exists>B. (A, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R')" by blast
      then obtain v w where P: "x = (A, v @ w) \<and> (\<exists>B. (A, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R')" by blast
      then have cfact:"(A, Nt C # w) \<in> ?X \<and> (C,v) \<in> ?R'" using cons5 
        by (metis (no_types, lifting) Pair_inject insert_iff list.inject singletonD sym.inject(1))
      then have "w = [Tm 0] \<or> w = [Tm 1]" using cons5
        by (metis (no_types, lifting) empty_iff insertE list.inject prod.inject)
      then show "x \<in> {(A, v @ [Tm 0]) | v. (C,v) \<in> ?R'} \<union> {(A, v @ [Tm 1]) | v. (C,v) \<in> ?R'}" 
        using P cfact by auto
    qed
  next
    show "{(A, v @ [Tm 0]) | v. (C,v) \<in> ?R'} \<union> {(A, v @ [Tm 1]) | v. (C,v) \<in> ?R'} \<subseteq> ?Y" 
      using cons5 by auto
  qed
  
  from Y_decomp have S_decomp: "?S = {v@[Tm 0] | v. (C, v) \<in> ?R'} \<union> {v@[Tm 1] | v. (C, v) \<in> ?R'}" 
    using S_from_Y by auto

  have cardCvR: "card {v. (C, v) \<in> ?R'} = 2^(n-1)" using 3 6 by auto
  have "bij_betw (\<lambda>x. x@[Tm 0]) {v. (C, v) \<in> ?R'} {v@[Tm 0] | v. (C, v) \<in> ?R'}"
    by (auto simp add: bij_betw_def inj_on_def)
  then have cardS1: "card {v@[Tm 0] | v. (C, v) \<in> ?R'} = 2^(n-1)"
    using cardCvR by (auto simp add: bij_betw_same_card)
  have "bij_betw (\<lambda>x. x@[Tm 1]) {v. (C, v) \<in> ?R'} {v@[Tm 1] | v. (C, v) \<in> ?R'}"
    by (auto simp add: bij_betw_def inj_on_def)
  then have cardS2: "card {v@[Tm 1] | v. (C, v) \<in> ?R'} = 2^(n-1)" 
    using cardCvR by (auto simp add: bij_betw_same_card)

  have fin_R': "finite ?R'" using finite_bad_grammar finite_expand_tri by blast
  let ?f1 = "\<lambda>(C,v). v@[Tm 0]"
  have "{v@[Tm 0] | v. (C, v) \<in> ?R'} \<subseteq> ?f1 ` ?R'" by auto
  then have fin1: "finite {v@[Tm 0] | v. (C, v) \<in> ?R'}"
    using fin_R' by (meson finite_SigmaI finite_surj)
  let ?f2 = "\<lambda>(C,v). v@[Tm 1]"
  have "{v@[Tm 1] | v. (C, v) \<in> ?R'} \<subseteq> ?f2 ` ?R'" by auto
  then have fin2: "finite {v@[Tm 1] | v. (C, v) \<in> ?R'}"
    using fin_R' by (meson finite_SigmaI finite_surj)

  have fin_sets: "finite {v@[Tm 0] | v. (C, v) \<in> ?R'} \<and> finite {v@[Tm 1] | v. (C, v) \<in> ?R'}"
    using fin1 fin2 by simp

  have "{v@[Tm 0] | v. (C, v) \<in> ?R'} \<inter> {v@[Tm 1] | v. (C, v) \<in> ?R'} = {}" by auto
  then have "card ?S = 2^(n-1) + 2^(n-1)"
    using S_decomp cardS1 cardS2 fin_sets 
    by (auto simp add: card_Un_disjoint)

  then show ?case using 3 by auto
qed

text \<open>The productions resulting from \<open>expand_tri (bad_grammar)\<close> have at least exponential size.\<close>
theorem expand_tri_blowup: assumes "n \<ge> 1"
  shows "card (expand_tri [0..<n] (bad_grammar [0..<n])) \<ge> 2^n"
proof -
  from assms have "length [0..<n] \<ge> 1 \<and> distinct [0..<n] \<and> length [0..<n] = n" by auto
  then have 1: "card ({v. (hd [0..<n], v) \<in> expand_tri [0..<n] (bad_grammar [0..<n])}) = 2 ^ n"
    using bad_gram_last_expanded_card assms by blast

  let ?S = "{v. (hd [0..<n], v) \<in> expand_tri [0..<n] (bad_grammar [0..<n])}"
  have 2: "card ?S = card ({hd [0..<n]} \<times> ?S)"
    by (simp add: card_cartesian_product_singleton)
  have 3: "({hd [0..<n]} \<times> ?S) \<subseteq> (expand_tri [0..<n] (bad_grammar [0..<n]))" by fastforce

  have "finite (expand_tri [0..<n] (bad_grammar [0..<n]))"
    using finite_bad_grammar finite_expand_tri by blast
  then show ?thesis using 1 2 3
    by (metis card_mono)
qed

end
