(*  Author:     Štěpán Holub, Department of Algebra, Charles University
    Author:     Zuzana Haniková, Institute of Computer Science of the Czech Academy of Sciences
*)

chapter \<open>Fragments of Zermelo-Fraenkel set theory without infinity\<close>
theory ZFfin
imports Main
begin

text \<open>We explore axiomatizations of the theory of hereditarily finite sets, their fragments and relationships between them.\<close>

section Preliminaries

\<comment> \<open>General auxiliary simplification rule\<close>
lemma ex_or_iff_or [simp]: "(\<exists>w. (w = x \<or> w = y) \<and> P u w) \<longleftrightarrow> (P u x \<or> P u y)"
   by blast

\<comment> \<open>A tautology recording the behaviour of bounded quantifiers. The logical equivalence between the axiom schemata \<open>regsch\<close> and \<open>epsind\<close> below is a particular instance.\<close>
lemma abstract_foundation_iff: "((\<exists>x. P x) \<longrightarrow> (\<exists>x. B x \<and> P x)) \<longleftrightarrow> (\<forall> x. B x \<longrightarrow> \<not> P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  by auto

section \<open>Signature\<close>

subsection \<open>Membership and basic set-theoretic notions\<close>

locale set_signature =
  fixes membership :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<epsilon>" 50)

begin

text \<open>General relation between regularity schema and epsilon-induction scheme. Applying the above remark about B-induction and B-foundation\<close>

thm abstract_foundation_iff[of "\<lambda> x. \<not> P x" "\<lambda> x. (\<forall> y. y \<epsilon> x \<longrightarrow> (P y))", unfolded not_not, symmetric]
thm abstract_foundation_iff[of  "\<lambda> y. P y" "\<lambda> x. (\<forall> y. y \<epsilon> x \<longrightarrow> \<not> (P y))", unfolded not_not]

subsection \<open>Set theoretical notions\<close>

text \<open>We use "M" (as in "Menge") for our defined versions of set-theoretical concepts, built upon membership.\<close>

definition subsetM :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<subseteq>\<^sub>M _" [51,51] 53) where
  "subsetM x y \<equiv> (\<forall> z. z \<epsilon> x \<longrightarrow> z \<epsilon> y)"

lemma subsetM_refl[simp]: "x \<subseteq>\<^sub>M x" 
  unfolding subsetM_def by blast

lemma subsetM_trans[simp]: assumes "x \<subseteq>\<^sub>M y" "y \<subseteq>\<^sub>M z" shows "x \<subseteq>\<^sub>M z"
  using assms subsetM_def by simp

definition proper_subsetM :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<subset>\<^sub>M _" [50,50] 50) where
  "proper_subsetM x y \<equiv> (\<forall> z::'a. z \<epsilon> x \<longrightarrow> z \<epsilon> y)  \<and> x \<noteq> y" 

named_theorems set_defs
lemmas[set_defs] = proper_subsetM_def subsetM_def 

lemma proper_subset_def': "x \<subset>\<^sub>M y \<longleftrightarrow> x \<subseteq>\<^sub>M y \<and> x \<noteq> y"
  unfolding set_defs by blast

lemma proper_subsetI: "x \<subseteq>\<^sub>M y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<subset>\<^sub>M y"
  unfolding set_defs by blast

lemma proper_subsetM_irrefl[simp]: "\<not> x \<subset>\<^sub>M x"
  unfolding set_defs by simp     

definition transM:: "'a \<Rightarrow> bool" where
 "transM x \<equiv> \<forall> y. y \<epsilon> x \<longrightarrow> y \<subseteq>\<^sub>M x "

text \<open>Hilbert's description operator @{term The} is used to define sets that are determined by their elements. 
Resulting set-theoretic operations can and will be used in appropriate contexts only that guarantee
the existence of corresponding sets, and their unicity (provable with extensionality).\<close>

definition collectM :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"  where
 "collectM Q \<equiv> THE z . (\<forall> u . (u \<epsilon> z \<longleftrightarrow> Q u))"

definition emptysetM ("\<emptyset>") where 
  "emptysetM \<equiv> collectM (\<lambda> x. x \<noteq> x)"

definition separationM :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
 "separationM y Q \<equiv> collectM (\<lambda> u. u \<epsilon> y \<and> Q u)"

definition powersetM :: "'a \<Rightarrow> 'a" ("\<PP>") where
  "powersetM x \<equiv> collectM (\<lambda> u. u \<subseteq>\<^sub>M x)"

definition binunionM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<union>\<^sub>M" 55) where
  "binunionM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<or> u \<epsilon> y)"

definition intersectionM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<inter>\<^sub>M _" [55,54] 60) where
  "intersectionM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<and> u \<epsilon> y)"

lemma intersection_symm: "x \<inter>\<^sub>M y = y \<inter>\<^sub>M x"
  unfolding intersectionM_def by metis

definition unionM :: "'a \<Rightarrow> 'a" ("\<Union>\<^sub>M")  where
  "unionM x \<equiv> collectM (\<lambda> u. (\<exists> v. v \<epsilon> x \<and> u \<epsilon> v))"

definition differenceM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (" _ \<setminus>\<^sub>M _") where
  "differenceM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<and> \<not> u \<epsilon> y )"

definition singletonM :: "'a \<Rightarrow> 'a" ("{_}\<^sub>M" 70) where
  "singletonM x \<equiv> collectM (\<lambda> u. u = x)"

definition pairM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("{_,_}\<^sub>M" [51,51] 60) where
  "pairM x y \<equiv> collectM (\<lambda> u. u = x \<or> u = y)"

\<comment> \<open>Set successor. Also known as adjunction.\<close>
definition setsucM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<ss>\<uu>\<cc>") where
  "setsucM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<or> u = y)"

definition replaceM :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a" where
   "replaceM P x \<equiv> collectM (\<lambda> u. \<exists> v. v \<epsilon> x \<and> P v u)"

definition leastM :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" ("\<Inter>\<^sub>M") where
 "leastM Q \<equiv> collectM (\<lambda> u. \<forall> y. Q y \<longrightarrow> u \<epsilon> y)"

text \<open>Least transitive superset\<close>
definition least_tsM :: "'a \<Rightarrow> 'a" where
  "least_tsM x = \<Inter>\<^sub>M (\<lambda> y. transM y \<and> x \<subseteq>\<^sub>M y)"

definition ordered_pairM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<langle>_,_\<rangle>" [51,51] 60) where
  "ordered_pairM a b \<equiv> {{a}\<^sub>M,{a,b}\<^sub>M}\<^sub>M"

definition relationM :: "'a \<Rightarrow> bool" where
  "relationM x \<equiv> \<forall> v. v \<epsilon> x \<longrightarrow> (\<exists> a b. v = \<langle>a,b\<rangle>)"

definition rel_inverseM :: "'a \<Rightarrow> 'a" where
  "rel_inverseM r \<equiv> collectM (\<lambda> u. \<exists> a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)"

definition functionM :: "'a \<Rightarrow> bool" where
  "functionM x \<equiv> relationM x \<and>  (\<forall> a b c. \<langle>a,b\<rangle> \<epsilon> x \<and> \<langle>a,c\<rangle> \<epsilon> x \<longrightarrow> b = c)"

lemma funD: "functionM f \<Longrightarrow> \<langle>a,b\<rangle> \<epsilon> f \<Longrightarrow> \<langle>a,c\<rangle> \<epsilon> f \<Longrightarrow>  b = c"
  unfolding functionM_def by blast

definition domM :: "'a \<Rightarrow> 'a" where
  "domM r \<equiv> collectM (\<lambda> u. \<exists> v. \<langle>u,v\<rangle> \<epsilon> r)"

definition rngM :: "'a \<Rightarrow> 'a" where
  "rngM r \<equiv> collectM (\<lambda> u. \<exists> v. \<langle>v,u\<rangle> \<epsilon> r)"

definition one_oneM :: "'a \<Rightarrow> bool" where
  "one_oneM f \<equiv> functionM f \<and>  (\<forall> a b c. \<langle>b,a\<rangle> \<epsilon> f \<and> \<langle>c,a\<rangle> \<epsilon> f \<longrightarrow> b = c)"

lemma one_one_inj: "one_oneM f \<Longrightarrow> \<langle>b,a\<rangle> \<epsilon> f \<Longrightarrow> \<langle>c,a\<rangle> \<epsilon> f \<Longrightarrow>  b = c"
  unfolding one_oneM_def by blast

lemma one_oneI: assumes "\<forall> v. v \<epsilon> f \<longrightarrow> (\<exists> a b. v = \<langle>a,b\<rangle>)" "(\<forall> a b c. \<langle>b,a\<rangle> \<epsilon> f \<and> \<langle>c,a\<rangle> \<epsilon> f \<longrightarrow> b = c)" "(\<forall> a b c. \<langle>a,b\<rangle> \<epsilon> f \<and> \<langle>a,c\<rangle> \<epsilon> f \<longrightarrow> b = c)"
  shows "one_oneM f"
  using assms unfolding one_oneM_def functionM_def relationM_def by blast+

lemma one_oneD1: "one_oneM f \<Longrightarrow> \<forall> v. v \<epsilon> f \<longrightarrow> (\<exists> a b. v = \<langle>a,b\<rangle>)"
  unfolding one_oneM_def functionM_def relationM_def by blast

lemma one_oneD2: "one_oneM f \<Longrightarrow> (\<forall> a b c. \<langle>b,a\<rangle> \<epsilon> f \<and> \<langle>c,a\<rangle> \<epsilon> f \<longrightarrow> b = c)"
  unfolding one_oneM_def functionM_def relationM_def by blast 

lemma one_oneD3: "one_oneM f \<Longrightarrow> (\<forall> a b c. \<langle>a,b\<rangle> \<epsilon> f \<and> \<langle>a,c\<rangle> \<epsilon> f \<longrightarrow> b = c)"
  unfolding one_oneM_def functionM_def relationM_def by blast

definition set_equivalent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<approx>\<^sub>M _" [51,51] 52) where
  "set_equivalent x y \<equiv> (\<exists> f. one_oneM f \<and> x = domM f \<and> y = rngM f)"

definition cartesian_productM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("_ \<times>\<^sub>M _ " [51,51] 60) where
  "cartesian_productM x y \<equiv> collectM (\<lambda> u. \<exists> v\<^sub>1 v\<^sub>2. v\<^sub>1 \<epsilon> x \<and> v\<^sub>2 \<epsilon> y \<and> u = \<langle>v\<^sub>1,v\<^sub>2\<rangle>)"

definition composeM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<circ>\<^sub>M _" [51,51] 60) where
  "f \<circ>\<^sub>M g = collectM (\<lambda> u. \<exists> a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)"

definition tarski_fin :: "'a \<Rightarrow> bool" where
   "tarski_fin x \<equiv> \<forall> y. (\<forall> z. z \<epsilon> y \<longrightarrow> z \<subseteq>\<^sub>M x) \<longrightarrow> (\<exists> z. z \<epsilon> y) \<longrightarrow> (\<exists> z. z \<epsilon> y \<and> \<not>(\<exists> w. w \<epsilon> y \<and> z \<subset>\<^sub>M w))"

lemma tarski_subset_tarski: assumes "tarski_fin x" "y \<subseteq>\<^sub>M x" shows "tarski_fin y"
  using assms unfolding tarski_fin_def subsetM_def by presburger

definition dedekind_fin :: "'a \<Rightarrow> bool" where
   "dedekind_fin x \<equiv> \<forall> y. (y \<subset>\<^sub>M x \<longrightarrow> \<not> x \<approx>\<^sub>M y)"

\<comment> \<open>\<open>x\<close> is regular if it contains no infinite \<open>\<epsilon>\<close>-decreasing chain as a subset\<close>
definition regular :: "'a \<Rightarrow> bool" where
   "regular x \<equiv> \<forall> y. y \<subseteq>\<^sub>M x \<longrightarrow>  (\<exists> z. z \<epsilon> y) \<longrightarrow> (\<exists> z. z \<epsilon> y \<and> (\<forall> v. \<not> (v \<epsilon> z \<and> v \<epsilon> y)))"

\<comment> \<open>Ordinals and natural numbers\<close>

definition epschain :: "'a \<Rightarrow> bool" where
  "epschain x \<equiv> transM x \<and> (\<forall> y z. y \<epsilon> x \<and> z \<epsilon> x \<longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y)"

\<comment> \<open>In theories that do not rely on the regularity axiom, ordinals are explicitly assumed not to contain infinite \<open>\<epsilon>\<close>-decreasing chains\<close>
definition ordM :: "'a \<Rightarrow> bool" where
  "ordM x \<equiv> epschain x \<and> regular x"

lemma ordM_I: "regular x \<Longrightarrow> epschain x \<Longrightarrow> ordM x"
  using ordM_def by blast

lemma ordM_regular[simp]: "ordM x \<Longrightarrow> regular x"
  unfolding ordM_def by blast

lemma ordM_D1: "ordM x \<Longrightarrow> y \<epsilon> x \<Longrightarrow> y \<subseteq>\<^sub>M x"
  using ordM_def unfolding transM_def epschain_def by blast

lemma ordM_trans: assumes "ordM v"  "w \<epsilon> u" "u \<epsilon> v"  shows "w \<epsilon> v"
  using assms ordM_D1 subsetM_def by blast

lemma ordM_D2: "ordM x \<Longrightarrow> y \<epsilon> x \<Longrightarrow> z \<epsilon> x \<Longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y"
  using ordM_def epschain_def by blast

definition is_sucM :: "'a \<Rightarrow> bool" where
  "is_sucM x \<equiv> \<exists> y. (\<forall> z. z \<epsilon> x \<longleftrightarrow> z \<epsilon> y \<or> z = y)" 

\<comment> \<open>A natural number is an ordinal \<open>x\<close> such that: \<open>x\<close> and all its elements are either empty or a successor\<close>
definition natM :: "'a \<Rightarrow> bool" where
  "natM x \<equiv> ordM x \<and> (\<forall> v. (v \<epsilon> x \<or> v = x) \<longrightarrow> (\<exists> u. u \<epsilon> v) \<longrightarrow> is_sucM v)"

lemma natM_I: "ordM x \<Longrightarrow> is_sucM x \<Longrightarrow> (\<And> v. \<exists> u. u \<epsilon> v \<Longrightarrow> v \<epsilon> x \<Longrightarrow> is_sucM v) \<Longrightarrow> natM x"
  unfolding natM_def by blast

lemma nat_is_suc: "natM x \<Longrightarrow> \<exists> u. u \<epsilon> x \<Longrightarrow> is_sucM x"
  unfolding natM_def by blast

lemma nat_mem_is_suc: "natM x \<Longrightarrow> v \<epsilon> x \<Longrightarrow> \<exists> u. u \<epsilon> v \<Longrightarrow> is_sucM v"
  unfolding natM_def by blast

lemma natM_D: "natM x \<Longrightarrow> ordM x"
  using natM_def by blast

definition cardinality :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cardinality x n \<equiv> natM n \<and> x \<approx>\<^sub>M n"

lemmas[set_defs] = transM_def epschain_def ordM_def tarski_fin_def is_sucM_def natM_def functionM_def relationM_def one_oneM_def rngM_def domM_def regular_def cardinality_def set_equivalent_def

subsection \<open>Set relations and properties\<close>

text \<open>We represent a set formula as the predicate it defines. 
A predicate assigns truth values to assignments. 
We consider countably many variables \<open>x\<^sub>i\<close>, represented by natural numbers.
An assignment maps variables to elements of the domain, i.e., it maps \<open>nat\<close> to \<open>'a\<close>.
Predicates defined by set formulas are defined inductively.
\<close>

inductive SetFormulaPredicate :: "((nat \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> bool"
  where 
  SFP_mem: "\<And> m n. SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> m) \<epsilon> (\<Xi> n))" \<comment> \<open>formula \<open>x\<^sub>m \<epsilon> x\<^sub>n\<close>\<close>
| SFP_eq: "\<And> m n. SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> m) = (\<Xi> n))"  \<comment> \<open>formula \<open>x\<^sub>m = x\<^sub>n\<close>\<close>
| SFP_neg: "SetFormulaPredicate P \<Longrightarrow> SetFormulaPredicate (\<lambda> \<Xi>. \<not> P \<Xi>)" \<comment> \<open>formula \<open>\<not> \<phi>\<close>\<close>
| SFP_disj: "SetFormulaPredicate P \<Longrightarrow> SetFormulaPredicate Q 
        \<Longrightarrow> SetFormulaPredicate (\<lambda> \<Xi>. P \<Xi> \<or> Q \<Xi>)"  \<comment> \<open>formula \<open>\<phi> \<or> \<psi>\<close>\<close>
| SFP_all: "\<And> n. SetFormulaPredicate P \<Longrightarrow> SetFormulaPredicate (\<lambda> \<Xi>. \<forall> a. P (\<Xi>(n:=a)))"
    \<comment> \<open>formula \<open>\<forall> x\<^sub>n. \<phi>\<close>\<close>

named_theorems SFP_rules 
lemmas[SFP_rules] = SFP_mem SFP_eq SFP_neg SFP_disj SFP_all

text \<open>Every set-theoretically definable predicate depends on finitely many values. Such values correspond to free variables.\<close>

lemma bounded_free: assumes "SetFormulaPredicate P"
  shows "\<exists> m. \<forall> \<Xi> \<Xi>'. (\<forall> i < m. \<Xi> i = \<Xi>' i) \<longrightarrow>  P(\<Xi>) = P (\<Xi>')"
proof (rule SetFormulaPredicate.induct[OF assms, of "\<lambda> Q. (\<exists> m. \<forall> \<Xi> \<Xi>'. (\<forall> i < m. \<Xi> i = \<Xi>' i) \<longrightarrow>  Q(\<Xi>) = Q (\<Xi>'))"])
  let ?Q = "\<lambda> x. True"
  show "\<exists>max. \<forall>\<Xi> \<Xi>'. (\<forall>i< max. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<Xi> m \<epsilon> \<Xi> n) = (\<Xi>' m \<epsilon> \<Xi>' n)" for m n :: nat
    by (rule exI[of _ "Suc(max m n)"]) force   
  show "\<exists>max. \<forall>\<Xi> \<Xi>'. (\<forall>i< max. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<Xi> m = \<Xi> n) = (\<Xi>' m = \<Xi>' n)" for m n :: nat
    by (rule exI[of _ "Suc(max m n)"]) force   
next
  fix Q :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assume "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'"
  then obtain m where "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'"
    by blast
  then have "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<not> Q \<Xi>) = (\<not> Q \<Xi>')" 
    by simp
  thus "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<not> Q \<Xi>) = (\<not> Q \<Xi>')"
    by blast
next
  fix Q R :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assume "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'" "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> R \<Xi> = R \<Xi>'"
  then obtain max_Q max_R where "\<forall>\<Xi> \<Xi>'. (\<forall>i<max_Q. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'" "\<forall>\<Xi> \<Xi>'. (\<forall>i<max_R. \<Xi> i = \<Xi>' i) \<longrightarrow> R \<Xi> = R \<Xi>'"
    by blast
  hence "\<forall>\<Xi> \<Xi>'. (\<forall>i<(max max_Q max_R). \<Xi> i = \<Xi>' i) \<longrightarrow> (Q \<Xi> \<or> R \<Xi>) = (Q \<Xi>' \<or> R \<Xi>')"
    unfolding less_max_iff_disj by metis
  thus "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (Q \<Xi> \<or> R \<Xi>) = (Q \<Xi>' \<or> R \<Xi>')"
    by blast
next
  fix Q :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and n :: nat
  assume "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'"
  then obtain max where max: "(\<forall>i<max. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'" for \<Xi> \<Xi>'
    by blast
  have "(\<forall>i<max. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<forall>a. Q (\<Xi>(n := a))) = (\<forall>a. Q (\<Xi>'(n := a)))" for \<Xi> \<Xi>'
    using max[of "\<Xi>(n := _)" "\<Xi>'(n := _)"] by force
  thus "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<forall>a. Q (\<Xi>(n := a))) = (\<forall>a. Q (\<Xi>'(n := a)))"  
    by blast
qed

\<comment>\<open>Renaming variables in any way (not necessarily permuting them) preserves the property of being a set-theoretically definable predicate.\<close>
lemma transform_variables: assumes "SetFormulaPredicate P"
  shows "SetFormulaPredicate (\<lambda> \<Xi>. P (\<lambda> n. \<Xi>(f n)))"
  using assms
proof(induction arbitrary: f rule:  SetFormulaPredicate.inducts)
  case (SFP_mem m n)
  then show ?case 
    using set_signature.SFP_mem by blast
next
  case (SFP_eq m n)
  then show ?case 
    using set_signature.SFP_eq  by blast
next
  case (SFP_neg P)                       
  then show ?case
    using SetFormulaPredicate.SFP_neg  by simp 
next
  case (SFP_disj P Q)
  then show ?case using SetFormulaPredicate.SFP_disj by simp
next
  case (SFP_all P n)
  then show ?case
  proof-
    obtain k  where k: "(\<forall>i < k. \<Xi> i = \<Xi>' i) \<Longrightarrow> P \<Xi> = P \<Xi>'" for \<Xi> \<Xi>' :: "nat \<Rightarrow> 'a"
      using bounded_free[OF \<open>SetFormulaPredicate P\<close>] by blast
    obtain M where M_bound: "(\<forall> b < k. f b < M)"
      using finite_imageI[OF finite_Collect_less_nat, of f k, unfolded finite_nat_set_iff_bounded]
      by blast
    let ?M = "Suc (M + n)"
    let ?Q = "\<lambda>a \<Xi>. P ((\<lambda>b. \<Xi> (f b))(n:=a))" 
    have M: "(\<forall>i < ?M. \<Xi> i = \<Xi>' i) \<Longrightarrow> ?Q a \<Xi> = ?Q a \<Xi>'" for \<Xi> \<Xi>' :: "nat \<Rightarrow> 'a" and a
      by (rule k[of "(\<lambda>b. \<Xi> (f b))(n := a)" "(\<lambda>b. \<Xi>' (f b))(n := a)"]) (use M_bound in auto) 
    have fsimp: "(\<lambda>b. (\<Xi>(p := a)) ((f(n := p)) b)) = (\<lambda>b. (\<Xi>(p := a)) (f b))(n:=a)"  for \<Xi> :: "nat \<Rightarrow> 'a"  and a p
      by auto
    have M_irrelevant: "P ((\<lambda>b. (\<Xi>(?M := a)) (f b))(n := a)) =  P ((\<lambda>b. \<Xi> (f b))(n := a))" for \<Xi> a
      by (rule M) simp
    show ?thesis
      using set_signature.SFP_all[OF SFP_all(2)[of "f(n:=?M)"], of ?M]
      unfolding fsimp M_irrelevant. 
  qed
qed

lemma update_variable[intro]: assumes "SetFormulaPredicate P"
  shows "SetFormulaPredicate (\<lambda> \<Xi>. P(\<Xi>(n:= \<Xi> m)))"
proof-
  have aux: "(\<lambda> a. \<Xi> ((id(n:=m)) a)) = (\<Xi> (n:=\<Xi> m))" for \<Xi> :: "nat \<Rightarrow> 'a"
    by force
  show ?thesis
    by (rule transform_variables[OF assms, of "id (n:=m)", unfolded aux]) 
qed

lemma swap_variables: assumes "SetFormulaPredicate P"
  shows "SetFormulaPredicate (\<lambda> \<Xi>. P (\<Xi>(k := \<Xi> l, l := \<Xi> k)))"
proof-
  have "(\<lambda>n. \<Xi> ((id(k := l, l := k)) n)) = \<Xi>(k := \<Xi> l, l := \<Xi> k)" for \<Xi> :: "nat \<Rightarrow> 'a"
    by fastforce
  from transform_variables[OF assms, of "id(k:=l,l:=k)", unfolded this]
  show ?thesis.
qed

text \<open>A rule allowing to get rid of quantifiers when proving that a predicate is a \<open>SetFormulaPredicate\<close>\<close>

lemma sfp_all_rule4 [SFP_rules]: assumes "\<And> m. SetFormulaPredicate (\<lambda> \<Xi>. Q (\<Xi> m) (\<Xi> k1) (\<Xi> k2) (\<Xi> k3) (\<Xi> k4))" 
  shows "SetFormulaPredicate (\<lambda> \<Xi>. \<forall> y. Q y (\<Xi> k1) (\<Xi> k2) (\<Xi> k3) (\<Xi> k4))"
  using SFP_all[OF assms, of "k1+k2+k3+k4+1" "k1+k2+k3+k4+1"] by simp

named_theorems logsimps
lemmas[logsimps] = not_not
lemma reduce_ex [logsimps]: "(\<lambda>\<Xi>. (\<exists>z. Q z \<Xi>)) = (\<lambda>\<Xi>. \<not> (\<forall> z. \<not> (Q z \<Xi>)))"
  by blast
lemma reduce_and [logsimps]: "(\<lambda> \<Xi>. (P \<Xi>) \<and> (Q \<Xi>)) = (\<lambda> \<Xi>. (\<not> ((\<not> (P \<Xi>)) \<or> (\<not> (Q \<Xi>)))))"
  by blast
lemma reduce_imp[logsimps]: "(\<lambda> \<Xi>. (P \<Xi>) \<longrightarrow> (Q \<Xi>)) = (\<lambda> \<Xi>. (\<not> (P \<Xi>) \<or> (Q \<Xi>)))"
  by blast
lemma reduce_iff[logsimps]: "(\<lambda> \<Xi>. (P \<Xi>) \<longleftrightarrow> (Q \<Xi>)) = (\<lambda>\<Xi>. \<not> (\<not> (\<not> P \<Xi> \<or> Q \<Xi>) \<or> \<not> (\<not> Q \<Xi> \<or> P \<Xi>)))"
  unfolding iff_conv_conj_imp unfolding logsimps  by blast
  
lemma SFP_const[intro,simp]: "SetFormulaPredicate (\<lambda>\<Xi>. b)"
  by (induct b) (use SFP_eq[of 0 0] SFP_neg[OF SFP_eq[of 0 0]] in force)+ 

lemma SFP_ex: assumes "SetFormulaPredicate P" shows "SetFormulaPredicate (\<lambda> \<Xi>. (\<exists> z. P (\<Xi> (m := z))))"
  unfolding logsimps by (rule SFP_neg, rule SFP_all, rule SFP_neg, fact)

lemma SFP_replace: assumes "SetFormulaPredicate P" and fresh_m: "\<forall> \<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow>  P \<Xi> = P \<Xi>'"
  shows "SetFormulaPredicate(\<lambda>\<Xi>. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> P (\<Xi> (0:=u,1:=v))))"
proof-
  let ?f = "id(0:= m+1, 1:= m+2)"
  let ?P = "\<lambda> \<Xi>. P (\<Xi>(0 := \<Xi>(m+1),1:=\<Xi>(m+2)))"
  have idsimp: "(\<lambda>n. \<Xi> (?f n)) = \<Xi> (0:= \<Xi>(m+1),1 :=\<Xi>(m+2))" for \<Xi> :: "nat \<Rightarrow> 'a" by fastforce
  have Psimp: "P (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u, 0 := (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u)) (m + 1),1 := (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u)) (m + 2))) 
    = P (\<Xi> (0:=u,1:=v))" for \<Xi> v u z 
    by (rule fresh_m[rule_format]) force    
  have sfp: "SetFormulaPredicate ?P"
    using transform_variables[OF assms(1), of ?f] unfolding idsimp.
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<not> \<Xi> (m+1) \<epsilon> \<Xi> m \<or> \<not> ?P \<Xi>)"
    by (rule SFP_rules)+ fact
  from SFP_all[OF this, of "m+1", simplified fun_upd_same fun_upd_other]
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>z. \<not> z \<epsilon> \<Xi> m \<or> \<not> ?P (\<Xi>(m + 1 := z)))"
    unfolding logsimps by simp
  have "SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> (m+2) \<epsilon> \<Xi> (m+3)) = (\<exists>u. u \<epsilon> \<Xi> m \<and> ?P (\<Xi>(m+1 := u))))"
    unfolding logsimps by (rule SFP_rules | fact)+
  from SFP_all[OF this, of "m+2", simplified fun_upd_same fun_upd_other]
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>a. (a \<epsilon> \<Xi> (m + 3)) = (\<exists>u. u \<epsilon> \<Xi> m \<and> ?P (\<Xi>(m + 2 := a, m + 1 := u))))" by simp
  note aux = SFP_all[OF SFP_neg[OF this], of "m+3", simplified fun_upd_same fun_upd_other]
  have " SetFormulaPredicate
   (\<lambda>\<Xi>. \<exists> z. (\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> ?P (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u)))))"
    unfolding logsimps using SFP_neg[OF aux[unfolded logsimps]] by simp  
  then show "SetFormulaPredicate (\<lambda>\<Xi>. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> P (\<Xi>(0 := u, 1 := v))))"
    unfolding Psimp.
qed

text \<open>A (binary) relation is set-theoretically definable if the predicate it defines by assigning values to variables \<open>x\<^sub>0\<close> and \<open>x\<^sub>1\<close> is set-theoretically definable. 
The value of the relation therefore cannot depend on other variables than \<open>x\<^sub>0\<close> and \<open>x\<^sub>1\<close>. In other words, if a formula \<open>\<phi>\<close> defining a set-theoretically definable relation contains a free variable \<open>x\<^sub>k, 1 < k\<close>, then it is equivalent to \<open>\<forall> x\<^sub>k. \<phi>\<close> \<close>

definition SetRelation :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where
   "SetRelation P \<equiv> SetFormulaPredicate (\<lambda> \<Xi>. P (\<Xi> 0) (\<Xi> 1))"

text \<open>A set-theoretically definable property is defined similarly.\<close>

definition SetProperty :: "('a \<Rightarrow>  bool) \<Rightarrow> bool"
  where
   "SetProperty P \<equiv> SetFormulaPredicate (\<lambda> \<Xi>. P (\<Xi> 0))"

subsubsection \<open>Auxiliary proofs for specific useful set-relations and set-properties\<close>

lemma SR_neg[simp, intro]: "SetRelation P \<Longrightarrow> SetRelation (\<lambda> x y. \<not> P x y)"
  unfolding SetRelation_def by (rule SFP_rules)

lemma SR_sym[simp, intro]: assumes "SetRelation P" shows "SetRelation (\<lambda> x y. P y x)"
  using swap_variables[OF assms[unfolded SetRelation_def], of 0 1, simplified fun_upd_same fun_upd_other]
  unfolding SetRelation_def.

lemma SR_neq[simp]: "SetRelation (\<noteq>)"
  unfolding SetRelation_def using SFP_eq SFP_neg by blast

lemma SP_const[simp]: "SetProperty (\<lambda> x. b)"
  unfolding SetProperty_def using SFP_const.
     
lemma SP_neg[simp, intro]: "SetProperty P \<Longrightarrow> SetProperty (\<lambda> x. \<not> P x)"
  unfolding  SetProperty_def using SFP_neg. 

lemma SP_tarski[simp]: "SetProperty tarski_fin"
  unfolding SetProperty_def  logsimps set_defs by (rule SFP_rules)+

lemma SP_setsuc[simp]: "SetProperty is_sucM"
  unfolding SetProperty_def  logsimps set_defs by (rule SFP_rules)+

lemma SP_nat[simp]: "SetProperty natM"
  unfolding SetProperty_def  logsimps set_defs by (rule SFP_rules)+

lemma empty_mem_ord': assumes "ordM x" "\<exists> z. z \<epsilon> x" 
  shows "\<exists> emp. (\<forall> u. \<not> u \<epsilon> emp) \<and> emp \<epsilon> x" 
proof-
  obtain u where "u \<epsilon> x" "\<forall> y. y \<epsilon> u \<longrightarrow> \<not> y \<epsilon> x"
    using \<open>ordM x\<close>  \<open>\<exists> z. z \<epsilon> x\<close> ordM_def regular_def subsetM_refl by metis
  have "y \<epsilon> u \<longrightarrow> y \<epsilon> x" for y
    using \<open>ordM x\<close> \<open>u \<epsilon> x\<close> ordM_D1 subsetM_def by blast 
  hence "\<not> y \<epsilon> u" for y
    using \<open>\<forall> y. y \<epsilon> u \<longrightarrow> \<not> y \<epsilon> x\<close> by simp
  then show ?thesis
    using \<open>u \<epsilon> x\<close> by blast  
qed

end

section \<open>Axiomatizations of hereditarily finite sets\<close>

subsection \<open>Finiteness axioms\<close>

text \<open>The aim of each of the axioms is to guarantee that each element of the domain will be finite.\<close>

text \<open>Usual axiom: there is no inductive set.\<close>
locale L_fin = set_signature + 
   assumes fin: "\<not> (\<exists> x. \<emptyset> \<epsilon> x \<and> (\<forall> y. y \<epsilon> x \<longrightarrow> setsucM y y \<epsilon> x))"

text \<open>Induction schema for set formulas, a.k.a. set induction schema or just set induction. 
Not to be confused with epsilon induction.\<close>
locale L_setind = set_signature +
  assumes setind: "\<And> P. SetFormulaPredicate P \<Longrightarrow> 
    P(\<Xi>(0:= \<emptyset>)) \<longrightarrow> (\<forall> x y. P(\<Xi>(0:= x)) \<longrightarrow> P (\<Xi>(0:= setsucM x y))) \<longrightarrow> (\<forall> x. P(\<Xi>(0:= x)))"
begin

lemma setind_SP:   assumes "SetProperty P" and "P \<emptyset>" and step:  "\<forall> x y. P x \<longrightarrow> P (setsucM x y)"
  shows  "P x"
  using setind[of "\<lambda> \<Xi>. P (\<Xi> 0)", folded SetProperty_def, OF assms(1), simplified] \<open>P \<emptyset>\<close> step by blast  

lemma setind_var:   assumes "SetFormulaPredicate P" "P(\<Xi>(n:= \<emptyset>))" and step: "\<forall> x y. P(\<Xi>(n:= x)) \<longrightarrow> P (\<Xi>(n:= setsucM x y))"
  shows "P(\<Xi>(n:= x))"
proof-
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m_def: "P \<Xi> = P \<Xi>'" if "\<forall>i<m. \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  let ?f = "id(0 := Suc (n + m), n:= 0)"
  let ?Q = "\<lambda> \<Xi>. (P (\<lambda> b. \<Xi> (?f  b)))"
  let ?X = "\<Xi>(Suc (n + m):= \<Xi> 0)"
  have sfpq:  "SetFormulaPredicate ?Q"
    using transform_variables[OF \<open>SetFormulaPredicate P\<close>] by simp
  have small: "\<forall> i < m. (?X (0 := u)) (?f i) = (\<Xi>(n := u)) i" for u
    by auto
  have equiv: "(?Q (?X (0 := u))) \<longleftrightarrow> (P (\<Xi>(n := u)))" for u
    by (rule m_def[of  "\<lambda> b. (?X (0 := u))(?f b)" "\<Xi>(n := u)"]) (rule small) 
  show "P(\<Xi>(n:= x))"
   unfolding equiv[symmetric]
   by (rule setind[rule_format, OF sfpq, of ?X], unfold equiv)
   (use assms in blast)+
qed

end

locale L_dedekind = set_signature + 
   assumes dedekind: "\<forall> x. dedekind_fin x"

locale L_tarski = set_signature + 
  assumes tarski: "\<forall> y. tarski_fin y"

subsection Extensionality

locale L_setext = set_signature +
  assumes setext: "x = y \<longleftrightarrow> (\<forall> z. z \<epsilon> x \<longleftrightarrow> z \<epsilon> y)"

begin

text \<open>set in HOL is defined as a class. Therefore, the following comprehension is an axiom.\<close>
lemma "x \<in> {u. P u} \<longleftrightarrow> P x"
   using mem_Collect_eq.

text \<open>In case of (our) M-sets, only uniqueness, not existence is guaranteed by extensionality.\<close>

lemma collect_def': 
  assumes "\<forall> u. (u \<epsilon> w \<longleftrightarrow> Q u)"
  shows "collectM Q = w"
proof-
  let ?P = "\<lambda> z. (\<forall> u. u \<epsilon> z \<longleftrightarrow> Q u)"
  have unique: "z' = w" if "?P z'" for z'
    unfolding setext[rule_format, of z' w] 
    using that assms by blast
  then show ?thesis
    using theI[of ?P w, OF assms unique] unfolding collectM_def by blast 
qed

lemma collect_def_ex: \<comment> \<open>A formulation useful in proofs\<close>
  assumes "\<exists> w. \<forall> u . (u \<epsilon> w \<longleftrightarrow> Q u)"
  shows "u \<epsilon> collectM Q \<longleftrightarrow> Q u"
  using assms collect_def' assms by auto

lemma proper_subset_diff[simp] : "y \<subset>\<^sub>M x \<Longrightarrow> \<exists> z. z \<epsilon> x \<and> \<not> z \<epsilon> y" 
  unfolding proper_subsetM_def setext by blast

lemma subsetM_antisym: "y \<subseteq>\<^sub>M x \<Longrightarrow> x \<subseteq>\<^sub>M y \<Longrightarrow> x = y" 
  unfolding subsetM_def setext by blast

lemma proper_subsetM_trans[simp]: assumes "x \<subset>\<^sub>M y" "y \<subset>\<^sub>M z" shows "x \<subset>\<^sub>M z"
proof (unfold proper_subsetM_def, rule conjI)
  show "(\<forall> u. u \<epsilon> x \<longrightarrow> u \<epsilon> z)"
    using assms proper_subsetM_def by simp
  show "x \<noteq> z"
    by (rule notI) (use assms proper_subsetM_def  setext[of z y] in auto)
qed

lemma emptyset_mem_ord: assumes "ordM x" "\<exists> z. z \<epsilon> x" shows "\<emptyset> \<epsilon> x"
  using empty_mem_ord'[OF assms] collect_def'[of _ "\<lambda> x. x \<noteq> x"] emptysetM_def by force

end                                                        
                                             
subsection \<open>Empty set\<close>  

locale L_empty = set_signature + 
  assumes empty: "\<exists> x. \<forall> y. (\<not> y \<epsilon> x)"

text \<open>Since the empty set is defined@{term collectM}, and hence Hilbert's @{term The}, nothing useful can be said about \<open>\<emptyset>\<close> without extensionality.\<close>
locale L_setext_empty = L_setext + L_empty

begin

\<comment> \<open>Here we can already prove that @{term \<emptyset>}, has the intended meaning.\<close>
lemma empty_is_empty[simp]: "\<forall> y. (\<not> y \<epsilon> \<emptyset>)"
proof-
  have ex: "\<exists> x. \<forall> z. z \<epsilon> x \<longleftrightarrow> z \<noteq> z"
    using empty by auto
  from collect_def_ex[OF this, folded emptysetM_def]
  show ?thesis 
    unfolding emptysetM_def collectM_def by auto
qed

lemma emptyset_def'[set_defs]: "x = \<emptyset> \<longleftrightarrow> (\<forall> u. \<not> u \<epsilon> x)"
  unfolding setext by simp

lemma empty_mem_false [set_defs]: "u \<epsilon> \<emptyset> \<longleftrightarrow> False"
  using emptyset_def'  by simp

lemma setsuc_empty_sing:  "setsucM \<emptyset> x = {x}\<^sub>M"
  unfolding singletonM_def setsucM_def empty_mem_false by simp

lemma SFP_empty_n [simp]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> n = \<emptyset>)"
  unfolding SetProperty_def  logsimps set_defs by (rule SFP_rules)+

lemma SP_empty[simp]: "SetProperty (\<lambda>x. x = \<emptyset>)"
  unfolding SetProperty_def by simp

lemma SFP_empty_n' [simp]: "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>u. \<not> u \<epsilon> \<Xi> n)"
  using SFP_empty_n emptyset_def' by simp

lemma empty_dedekind[simp]: shows "dedekind_fin \<emptyset>"
  unfolding dedekind_fin_def set_defs by auto

lemma subset_of_empty[simp]: "u \<subseteq>\<^sub>M \<emptyset> \<longleftrightarrow> u = \<emptyset>"
  unfolding subsetM_def emptyset_def' by simp

lemma empty_tarski[simp]: shows "tarski_fin \<emptyset>"
  unfolding tarski_fin_def proper_subsetM_def by auto

lemma nemp_setI[intro]: "x \<epsilon> y \<Longrightarrow> y \<noteq> \<emptyset>"
  by force

lemma nemp_setI_ex: "\<exists> x. x \<epsilon> y \<Longrightarrow> y \<noteq> \<emptyset>"
  by force

lemma empty_is_subset: "\<emptyset> \<subseteq>\<^sub>M A"
  unfolding subsetM_def by force

lemma empty_regular[simp]: "regular \<emptyset>"
  unfolding regular_def by simp

lemma empty_trans[simp]: "transM \<emptyset>"
  unfolding transM_def by simp

lemma emp_natM[simp]: "natM \<emptyset>"
  by (simp add: natM_def ordM_def epschain_def) 

lemma binunion_emp[simp]: "\<emptyset> \<union>\<^sub>M t = t" "t \<union>\<^sub>M \<emptyset> = t"
  unfolding setext[of _ t] binunionM_def using empty_is_empty
    collect_def'[of t "\<lambda> u. u \<epsilon> t"] by simp_all

end

subsection \<open>Set pair\<close>

text \<open>Pairing is a simple set construction which can be easily obtained by set successor and empty set. It is interesting on its own, in particular in a context without the empty set axiom.\<close>

locale L_pair = set_signature + 
  assumes pair: "\<forall> x y. \<exists> z. \<forall> v. v \<epsilon> z \<longleftrightarrow> v = x \<or> v = y"

locale L_setext_pair = L_setext + L_pair

begin

lemma singleton_def'[set_defs]: "u \<epsilon> {y}\<^sub>M \<longleftrightarrow>  u = y"
proof-
  have "\<exists> x. \<forall> u. u \<epsilon> x \<longleftrightarrow>  u = y" 
    using pair by meson
  from collect_def_ex[OF this[rule_format], folded singletonM_def]
  show ?thesis.
qed

lemma singleton_eq[set_defs]: "u = {y}\<^sub>M \<longleftrightarrow>  (\<forall> v. v \<epsilon> u \<longleftrightarrow> v = y)"
  unfolding setext  set_defs by blast

lemma pair_def'[set_defs]: "u \<epsilon> {x,y}\<^sub>M \<longleftrightarrow> u = x \<or> u = y"
  using collect_def_ex[OF pair[rule_format], folded pairM_def].

lemma pair_eq [set_defs]: "w = {x,y}\<^sub>M \<longleftrightarrow> (\<forall> u. (u \<epsilon> w) \<longleftrightarrow>  u = x \<or> u = y)"
  unfolding setext[of w] set_defs by simp 

lemma regular_not_self_mem: assumes "regular x" shows "\<not> x \<epsilon> x"
proof
  assume "x \<epsilon> x"
  with assms[unfolded regular_def, rule_format, of "{x}\<^sub>M"]
  show False
    unfolding subsetM_def singleton_def' by blast
qed

lemma ordered_pair_unique[simp]: "\<langle>u,v\<rangle> = \<langle>u',v'\<rangle> \<longleftrightarrow> u = u' \<and> v = v'"
  unfolding setext[of "{_,_}\<^sub>M"] ordered_pairM_def using pair_def' singleton_def' by metis 

lemma sing_eq_iff: "{a}\<^sub>M = {b}\<^sub>M \<longleftrightarrow> a = b"
  unfolding setext[of "{_}\<^sub>M"] singleton_def' by metis 

lemma sing_eq_pair_iff: "{a}\<^sub>M = {b,c}\<^sub>M \<longleftrightarrow> a = b \<and> b = c" 
  unfolding setext[of "{_}\<^sub>M"] pair_def' singleton_def' by metis 

lemma sing_eq_pair_iff': "{b,c}\<^sub>M = {a}\<^sub>M \<longleftrightarrow> a = b \<and> b = c" 
  using sing_eq_pair_iff by metis

lemma SFP_mem_ordered_pair[SFP_rules]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k \<epsilon> \<langle>\<Xi> l, \<Xi> m\<rangle>)"
  unfolding ordered_pairM_def set_defs logsimps by (rule SFP_rules)+

lemma SFP_eq_ordered_pair [SFP_rules]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k = \<langle>\<Xi> l,\<Xi> m\<rangle>)"
  unfolding setext logsimps by (rule SFP_rules)+

lemma SFP_ordered_pair_mem[SFP_rules]: "SetFormulaPredicate (\<lambda>\<Xi>. \<langle>\<Xi> k,\<Xi> l\<rangle> \<epsilon> \<Xi> m)"
proof-
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<exists> u. u = \<langle>\<Xi> k,\<Xi> l\<rangle> \<and> u \<epsilon> \<Xi> m)"
    unfolding setext logsimps by (rule SFP_rules)+
  thus ?thesis
    by simp
qed   

end

subsection \<open>Set successor\<close>

text \<open>Also known as adjunction. Enables constructing sets in steps. This axiom plays an important role in the fragment of set theory axiomatized by extensionality, empty set and set successor (see  \<open>L_setext_empty_setsuc\<close> below), mutually interpretable with Robinson's arithmetic Q.\<close>

locale L_setsuc = set_signature + 
  assumes setsuc: "\<forall> x y. \<exists> z. \<forall> u. u \<epsilon> z \<longleftrightarrow> u \<epsilon> x \<or> u = y"


locale L_setext_setsuc  = L_setext + L_setsuc 
\<comment> \<open>some statements  do not need the empty set\<close>

begin

lemma setsuc_def'[set_defs, simp]: "u \<epsilon> setsucM x y \<longleftrightarrow> (u \<epsilon> x \<or> u = y)"
  using collect_def_ex[OF setsuc[rule_format]] unfolding setsucM_def.

lemma setsuc_triv[simp]: "y \<epsilon> x \<Longrightarrow> setsucM x y = x"
   unfolding setext[of _ x] setsuc_def' by blast

lemma is_suc_def': "is_sucM x \<longleftrightarrow> (\<exists> y. x = setsucM y y)"
  unfolding is_sucM_def setsuc_def' setext..

lemma trans_suc_trans: "transM  x \<Longrightarrow> transM (setsucM x x)"
  unfolding transM_def set_defs by blast

lemma epschain_suc_epschain: "epschain  x \<Longrightarrow> epschain (setsucM x x)"
  unfolding epschain_def  using trans_suc_trans
  using setsuc_def' by auto

lemma ord_pred_fun: assumes "ordM x" "ordM y" "setsucM x x = setsucM y y" 
  shows "x = y"
  using assms unfolding setext[of x] setext[of "setsucM x x"] set_defs by metis

lemma SFP_setsuc_mem[SFP_rules]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k \<epsilon> setsucM (\<Xi> l) (\<Xi> m))"
  unfolding  setsuc_def'  by (rule SFP_rules)+ 

lemma SFP_setsuc_eq[SFP_rules]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = setsucM (\<Xi> l) (\<Xi> m))"
  unfolding setsuc_def' setext logsimps by (rule SFP_rules)+ 

end

locale L_empty_setsuc  = L_empty + L_setsuc 
\<comment> \<open>some statements do not need extensionality\<close>

begin

sublocale L_pair
proof (unfold_locales, rule allI, rule allI)
  fix x y
  obtain empty where emp: "\<forall> u. \<not> u \<epsilon> empty"
    using empty by blast
  obtain sing where "\<forall> u. u \<epsilon> sing \<longleftrightarrow>  u = x"
    using setsuc[rule_format, of empty x] emp by blast
  then obtain pair where "\<forall>v. (v \<epsilon> pair) = (v = x \<or> v = y)" 
    using setsuc[rule_format, of sing y] by blast
  then show "\<exists>z. \<forall>v. (v \<epsilon> z) = (v = x \<or> v = y)"
    by blast
qed

lemma singleton_setsuc: shows "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z"
proof-
  obtain emp where "\<forall> u. \<not> u \<epsilon> emp"
    using empty by blast 
  then show ?thesis
    using setsuc[rule_format, of emp z] by blast 
qed

lemma pair_setsuc: shows "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2"
proof-
  obtain z1 where "\<forall> u. u \<epsilon> z1 \<longleftrightarrow> u = z\<^sub>1"
    using singleton_setsuc by blast 
  then show ?thesis
    using setsuc[rule_format, of z1 z\<^sub>2] by simp
qed

lemma triple_setsuc:  shows "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2 \<or> u = z\<^sub>3"
proof-
  obtain z2 where "\<forall> u. u \<epsilon> z2 \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2"
    using pair_setsuc by blast 
  then show ?thesis
    using setsuc[rule_format, of z2 z\<^sub>3] by simp
qed

lemma regular_antisym_mem: assumes "regular x" "z\<^sub>1 \<epsilon> x" "z\<^sub>2 \<epsilon> x" shows "\<not> (z\<^sub>1 \<epsilon> z\<^sub>2 \<and> z\<^sub>2 \<epsilon> z\<^sub>1)"
proof
  obtain pair where pair: "\<forall> u. u \<epsilon> pair \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2"
    using pair_setsuc by blast
  assume "z\<^sub>1 \<epsilon> z\<^sub>2 \<and> z\<^sub>2 \<epsilon> z\<^sub>1"
  with \<open>regular x\<close>[unfolded regular_def, rule_format, of pair]
  show False
     unfolding subsetM_def using \<open>z\<^sub>1 \<epsilon> x\<close> \<open>z\<^sub>2 \<epsilon> x\<close> pair by auto 
qed

lemma regular_antisym2_mem: assumes "regular x" "z\<^sub>1 \<epsilon> x" "z\<^sub>2 \<epsilon> x" "z\<^sub>3 \<epsilon> x" shows "\<not> (z\<^sub>1 \<epsilon> z\<^sub>2 \<and> z\<^sub>2 \<epsilon> z\<^sub>3 \<and> z\<^sub>3 \<epsilon> z\<^sub>1)"
proof
  obtain triple where triple: "\<forall> u. u \<epsilon> triple \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2 \<or> u = z\<^sub>3"
    using triple_setsuc by blast
  assume "z\<^sub>1 \<epsilon> z\<^sub>2 \<and> z\<^sub>2 \<epsilon> z\<^sub>3 \<and> z\<^sub>3 \<epsilon> z\<^sub>1"
  with \<open>regular x\<close>[unfolded regular_def, rule_format, of triple]
  show False
     unfolding subsetM_def using \<open>z\<^sub>1 \<epsilon> x\<close> \<open>z\<^sub>2 \<epsilon> x\<close> \<open>z\<^sub>3 \<epsilon> x\<close> triple by auto 
qed

lemma ord_mem_ord: assumes  "ordM v" "u \<epsilon> v" shows "ordM u"
  unfolding ordM_def epschain_def conj_assoc[symmetric]
proof (rule conjI, rule conjI)
  have "regular v" "u \<subseteq>\<^sub>M v"
    using \<open>ordM v\<close> ordM_D1 \<open>u \<epsilon> v\<close> ordM_def by blast+
  then show "regular u"
    unfolding regular_def using subsetM_trans[OF _ \<open>u \<subseteq>\<^sub>M v\<close>] by blast
  have "u \<subseteq>\<^sub>M v" "epschain v" "regular v" "transM v"
    using assms unfolding natM_def ordM_def transM_def epschain_def by blast+
  thus "\<forall>y z. y \<epsilon> u \<and> z \<epsilon> u \<longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y"
    using \<open>ordM v\<close> unfolding ordM_def subsetM_def epschain_def by blast
  show "transM u"
    unfolding transM_def set_defs
  proof (rule allI, rule impI, rule allI, rule impI)
    fix z y
    assume "y \<epsilon> u" "z \<epsilon> y"
    hence "z \<epsilon> v" "y \<epsilon> v" 
      using \<open>u \<epsilon> v\<close> \<open>transM v\<close> unfolding transM_def set_defs by blast+
    have "u \<noteq> z"
      using regular_antisym_mem[OF \<open>regular v\<close> \<open>y \<epsilon> v\<close> \<open>z \<epsilon> v\<close>] \<open>y \<epsilon> u\<close> \<open>z \<epsilon> y\<close> by blast
    have "\<not> u \<epsilon> z"
      using regular_antisym2_mem[OF \<open>regular v\<close> \<open>u \<epsilon> v\<close> \<open>z \<epsilon> v\<close> \<open>y \<epsilon> v\<close>] \<open>y \<epsilon> u\<close> \<open>z \<epsilon> y\<close> by blast
    show "z \<epsilon> u"
      using ordM_D2[OF \<open>ordM v\<close> \<open>u \<epsilon> v\<close> \<open>z \<epsilon> v\<close>] \<open>u \<noteq> z\<close> \<open>\<not> u \<epsilon> z\<close> by blast
  qed
qed   

end

locale L_setext_empty_setsuc  = L_setext + L_empty + L_setsuc 

begin

sublocale L_setext_empty
 by unfold_locales

sublocale L_setext_setsuc
  by unfold_locales

sublocale L_empty_setsuc
  by unfold_locales

sublocale L_setext_pair
  by unfold_locales

lemma empty_mem_ord: assumes "ordM x" "x \<noteq> \<emptyset>" shows "\<emptyset> \<epsilon> x"
proof-
  have "\<exists> z. z \<epsilon> x"
    using \<open>x \<noteq> \<emptyset>\<close>  by (simp add: setext) 
  then obtain u where "u \<epsilon> x" "\<forall> y. y \<epsilon> u \<longrightarrow> \<not> y \<epsilon> x"
    using \<open>ordM x\<close>  ordM_def regular_def subsetM_refl by metis
  have "y \<epsilon> u \<longrightarrow> y \<epsilon> x" for y
    using \<open>ordM x\<close> \<open>u \<epsilon> x\<close> ordM_D1 subsetM_def by blast 
  hence "u = \<emptyset>"
    using \<open>\<forall> y. y \<epsilon> u \<longrightarrow> \<not> y \<epsilon> x\<close>
    by (simp add: emptyset_def') 
  then show "\<emptyset> \<epsilon> x"
    using \<open>u \<epsilon> x\<close> by blast  
qed

lemma SP_injective [simp]: "SetProperty (\<lambda>x. \<forall>a b c. \<langle>b,a\<rangle> \<epsilon> x \<and> \<langle>c,a\<rangle> \<epsilon> x \<longrightarrow> b = c)"
  unfolding set_defs logsimps SetProperty_def by (rule SFP_rules)+

lemma SP_unique_image [simp]: "SetProperty (\<lambda>x. \<forall>a b c. \<langle>a,b\<rangle> \<epsilon> x \<and> \<langle>a,c\<rangle> \<epsilon> x \<longrightarrow> b = c)"
  unfolding set_defs logsimps SetProperty_def by (rule SFP_rules)+

lemma SFP_compose [simp,intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<exists>a b c. \<langle>a,b\<rangle> \<epsilon> \<Xi> k \<and> \<langle>b,c\<rangle> \<epsilon> \<Xi> l \<and> \<Xi> m = \<langle>a,c\<rangle>)"
proof-
  have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. \<langle>\<Xi> (k+l+m+3),\<Xi> (k+l+m+4)\<rangle> \<epsilon> \<Xi> k \<and> \<langle>\<Xi> (k+l+m+4),\<Xi> (k+l+m+5)\<rangle> \<epsilon> \<Xi> l \<and> \<Xi> m = \<langle>\<Xi> (k+l+m+3), \<Xi> (k+l+m+5)\<rangle>)"
    unfolding logsimps by (rule SFP_rules)+
  show ?thesis
    using SFP_ex[OF SFP_ex[OF SFP_ex], of _ "k+l+m+3" "k+l+m+4" "k+l+m+5", OF sfp] by simp 
qed

lemma SP_function[simp]: "SetProperty (\<lambda> x. functionM x)"
  unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+

lemma SP_one_one[simp]: "SetProperty (\<lambda> x. one_oneM x)"
  unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+

lemma dom_SR [simp]: "SetRelation (\<lambda>x u. \<exists>w. x = \<langle>u,w\<rangle>)"
      unfolding SetRelation_def logsimps by (rule SFP_rules)+

lemma rng_SR [simp]: "SetRelation (\<lambda>x u. \<exists>w. x = \<langle>w,u\<rangle>)"
      unfolding SetRelation_def logsimps by (rule SFP_rules)+

end 

locale L_binunion = set_signature + 
  assumes binunion: "\<forall> x y. \<exists> z. \<forall> v. v \<epsilon> z \<longleftrightarrow> (v \<epsilon> x \<or> v \<epsilon> y)"

locale L_setext_binunion = L_setext + L_binunion 

begin

lemma binunion_def'[set_defs]: "u \<epsilon> x \<union>\<^sub>M y \<longleftrightarrow> u \<epsilon> x \<or> u \<epsilon> y"
  unfolding binunionM_def
  using collect_def_ex[OF binunion[rule_format], of u]
  by force


end

locale L_setext_pair_binunion = L_setext + L_pair + L_binunion
\<comment> \<open>A specific minimalist combination of axioms that guarantees the existence of both ordered pair and set successor\<close>

begin

sublocale L_setext_binunion
  by unfold_locales

sublocale L_setext_pair
  by unfold_locales

sublocale  L_setsuc
proof (unfold_locales, (rule allI)+, rule exI, rule allI)
  show "u \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<longleftrightarrow> (u \<epsilon> x \<or> u = y)" for x y u 
    unfolding binunion_def' singleton_def' by blast
qed

sublocale L_setext_setsuc
  by unfold_locales

lemma SFP_ordered_pair_setsuc_eq[SFP_rules]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = \<langle>\<Xi> l, setsucM (\<Xi> m) (\<Xi> n)\<rangle>)"
proof-
\<comment>\<open>An explicit proof avoiding too many quantifiers, beyond reach of @{thm sfp_all_rule4}\<close>
  let ?Q = "\<lambda> \<Xi>. \<Xi> (m+n+l+k+1) = setsucM (\<Xi> m) (\<Xi> n) \<and> \<Xi> k = \<langle>\<Xi> l,\<Xi> (m+n+l+k+1)\<rangle>"
  thm SFP_ex[of ?Q "m+n+l+k+1", simplified]
  show ?thesis
    by (rule SFP_ex[of ?Q "m+n+l+k+1", simplified], unfold logsimps) (rule SFP_rules)+
qed

end

subsection Regularity

locale  L_reg = set_signature +
  assumes reg: "\<forall> x. (\<exists> y. y \<epsilon> x) \<longrightarrow> (\<exists> y. y \<epsilon> x \<and> (\<forall> v. \<not> (v \<epsilon> y \<and> v \<epsilon> x)))"

begin

lemma any_reg[simp]: "regular x"
  using reg unfolding regular_def by blast

text \<open>Note that \<open>\<not> x \<epsilon> x\<close> cannot be proved without existence of a singleton.\<close>

end

lemma (in set_signature) reg_all_regular_iff:
  "L_reg (\<epsilon>) \<longleftrightarrow> (\<forall> x. regular x)"
proof
  assume "L_reg (\<epsilon>)"
  then interpret L_reg "(\<epsilon>)".
  show "\<forall> x. regular x"
    using reg unfolding regular_def by blast
next
  assume all_reg: "\<forall> x. regular x"
  show "L_reg (\<epsilon>)"
    by unfold_locales (meson all_reg regular_def set_signature.subsetM_refl)  
qed

text \<open>Schema of regularity\<close>
locale L_regsch = set_signature +
  assumes regsch: "SetFormulaPredicate P \<Longrightarrow> (\<exists> x. P (\<Xi> (0:=x))) \<longrightarrow>  (\<exists> x. P (\<Xi> (0:=x)) \<and> (\<forall> y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi> (0:=y))))"

begin

text \<open>\<open>regsch\<close> is stronger than normal regularity in the absence of infinity axiom, since one cannot prove the existence of transitive supersets/closures. See \<open>not_reg_setind_implies_regsch\<close> in\<open>ZFfin_regsch_model.thy\<close>\<close>

sublocale L_reg
proof
  have SFP: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<epsilon> \<Xi> 1)"
    by (rule SFP_rules)
  show "\<forall>x. (\<exists>y. y \<epsilon> x) \<longrightarrow> (\<exists>y. y \<epsilon> x \<and> (\<forall>v. \<not> (v \<epsilon> y \<and> v \<epsilon> x)))" 
    using regsch[OF SFP, unfolded fun_upd_apply] by force
qed

lemma regsch_epsind:
   "SetFormulaPredicate Q \<Longrightarrow> (\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> Q (\<Xi> (0:=y))))  \<longrightarrow>  Q (\<Xi> (0:=x))) \<longrightarrow>  (\<forall> x. Q (\<Xi> (0:=x)))"
  using regsch[of "\<lambda> x. \<not> Q x" \<Xi>] using SFP_neg by blast 

lemma regsch_mem_not_refl: "\<not> u \<epsilon> u"
proof
  assume "u \<epsilon> u"
  hence ex: "\<exists>x. (undefined(1 := u, 0 := x)) 0 = (undefined(1 := u, 0 := x)) 1"
    by force
  have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. (\<Xi> 0) = (\<Xi> 1))"
    by (rule SFP_rules)
  from regsch[of "\<lambda> \<Xi>. (\<Xi> 0) = (\<Xi> 1)", rule_format, OF sfp ex]
  show False
    using \<open>u \<epsilon> u\<close> by auto
qed

end 

text \<open>Epsilon induction schema is logically equivalent to the regularity schema (that is, regardless of what \<open>\<epsilon>\<close> means), see @{thm abstract_foundation_iff} above.\<close>

locale L_epsind = set_signature + 
  assumes epsind: "SetFormulaPredicate Q \<Longrightarrow> (\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> Q (\<Xi> (0:=y))))  \<longrightarrow>  Q (\<Xi> (0:=x))) \<longrightarrow>  (\<forall> x. Q (\<Xi> (0:=x)))"

begin

lemma epsind_regsch: assumes "SetFormulaPredicate P" "\<exists> x. P (\<Xi> (0:=x))" 
  shows "\<exists> x. P (\<Xi> (0:=x)) \<and> (\<forall> y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi> (0:=y)))"   
proof-
  have SP: "SetFormulaPredicate (\<lambda> x. \<not> P x)"
    using \<open>SetFormulaPredicate P\<close> by (simp add: SFP_rules)
  show ?thesis
    unfolding  abstract_foundation_iff[of "\<lambda> x. \<forall> y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0:=y))" "\<lambda> x. \<not> P (\<Xi>(0:=x))", unfolded not_not]
    using  epsind[OF SP, rule_format, of \<Xi>] \<open>\<exists> x. P (\<Xi> (0:=x))\<close>
    by blast+
qed

sublocale L_regsch
  using epsind_regsch by unfold_locales blast

end 

subsection Separation

text \<open>Separation is often an alternative to set successor. It allows one to construct ``from above'' many sets that set successor builds ``from below''.\<close>

locale L_sep = set_signature + 
  assumes sep: "SetFormulaPredicate P \<Longrightarrow> \<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P (\<Xi>(0:= u)))" 

begin

sublocale L_empty
  by unfold_locales (use sep[OF SFP_const[of False]] in force) 

lemma sep_var: assumes "SetFormulaPredicate P" shows "\<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P (\<Xi>(n:= u)))"
  using sep[OF swap_variables, OF assms, of "\<Xi>(n:= \<Xi> 0)" n 0]
  by (cases "n = 0", simp) (simp del: neq0_conv add: fun_upd_twist[of n 0])

lemma sep_SP: assumes "SetProperty P" shows "\<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P u)" 
  using sep[OF assms[unfolded SetProperty_def]] by simp

lemma sep_SR: assumes "SetRelation P" shows "\<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P u r)" 
  using sep[OF assms[unfolded SetRelation_def]] by simp

lemma singleton_sep: assumes "z \<epsilon> x"
  shows "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z"
  using sep[rule_format, of "\<lambda>\<Xi>. \<Xi> 0 = \<Xi> 1" x "undefined(1:=z)", OF SFP_eq, unfolded fun_upd_apply] assms by auto

lemma pair_sep: assumes "z\<^sub>1 \<epsilon> x" "z\<^sub>2 \<epsilon> x"
  shows "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2"
proof-
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 = \<Xi> 1 \<or> \<Xi> 0 = \<Xi> 2)"
    by (rule SFP_rules)+
  from sep[rule_format, OF this, of x "undefined(1:=z\<^sub>1,2:=z\<^sub>2)", simplified]
  show "\<exists>y. \<forall>u. (u \<epsilon> y) = (u = z\<^sub>1 \<or> u = z\<^sub>2)"
    using assms by blast
qed

lemma triple_sep: assumes "z\<^sub>1 \<epsilon> x" "z\<^sub>2 \<epsilon> x" "z\<^sub>3 \<epsilon> x"
  shows "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2 \<or> u = z\<^sub>3"
proof-
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 = \<Xi> (Suc 0) \<or> \<Xi> 0 = \<Xi> 2 \<or> \<Xi> 0 = \<Xi> 3)"
    by (rule SFP_rules)+
  from sep[rule_format, OF this, of x "undefined(1:=z\<^sub>1,2:=z\<^sub>2,3:=z\<^sub>3)", simplified] 
  show "\<exists> y. \<forall> u. u \<epsilon> y \<longleftrightarrow> u = z\<^sub>1 \<or> u = z\<^sub>2 \<or> u = z\<^sub>3" 
    using assms by blast    
qed

lemma regular_not_self_mem_sep: assumes "regular x" shows "\<not> x \<epsilon> x"
proof
  assume "x \<epsilon> x"
  then obtain t where t: "\<forall> u. u \<epsilon> t \<longleftrightarrow> u = x"
    using singleton_sep by blast 
  from assms[unfolded regular_def, rule_format, of t]
  show False
    unfolding subsetM_def t[rule_format] using \<open>x \<epsilon> x\<close> by blast 
qed

lemma regular_antisym_mem_sep: assumes "regular x" "y\<^sub>1 \<epsilon> x" "y\<^sub>2 \<epsilon> x" shows "\<not> (y\<^sub>1 \<epsilon> y\<^sub>2 \<and> y\<^sub>2 \<epsilon> y\<^sub>1)"
proof
  obtain t where t: "\<forall> u. u \<epsilon> t \<longleftrightarrow> u = y\<^sub>1 \<or> u = y\<^sub>2"
    using pair_sep[OF assms(2-)] by blast
  assume "y\<^sub>1 \<epsilon> y\<^sub>2 \<and> y\<^sub>2 \<epsilon> y\<^sub>1"
  with \<open>regular x\<close>[unfolded regular_def, rule_format, of t]
  show False
     unfolding subsetM_def t[rule_format] using assms regular_def by blast 
qed

lemma regular_antisym2_mem_sep: assumes "regular x" "y\<^sub>1 \<epsilon> x" "y\<^sub>2 \<epsilon> x" "y\<^sub>3 \<epsilon> x" shows "\<not> (y\<^sub>1 \<epsilon> y\<^sub>2 \<and> y\<^sub>2 \<epsilon> y\<^sub>3 \<and> y\<^sub>3 \<epsilon> y\<^sub>1)"
proof
  obtain t where t: "\<forall> u. u \<epsilon> t \<longleftrightarrow> u = y\<^sub>1 \<or> u = y\<^sub>2 \<or> u = y\<^sub>3"
    using triple_sep[OF assms(2-)] by blast
  assume "y\<^sub>1 \<epsilon> y\<^sub>2 \<and> y\<^sub>2 \<epsilon> y\<^sub>3 \<and> y\<^sub>3 \<epsilon> y\<^sub>1"
  with \<open>regular x\<close>[unfolded regular_def, rule_format, of t]
  show False
    unfolding set_defs t[rule_format] using assms regular_def by blast
qed

lemma ord_mem_ord_sep: assumes  "ordM v" "u \<epsilon> v" shows "ordM u"
  unfolding ordM_def epschain_def conj_assoc[symmetric]
proof (rule conjI)+
  have "regular v" "u \<subseteq>\<^sub>M v"
    using \<open>ordM v\<close> ordM_D1 \<open>u \<epsilon> v\<close> ordM_def by blast+
  then show "regular u"
    unfolding regular_def using subsetM_trans[OF _ \<open>u \<subseteq>\<^sub>M v\<close>] by blast
  have "u \<subseteq>\<^sub>M v" "epschain v" "regular v" "transM v"
    using assms unfolding natM_def ordM_def transM_def epschain_def by blast+
  thus "\<forall>y z. y \<epsilon> u \<and> z \<epsilon> u \<longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y"
    using \<open>ordM v\<close> unfolding ordM_def subsetM_def epschain_def by blast
  show "transM u"
    unfolding transM_def set_defs
  proof (rule allI, rule impI)+
    fix z y
    assume "y \<epsilon> u" "z \<epsilon> y"
    hence "z \<epsilon> v" "y \<epsilon> v" 
      using \<open>u \<epsilon> v\<close> \<open>transM v\<close> unfolding transM_def set_defs by blast+
    have "u \<noteq> z"
      using regular_antisym_mem_sep[OF \<open>regular v\<close> \<open>y \<epsilon> v\<close> \<open>z \<epsilon> v\<close>] \<open>y \<epsilon> u\<close> \<open>z \<epsilon> y\<close> by blast
    have "\<not> u \<epsilon> z"
      using regular_antisym2_mem_sep[OF \<open>regular v\<close> \<open>u \<epsilon> v\<close> \<open>z \<epsilon> v\<close> \<open>y \<epsilon> v\<close>] \<open>y \<epsilon> u\<close> \<open>z \<epsilon> y\<close> by blast
    show "z \<epsilon> u"
      using ordM_D2[OF \<open>ordM v\<close> \<open>u \<epsilon> v\<close> \<open>z \<epsilon> v\<close>] \<open>u \<noteq> z\<close> \<open>\<not> u \<epsilon> z\<close> by blast
  qed
qed   

end

text \<open>The interest of this locale is to investigate intersections of various kinds.\<close>

locale L_setext_sep = L_setext + L_sep

begin

sublocale L_setext_empty
  by unfold_locales

lemma separ_def_SFP: assumes "SetFormulaPredicate P"
  shows "u \<epsilon> separationM y (\<lambda> x. P(\<Xi>(n:=x))) \<longleftrightarrow> (u \<epsilon> y \<and> (P (\<Xi>(n:= u))))"
  using  collect_def_ex[OF sep_var[rule_format], OF assms] separationM_def by simp

lemma separ_def_SP: assumes "SetProperty P"
  shows "u \<epsilon> separationM y (\<lambda> x. P x) \<longleftrightarrow> (u \<epsilon> y \<and> P u)"
  using separ_def_SFP[OF assms[unfolded SetProperty_def], of _ _ _ 0] by simp

lemma separ_def_SR: assumes "SetRelation P"
  shows "u \<epsilon> separationM y (\<lambda> x. P x r) \<longleftrightarrow> (u \<epsilon> y \<and> P u r)"
  using separ_def_SFP[OF assms[unfolded SetRelation_def], of _ _ _ 0] by simp

lemma least_def':
  assumes "Q (\<Xi>(n:=w))" and "SetFormulaPredicate Q"
  shows "u \<epsilon> \<Inter>\<^sub>M (\<lambda> x. Q (\<Xi>(n:=x))) \<longleftrightarrow> (\<forall> y. Q (\<Xi>(n:=y)) \<longrightarrow> u \<epsilon> y)"
proof-
  from bounded_free[OF assms(2)]
  obtain m where m: "Q \<Xi> = Q \<Xi>'" if "\<forall>i. i < m \<longrightarrow> \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  have k: "Q (\<Xi>(m+n+1 := x, n := y)) \<longleftrightarrow> Q (\<Xi>(n := y))" for x y
    by (rule m) force+
  have aux: "(\<Xi>(n := a)) n = a" for \<Xi> and a::'a
    by simp
  have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. (\<forall> y. Q (\<Xi>(n:=y)) \<longrightarrow> ((\<Xi>(n:=y)) (m+n+1)) \<epsilon> y))"
    by (rule SFP_all[of "\<lambda> \<Xi>.  Q (\<Xi>) \<longrightarrow> (\<Xi>) (m+n+1) \<epsilon> (\<Xi> n)", of n, unfolded aux], unfold logsimps) (rule | fact)+
  have iff: "(v \<epsilon> w \<and> (\<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> v \<epsilon> y)) \<longleftrightarrow> (\<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> v \<epsilon> y)" for v
    using assms(1) by blast
  have sep: "(v \<epsilon> separationM w (\<lambda>x. \<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> x \<epsilon> y)) = (\<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> v \<epsilon> y)" for v
    using separ_def_SFP[of _  v, OF sfp, of w \<Xi> "m+n+1"] iff[of v] 
     unfolding k by force 
  show ?thesis
    unfolding leastM_def using collect_def'
    using collect_def'[of "separationM w (\<lambda>x. \<forall>y. Q (\<Xi>(0 := y)) \<longrightarrow> u \<epsilon> y)"] sep by force
qed

lemma least_def_ex:
   "\<exists> w. Q (\<Xi>(n := w)) \<Longrightarrow> SetFormulaPredicate Q \<Longrightarrow> 
   u \<epsilon> \<Inter>\<^sub>M (\<lambda> x. Q (\<Xi>(n:=x))) \<longleftrightarrow> (\<forall> y. Q (\<Xi>(n:=y)) \<longrightarrow> u \<epsilon> y)"
  using least_def' by force

lemma intersection_def'[set_defs]: "z \<epsilon> x \<inter>\<^sub>M y \<longleftrightarrow> z \<epsilon> x \<and> z \<epsilon> y"
proof-
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<epsilon> \<Xi> (Suc 0))"
    by (rule SFP_rules)
  from separ_def_SFP[OF this, of z x, rule_format, of "undefined(1:=y)" 0, simplified] 
  show "(z \<epsilon> x \<inter>\<^sub>M y) = (z \<epsilon> x \<and> z \<epsilon> y)"
    unfolding intersectionM_def separationM_def.
qed

lemma intersect_subset: "x \<inter>\<^sub>M y \<subseteq>\<^sub>M x" "x \<inter>\<^sub>M y \<subseteq>\<^sub>M y"
  unfolding set_defs by simp_all 

lemma intersect_regular: assumes "regular x" "regular y"
  shows "regular (x \<inter>\<^sub>M y)"
  using assms unfolding regular_def intersection_def' subsetM_def by blast

lemma intersect_transM: assumes "transM x" "transM y"
  shows "transM (x \<inter>\<^sub>M y)"
  using assms unfolding intersection_def' transM_def subsetM_def by blast

lemma intersect_epschain: assumes "epschain x" "epschain y"
  shows "epschain (x \<inter>\<^sub>M y)"
  using assms intersect_transM unfolding intersection_def' epschain_def subsetM_def by blast

lemma intersect_ordM: assumes "ordM x" "ordM y"
  shows "ordM (x \<inter>\<^sub>M y)"
  using assms intersect_transM intersect_regular  unfolding ordM_def
  unfolding  intersection_def' epschain_def by simp

lemma ordM_subset_mem: assumes "ordM x" "ordM y" "y \<subset>\<^sub>M x"
  shows "y \<epsilon> x"
proof-
  have SR: "SetRelation (\<lambda> v y. \<not> v \<epsilon> y)" 
    unfolding SetRelation_def by (rule SFP_rules)+
  have "regular x"
    using \<open>ordM x\<close> by simp 
  have dif: "u \<epsilon> separationM x (\<lambda> v. \<not> v \<epsilon> y) \<longleftrightarrow> u \<epsilon> x \<and> \<not> u \<epsilon> y" for u
    using separ_def_SR[OF SR].
  hence "separationM  x (\<lambda> v. \<not> v \<epsilon> y) \<subseteq>\<^sub>M x"
    unfolding subsetM_def by blast
  from \<open>regular x\<close>[unfolded regular_def, rule_format, OF this, unfolded dif]
  obtain c where "c \<epsilon> x" "\<not> c \<epsilon> y" and c: "\<forall>v. v \<epsilon> c \<longrightarrow> (v \<epsilon> y \<or> \<not> v \<epsilon> x)"
    using  proper_subset_diff[OF \<open>y \<subset>\<^sub>M x\<close>] by blast 
  have "c \<subseteq>\<^sub>M x"
    using \<open>c \<epsilon> x\<close> assms(1) natM_def ordM_D1 by blast
  hence "c \<subseteq>\<^sub>M y"
    using \<open>y \<subset>\<^sub>M x\<close> c unfolding subsetM_def proper_subsetM_def by blast 
  have "y = c"
  proof (rule subsetM_antisym[OF \<open>c \<subseteq>\<^sub>M y\<close>], unfold subsetM_def, rule allI, rule impI)
    fix z assume "z \<epsilon> y"   
    hence "z \<epsilon> x" 
      using \<open>y \<subset>\<^sub>M x\<close> unfolding proper_subsetM_def by blast
    from ordM_D2[OF \<open>ordM x\<close> this \<open>c \<epsilon> x\<close>]
    show "z \<epsilon> c"
      using \<open>\<not> c \<epsilon> y\<close> \<open>z \<epsilon> y\<close> ordM_D1[OF \<open>ordM y\<close> \<open>z \<epsilon> y\<close>, unfolded subsetM_def] by blast
  qed
  thus ?thesis  
    using \<open>c \<epsilon> x\<close> by blast
qed

lemma ordM_total: assumes "ordM x" "ordM y"
  shows "x \<epsilon> y \<or> y \<epsilon> x \<or> x = y"
  using ordM_def[unfolded epschain_def]
proof-
  have "regular (x \<inter>\<^sub>M y)"
    using intersect_ordM[OF \<open>ordM x\<close> \<open>ordM y\<close>] by simp
  from regular_not_self_mem_sep[OF this]
  have "\<not> (x \<inter>\<^sub>M y \<subset>\<^sub>M x \<and> x \<inter>\<^sub>M y \<subset>\<^sub>M y)"
    using ordM_subset_mem[OF assms(1) intersect_ordM, OF assms]  
      intersection_def' assms(1,2) ord_mem_ord_sep ordM_subset_mem by blast  
  with sep_SR[rule_format, of "\<lambda> v y. v \<epsilon> y"]
  consider "x \<inter>\<^sub>M y = x" | "x \<inter>\<^sub>M y = y" 
    unfolding proper_subsetM_def using intersection_def' by blast  
  then show ?thesis
  proof (cases)
    assume "x \<inter>\<^sub>M y = x"
    hence "x = y \<or> x \<subset>\<^sub>M y"
      unfolding proper_subsetM_def setext using intersection_def' by blast
    with ordM_subset_mem[OF assms(2,1)] 
    show ?thesis
      by blast
  next
    assume "x \<inter>\<^sub>M y = y"
    hence "x = y \<or> y \<subset>\<^sub>M x"
      unfolding proper_subsetM_def setext using intersection_def' by blast
    with ordM_subset_mem[OF assms] 
    show ?thesis
      by blast
  qed
qed

lemma nat_mem_nat: assumes  "natM v" "u \<epsilon> v" shows "natM u"
  unfolding natM_def 
proof
  show "ordM u"
    using assms ord_mem_ord_sep unfolding natM_def by blast
  show "\<forall>v. v \<epsilon> u \<or> v = u \<longrightarrow> (\<exists>u. u \<epsilon> v) \<longrightarrow> is_sucM v"
    using assms natM_D nat_mem_is_suc  ordM_D1 subsetM_def  by blast  
qed    
      
lemma set_of_ords_regular: assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y"
  shows "regular s"   
  unfolding regular_def
proof (rule allI, rule impI, rule impI)
  fix y assume "y \<subseteq>\<^sub>M s" "\<exists>z. z \<epsilon> y"
  then obtain z where "z \<epsilon> y"
    by blast
  have "ordM z"
    using \<open>y \<subseteq>\<^sub>M s\<close> \<open>z \<epsilon> y\<close> assms subsetM_def by blast
  hence "regular z"
    by simp
  show "\<exists>u. u \<epsilon> y \<and> (\<forall>v. \<not> (v \<epsilon> u \<and> v \<epsilon> y))"
  proof (cases "\<forall>v. \<not> (v \<epsilon> z \<and> v \<epsilon> y)", use \<open>z \<epsilon> y\<close> in blast)   
    assume a: "\<not> (\<forall>v. \<not> (v \<epsilon> z \<and> v \<epsilon> y))"
    from sep_SR[of "\<lambda> x y. x \<epsilon> y", rule_format, of z, unfolded SetRelation_def, OF SFP_mem]
    obtain u where u: "\<forall> v. v \<epsilon> u \<longleftrightarrow> v \<epsilon> z \<and> v \<epsilon> y"
      by auto
    hence "u \<subseteq>\<^sub>M z" "\<exists> v. v \<epsilon> u"
      using a unfolding u[rule_format] set_defs by blast+
    from \<open>regular z\<close>[unfolded regular_def, rule_format, OF this]
    obtain m where "m \<epsilon> u" "\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> u)" 
      by blast
    hence "m \<epsilon> y \<and> (\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> y))"
      unfolding u[rule_format] using \<open>ordM z\<close> ordM_trans by presburger
    thus ?thesis
      by blast
  qed
qed
   
lemma intersect_natM: assumes "natM x" "natM y"
  shows "natM (x \<inter>\<^sub>M y)"
proof (cases "x = x \<inter>\<^sub>M y", use assms in argo)
  assume "x \<noteq> x \<inter>\<^sub>M y"
  show "natM (x \<inter>\<^sub>M y)"
  proof (cases "x \<inter>\<^sub>M y = \<emptyset>") 
    assume "x \<inter>\<^sub>M y \<noteq> \<emptyset>" 
    show "natM (x \<inter>\<^sub>M y)"
    proof (rule natM_I) 
      show "\<And>v. \<exists>u. u \<epsilon> v \<Longrightarrow> v \<epsilon> x \<inter>\<^sub>M y \<Longrightarrow> is_sucM v"
        using \<open>natM x\<close>[unfolded natM_def] unfolding intersection_def' by blast
      show "is_sucM (x \<inter>\<^sub>M y)"
      proof (rule nat_mem_is_suc)
        have "\<not> x \<epsilon> x \<inter>\<^sub>M y"
          using assms(1) natM_def ordM_def regular_not_self_mem_sep unfolding intersection_def' by fast
        thus "(x \<inter>\<^sub>M y) \<epsilon> x"
          using ordM_total[OF _ intersect_ordM, of x x y] \<open>\<not> x = x \<inter>\<^sub>M y\<close> natM_D assms by blast
        show "\<exists>u. u \<epsilon> x \<inter>\<^sub>M y"
          using \<open>x \<inter>\<^sub>M y \<noteq> \<emptyset>\<close> emptyset_def' by auto 
      qed fact
    qed (simp add: assms  intersect_ordM natM_D)
  qed simp
qed

end

locale L_setext_setsuc_sep = L_setext + L_setsuc + L_sep

begin

text \<open>
We want to prove that ordinals are closed under the successor operation. However, regularity is a problem. It is not necessarily preserved by taking successors.

Separation is needed to avoid the following pathological situation:
consider an epschain \<open>C = {c\<^sub>z | z \<in> \<int>}\<close> of type \<open>\<int>\<close> where moreover \<open>\<emptyset> \<in> c\<^sub>z\<close> for each \<open>z\<close>. That is, \<open>u \<epsilon> c\<^sub>m\<close> iff \<open>u = c\<^sub>k\<close> with \<open>k < m\<close>, or \<open>u = \<emptyset>\<close>.  
We postulate that an infinite subclass of \<open>C\<close> is a set iff it contains \<open>c\<^sub>0\<close>.
Now, \<open>c\<^sub>z\<close> are ordinals for all  \<open>z \<le> 0\<close>. But \<open>c\<^sub>1\<close> is not regular, since it contains an infinite descending chain \<open>{c\<^sub>k | k \<le> 0}\<close> as a subset.
\<close>

sublocale L_setext_empty_setsuc
  by unfold_locales

sublocale L_setext_sep
  by unfold_locales

lemma regular_setsuc: assumes "transM x" "regular x" "regular y"
  shows "regular (setsucM x y)"
proof (cases "y \<epsilon> x")
  assume "y \<epsilon> x"
  hence "setsucM x y = x"
    unfolding setext[of _ x] set_defs by blast
  thus "regular (setsucM x y)"
    using \<open>regular x\<close> by simp
next
  assume "\<not> y \<epsilon> x" 
  show "regular (setsucM x y)"
    unfolding regular_def 
  proof (rule allI, rule impI, rule impI)
    fix w 
    assume "w \<subseteq>\<^sub>M setsucM x y" "\<exists> z. z \<epsilon> w"
    have "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<noteq> \<Xi> 1)"
      by (rule SFP_rules)+
    from sep_SR[of "\<lambda> x y. x \<noteq> y", unfolded SetRelation_def, OF this]
    obtain w' where w': "\<And> z. z \<epsilon> w' \<longleftrightarrow> z \<epsilon> w \<and> z \<noteq> y"
      by presburger
    have  "w' \<subseteq>\<^sub>M x"
      using \<open>w \<subseteq>\<^sub>M setsucM x y\<close> w' subsetM_def setsuc_def' by auto 
    show "\<exists>z. z \<epsilon> w \<and> (\<forall>v. \<not> (v \<epsilon> z \<and> v \<epsilon> w))"
    proof (cases "y \<epsilon> w")
      assume "y \<epsilon> w"
      show ?thesis
      proof (cases "w' = \<emptyset>")
        assume "w' = \<emptyset>"
        have "w = {y}\<^sub>M"
          using w' empty_is_empty \<open>y \<epsilon> w\<close> unfolding setext[of w] set_defs \<open>w' = \<emptyset>\<close> singleton_def' by metis 
        hence "y \<epsilon> w \<and> (\<forall>v. \<not> (v \<epsilon> y \<and> v \<epsilon> w))"
          unfolding \<open>w = {y}\<^sub>M\<close> set_defs  using regular_not_self_mem[OF \<open>regular y\<close>] singleton_def'
          by auto
        then show ?thesis
          by blast
      next
        assume "\<not> w' = \<emptyset>"
        hence "\<exists> z. z \<epsilon> w'"
          by (simp add: emptyset_def')
        from \<open>regular x\<close>[unfolded regular_def, rule_format, OF \<open>w' \<subseteq>\<^sub>M x\<close> this]
        obtain m where "m \<epsilon> w'" and m: "\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> w')"
          by blast
        hence "m \<epsilon> w"
          using w' by blast
        have "\<not> y \<epsilon> m"
          using \<open>transM x\<close>[unfolded transM_def] \<open>m \<epsilon> w'\<close> \<open>w' \<subseteq>\<^sub>M x\<close> \<open>\<not> y \<epsilon> x\<close> subsetM_def by blast
        have "\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> w)"
          using m unfolding w' using \<open>\<not> y \<epsilon> m\<close> by blast 
        then show ?thesis
          using \<open>m \<epsilon> w\<close> by blast
      qed
    next
      assume "\<not> y \<epsilon> w"
      hence "w \<subseteq>\<^sub>M x"
        using \<open>w \<subseteq>\<^sub>M setsucM x y\<close> w' subsetM_def
        by (metis \<open>w' \<subseteq>\<^sub>M x\<close>)
      from \<open>regular x\<close>[unfolded regular_def, rule_format, OF this \<open>\<exists> z. z \<epsilon> w\<close>]
      show ?thesis.
    qed
  qed
qed

lemma ord_suc_ord: assumes "ordM x" shows "ordM (setsucM x x)"
proof(rule ordM_I)
  show epschain: "epschain (setsucM x x) "
    using assms
    using ordM_def epschain_suc_epschain by blast 
  show "regular (setsucM x x)"
    unfolding regular_def  using assms epschain_def ordM_def regular_def regular_setsuc by blast 
qed  

lemma nat_suc_nat: assumes "natM x" shows "natM (setsucM x x)"
proof-
  have "(\<forall>v. v \<epsilon> x \<or> v = x \<longrightarrow> (\<exists>u. u \<epsilon> v) \<longrightarrow> (\<exists>y. \<forall>z. (z \<epsilon> v) = (z \<epsilon> y \<or> z = y))) \<Longrightarrow>
    (\<forall>v. v \<epsilon> setsucM x x \<or> v = setsucM x x \<longrightarrow> (\<exists>u. u \<epsilon> v) \<longrightarrow> (\<exists>y. \<forall>z. (z \<epsilon> v) = (z \<epsilon> y \<or> z = y)))"
    using setsuc_def' by auto
  thus  "natM (setsucM x x)"
    using assms ord_suc_ord unfolding natM_def is_sucM_def by fast
qed

lemma one_natM[simp]: "natM ({\<emptyset>}\<^sub>M)"
  using nat_suc_nat[OF emp_natM] unfolding setsuc_empty_sing.

lemma ord_mem_suc: assumes "ordM x" and "y \<epsilon> x" 
  shows  "setsucM y y \<epsilon> x \<or> setsucM y y = x"
proof-
  have "ordM y"
    using ord_mem_ord[OF \<open>ordM x\<close> \<open>y \<epsilon> x\<close>].
  have "ordM(setsucM y y)"
    by (simp add: \<open>ordM y\<close> ord_suc_ord)
  have "\<not> x \<epsilon> setsucM y y"
  proof
    assume "x \<epsilon> setsucM y y"
    then consider "x \<epsilon> y" | "x = y"
      unfolding setsuc_def' by blast
    then show False
      by (cases) (use  \<open>y \<epsilon> x\<close> \<open>ordM x\<close> ordM_def ordM_trans regular_not_self_mem in blast)+
  qed
  with ordM_total[OF  \<open>ordM x\<close> \<open>ordM(setsucM y y)\<close>]    
  show ?thesis
    by blast
qed

lemma ord_limit_or_suc: assumes "ordM x" 
  shows "is_sucM x \<or> (\<forall> u. u \<epsilon> x \<longrightarrow> setsucM u u \<epsilon> x)"
  using assms is_suc_def' ord_mem_suc by auto

lemma assumes "regular x" "regular y" 
  shows "regular (setsucM x y)"
  unfolding regular_def setsuc_def' 
  oops
\<comment> \<open>not true, consider \<open>{x} \<epsilon> x\<close>. Then \<open>x \<union> {x}\<close> contains a subset \<open>{x,{x}}\<close> which is a cycle\<close>

end 


subsection \<open>Transitive superset\<close>

text \<open>The existence of transitive supersets needs to be assumed explicitly if the axiom of infinity is absent (or negated). It is related to regularity, since it enables obtaining an infinite set from infinite descending epsilon chains.\<close>

locale L_ts = set_signature +
  assumes ts: "\<forall> x. \<exists> z. (transM z \<and> (x \<subseteq>\<^sub>M z))" 

locale L_setext_sep_ts = L_setext + L_sep + L_ts

begin

sublocale L_setext_sep
  by unfold_locales

lemma least_ts_def' : "u \<epsilon> least_tsM x \<longleftrightarrow> (\<forall> v. transM v \<and> x \<subseteq>\<^sub>M v \<longrightarrow> u \<epsilon> v)" 
   (is "u \<epsilon> least_tsM x \<longleftrightarrow> (\<forall> v. ?Q v \<longrightarrow> u \<epsilon> v)")
  by (rule least_def_ex[of "\<lambda> \<Xi>. transM (\<Xi> 0) \<and> \<Xi> 1 \<subseteq>\<^sub>M \<Xi> 0" "undefined(1:=x)" 0, 
  simplified, OF ts[rule_format], folded least_tsM_def], unfold logsimps set_defs)
  (rule SFP_rules)+

lemma least_ts_is_transitive: "transM (least_tsM x)"
  using least_ts_def' unfolding transM_def subsetM_def by blast

end

locale L_setext_sep_reg = L_setext + L_sep + L_reg

locale L_setext_sep_reg_ts = L_setext + L_sep + L_reg + L_ts

begin

sublocale L_setext_sep_ts
  by unfold_locales

text \<open>The schema of regularity follows from regularity and transitive superset.\<close>

sublocale L_regsch
proof (unfold_locales, rule impI)
  fix P \<Xi>
  assume "SetFormulaPredicate P"
  assume "\<exists> x. P (\<Xi>(0:=x))"
  then obtain x where "P (\<Xi>(0:=x))" 
    by blast
  have "x \<subseteq>\<^sub>M (least_tsM x)"  
    using least_ts_def' subsetM_def by blast
  define w where "w = separationM (least_tsM x) (\<lambda> x. P (\<Xi>(0:=x)))"
  then have w: "u \<epsilon> w \<longleftrightarrow> u \<epsilon> least_tsM x \<and> P (\<Xi>(0:=u))" for u 
    using separ_def_SFP[OF \<open>SetFormulaPredicate P\<close>] by blast
  show "\<exists>x. P (\<Xi>(0 := x)) \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0 := y)))"
  proof(cases)
    assume "\<exists> v. v \<epsilon> w"
    have "(\<exists> v. v \<epsilon> w)\<longrightarrow>(\<exists> v. (v \<epsilon> w \<and> ( \<forall> t. (t \<epsilon> v  \<longrightarrow> \<not> t \<epsilon> w ) ) ) )" 
      using reg by blast    
    then have "(\<exists> v. (v \<epsilon> w \<and> ( \<forall> t. (t \<epsilon> v  \<longrightarrow> \<not> t \<epsilon> w ) ) ) )" using \<open>\<exists> v. v \<epsilon> w\<close> by blast
    then obtain v where "v \<epsilon> w" and v: "t \<epsilon> v  \<longrightarrow> \<not> t \<epsilon> w" for t by blast  
    have "P (\<Xi>(0 := v))" 
      using w \<open>v \<epsilon> w\<close> by blast
    have "v \<epsilon> least_tsM x" 
      using w \<open>v \<epsilon> w\<close> by blast
    have "v \<subseteq>\<^sub>M least_tsM x"
      using least_ts_is_transitive \<open>v \<epsilon> least_tsM x\<close> transM_def by blast
    have "t \<epsilon> v \<longrightarrow> \<not> P (\<Xi>(0 := t))" for t 
      using \<open>v \<subseteq>\<^sub>M least_tsM x\<close> w v unfolding subsetM_def by blast 
    then have "\<forall> t. (t \<epsilon> v \<longrightarrow> \<not> P (\<Xi>(0 := t)))" by blast
    then have "\<exists>x. P (\<Xi>(0 := x))\<and> (\<forall>y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0 := y)))"
      using \<open>P (\<Xi>(0 := v))\<close> by blast
    then show ?thesis by blast
  next
    assume  "\<not> (\<exists> v. v \<epsilon> w)"
    then have "\<forall> v. (v \<epsilon> least_tsM x \<longrightarrow> \<not> P (\<Xi>(0 := v)) )" 
      using w  by blast
    then have  "\<forall> v. (v \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0 := v)) )" 
       using subsetM_def \<open>x \<subseteq>\<^sub>M least_tsM x\<close> by blast
     then show ?thesis 
       using \<open>P (\<Xi>(0 := x))\<close> by blast 
  qed
qed

end

subsection Replacement

locale L_repl = set_signature + 
  assumes replf:  "SetFormulaPredicate P \<Longrightarrow> (\<forall> u. \<exists>! v. P (\<Xi>(0:=u, 1:= v))) \<longrightarrow> (\<forall> x. \<exists> z. \<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))))"
\<comment> \<open>We can replace \<open>x\<^sub>0\<close> by the unique \<open>x\<^sub>1\<close> satisfying \<open>P(x\<^sub>0,x\<^sub>1)\<close>. Note the presence of parameters \<open>x\<^sub>i, i \<ge> 2\<close>\<close>

locale L_setext_empty_repl = L_setext + L_empty + L_repl

begin

text \<open>Replacing using total functions is equivalent to replacing using partial functions.\<close>

lemma replp: assumes "SetFormulaPredicate P" and func: "\<forall> u v w. P (\<Xi>(0:=u, 1:= v)) \<and> P (\<Xi>(0:=u, 1:= w)) \<longrightarrow> v = w"
  shows "\<forall> x. \<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))))"
proof
  fix x
  show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v)))"
  proof (cases "\<exists> u v. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))")
    assume "\<nexists>u v. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))"
    then show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v)))"
      using exI[of "\<lambda> z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v)))" \<emptyset>] empty by blast 
  next    
    assume ex: "\<exists> u v. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))"
    then obtain v where ex: "\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))"  
      by blast
    from bounded_free[OF assms(1)]
    obtain k where k0: "\<forall>\<Xi> \<Xi>'. (\<forall>i<k. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'"
      by blast
    let ?k = "Suc (max k 1)"
    have k: "P(\<Xi>) \<longleftrightarrow> P(\<Xi>(?k:= a))" "1 < ?k" for \<Xi> a
      by (rule k0[rule_format, of \<Xi> "\<Xi>(?k:= a)"], force) simp   
    have twist: "\<Xi>(Suc (max k 1) := a, 0 := b, 1 := c) = \<Xi>(0 := b, 1 := c, Suc (max k 1) := a)" for a b c
      by auto
    have canc: "P(\<Xi>(?k:=a,0:=b,1:=c)) = P(\<Xi>(0:=b,1:=c))" "\<Xi>(?k:=a,0:=b,1:=c,1:=d) = \<Xi>(?k:=a,0:=b,1:=d)"
     "(\<Xi>(?k := a, 0 := b, 1 := c)) 1 = c" "(\<Xi>(?k := a, 0 := b, 1 := c)) ?k = a" for a b c d
      unfolding twist using k(1) by auto
    define Q :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where 
    "Q = (\<lambda> \<Xi>. (if \<exists> c. P (\<Xi>(1:= c)) then P \<Xi>  else \<Xi> 1 = \<Xi> ?k))"
    have "\<exists>! v'. Q (\<Xi>(?k:=v,0:=u,1:=v'))" for u
      unfolding Q_def canc using ex func by metis
    hence ex1: "\<forall> u. \<exists>! w. Q (\<Xi>(?k:=v,0:=u,1:=w))"
      by simp 
    have "SetFormulaPredicate Q"
      unfolding Q_def by (simp, unfold logsimps) (rule SFP_rules | fact)+
    from replf[rule_format, OF this ex1[rule_format], of x] 
    have  Qset: "\<exists>z. \<forall>w. (w \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> Q(\<Xi>(?k:=v,0:=u,1:=w)))".
    have P_iff_Q: "(\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := w))) \<longleftrightarrow> (\<exists>u. u \<epsilon> x \<and> Q (\<Xi>(?k:=v, 0 := u, 1 := w)))" for w
      unfolding Q_def canc  using ex by auto 
    show ?thesis
      using Qset unfolding P_iff_Q.
  qed
qed

lemma replp_vars: assumes "SetFormulaPredicate P" and func: "\<forall> u v w. P (\<Xi>(k:=u, l:= v)) \<and> P (\<Xi>(k:=u, l:= w)) \<longrightarrow> v = w"
  shows "\<forall> x. \<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P (\<Xi>(k:=u, l:= v))))"
proof-
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "P \<Xi> = P \<Xi>'" if "\<forall>i<m. \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  let ?m = "Suc (k + l + m)"  
  let ?f = "id(0 := ?m, 1 := Suc ?m, k:= 0,l := 1)"
  let ?Q = "\<lambda> X. (P (\<lambda> b. X (?f  b)))"
  let ?X = "\<Xi>(?m:= \<Xi> 0,(Suc ?m):= \<Xi> 1)" 
  have sfpq:  "SetFormulaPredicate ?Q"
    using transform_variables[OF \<open>SetFormulaPredicate P\<close>] by simp
  have small: "\<forall> i < m. (\<Xi>(k := u, l := v)) i = (?X (0 := u, 1 := v)) (?f i)" for u v
    by auto
  have equiv: "(P (\<Xi>(k := u, l := v))) \<longleftrightarrow> (?Q (?X (0 := u, 1 := v)))" for u v
    by (rule m[of "\<Xi>(k := u, l := v)" "\<lambda> b. (?X (0 := u, 1 := v))(?f b)"]) fact
  then have funcq: "(\<forall>u v w. ?Q (?X(0 := u, 1 := v)) \<and> ?Q (?X(0 := u, 1 := w)) \<longrightarrow> v = w)"
    using func by blast 
  show ?thesis
    using replp[OF sfpq funcq] unfolding equiv.    
qed

lemma repl_SR: assumes "SetRelation P" "\<forall> u v w. P u v \<and> P u w \<longrightarrow> v = w"
  shows "\<forall> x. \<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P u v))"
  using assms unfolding SetRelation_def using replp[of "\<lambda>\<Xi>. P (\<Xi> 0) (\<Xi> 1)"] by fastforce    

lemma replace_def':  
  assumes "SetFormulaPredicate P" "\<forall> u v w. P(\<Xi>(k:=u, l:= v)) \<and> P(\<Xi>(k:=u, l:= w)) \<longrightarrow> v = w"
  shows "\<forall> v. v \<epsilon> replaceM (\<lambda> u v. P(\<Xi>(k:=u, l:= v))) x \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> (P(\<Xi>(k:=u, l:= v))))"
  using collect_def_ex[of  "\<lambda> v. (\<exists>u. u \<epsilon> x \<and> P(\<Xi>(k:=u, l:= v)))", OF replp_vars[OF assms, rule_format], folded replaceM_def] by blast

text \<open>Separation can be obtained from replacement.\<close>

sublocale L_setext_sep
proof (unfold_locales, rule allI)
  fix P \<Xi> x
  assume sfp: "SetFormulaPredicate P"
  \<comment> \<open>The idea is clear: we replace \<open>x\<^sub>0\<close> with itself, that is, with \<open>x\<^sub>1 = x\<^sub>0\<close>. A technical complication is that we have to rename parameters \<open>x\<^sub>i\<close> which for separation include \<open>x\<^sub>1\<close> while for replacement they have to start with \<open>x\<^sub>2\<close>\<close>
  have t: "(\<lambda>n. if n = 0 then v else ((\<lambda>i. \<Xi> (i - 1))(0 := v)) (n+1)) = \<Xi>(0 := v)" for v and \<Xi> :: "nat \<Rightarrow> 'a"
    by auto
  have "SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> 0) = (\<Xi> 1) \<and> P (\<lambda> n. \<Xi> (n+1)))"
    unfolding logsimps by (rule SFP_rules)+ (rule transform_variables[OF sfp])
  from replp[rule_format, OF this, of "\<lambda> i. \<Xi> (i - 1)" x]
  show "\<exists>z. \<forall>u. (u \<epsilon> z) = (u \<epsilon> x \<and> P (\<Xi>(0 := u)))"
    by (simp del: One_nat_def add: t)  
qed

end

text \<open>Separation does not follow from replacement without the empty set axiom. We show it by constructing a counter-model.\<close>

theorem not_repl_ext_implies_separ: "\<not> (\<forall> mem. L_repl mem \<and> L_setext mem \<longrightarrow> L_sep mem)"
proof-
  define loop :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where  "loop \<equiv> \<lambda> x y. x = y"
  interpret eq_mem : set_signature loop.
  have loop_ext: "L_setext loop"
    by (unfold_locales, unfold loop_def) force
  have loop_repl: "L_repl loop"
  proof (unfold_locales, rule impI)
    fix P :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and \<Xi>
    assume "\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))"
    then show "\<forall>x. \<exists>z. \<forall>v. loop v z = (\<exists>u. loop u x \<and> P (\<Xi>(0 := u, 1 := v)))"
      unfolding loop_def by metis 
  qed
  have SP: "eq_mem.SetFormulaPredicate (\<lambda> \<Xi>. False)"
    by simp
  have "\<not> L_sep loop"
    unfolding L_sep_def using loop_def  SP by blast 
  show ?thesis
    using \<open>\<not> L_sep loop\<close> loop_ext loop_repl by auto
qed
 

locale L_setext_empty_setsuc_repl = L_setext + L_empty + L_setsuc + L_repl

begin

sublocale L_setext_empty_setsuc
  by unfold_locales

sublocale L_setext_empty_repl
  by unfold_locales

lemma tarski_setsuc_tarski: assumes "tarski_fin x" shows "tarski_fin (setsucM x y)"
  unfolding tarski_fin_def
proof (rule, rule, rule)
  \<comment> \<open>fix a system \<open>w\<close> for which we want to find the maximum\<close>
  fix w assume w: "\<forall>z. z \<epsilon> w \<longrightarrow> z \<subseteq>\<^sub>M setsucM x y" and "\<exists> z. z \<epsilon> w"
    \<comment> \<open>remove \<open>y\<close> from each element of \<open>w\<close>, call the result \<open>w'\<close>\<close>  
  let ?P = "\<lambda> \<Xi>. \<forall> a. a \<epsilon> \<Xi> 1 \<longleftrightarrow> a \<epsilon> \<Xi> 0 \<and> a \<noteq> \<Xi> 2"
  have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>v. (v \<epsilon> \<Xi> 1) = (v \<epsilon> \<Xi> 0 \<and> v \<noteq> \<Xi> 2))"
    unfolding logsimps by (rule SFP_rules)+
  have sfp': "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<noteq> \<Xi> 1)"
        by (rule SFP_rules)+
  have aux:  "(\<Xi>(2::nat := y, 0 := u, 1 := v)) 0 = u"
             "(\<Xi>(2 := y, 0 := u, 1 := v)) 1 = v"
             "(\<Xi>(2 := y, 0 := u, 1 := v)) 2 = y" for u v \<Xi>
    by simp_all
  have "\<exists> w'. \<forall> z. z \<epsilon> w' \<longleftrightarrow> (\<exists> u. u \<epsilon> w \<and> (\<forall> v. v \<epsilon> z \<longleftrightarrow> v \<epsilon> u \<and> v \<noteq> y))"
       
   by (rule replp[rule_format, of ?P "undefined(2:= y)" w, unfolded aux], fact)
    (unfold setext, simp)
  then obtain w' where w': "\<forall> z. z \<epsilon> w' \<longleftrightarrow> (\<exists> u. u \<epsilon> w \<and> (\<forall> v. v \<epsilon> z \<longleftrightarrow> v \<epsilon> u \<and> v \<noteq> y))"  
    by blast
   \<comment> \<open>get the maximum of \<open>w'\<close>\<close>
  obtain wmax' where wmax': "wmax' \<epsilon> w' \<and> (\<nexists>w. w \<epsilon> w' \<and> wmax' \<subset>\<^sub>M w)"
  proof (rule exE[OF assms[unfolded tarski_fin_def, rule_format, of w'], of thesis])   
    show "z \<subseteq>\<^sub>M x" if "z \<epsilon> w'" for z
      using \<open>z \<epsilon> w'\<close>[unfolded w'[rule_format, of z]] w unfolding subsetM_def setsuc_def' by auto
    show "\<exists>x. x \<epsilon> w'"
    proof-
      obtain u where "u \<epsilon> w"
        using \<open>\<exists> z. z \<epsilon> w\<close> by blast 
      from sep[rule_format, OF sfp', of u "undefined(1:=y)"]
      obtain u' where u': "\<forall> v. v \<epsilon> u' \<longleftrightarrow> v \<epsilon> u \<and> v \<noteq> y"
         by auto 
      show "\<exists>x. x \<epsilon> w'"
        unfolding w'[rule_format] using \<open>u \<epsilon> w\<close> u' by blast
    qed
  qed
  have "\<not> y \<epsilon> wmax'" "wmax' \<epsilon> w'" "\<nexists>w. w \<epsilon> w' \<and> wmax' \<subset>\<^sub>M w"
    using w' wmax' by blast+
  \<comment> \<open>Either \<open>wmax'\<close> or \<open>setsucM wmax' y\<close> is the desired maximum of \<open>w\<close>\<close>
  show "\<exists>z. z \<epsilon> w \<and> (\<nexists>v. v \<epsilon> w \<and> z \<subset>\<^sub>M v)"
  proof(cases) 
    assume "setsucM wmax' y \<epsilon> w"
    have "(\<nexists>v. v \<epsilon> w \<and> setsucM wmax' y \<subset>\<^sub>M v)"
    proof
      assume "\<exists>v. v \<epsilon> w \<and> setsucM wmax' y \<subset>\<^sub>M v"
      then obtain v where "v \<epsilon> w" and "setsucM wmax' y \<subset>\<^sub>M v"
        by blast
      from sep[rule_format, OF sfp', of v "undefined(1:=y)"]  
      obtain v' where v': "\<And> t. t \<epsilon> v' \<longleftrightarrow> t \<epsilon> v \<and> t \<noteq> y"
        by auto
      have "v' \<epsilon> w'"
        using \<open>v \<epsilon> w\<close> v' w' by auto
      have "wmax' \<subset>\<^sub>M v'"
        using \<open>setsucM wmax' y \<subset>\<^sub>M v\<close> \<open>\<not> y \<epsilon> wmax'\<close> unfolding set_defs setext[of wmax'] setext[of _ v] v' by blast 
      show False
        using wmax' \<open>v' \<epsilon> w'\<close> \<open>wmax' \<subset>\<^sub>M v'\<close> by blast
    qed 
    thus ?thesis
      using \<open>setsucM wmax' y \<epsilon> w\<close> by blast
  next
    assume "\<not> setsucM wmax' y \<epsilon> w" 
    hence "wmax' \<epsilon> w" 
    proof-
      obtain wmax where "wmax \<epsilon> w" and wmax: "\<forall> v. (v \<epsilon> wmax') = (v \<epsilon> wmax \<and> v \<noteq> y)"
        using \<open>wmax' \<epsilon> w'\<close>[unfolded w'[rule_format, of wmax']] \<open>\<not> y \<epsilon> wmax'\<close> by blast
      have "\<not> y \<epsilon> wmax"
      proof
        assume "y \<epsilon> wmax"
        hence "wmax = setsucM wmax' y"
          unfolding setext[of wmax] set_defs wmax[rule_format] by blast
        then show False
          using \<open>\<not> setsucM wmax' y \<epsilon> w\<close> \<open>wmax \<epsilon> w\<close> by blast 
      qed
      hence "wmax = wmax'"
        using setext wmax by blast
      then show "wmax' \<epsilon> w"
        using \<open>wmax \<epsilon> w\<close> by blast
    qed
    have "(\<nexists>v. v \<epsilon> w \<and> wmax' \<subset>\<^sub>M v)"
    proof
      assume "\<exists>v. v \<epsilon> w \<and> wmax' \<subset>\<^sub>M v"
      then obtain v where "v \<epsilon> w" and "wmax' \<subseteq>\<^sub>M v" and "wmax' \<noteq> v"
        unfolding proper_subset_def' by blast
      obtain v' where v': "\<And> t. t \<epsilon> v' \<longleftrightarrow> t \<epsilon> v \<and> t \<noteq> y"
      using sep[rule_format, OF sfp', of  v "undefined(1:=y)"] by auto 
      have "v' \<epsilon> w'"
        using \<open>v \<epsilon> w\<close> v' w' by auto
      have "wmax' \<subseteq>\<^sub>M v'"
        using \<open>wmax' \<subseteq>\<^sub>M v\<close> \<open>\<not> y \<epsilon> wmax'\<close> unfolding setext[of _ v] v' set_defs by blast
      hence "wmax' = v'"
        using wmax' \<open>v' \<epsilon> w'\<close> unfolding  proper_subset_def' by blast
      have "v = setsucM wmax' y"
        using \<open>wmax' \<noteq> v\<close> unfolding \<open>wmax' = v'\<close> setext[of v] setext[of _ v] set_defs v' by blast 
      then show False
        using \<open>\<not> setsucM wmax' y \<epsilon> w\<close> \<open>v \<epsilon> w\<close> by blast
      qed
    thus ?thesis
      using \<open>wmax' \<epsilon> w\<close> by blast
  qed
qed

end

subsection Powerset

locale L_power = set_signature +
  assumes 
          power: "\<forall> x. \<exists> y. (\<forall> u. u \<epsilon> y \<longleftrightarrow> u \<subseteq>\<^sub>M x)"

locale L_setext_empty_power = L_setext + L_empty + L_power

begin

sublocale L_setext_empty
  by unfold_locales

lemma powerset_def'[set_defs]: "u \<epsilon> (\<PP> x) \<longleftrightarrow> u \<subseteq>\<^sub>M x"
  using collect_def_ex[OF power[rule_format], folded powersetM_def].

lemma "\<emptyset> \<epsilon> \<PP> \<emptyset>"
  using empty_is_subset powerset_def' by blast

lemma set_one_mem [simp]: "u \<epsilon> \<PP> \<emptyset> \<longleftrightarrow> u = \<emptyset>"
  unfolding powerset_def' subsetM_def emptyset_def' by force 

lemma set_one_def: "\<PP> \<emptyset> = {\<emptyset>}\<^sub>M"
  unfolding singletonM_def using collect_def'[of "\<PP> \<emptyset>"] unfolding set_one_mem by force 

lemma set_two_mem: "u \<epsilon> \<PP> (\<PP> \<emptyset>) \<longleftrightarrow> u = \<emptyset> \<or> u = {\<emptyset>}\<^sub>M"
  unfolding powerset_def' set_one_def 
proof
  show "u = \<emptyset> \<or> u = {\<emptyset>}\<^sub>M" if "u \<subseteq>\<^sub>M {\<emptyset>}\<^sub>M" 
    using  that[unfolded subsetM_def] emptyset_def'
    unfolding setext[of _ "{\<emptyset>}\<^sub>M"]  set_one_mem[unfolded set_one_def] by blast 
  show "u = \<emptyset> \<or> u = {\<emptyset>}\<^sub>M \<Longrightarrow> u \<subseteq>\<^sub>M {\<emptyset>}\<^sub>M"
    using empty_is_subset subsetM_refl by blast
qed

end

locale L_setext_empty_power_repl = L_setext + L_empty + L_power + L_repl

\<comment> \<open>Subsumes many already existing locales. In particular, we obtain set successor from powerset and replacement\<close>

begin

sublocale L_setext_empty_repl
  by unfold_locales

sublocale L_setext_empty_power
  by unfold_locales

sublocale L_setext_empty_setsuc
proof (unfold_locales, rule allI, rule allI)
  fix x y 
  let ?P = "(\<lambda> \<Xi>. ((\<exists> q. q \<epsilon> (\<Xi> (0::nat))) \<and> (\<forall> q. (q \<epsilon> (\<Xi> 0) \<longleftrightarrow> q = (\<Xi> 1))) \<or> (\<Xi> 1 = \<Xi> 2 \<and> \<not>(\<exists> z. \<forall> q. (q \<epsilon> (\<Xi> 0) \<longleftrightarrow> q = z)))))"
  have sfp: "SetFormulaPredicate ?P"
    unfolding logsimps set_defs by (rule SFP_rules)+
  have func: "\<forall>u v w.
   ((\<exists>q. q \<epsilon> u) \<and> (\<forall>q. (q \<epsilon> u) \<longleftrightarrow> (q = v)) \<or> v = y \<and> (\<nexists>z. \<forall>q. (q \<epsilon> u) \<longleftrightarrow> (q = z))) \<and>
   ((\<exists>q. q \<epsilon> u) \<and> (\<forall>q. (q \<epsilon> u) \<longleftrightarrow> (q = w)) \<or> w = y \<and> (\<nexists>z. \<forall>q. (q \<epsilon> u) \<longleftrightarrow> (q = z))) \<longrightarrow>
   v = w"
    by blast   
  have aux: "(undefined(2 :: nat := y, 0 := u, 1 := v)) 0 = u" "(undefined(2 :: nat := y, 0 := u, 1 := v)) 1 = v" "(undefined(2 :: nat := y, 0 := u, 1 := v)) 2 = y" for u v 
    by simp_all
  have "\<exists>z. \<forall>v. (v \<epsilon> z) =
        (\<exists>u. u \<epsilon> \<PP> x \<and> ((\<exists>q. q \<epsilon> u) \<and> (\<forall>q. (q \<epsilon> u) = (q = v)) \<or> v = y \<and> (\<forall>z. \<exists>q. (q \<epsilon> u) = (q \<noteq> z))))"
    using  replp[OF sfp, simplified, of "undefined(2:=y)", unfolded fun_upd_same, OF func[simplified]]  by simp   
  \<comment> \<open>singletons from \<open>\<PP> x\<close> are replaced by their elements, other sets by \<open>y\<close>\<close> 
  then obtain s where s: "\<forall>v. (v \<epsilon> s) =
  (\<exists>u. u \<epsilon> \<PP> x \<and> ((\<exists>q. q \<epsilon> u) \<and> (\<forall>q. (q \<epsilon> u) = (q = v)) \<or> v = y \<and> (\<forall>z. \<exists>q. (q \<epsilon> u) = (q \<noteq> z))))"
    by auto
  have "v \<epsilon> s \<longleftrightarrow> (v \<epsilon> x \<or> v = y)" for v
  proof
    show "v \<epsilon> s \<Longrightarrow> v \<epsilon> x \<or> v = y"
      unfolding s[rule_format] powerset_def'[unfolded subsetM_def]  by blast 
    show "v \<epsilon> x \<or> v = y \<Longrightarrow> v \<epsilon> s"
    proof (erule disjE)
      assume "v \<epsilon> x"
      obtain singv where singv: "singv \<epsilon> \<PP> x" "\<forall>a. (a \<epsilon> singv) \<longleftrightarrow> a = v"
      proof-
        have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> 0 = \<emptyset> \<and> \<Xi> 1 = \<Xi> 2)" 
          unfolding logsimps set_defs by (rule SFP_rules)+
        then obtain singv where "\<forall>a. (a \<epsilon> singv) \<longleftrightarrow> a = v" 
          using replp[OF sfp, rule_format, of "undefined(2 := v)"  "\<PP> \<emptyset>", simplified] by blast
        then have "singv \<epsilon> \<PP> x"
          using \<open>v \<epsilon> x\<close> by (simp add: powerset_def' subsetM_def) 
        from that[OF this \<open>\<forall>a. (a \<epsilon> singv) \<longleftrightarrow> a = v\<close>]
        show thesis.
      qed
      then show "v \<epsilon> s"
           unfolding s[rule_format] by blast
       next
      assume "v = y"
      hence "\<emptyset> \<epsilon> \<PP> x \<and> \<emptyset> \<subseteq>\<^sub>M x \<and> (v = y \<and> (\<nexists>z. \<forall>q. (q \<epsilon> \<emptyset>) = (q = z)))"  
        unfolding set_defs by force
      then show "v \<epsilon> s"
        unfolding s[rule_format] by blast
    qed
  qed
  then show "\<exists>z. \<forall>u. (u \<epsilon> z) = (u \<epsilon> x \<or> u = y)"
    by blast
qed

sublocale L_setext_empty_setsuc_repl
  by unfold_locales

end

subsection \<open>Union\<close>

locale L_union = set_signature + 
  assumes union: "\<forall> x. \<exists> y.\<forall> v. v \<epsilon> y \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> v \<epsilon> u)"

locale L_setext_union = L_setext + L_union 

begin

lemma union_def'[set_defs]: "u \<epsilon> \<Union>\<^sub>M x \<longleftrightarrow> (\<exists> v. v \<epsilon> x \<and> u \<epsilon> v)"
  using collect_def_ex[OF union[rule_format, of x], folded unionM_def[of x]].

lemma union_trans_trans: assumes "\<forall> v. v \<epsilon> x \<longrightarrow> transM v"
  shows "transM (\<Union>\<^sub>M x)"
  using assms unfolding transM_def union_def' subsetM_def by blast

end

locale L_setext_sep_binunion_ts = L_setext + L_sep +  L_binunion + L_ts

begin

sublocale L_setext_binunion
  by unfold_locales

sublocale L_setext_sep_ts
  by unfold_locales

lemma trans_union: "transM u \<Longrightarrow> transM v \<Longrightarrow> transM (u \<union>\<^sub>M v)"
  by (simp add: binunion_def' subsetM_def transM_def)

lemma leastTS_union: "least_tsM (u \<union>\<^sub>M v) = least_tsM u \<union>\<^sub>M least_tsM v"
  unfolding setext least_ts_def' binunion_def'
proof (rule allI, rule iffI)
  fix z
  assume trans: "\<forall>x. transM x \<and> u \<union>\<^sub>M v \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x"
  show "(\<forall>x. transM x \<and> u \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x) \<or> (\<forall>x. transM x \<and> v \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x)"
  proof (rule disjCI)
    assume "\<not> (\<forall>x. transM x \<and> v \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x)"
    then obtain x where "transM x" "v \<subseteq>\<^sub>M x" "\<not> z \<epsilon> x"
      by blast
    show "\<forall>x. transM x \<and> u \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x"
    proof (rule allI, rule impI)
      fix y
      assume "transM y \<and> u \<subseteq>\<^sub>M y"
      with trans_union[OF \<open>transM x\<close>, of y]  
      have "transM (x \<union>\<^sub>M y) \<and> u \<union>\<^sub>M v \<subseteq>\<^sub>M x \<union>\<^sub>M y"
        using \<open>v \<subseteq>\<^sub>M x\<close>  binunion_def' subsetM_def by auto
      from trans[rule_format, OF this]
      show "z \<epsilon> y"
        using \<open>\<not> z \<epsilon> x\<close> unfolding binunion_def' by blast
    qed
  qed
next
  fix z
  assume or: "(\<forall>x. transM x \<and> u \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x) \<or> (\<forall>x. transM x \<and> v \<subseteq>\<^sub>M x \<longrightarrow> z \<epsilon> x)"
  show "\<forall>y. transM y \<and> u \<union>\<^sub>M v \<subseteq>\<^sub>M y \<longrightarrow> z \<epsilon> y"
  proof (rule allI, rule impI)  
    fix y
    assume "transM y \<and> u \<union>\<^sub>M v \<subseteq>\<^sub>M y"
    hence ins: "transM y \<and> u \<subseteq>\<^sub>M y" "transM y \<and> v \<subseteq>\<^sub>M y"
      unfolding subsetM_def binunion_def' by auto 
    show "z \<epsilon> y"
      by (rule disjE[OF or, rule_format]) (use ins in blast)+
  qed
qed

end

text \<open>The following locale is called Elementary Set Theory (EST) in Baratella and Ferro, "A theory of Sets with the Negation of the Axiom of Infinity", 1993.\<close>

locale L_setext_empty_union_repl_pair = L_setext + L_empty + L_union + L_repl + L_pair

begin

\<comment> \<open>binunion is the union of a pair\<close>
sublocale L_setext_pair_binunion
proof (unfold_locales, rule allI, rule allI) 
  fix x y
  from pair[rule_format, of x y] 
  obtain pair where pair: "\<forall>v. (v \<epsilon> pair) = (v = x \<or> v = y)"
    by blast
  show "\<exists>z. \<forall>v. (v \<epsilon> z) = (v \<epsilon> x \<or> v \<epsilon> y)"
    using union[rule_format, of pair] unfolding pair[rule_format] by simp
qed

end

text \<open>The locale  \<open>L_setext_empty_union_repl_pair\<close> (i.e., the fragment EST also used by Baratella and Ferro \<^cite>\<open>BaratellaFerro1993\<close>) is the right context in which to show that the schema of regularity yields existence of transitive closures (least transitive supersets)\<close>

locale L_setext_empty_union_repl_pair_regsch = L_setext + L_empty + L_union + L_repl + L_pair + L_regsch

begin

sublocale L_setext_empty_union_repl_pair
  by unfold_locales

sublocale L_setext_empty_repl
  by unfold_locales

sublocale L_setext_union
  by unfold_locales

lemma transitive_closure_ex:
  shows "\<forall> x. \<exists> z. x \<subseteq>\<^sub>M z \<and> transM z \<and> (\<forall> u. u \<epsilon> z \<longleftrightarrow> (\<forall> t. x \<subseteq>\<^sub>M t \<and> transM t \<longrightarrow> u \<epsilon> t))"
    (is "\<forall> x. \<exists> z. ?TC x z" is "\<forall> x. ?hasTC x") 
proof
  fix x' :: 'a
  have ind_rule: "SetFormulaPredicate (\<lambda>\<Xi>. ?hasTC(\<Xi> 0)) \<Longrightarrow> (\<And>x. (\<And>y. y \<epsilon> x \<Longrightarrow> ?hasTC y) \<Longrightarrow> ?hasTC x) \<Longrightarrow> ?hasTC x'"
    using  regsch_epsind[rule_format, of "\<lambda> \<Xi>. ?hasTC(\<Xi> 0)" "undefined" x', unfolded fun_upd_same] by argo
  show "\<exists>z. x' \<subseteq>\<^sub>M z \<and> transM z \<and> (\<forall>u. (u \<epsilon> z) = (\<forall>t. x' \<subseteq>\<^sub>M t \<and> transM t \<longrightarrow> u \<epsilon> t))"
  proof (rule ind_rule)
    fix x
    define TC where "TC = ?TC" \<comment> \<open>\<open>TC x z\<close> \<close>
    have sfp_tc: "SetFormulaPredicate (\<lambda>\<Xi>. TC (\<Xi> 0) (\<Xi> 1))"
      unfolding TC_def set_defs logsimps by (rule SFP_rules)+
    have tc_fun: "\<forall>u v w. TC u v \<and> TC u w \<longrightarrow> v = w"
      unfolding TC_def setext by blast
    show "SetFormulaPredicate (\<lambda>\<Xi>. ?hasTC(\<Xi> 0))"
      unfolding TC_def set_defs logsimps by (rule SFP_rules)+
    assume IP: "?hasTC y" if "y \<epsilon> x" for y
    define tcs where "tcs = \<Union>\<^sub>M (replaceM TC x)"
    have repl_x: "\<forall>v. (v \<epsilon> replaceM TC x) \<longleftrightarrow> (\<exists>u. u \<epsilon> x \<and> TC u v)" 
      by (rule replace_def'[OF sfp_tc, of _ 0 1 x, simplified fun_upd_same fun_upd_other]) fact   
    hence "transM tcs"
      unfolding TC_def tcs_def union_def' transM_def subsetM_def by blast
    hence tcs_mem: "w \<epsilon> tcs \<longleftrightarrow> (\<exists> y. y \<epsilon> x \<and> (\<exists> v. TC y v \<and> w \<epsilon> v))" for w
      unfolding tcs_def using union_def' repl_x by auto 
    show "?hasTC x"
    proof (rule exI[of _ "tcs \<union>\<^sub>M x"], fold conj_assoc, rule conjI, rule conjI)
      show "x \<subseteq>\<^sub>M tcs \<union>\<^sub>M x"
        unfolding tcs_def set_defs by blast
      show trans: "transM (tcs \<union>\<^sub>M x)" 
        unfolding transM_def binunion_def'
      proof (rule allI, rule impI, erule disjE)
        show "y \<subseteq>\<^sub>M tcs \<union>\<^sub>M x" if "y \<epsilon> tcs" for y
          using \<open>transM tcs\<close> that unfolding transM_def binunion_def' subsetM_def by blast 
        show "y \<subseteq>\<^sub>M tcs \<union>\<^sub>M x" if "y \<epsilon> x" for y
          unfolding subsetM_def tcs_def binunion_def' union_def' repl_x[rule_format] 
        proof (rule allI, rule impI, rule disjI1)
          fix z
          assume "z \<epsilon> y" 
          obtain w where  "TC y w"
            unfolding TC_def using IP[OF \<open>y \<epsilon> x\<close>] by blast
          hence "z \<epsilon> w"
            using \<open>z \<epsilon> y\<close> unfolding TC_def subsetM_def by blast
          hence "(y \<epsilon> x \<and> TC y w) \<and> z \<epsilon> w"
            using \<open>y \<epsilon> x\<close> \<open>TC y w\<close> by blast
          then show "\<exists>v. (\<exists>u. u \<epsilon> x \<and> TC u v) \<and> z \<epsilon> v"
            by blast
        qed
      qed
      show "\<forall>u. (u \<epsilon> tcs \<union>\<^sub>M x) \<longleftrightarrow> (\<forall>t. x \<subseteq>\<^sub>M t \<and> transM t \<longrightarrow> u \<epsilon> t)"
      proof (rule, rule, rule, rule)
        \<comment> \<open> \<open>tcs \<union>\<^sub>M x\<close> is the least transitive superset\<close>
        fix u t
        assume "u \<epsilon> tcs \<union>\<^sub>M x" "x \<subseteq>\<^sub>M t \<and> transM t"
        consider "\<exists> y. y \<epsilon> x \<and> (\<exists> w. TC y w \<and> u \<epsilon> w)" | "u \<epsilon> x"
          using \<open>u \<epsilon> tcs \<union>\<^sub>M x\<close> unfolding set_defs tcs_def repl_x[rule_format] by blast
        then show "u \<epsilon> t"
        proof (cases)
          assume "\<exists> y. y \<epsilon> x \<and> (\<exists> w. TC y w \<and> u \<epsilon> w)"
          then obtain y w where y_w: "y \<epsilon> x" "TC y w" "u \<epsilon> w"
            by blast
          have "y \<subseteq>\<^sub>M t"
            using \<open>y \<epsilon> x\<close> \<open>x \<subseteq>\<^sub>M t \<and> transM t\<close> unfolding transM_def subsetM_def by blast
          then show "u \<epsilon> t"
            using \<open>x \<subseteq>\<^sub>M t \<and> transM t\<close> y_w unfolding TC_def by blast
        qed (use \<open>x \<subseteq>\<^sub>M t \<and> transM t\<close> subsetM_def in blast) \<comment> \<open>the trivial case \<open>u \<epsilon> x\<close>\<close>
      qed (use \<open>x \<subseteq>\<^sub>M tcs \<union>\<^sub>M x\<close> local.trans in blast)  \<comment> \<open>the trivial implication: \<open>tcs \<union>\<^sub>M x\<close> is a transitive  superset\<close>
    qed
  qed
qed

sublocale L_setext_sep_reg_ts
    using transitive_closure_ex by unfold_locales blast   

end

locale L_setext_empty_power_union_repl  = L_setext + L_empty + L_power + L_union + L_repl

\<comment> \<open>ZF without infinity and regularity.
Axioms enabling reasoning about functions, cardinality, and therefore about Dedekind finiteness.\<close>

begin

sublocale L_setext_empty_power_repl
  by unfold_locales

sublocale L_setext_setsuc_sep
  by unfold_locales

sublocale L_setext_union
  by unfold_locales

sublocale L_setext_empty_union_repl_pair
  by unfold_locales

lemma ordered_pair_mem: assumes "v \<epsilon> x" "v' \<epsilon> y" shows "\<langle>v,v'\<rangle> \<epsilon> \<PP> (\<PP> (x \<union>\<^sub>M y))"
proof-
  have "{v}\<^sub>M \<epsilon> \<PP> (x \<union>\<^sub>M y)" "{v,v'}\<^sub>M \<epsilon> \<PP> (x \<union>\<^sub>M y)"
    using \<open>v \<epsilon> x\<close> \<open>v' \<epsilon> y\<close> unfolding set_defs by blast+
  thus ?thesis
    unfolding setext[of _ "\<PP> _"] powerset_def'[of _ "\<PP> _"]
      pair_def' subsetM_def ordered_pairM_def  by blast
qed

lemma ordered_pair_mem_union: assumes "\<langle>u,v\<rangle> \<epsilon> r" shows "u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)" "v \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)"
proof-
  have "(\<langle>u,v\<rangle> \<epsilon> r \<and> {u,v}\<^sub>M \<epsilon> \<langle>u,v\<rangle>) \<and> u \<epsilon> {u,v}\<^sub>M" "(\<langle>u,v\<rangle> \<epsilon> r \<and> {u,v}\<^sub>M \<epsilon> \<langle>u,v\<rangle>) \<and> v \<epsilon> {u,v}\<^sub>M"
    using assms unfolding pair_def' ordered_pairM_def by blast+
  then show "u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)" "v \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)" 
    unfolding union_def' by blast+
qed

lemma car_prod_ex: "\<exists> z. \<forall> u. u \<epsilon> z \<longleftrightarrow> (\<exists> v v'. v \<epsilon> x \<and> v' \<epsilon> y \<and> u = \<langle>v,v'\<rangle>)"
proof-
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<exists>v v'. v \<epsilon> \<Xi> 1 \<and> v' \<epsilon> \<Xi> 2 \<and> \<Xi> 0 = \<langle>v,v'\<rangle>)"
    unfolding set_defs logsimps by (rule SFP_rules)+
  from sep[rule_format, of _ "\<PP> (\<PP> (x \<union>\<^sub>M y))" "undefined(1:=x,2:=y)", OF this, simplified]
  show ?thesis
    using ordered_pair_mem by metis
qed

lemma car_prod_def': "u \<epsilon> x \<times>\<^sub>M y \<longleftrightarrow> (\<exists> v v'.  v \<epsilon> x \<and> v' \<epsilon> y \<and>  u = \<langle>v,v'\<rangle>)"
  unfolding cartesian_productM_def[rule_format] 
  using collect_def_ex[OF car_prod_ex, of _ x y] ordered_pair_mem by blast

lemma rel_inv_def': "u \<epsilon> rel_inverseM r \<longleftrightarrow> (\<exists> a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)"
proof-
  have SR: "SetRelation (\<lambda>u r. \<exists>a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)"
    unfolding SetRelation_def logsimps by (rule SFP_rules)+ 
  have eq: "(u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r) \<times>\<^sub>M \<Union>\<^sub>M (\<Union>\<^sub>M r) \<and> (\<exists>a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>))
            \<longleftrightarrow> (\<exists>a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)" for u
    unfolding car_prod_def'[rule_format] using ordered_pair_mem_union by blast 
    show ?thesis
      unfolding rel_inverseM_def 
      using collect_def_ex[of "\<lambda> v. (\<exists> a b. \<langle>a,b\<rangle> \<epsilon> r \<and> v = \<langle>b,a\<rangle>)"]
      sep_SR[rule_format,OF SR, of "\<Union>\<^sub>M (\<Union>\<^sub>M r) \<times>\<^sub>M \<Union>\<^sub>M (\<Union>\<^sub>M r)" r, unfolded eq] by simp
qed

lemma dom_def': "u \<epsilon> domM r \<longleftrightarrow> (\<exists>v. \<langle>u,v\<rangle> \<epsilon> r)"
  unfolding domM_def 
proof (rule collect_def_ex)
  have aux: "(\<exists>v. \<langle>u,v\<rangle> \<epsilon> r) \<longleftrightarrow> (\<exists> x. x \<epsilon> r \<and> (\<exists> w. x = \<langle>u,w\<rangle>))" for u
    by blast
  show "\<exists>w. \<forall>u. (u \<epsilon> w) = (\<exists>v. \<langle>u,v\<rangle> \<epsilon> r)"
    unfolding aux
    by (rule repl_SR[rule_format, of "\<lambda> x u. \<exists> w. x = \<langle>u,w\<rangle>" r]) force+
qed

lemma rng_def': "u \<epsilon> rngM r \<longleftrightarrow> (\<exists>v. \<langle>v,u\<rangle> \<epsilon> r)" 
  unfolding rngM_def 
proof (rule collect_def_ex)
  have aux: "(\<exists>v. \<langle>v,u\<rangle> \<epsilon> r) \<longleftrightarrow> (\<exists> x. x \<epsilon> r \<and> (\<exists> w. x = \<langle>w,u\<rangle>))" for u
    by blast
  show "\<exists>w. \<forall>u. (u \<epsilon> w) = (\<exists>v. \<langle>v,u\<rangle> \<epsilon> r)"
    unfolding aux
    by (rule repl_SR[rule_format, of "\<lambda> x u. \<exists> w. x = \<langle>w,u\<rangle>" r]) force+
qed

lemma SFP_dom[simp, intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k = domM (\<Xi> l))"
  unfolding setext dom_def' logsimps by (rule SFP_rules)+ 

lemma SFP_rng[simp, intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k = rngM (\<Xi> l))"
  unfolding setext rng_def' logsimps by (rule SFP_rules)+ 

lemmas[SFP_rules] = SFP_rng[unfolded set_defs logsimps] SFP_dom[unfolded set_defs logsimps]

lemma "SetRelation (\<lambda>x y. \<exists>f. one_oneM f \<and> x = domM f \<and> y = rngM f)"
    (is "SetRelation (\<lambda> x y. (\<exists> f. ?P x y f))")
    unfolding set_defs logsimps SetRelation_def by (rule SFP_rules)+

lemma SR_equiv[simp]: "SetRelation (\<lambda> x y. x \<approx>\<^sub>M y)"
  unfolding SetRelation_def  set_defs logsimps by (rule SFP_rules)+

lemma SP_dedekind[simp]: "SetProperty dedekind_fin"
  unfolding SetProperty_def dedekind_fin_def one_oneM_def set_equivalent_def set_defs logsimps by (rule SFP_rules)+

lemma SR_card: "SetRelation cardinality"
  unfolding set_defs logsimps SetRelation_def by (rule SFP_rules)+

lemma rel_inv_dom_rng: "domM (rel_inverseM r) = rngM r" "rngM (rel_inverseM r) = domM r"
  unfolding setext[of _ "rngM _"] setext[of _ "domM _"] dom_def' rng_def' rel_inv_def' ordered_pair_unique by blast+

lemma rel_inv_rel: "relationM f \<Longrightarrow> relationM (rel_inverseM f)"
  unfolding relationM_def rel_inv_def' by blast  

lemma one_one_inv: "one_oneM f \<Longrightarrow> one_oneM (rel_inverseM f)"
  unfolding one_oneM_def rel_inv_def' functionM_def ordered_pair_unique using rel_inv_rel by auto

lemma dedekind_setsuc_dedekind: assumes "dedekind_fin x" shows "dedekind_fin (setsucM x t)"
proof (cases "t \<epsilon> x") 
  assume "\<not> t \<epsilon> x"
  show ?thesis
    unfolding dedekind_fin_def  
  proof (rule allI, rule impI)
    have IH: "u \<subset>\<^sub>M x \<Longrightarrow> x \<approx>\<^sub>M u \<Longrightarrow> False" for u
      using assms unfolding dedekind_fin_def  by blast
    show "\<not> setsucM x t \<approx>\<^sub>M y" if "y \<subset>\<^sub>M setsucM x t" for y
    proof
      assume "setsucM x t \<approx>\<^sub>M y"
      then obtain f where f_bij: "one_oneM f" and f_dom: "domM f = setsucM x t" and f_rng: "rngM f = y" 
        unfolding set_equivalent_def by force
      obtain ft where "\<langle>t,ft\<rangle> \<epsilon> f"
        using f_dom[unfolded setext dom_def', rule_format, of t] unfolding setsuc_def' by force          
          \<comment> \<open>From this we construct a bijection \<open>g\<close> between  strict subset \<open>y'\<close> of \<open>x\<close> and \<open>x\<close>
       There are two different constructions. Depending on whether removing the pair \<open>fx,x\<close> from \<open>f\<close> 
       yields directly a bijection of \<open>x\<close> on its subset, or whether a modification is needed. 
       \<close>
      have "ft \<epsilon> y"
        using \<open>rngM f = y\<close> \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> unfolding setext rng_def' by blast
      consider "t \<epsilon> y \<and> ft \<noteq> t" | "y \<subseteq>\<^sub>M x \<or> ft = t" 
        using \<open>y \<subset>\<^sub>M setsucM x t\<close> unfolding subsetM_def proper_subsetM_def setsuc_def' by blast
      then show False
      proof (cases) 
        assume "y \<subseteq>\<^sub>M x \<or> ft = t" 
          \<comment> \<open>First construction just removes \<open>\<langle>t,ft\<rangle>\<close>\<close>
        from sep_SR[rule_format, OF SR_neq]  
        obtain y' where y': "\<forall> u. u \<epsilon> y' \<longleftrightarrow> u \<epsilon> y \<and> u \<noteq> ft"
          by presburger
        from sep_SR[rule_format, OF SR_neq]  
        obtain g where g: "\<forall> u. u \<epsilon> g \<longleftrightarrow> u \<epsilon> f \<and> u \<noteq> \<langle>t,ft\<rangle>" 
          by presburger
        show False
        proof (rule IH)
          show "y' \<subset>\<^sub>M x"
            using y' \<open>y \<subseteq>\<^sub>M x \<or> ft = t\<close>[unfolded subsetM_def] \<open>ft \<epsilon> y\<close> proper_subsetM_def \<open>y \<subset>\<^sub>M setsucM x t\<close>[unfolded proper_subsetM_def setsuc_def' setext[of y]] by metis 
          show "x \<approx>\<^sub>M y'"
          proof-  
            have "one_oneM g"
              using \<open>one_oneM f\<close> g unfolding one_oneM_def functionM_def relationM_def by blast
            have "domM g = x"
              using funD[OF conjunct1[OF f_bij[unfolded one_oneM_def]] \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close>] f_dom  \<open>\<not> t \<epsilon> x\<close>  
              unfolding setext[of "domM _"] dom_def' y'[rule_format] g[rule_format] one_oneM_def functionM_def setsuc_def' ordered_pair_unique 
              by auto
            have "rngM g = y'"
              using one_one_inj[OF f_bij \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close>] f_rng 
              unfolding setext[of "rngM _"] rng_def' y'[rule_format] g[rule_format] ordered_pair_unique
              by blast
            show "x \<approx>\<^sub>M y'"
              unfolding set_equivalent_def using \<open>rngM g = y'\<close> \<open>domM g = x\<close> \<open>one_oneM g\<close>  by blast 
          qed
        qed
      next
        assume "t \<epsilon> y \<and> ft \<noteq> t"
        then obtain pt where "\<langle>pt,t\<rangle> \<epsilon> f"
          using f_rng[unfolded setext rng_def', rule_format, of t] by blast
        hence "pt \<epsilon> x"
          using f_dom[unfolded setext[of "domM _"] dom_def' setsuc_def']
            one_oneD3[OF f_bij, rule_format, of t ft t] \<open>\<langle>pt,t\<rangle> \<epsilon> f\<close> \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> \<open>t \<epsilon> y \<and> ft \<noteq> t\<close> by blast  
        then show False
        proof- 
          \<comment> \<open>the second construction requires to modify the mapping \<open>f\<close> by adding \<open>\<langle>fx,px\<rangle>\<close>, not just to restrict \<open>f\<close>\<close>
          from sep_SR[rule_format, OF SR_neq]
          obtain y' where y': "\<forall> u. u \<epsilon> y' \<longleftrightarrow> u \<epsilon> y \<and> u \<noteq> t"
            by force
          have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> 0 = \<langle>\<Xi> 1,\<Xi> 2\<rangle> \<or> (\<Xi> 0 \<epsilon> \<Xi> 4 \<and> \<Xi> 0 \<noteq> \<langle>\<Xi> 3,\<Xi> 2\<rangle> \<and> \<Xi> 0 \<noteq> \<langle>\<Xi> 1,\<Xi> 3\<rangle>))"
            unfolding logsimps by (rule SFP_rules)+
          obtain g where g: "\<forall> u. u \<epsilon> g \<longleftrightarrow> (u = \<langle>pt,ft\<rangle> \<or> (u \<epsilon> f \<and> u \<noteq> \<langle>t,ft\<rangle> \<and> u \<noteq> \<langle>pt,t\<rangle>))"
            using sep[rule_format, OF sfp, of "setsucM f (\<langle>pt,ft\<rangle>)" "undefined(1:=pt, 2:=ft, 3:= t ,4:=f)", simplified] by auto
          show False
          proof (rule IH)
            show "y' \<subset>\<^sub>M x"
              using \<open>y \<subset>\<^sub>M setsucM x t\<close> \<open>t \<epsilon> y \<and> ft \<noteq> t\<close> unfolding proper_subsetM_def y'[rule_format] setsuc_def' setext[of y] setext[of y'] by blast
            show "x \<approx>\<^sub>M y'"
            proof-  
              have "one_oneM g"
                by (rule one_oneI, unfold g[rule_format] ordered_pair_unique) 
                (use one_oneD1[OF f_bij] in blast, 
                use one_oneD2[OF f_bij] \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> in blast,
                use one_oneD3[OF f_bij] \<open>\<langle>pt,t\<rangle> \<epsilon> f\<close> in blast) 
              have "domM g = x"
                unfolding setext[of "domM _"] dom_def' 
              proof (rule allI, rule iffI)
                fix z assume "\<exists>v. \<langle>z,v\<rangle> \<epsilon> g" 
                show "z \<epsilon> x"
                  using \<open>\<exists>v. \<langle>z,v\<rangle> \<epsilon> g\<close> \<open>pt \<epsilon> x\<close>  one_oneD3[OF f_bij, rule_format, of t ft _] \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> f_dom[unfolded setext[of "domM _"] setsuc_def' dom_def'] unfolding ordered_pair_unique 
                    g[rule_format] by blast
              next
                fix z assume " z \<epsilon> x" 
                then show "\<exists>v. \<langle>z,v\<rangle> \<epsilon> g"
                  unfolding g[rule_format] using f_dom[unfolded setext[of "domM _"] setsuc_def' dom_def'] by (cases "z = pt") (use \<open>\<not> t \<epsilon> x\<close> in auto) 
              qed
              have "rngM g = y'"
                unfolding setext[of "rngM _"] rng_def'
              proof (rule allI, rule iffI)
                fix z assume "\<exists>v. \<langle>v,z\<rangle> \<epsilon> g"
                show "z \<epsilon> y'"
                  using 
                    one_oneD2[OF f_bij]
                   \<open>\<exists>v. \<langle>v,z\<rangle> \<epsilon> g\<close> \<open>ft \<epsilon> y\<close> \<open>t \<epsilon> y \<and> ft \<noteq> t\<close>  \<open>\<langle>pt,t\<rangle> \<epsilon> f\<close> \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close>
                  unfolding f_rng[unfolded setext[of "rngM _"]  rng_def', rule_format, symmetric, of z]  y'[rule_format] ordered_pair_unique g[rule_format] by blast
              next
                fix z assume "z \<epsilon> y'"
                show "\<exists>v. \<langle>v,z\<rangle> \<epsilon> g"
                  using \<open>z \<epsilon> y'\<close>[unfolded y'[rule_format]]
                  unfolding f_rng[unfolded setext[of "rngM _"]  rng_def', rule_format, symmetric, of z] g[rule_format] ordered_pair_unique by blast
              qed
              show "x \<approx>\<^sub>M y'"
                unfolding set_equivalent_def using \<open>rngM g = y'\<close> \<open>domM g = x\<close> \<open>one_oneM g\<close>  by blast 
            qed
          qed
        qed
      qed
    qed
  qed
qed (simp add: assms)    

lemma set_equivalent_sym: "x \<approx>\<^sub>M y \<longleftrightarrow> y \<approx>\<^sub>M x"
proof-
  have "x \<approx>\<^sub>M y \<Longrightarrow>  y \<approx>\<^sub>M x" for x y
  proof-
    assume "x \<approx>\<^sub>M y"
    then obtain f where f : "one_oneM f" "x = domM f" "y = rngM f"     
      unfolding set_equivalent_def by blast
    show "y \<approx>\<^sub>M x"
      unfolding set_equivalent_def 
      by (rule exI[of _ "rel_inverseM f"]) (simp add: one_one_inv[OF \<open>one_oneM f\<close>] f(2,3) rel_inv_dom_rng) 
  qed
  thus ?thesis 
    by blast
qed

lemma compose_def': "u \<epsilon> f \<circ>\<^sub>M g \<longleftrightarrow> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)"
proof-
  have ex: "\<exists>w. \<forall>u. (u \<epsilon> w) = (u \<epsilon> domM g \<times>\<^sub>M rngM f  \<and> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>))"
    using sep[rule_format, OF SFP_compose[of 1 2 0], of "domM g \<times>\<^sub>M rngM f" "undefined(1:=g, 2:= f)"] 
    by simp
  have aux: "u \<epsilon> domM g \<times>\<^sub>M rngM f  \<and> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>) \<longleftrightarrow> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)" for u
    using dom_def' rng_def' car_prod_def' by auto
  have "u \<epsilon> f \<circ>\<^sub>M g \<longleftrightarrow> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)" (is "u \<epsilon> f \<circ>\<^sub>M g \<longleftrightarrow> ?Q u")
    unfolding composeM_def  
    using collect_def_ex[of "\<lambda> u. ?Q u", OF ex[unfolded aux]].  
  then show ?thesis
    unfolding car_prod_def' dom_def'[of _ g] rng_def'[of _ f]  by blast 
qed  

lemma rel_comp: assumes "relationM f" "relationM g" shows "relationM (f \<circ>\<^sub>M g)"
  using assms unfolding relationM_def compose_def' by blast

lemma fun_comp: assumes "functionM f" "functionM g" shows "functionM (f \<circ>\<^sub>M g)"
  using assms rel_comp unfolding functionM_def  compose_def' ordered_pair_unique by blast 

lemma one_one_comp: assumes "one_oneM f" "one_oneM g" shows "one_oneM (f \<circ>\<^sub>M g)"
  using assms fun_comp unfolding one_oneM_def  compose_def' ordered_pair_unique by blast  

lemma set_equivalent_trans: assumes "x \<approx>\<^sub>M y" "y \<approx>\<^sub>M z" shows "x \<approx>\<^sub>M z"
proof-
  obtain f1 where f1: "one_oneM f1" and  "x = domM f1" "y = rngM f1"
    using \<open>x \<approx>\<^sub>M y\<close> unfolding set_equivalent_def by blast
  obtain f2 where f2: "one_oneM f2" and "y = domM f2" "z = rngM f2"
    using \<open>y \<approx>\<^sub>M z\<close> unfolding set_equivalent_def by blast
  have "one_oneM (f2 \<circ>\<^sub>M f1)"
    using f1 f2 one_one_comp by blast
  have "x = domM (f2 \<circ>\<^sub>M f1)"
     unfolding dom_def'  setext unfolding compose_def' ordered_pair_unique
   proof (rule allI, rule iffI)
     fix u assume "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> u = a \<and> v = c"
     then show "u \<epsilon> x"
       unfolding \<open>x = domM f1\<close>[unfolded setext dom_def', rule_format] by blast
   next
     fix u assume "u \<epsilon> x"
     then obtain b where \<open>\<langle>u,b\<rangle> \<epsilon> f1\<close> "b \<epsilon> y"
       unfolding \<open>x = domM f1\<close>[unfolded setext dom_def', rule_format]
                 \<open>y = rngM f1\<close>[unfolded setext rng_def', rule_format] by blast
     then obtain c where \<open>\<langle>b,c\<rangle> \<epsilon> f2\<close> "c \<epsilon> z"
       unfolding \<open>y = domM f2\<close>[unfolded setext dom_def', rule_format]
                 \<open>z = rngM f2\<close>[unfolded setext rng_def', rule_format] by blast
     show "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> u = a \<and> v = c"
       using \<open>\<langle>u,b\<rangle> \<epsilon> f1\<close> \<open>\<langle>b,c\<rangle> \<epsilon> f2\<close> by auto
   qed
  have "z = rngM (f2 \<circ>\<^sub>M f1)"
     unfolding rng_def'  setext unfolding compose_def' ordered_pair_unique
   proof (rule allI, rule iffI)
     fix u assume "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> v = a \<and> u = c"
     then show "u \<epsilon> z"
       unfolding \<open>z = rngM f2\<close>[unfolded setext rng_def', rule_format] by blast
   next
     fix u assume "u \<epsilon> z"
     then obtain b where \<open>\<langle>b,u\<rangle> \<epsilon> f2\<close> "b \<epsilon> y"
       unfolding \<open>y = domM f2\<close>[unfolded setext dom_def', rule_format]
                 \<open>z = rngM f2\<close>[unfolded setext rng_def', rule_format] by blast
     then obtain c where \<open>\<langle>c,b\<rangle> \<epsilon> f1\<close> "c \<epsilon> x"
       unfolding \<open>x = domM f1\<close>[unfolded setext dom_def', rule_format]
                 \<open>y = rngM f1\<close>[unfolded setext rng_def', rule_format] by blast
     show "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> v = a \<and> u = c"
       using \<open>\<langle>b,u\<rangle> \<epsilon> f2\<close> \<open>\<langle>c,b\<rangle> \<epsilon> f1\<close> by auto
   qed
  show ?thesis
      unfolding set_equivalent_def
      using \<open>one_oneM (f2 \<circ>\<^sub>M f1)\<close> \<open>x = domM (f2 \<circ>\<^sub>M f1)\<close> \<open>z = rngM (f2 \<circ>\<^sub>M f1)\<close> by blast 
qed

lemma union_of_ords_regular: assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y"
  shows "regular (\<Union>\<^sub>M s)"
  using assms ord_mem_ord set_of_ords_regular union_def' by blast

lemma union_of_ords_ord: assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y"
  shows "ordM (\<Union>\<^sub>M s)"   
proof-
  have t: "transM (\<Union>\<^sub>M s)"
    using assms epschain_def ordM_def union_trans_trans by blast 
  have r: "regular (\<Union>\<^sub>M s)"
    by (simp add: assms union_of_ords_regular)
  have o: "ordM v" if "v \<epsilon> (\<Union>\<^sub>M s)" for v
    using assms(1) ord_mem_ord that union_def' by blast
  show "ordM (\<Union>\<^sub>M s)"
    unfolding ordM_def epschain_def using t r o ordM_total by blast
qed

lemma union_ord: assumes "ordM x" shows "ordM (\<Union>\<^sub>M x)"
  using assms ord_mem_ord union_of_ords_ord by blast

lemma non_limit_union_ord_mem: assumes "\<forall> u. u \<epsilon> s \<longrightarrow> ordM u" "is_sucM (\<Union>\<^sub>M s)"
  shows "\<Union>\<^sub>M s \<epsilon> s"
proof-
  obtain m where m: "\<forall> z. z \<epsilon> \<Union>\<^sub>M s \<longleftrightarrow> z \<epsilon> m \<or> z = m"
    using \<open>is_sucM (\<Union>\<^sub>M s)\<close> is_sucM_def by blast
  then obtain ymax where "ymax \<epsilon> s" "m \<epsilon> ymax" 
    unfolding union_def' by blast
  from assms(1)[rule_format, OF \<open>ymax \<epsilon> s\<close>]
  have "\<Union>\<^sub>M s \<subseteq>\<^sub>M ymax"
    unfolding subsetM_def m[rule_format] using \<open>m \<epsilon> ymax\<close> using ordM_trans[of ymax _ m] by blast 
  then have "ymax = \<Union>\<^sub>M s"
    using \<open>ymax \<epsilon> s\<close> unfolding setext subsetM_def subsetM_def union_def' by blast
  then show "\<Union>\<^sub>M s \<epsilon> s"
    using \<open>ymax \<epsilon> s\<close> by blast 
qed

lemma limit_ord: assumes "\<forall> u. u \<epsilon> s \<longrightarrow> ordM u \<and> setsucM u u \<epsilon> s"
  shows "\<not> is_sucM (\<Union>\<^sub>M s)"
  by (metis assms non_limit_union_ord_mem ordM_regular regular_not_self_mem_sep setsuc_def'
      union_def') 

lemma not_limit_ord: assumes "ordM x" "is_sucM x" 
  shows "x = setsucM (\<Union>\<^sub>M x) (\<Union>\<^sub>M x)"
proof-
  obtain m where m: "x = setsucM m m"
    using \<open>is_sucM x\<close> unfolding setext is_sucM_def setsuc_def' by blast
  hence "ordM m"
    using \<open>ordM x\<close> ord_mem_ord setsuc_def' by presburger
  have "m = \<Union>\<^sub>M x"
    unfolding m setext[of m] union_def' setsuc_def'  
    using ordM_trans[OF \<open>ordM m\<close>] by blast  
  then show ?thesis
    using m by force
qed

lemma natM_fin: assumes "s \<subseteq>\<^sub>M x" "s \<noteq> \<emptyset>" "\<forall> u. u \<epsilon> s \<longrightarrow> setsucM u u \<epsilon> s" 
  shows "\<not> natM x"
proof
  have "\<exists> u. u \<epsilon> \<Union>\<^sub>M s"
    using assms union_def'[of _ s] setsuc_def' emptyset_def' by metis
  assume "natM x"
  from natM_D[OF this]
  have "\<Union>\<^sub>M s \<subseteq>\<^sub>M x"
    unfolding subsetM_def union_def' using ordM_trans \<open>s \<subseteq>\<^sub>M x\<close>[unfolded  subsetM_def] by blast 
  have "ordM (\<Union>\<^sub>M s)"
    using \<open>ordM x\<close> union_of_ords_ord ord_mem_ord \<open>s \<subseteq>\<^sub>M x\<close>[unfolded subsetM_def] by blast
  have "natM (\<Union>\<^sub>M s)"
    using ordM_subset_mem[OF \<open>ordM x\<close> \<open>ordM (\<Union>\<^sub>M s)\<close>, unfolded proper_subset_def'] \<open>natM x\<close>
     nat_mem_nat \<open>\<Union>\<^sub>M s \<subseteq>\<^sub>M x\<close> by blast
  from nat_is_suc[OF this \<open>\<exists> u. u \<epsilon> \<Union>\<^sub>M s\<close>]
  show False
    using assms limit_ord natM_D[OF nat_mem_nat[OF \<open>natM x\<close>]] unfolding subsetM_def by force
qed

lemma nat_induction_sfp: assumes "SetFormulaPredicate P" and  "P (\<Xi>(0:=\<emptyset>))"  and
  step: "\<And> x. natM x \<Longrightarrow> P (\<Xi>(0:=x)) \<Longrightarrow> P (\<Xi>(0:=setsucM x x))" and "natM x"
  shows "P (\<Xi>(0:=x))"
proof (rule ccontr)
  assume "\<not> P (\<Xi>(0:=x))"
  define v where "v = separationM x (\<lambda> x. P(\<Xi>(0:=x)))"
  from separ_def_SFP[OF \<open>SetFormulaPredicate P\<close>]
  have v: "u \<epsilon> v \<longleftrightarrow> u \<epsilon> x \<and> P(\<Xi>(0:=u))" for u
    unfolding v_def by simp 
  hence "\<emptyset> \<epsilon> v"
    using \<open>P (\<Xi>(0:=\<emptyset>))\<close> \<open>\<not> P (\<Xi>(0:=x))\<close> \<open>natM x\<close> emp_natM empty_is_empty ordM_total unfolding natM_def by fast
  have "(setsucM y y) \<epsilon> v" if "y \<epsilon> v" for y
    unfolding v[of "setsucM y y"] using \<open>\<not> P (\<Xi>(0:=x))\<close> \<open>natM x\<close> that[unfolded v[of y]] step[of y] ord_mem_suc[of x y] nat_mem_nat[of x y] natM_D[OF \<open>natM x\<close>]
    by fast
  thus False
    using \<open>\<emptyset> \<epsilon> v\<close> notE[OF natM_fin[of v x], OF _ _ _ \<open>natM x\<close>] v
    by (metis emptyset_def' subsetM_def) 
qed

\<comment> \<open>Schema of induction for natural numbers\<close>
lemma nat_induction_sp: assumes "SetProperty P" and  "P \<emptyset>" and "natM x" and
  step: "\<And> x. natM x \<Longrightarrow> P x \<Longrightarrow> P (setsucM x x)"
shows "P x"
  using assms unfolding SetProperty_def using nat_induction_sfp by force  

theorem nat_tarski_fin: assumes "natM x" shows "tarski_fin x"
  using nat_induction_sp[OF SP_tarski empty_tarski \<open>natM x\<close>] tarski_setsuc_tarski by blast

lemma nat_dedekind_finite: assumes "natM x"  shows "dedekind_fin x"
  using nat_induction_sp[OF SP_dedekind empty_dedekind \<open>natM x\<close>] dedekind_setsuc_dedekind by blast

lemma card_emp: "cardinality \<emptyset> \<emptyset>" 
proof-
  have "natM \<emptyset>"
    by simp
  moreover have "one_oneM \<emptyset>" 
    unfolding one_oneM_def functionM_def relationM_def by simp
  moreover have "\<emptyset> = domM \<emptyset>" "\<emptyset> = rngM \<emptyset>"                          
    unfolding setext dom_def' rng_def' by simp_all 
  ultimately show ?thesis
    unfolding cardinality_def set_equivalent_def 
    using exI[of "\<lambda> f.  one_oneM f \<and> \<emptyset> = domM f \<and> \<emptyset> = rngM f" \<emptyset>] by blast
qed

lemma nat_equiv_unique: assumes "natM x" "natM y" "x \<approx>\<^sub>M y"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  have "\<not> y \<epsilon> x"  
    using \<open>x \<noteq> y\<close> assms nat_dedekind_finite[unfolded dedekind_fin_def, rule_format, OF \<open>natM x\<close>] ordM_D1[OF natM_D[OF \<open>natM x\<close>]] subsetM_def proper_subset_def' by blast 
  have "\<not> x \<epsilon> y"  
    using \<open>x \<noteq> y\<close> assms nat_dedekind_finite[unfolded dedekind_fin_def, rule_format, OF \<open>natM y\<close>] ordM_D1[OF natM_D[OF \<open>natM y\<close>]] 
     subsetM_def proper_subset_def' set_equivalent_sym[of x y] by blast
  show False
    using \<open>\<not> x \<epsilon> y\<close> \<open>\<not> y \<epsilon> x\<close> \<open>x \<noteq> y\<close>  ordM_total[OF natM_D natM_D, OF assms(1,2)] by blast
qed     

lemma card_fun: assumes "cardinality x n" "cardinality x m" shows "n = m"
  using assms unfolding cardinality_def  using nat_equiv_unique set_equivalent_sym set_equivalent_trans  by blast

end

locale L_setext_empty_power_union_repl_reg  = L_setext + L_empty + L_power + L_union + L_repl 
+ L_reg

begin
text \<open>Some consequences of the axiom of regularity\<close>

sublocale L_setext_empty_power_union_repl
  by unfold_locales

lemma mem_not_refl: "\<not> x \<epsilon> x"
 by (simp add: regular_not_self_mem)    

lemma mem_antisym: "\<not> (u \<epsilon> v \<and> v \<epsilon> u)"
  by (meson any_reg regular_antisym_mem setsuc)   

lemma  suc_unique:  assumes "setsucM c c = setsucM d d" 
  shows "c = d"
proof (rule ccontr)
  assume "c \<noteq> d"
  from assms[unfolded setext setsuc_def'[of "_ \<union>\<^sub>M _"], unfolded setsuc_def']
  have "c \<epsilon> d" "d \<epsilon> c"
    using \<open>c \<noteq> d\<close> by blast+
  thus False
    using mem_antisym by blast
qed

lemma mem_neq_singleton: "x \<noteq> {x}\<^sub>M"
  by (metis reg singleton_def')
   
lemma suc_subset[simp]: "z \<subset>\<^sub>M setsucM z z"
  unfolding proper_subsetM_def  setext setsuc_def'
  singleton_def' using mem_not_refl[of z] by blast

lemma card_setsuc: assumes "\<not> y \<epsilon> x" "cardinality x m" shows "cardinality (setsucM x y)  (setsucM m m)"
proof-
  obtain f where "one_oneM f" "x = domM f" "m = rngM f" "natM m"
    using \<open>cardinality x m\<close> unfolding cardinality_def set_equivalent_def by blast
  let ?f = "setsucM f (\<langle>y,m\<rangle>)"
  have "natM (setsucM m m)"
    by (simp add: \<open>natM m\<close> nat_suc_nat)
  have "setsucM x y = domM ?f"
    using \<open>x = domM f\<close> unfolding setext dom_def' by auto
  have "setsucM m m = rngM ?f"
    using \<open>m = rngM f\<close> unfolding setext rng_def' by auto
  have "relationM ?f"
    unfolding relationM_def
    using \<open>one_oneM f\<close> functionM_def one_oneM_def relationM_def by auto 
  then have "functionM ?f"
    unfolding functionM_def
    using \<open>one_oneM f\<close> \<open>x = domM f\<close> \<open>\<not> y \<epsilon> x\<close> dom_def' funD one_oneD3 by auto 
  then have "one_oneM ?f"
    unfolding one_oneM_def 
    using   \<open>\<not> y \<epsilon> x\<close> one_one_inj[OF \<open>one_oneM f\<close>] \<open>m = rngM f\<close> mem_not_refl[of m] 
    rng_def'  by auto 
  show ?thesis
    unfolding cardinality_def set_equivalent_def 
    using \<open>setsucM m m = rngM ?f\<close> \<open>natM (setsucM m m)\<close> \<open>one_oneM ?f\<close> \<open>setsucM x y = domM ?f\<close> by blast
qed                                    

end

subsection \<open>Successor induction\<close> 

text \<open>An important fragment of the theory of hereditarily finite sets. The finiteness principle used is the induction schema for set formulas.
 This route to axiomatizating ZFfin is developed in Vopěnka: Mathematics in the alternative set theory \<^cite>\<open>Vopenka1979\<close>.
Notice that no regularity principles are used in this fragment.\<close>

locale L_setext_empty_setsuc_setind = L_setext + L_empty + L_setsuc + L_setind 

begin

sublocale L_setext_empty_setsuc
  by unfold_locales

lemma binunion_ex:
  shows "\<exists> z. (\<forall> u. u \<epsilon> z \<longleftrightarrow> u \<epsilon> x \<or> u \<epsilon> x')" (is "?P x x'")
proof-
  have SR: "SetRelation ?P"
    unfolding SetRelation_def logsimps by (rule SFP_rules)+ 
  show ?thesis
  proof (rule  setind[rule_format, OF  SR[unfolded SetRelation_def], of "undefined(0:=x,1:=x')", simplified], force)
    fix x y :: 'a
    assume ex: "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (u \<epsilon> x \<or> u \<epsilon> x')"
    then show "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (u \<epsilon> x \<or> u = y \<or> u \<epsilon> x')"
      unfolding setsuc_def' using setsuc[rule_format, of _ y]  by metis
  qed  
qed

sublocale L_union
proof (unfold_locales, rule allI, rule setind_SP[rule_format])
  show "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. v \<epsilon> \<emptyset> \<and> u \<epsilon> v)"
    by (meson empty_is_empty)
next 
  fix x y
  have aux: "(\<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. (v \<epsilon> x \<or> v = y) \<and> u \<epsilon> v)) \<longleftrightarrow> (\<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists> v. v \<epsilon> x \<and> u \<epsilon> v) \<or> u \<epsilon> y)" for z
    by blast
  let ?Q = "\<lambda> z. \<forall>u. (u \<epsilon> z) = (\<exists>v. (v \<epsilon> x \<or> v = y) \<and> u \<epsilon> v)"
  assume "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. v \<epsilon> x \<and> u \<epsilon> v)"
  thus "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. v \<epsilon> (setsucM x y) \<and> u \<epsilon> v)"
    unfolding setsuc_def' aux using binunion_ex[rule_format, of _ y] by metis
next
  show "SetProperty (\<lambda>a. \<exists>z. \<forall>u. (u \<epsilon> z) = (\<exists>v. v \<epsilon> a \<and> u \<epsilon> v))"
    unfolding SetProperty_def logsimps by (rule SFP_rules)+
qed

sublocale L_repl
proof (unfold_locales, rule impI, rule allI)
  fix P x \<Xi> 
  assume "SetFormulaPredicate P" and func: "\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))"
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "\<forall> \<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow>  P \<Xi> = P \<Xi>'"
    by blast
  hence small: "P (\<Xi>(m := x, 0 := u, 1 := v)) = P (\<Xi>(0 := u, 1 := v))" for u v x
    by simp
  let ?P = "\<lambda>\<Xi>. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> P (\<Xi> (0:=u,1:=v)))"
  have sfp: "SetFormulaPredicate ?P"
    by (rule SFP_replace) fact+  
  note aux_rule = setind_var[rule_format, of ?P \<Xi> m x, OF sfp, unfolded small, simplified, unfolded One_nat_def[symmetric]] 
  show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
  proof (rule aux_rule)
    fix x y
    assume "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
    then obtain z where z: "\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
      by blast
    obtain y' where y': "P (\<Xi>(0 := y, 1 := y'))"
      using func by blast
    show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. (u \<epsilon> x \<or> u = y) \<and> P (\<Xi>(0 := u, 1 := v)))"
      by (rule exI[of "\<lambda> z. \<forall>v. (v \<epsilon> z) = (\<exists>u. (u \<epsilon> x \<or> u = y) \<and> P (\<Xi>(0 := u, 1 := v)))" "setsucM z y'"])
       (unfold setsuc_def', use y' z func in blast)
  qed (simp only: empty)
qed

sublocale L_setext_empty_repl
  by unfold_locales

lemma setsuc_separ: assumes "y \<epsilon> u" 
  shows "u = setsucM (separationM u (\<lambda> x. x \<noteq> y)) y"
proof-
  have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<noteq> \<Xi> 1)"
    by (rule SFP_rules)+
  show ?thesis 
    unfolding setext[of u] setsuc_def' separ_def_SR[of "(\<noteq>)" _ u y, unfolded SetRelation_def, OF sfp] using \<open>y \<epsilon> u\<close> by blast
qed

lemma setsuc_subset_setind: "u \<subseteq>\<^sub>M setsucM x y \<longleftrightarrow> u \<subseteq>\<^sub>M x \<or> (\<exists> u'. u' \<subseteq>\<^sub>M x \<and> u = setsucM u' y)"
proof
  assume "u \<subseteq>\<^sub>M setsucM x y"
  show "u \<subseteq>\<^sub>M x \<or> (\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = setsucM u' y)"
  proof (unfold disj_imp, rule impI)   
    assume "\<not> u \<subseteq>\<^sub>M x"
    hence "y \<epsilon> u"
      using \<open>u \<subseteq>\<^sub>M setsucM x y\<close> subsetM_def setsuc_def' by auto 
    have "separationM u (\<lambda> x. x \<noteq> y)  \<subseteq>\<^sub>M x"
      using \<open>u \<subseteq>\<^sub>M setsucM x y\<close> unfolding subsetM_def
      separ_def_SR[of "(\<noteq>)", unfolded SetRelation_def, OF SFP_neg[OF SFP_eq]] setsuc_def' by blast
    with setsuc_separ[OF \<open>y \<epsilon> u\<close>]
    show "\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = setsucM u' y"
      by blast
  qed
next
  assume "u \<subseteq>\<^sub>M x \<or> (\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = setsucM u' y)"
  then show "u \<subseteq>\<^sub>M setsucM x y "
  proof
    show "u \<subseteq>\<^sub>M x \<Longrightarrow> u \<subseteq>\<^sub>M setsucM x y"
      unfolding subsetM_def setsuc_def' by blast
    assume "\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = setsucM u' y"
    then show "u \<subseteq>\<^sub>M setsucM x y"
      unfolding subsetM_def setext[of u] setsuc_def' by blast
  qed
qed
        
sublocale L_power
proof (unfold_locales, rule allI)
  fix x
  show "\<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M x"
proof (rule setind_SP[rule_format])
  show "SetProperty (\<lambda>a. \<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M a)"
    unfolding SetProperty_def logsimps set_defs by (rule SFP_rules)+
  show "\<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M \<emptyset>"
    using singleton_def'[of _ "\<emptyset>"]  by auto   
    fix x y 
    let ?P = "\<lambda> \<Xi>. \<Xi> 1 = setsucM (\<Xi> 0) (\<Xi> 2)"
    have sfp: "SetFormulaPredicate ?P"
      unfolding setext logsimps set_defs by (rule SFP_rules)+
    have ex1: "\<exists>! v. v = u \<union>\<^sub>M {y}\<^sub>M" for u
      by blast 
    have binunion_def': "u \<epsilon> x \<union>\<^sub>M y \<longleftrightarrow> u \<epsilon> x \<or> u \<epsilon> y" for u x y
       using collect_def_ex[OF binunion_ex[rule_format, of x y], folded binunionM_def].
    assume "\<exists>z. \<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M x"
    then obtain z where z: "\<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M x"
      by blast
    obtain z' where z': "\<forall> v. v \<epsilon> z' \<longleftrightarrow> (\<exists> u. u \<epsilon> z \<and> v = setsucM u y)"
      using replf[OF sfp, of "undefined(2:=y)",  simplified] by blast
    show "\<exists>z. \<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M setsucM x y"
      by (rule exI[of "\<lambda> z.(\<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M setsucM x y)" "z \<union>\<^sub>M z'"])
        (unfold binunion_def' setsuc_subset_setind, use z z' in simp)
  qed 
qed


\<comment> \<open>Axioms of ZF without infinity and regularity are theorems\<close>

sublocale L_setext_empty_power_union_repl
  by unfold_locales

lemma min_subset_ex: assumes "u \<noteq> \<emptyset>" shows "\<exists> z. z \<epsilon> u \<and> (\<nexists> w. w \<epsilon> u \<and> w \<subset>\<^sub>M z)"
proof (rule mp[OF _ assms], rule setind_SP[rule_format])
  show "SetProperty (\<lambda>a. a \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> a \<and> (\<nexists>w. w \<epsilon> a \<and> w \<subset>\<^sub>M z)))"
    unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+
next
  fix  x y
  assume IH: "x \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> x \<and> (\<nexists>w. w \<epsilon> x \<and> w \<subset>\<^sub>M z))"
  show "setsucM x y \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> setsucM x y \<and> (\<nexists>w. w \<epsilon> setsucM x y \<and> w \<subset>\<^sub>M z))" 
  proof (rule impI, cases "x = \<emptyset>")
    assume "x = \<emptyset>"
    then show "\<exists>z. z \<epsilon> setsucM x y \<and> (\<nexists>w. w \<epsilon> setsucM x y \<and> w \<subset>\<^sub>M z)"
      using setsuc_def' by force
  next
    assume "x \<noteq> \<emptyset>"
    from IH[rule_format, OF this]
    obtain u where "u \<epsilon> x" and nex: "\<nexists>w. w \<epsilon> x \<and> w \<subset>\<^sub>M u"
      by blast
    show "\<exists>z. z \<epsilon> setsucM x y \<and> (\<nexists>w. w \<epsilon> setsucM x y \<and> w \<subset>\<^sub>M z)"
    proof (cases "y \<subset>\<^sub>M u")
      assume "y \<subset>\<^sub>M u"
      have "y \<epsilon> setsucM x y"
        using setsuc_def' by auto
      show ?thesis
      proof (rule exI[of _ y], rule conjI[OF \<open>y \<epsilon> setsucM x y\<close>], rule notI)
        assume "\<exists>w. w \<epsilon> setsucM x y \<and> w \<subset>\<^sub>M y"
        then show False
          using \<open>y \<subset>\<^sub>M u\<close> \<open>y \<epsilon> setsucM x y\<close> nex proper_subsetM_trans[OF _ \<open>y \<subset>\<^sub>M u\<close>]
          by (metis proper_subsetM_def setsuc_def') 
      qed
    next
      assume "\<not> y \<subset>\<^sub>M u"
      show ?thesis
        by (rule exI[of _ u]) (use setsuc_def' \<open>u \<epsilon> x\<close> nex \<open>\<not> y \<subset>\<^sub>M u\<close> in metis)
    qed
  qed
qed simp

text \<open>A general variant of Tarski finiteness axiom (also proved in Vopěnka's book). 
Nonempty sets have maximal (and minimal) elements under inclusion.\<close>

lemma max_subset_ex: assumes "u \<noteq> \<emptyset>" shows "\<exists> z. z \<epsilon> u \<and> (\<nexists> w. w \<epsilon> u \<and> z \<subset>\<^sub>M w)"
proof (rule mp[OF _ assms], rule setind_SP[rule_format])
  show "SetProperty (\<lambda>a. a \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> a \<and> (\<nexists>w. w \<epsilon> a \<and> z \<subset>\<^sub>M w)))"
    unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+
next
  fix  x y
  assume IH: "x \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> x \<and> (\<nexists>w. w \<epsilon> x \<and> z \<subset>\<^sub>M w))"
  show "setsucM x y \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> setsucM x y \<and> (\<nexists>w. w \<epsilon> setsucM x y \<and> z \<subset>\<^sub>M w))" 
  proof (rule impI, cases "x = \<emptyset>")
    assume "x = \<emptyset>"
    then show "\<exists>z. z \<epsilon> setsucM x y \<and> (\<nexists>w. w \<epsilon> setsucM x y \<and> z \<subset>\<^sub>M w)"
      using setsuc_def' by force
  next
    assume "x \<noteq> \<emptyset>"
    from IH[rule_format, OF this]
    obtain u where "u \<epsilon> x" and nex: "\<nexists>w. w \<epsilon> x \<and> u \<subset>\<^sub>M w"
      by blast
    show "\<exists>z. z \<epsilon> setsucM x y \<and> (\<nexists>w. w \<epsilon> setsucM x y \<and> z \<subset>\<^sub>M w)"
    proof (cases "u \<subset>\<^sub>M y")
      assume "u \<subset>\<^sub>M y"
      have "y \<epsilon> setsucM x y"
        using setsuc_def' by auto
      show ?thesis
      proof (rule exI[of _ y], rule conjI[OF \<open>y \<epsilon> setsucM x y\<close>], rule notI)
        assume "\<exists>w. w \<epsilon> setsucM x y \<and> y \<subset>\<^sub>M w"
        then show False
          using \<open>u \<subset>\<^sub>M y\<close> \<open>y \<epsilon> setsucM x y\<close> nex proper_subsetM_trans[OF _ \<open>u \<subset>\<^sub>M y\<close>]
          by (metis proper_subsetM_def setsuc_def')
      qed
    next
      assume "\<not> u \<subset>\<^sub>M y"
      show ?thesis
        by (rule exI[of _ u]) (use setsuc_def' \<open>u \<epsilon> x\<close> nex \<open>\<not> u \<subset>\<^sub>M y\<close> in metis)
    qed
  qed
qed simp

lemma max_mem: assumes "P n" "n \<epsilon> x" "SetProperty P"
  shows "\<exists> m. m \<epsilon> x \<and> P m \<and> (\<forall> k. k \<epsilon> x \<and> P k \<longrightarrow> \<not> m \<subset>\<^sub>M k)"
proof (rule ccontr)
  assume contr: "\<nexists>m. m \<epsilon> x \<and> P m \<and> (\<forall>k. k \<epsilon> x \<and> P k \<longrightarrow> \<not> m \<subset>\<^sub>M k)"
  hence chain: "\<exists> k. k \<epsilon> x \<and> P k \<and>  m \<subset>\<^sub>M k" if a: "P m" "m \<epsilon> x" for m
    using that by blast
  define y where "y = separationM x P"    
  from separ_def_SP[OF \<open>SetProperty P\<close>, of _ x, folded y_def]
  have y_def: "(u \<epsilon> y) \<longleftrightarrow> (u \<epsilon> x \<and> P u)" for u
    by simp
  have "y \<noteq> \<emptyset>"
    using assms y_def by force
  show False
    using max_subset_ex[OF \<open>y \<noteq> \<emptyset>\<close>] chain unfolding y_def by blast
qed

sublocale L_tarski
  using max_subset_ex 
  by unfold_locales (simp add: tarski_fin_def, metis empty)  

sublocale L_dedekind
  by unfold_locales
  (use setind_SP[rule_format, OF SP_dedekind empty_dedekind] dedekind_setsuc_dedekind in blast) 
    
lemma fun_images: assumes "SetFormulaPredicate P" and "\<forall> u. (\<exists>! v. P(\<Xi>(0:=u,1:=v)))"
  shows "\<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P(\<Xi>(0:=u,1:=v))))" 
proof-
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'" 
    by blast
  hence m: "\<forall>\<Xi> \<Xi>'. (\<forall>i<m+2. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'" 
    by simp
  have small: "P (\<Xi>(Suc (Suc m) := x, 0 := u, Suc 0 := v)) = P (\<Xi>(0 := u, Suc 0 := v))" for u v x
    by (rule m[rule_format]) simp 
  let ?P = "\<lambda> X. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> (X (m+2)) \<and> P (X(0 := u, 1 := v)))"
  have "SetFormulaPredicate ?P"
    using SFP_replace[OF \<open>SetFormulaPredicate P\<close> m].
  note aux_rule = setind_var[OF this, of "\<Xi>((m+2):= x)" "m+2", simplified, unfolded small, folded One_nat_def] 
  show "\<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P(\<Xi>(0:=u,1:=v))))"
  proof (rule aux_rule[rule_format]) 
    show "\<exists>z. \<forall>v. \<not> v \<epsilon> z"
      using empty by blast
  next
    fix x y
    assume "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
    then obtain z where z_def: "\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))" 
      by blast
    obtain y' where "P (\<Xi>(0 := y, 1 := y'))"
      using assms(2) by blast
    have witness: "\<forall> v. v \<epsilon> setsucM z y' \<longleftrightarrow> (\<exists> u. u \<epsilon> setsucM x y \<and> P (\<Xi>(0 := u, 1 := v)))"
      unfolding setsuc_def' using  \<open>P (\<Xi>(0 := y, 1 := y'))\<close> assms(2) z_def by auto
    show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. (u \<epsilon> x \<or> u = y) \<and> P (\<Xi>(0 := u, 1 := v)))"
      by (rule exI[of _ "setsucM z y'"]) (use witness in force) 
  qed
qed

sublocale L_fin
proof (unfold_locales, rule notI)
  assume "\<exists>x. \<emptyset> \<epsilon> x \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> setsucM y y \<epsilon> x)"
  then obtain x where "\<emptyset> \<epsilon> x" and suc: "\<forall>y. y \<epsilon> x \<longrightarrow> setsucM y y \<epsilon> x" 
    by blast
  have SP: "SetProperty (\<lambda> x. regular x \<and> transM x)"
    unfolding SetProperty_def unfolding set_defs logsimps by (rule SFP_rules)+
  from sep_SP[OF this, rule_format, of x]
  obtain x' where x': "\<forall> u. u \<epsilon> x' \<longleftrightarrow> u \<epsilon> x \<and> regular u \<and> transM u"
    by blast
  have "x' \<noteq> \<emptyset>" "\<emptyset> \<epsilon> x'"
    using x' \<open>\<emptyset> \<epsilon> x\<close> by force+ 
  have suc': "y \<epsilon> x' \<longrightarrow> setsucM y y \<epsilon> x'" for y
    unfolding x'[rule_format] using suc by (simp add: regular_setsuc trans_suc_trans) 
  from max_subset_ex[OF \<open>x' \<noteq> \<emptyset>\<close>]
  obtain xmax where "xmax \<epsilon> x'" "\<nexists> w. w \<epsilon> x' \<and> xmax \<subset>\<^sub>M w"
    by blast
  with suc'[rule_format, OF \<open>xmax \<epsilon> x'\<close>]
  have "\<not> xmax \<subset>\<^sub>M setsucM xmax xmax"
    by blast
  then have "xmax \<epsilon> xmax"
    unfolding set_defs setext[of xmax] by blast
  then show False
    using \<open>xmax \<epsilon> x'\<close> regular_not_self_mem x' by blast
qed    

theorem ord_is_suc: assumes "ordM x"  shows "x = \<emptyset> \<or> is_sucM x"
  using assms empty_mem_ord fin ord_limit_or_suc by blast

theorem ord_iff_nat: "ordM x \<longleftrightarrow> natM x"
proof (rule iffI)
  assume "ordM x"
  show "natM x"
  proof (cases "x = \<emptyset>") 
    assume "x \<noteq> \<emptyset>"
    show "natM x"
    proof (rule natM_I, fact)
      fix v assume "\<exists> u. u \<epsilon> v" "v \<epsilon> x" 
      then show "is_sucM v"
        using ord_mem_ord[OF \<open>ordM x\<close> \<open>v \<epsilon> x\<close>] ord_is_suc[of v] by fastforce
    qed (use ord_is_suc[OF \<open>ordM x\<close>] \<open>x \<noteq> \<emptyset>\<close> in auto)
  qed simp
qed (use natM_def in blast)

lemma ord_iff_empty_or_suc: "ordM x \<longleftrightarrow> x = \<emptyset> \<or> (\<exists> y. ordM y \<and> x = setsucM y y)"
  by (metis emp_natM not_limit_ord ord_is_suc ord_iff_nat ord_suc_ord union_ord)

lemma union_of_ords_mem:  assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y" "s \<noteq> \<emptyset>" 
  shows "\<Union>\<^sub>M s \<epsilon> s"
  using \<open>s \<noteq> \<emptyset>\<close> emptyset_def' non_limit_union_ord_mem[OF assms(1)] ord_is_suc[OF union_of_ords_ord[OF assms(1)]]
    union_def' by metis

end

subsection \<open>Negation of inf\<close>

text \<open>ZF with inf replaced by fin\<close>

locale L_setext_empty_power_union_repl_reg_fin  = L_setext + L_empty + L_power + L_union + L_repl + L_reg + L_fin

begin

sublocale L_setext_empty_power_union_repl_reg
  by unfold_locales

sublocale L_setind
proof (unfold_locales, (rule impI)+, rule allI, rule ccontr)
  fix P \<Xi> x
  assume "SetFormulaPredicate P" "P (\<Xi> (0:= \<emptyset>))" and step:  "\<forall>x y. P (\<Xi> (0:= x)) \<longrightarrow> P ((\<Xi> (0:=setsucM x y)))" and "\<not> (P (\<Xi> (0:=x)))"
  have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. cardinality (\<Xi> 0) (\<Xi> 1))"
    unfolding set_defs logsimps by (rule SFP_rules)+
  have cinj: "cardinality u v \<and> cardinality u w \<Longrightarrow> v = w" for u v w
    using card_fun by auto
  from sep[OF \<open>SetFormulaPredicate P\<close>, rule_format, of"\<PP> x" \<Xi>]
  obtain s where s: "\<forall>u. (u \<epsilon> s) = (u \<epsilon> \<PP> x \<and> P (\<Xi>(0 := u)))"
    by blast
  from replp_vars[rule_format, OF sfp, of \<Xi> 0 1 s, simplified] 
  obtain m where m: "\<forall>v. (v \<epsilon> m) = (\<exists>a. a \<epsilon> s \<and> cardinality a v) " 
    using cinj by blast
  have "\<emptyset> \<epsilon> m"
    using card_emp exI[of "\<lambda> x. x \<subseteq>\<^sub>M x \<and> P (\<Xi> (0:=x, 1:=\<emptyset>)) \<and> cardinality x \<emptyset>" \<emptyset>] \<open>P (\<Xi> (0:=\<emptyset>))\<close> 
    unfolding m[rule_format] powerset_def' subsetM_def s[rule_format]
    using emptyset_def'  by auto 
  have "setsucM n n \<epsilon> m" if "n \<epsilon> m" for n
  proof-                  
    obtain y where "y \<epsilon> \<PP> x" "cardinality y n" "P (\<Xi> (0:=y))"
      using m  \<open>n \<epsilon> m\<close> s by fast
    obtain y' where "y' \<epsilon> x" "\<not> y' \<epsilon> y" 
      using \<open>y \<epsilon> \<PP> x\<close> \<open>P (\<Xi> (0:=y))\<close> \<open>\<not> P (\<Xi> (0:=x))\<close> subsetM_antisym powerset_def' subsetM_def by blast
    show "setsucM n n \<epsilon> m"
      unfolding m[rule_format] 
    proof (rule exI[of _ "setsucM y y'"])  
      show "setsucM y y' \<epsilon> s \<and> cardinality (setsucM y y') (setsucM n n)"
        using card_setsuc[OF \<open>\<not> y' \<epsilon> y\<close> \<open>cardinality y n\<close>] \<open>y \<epsilon> \<PP> x\<close> \<open>y' \<epsilon> x\<close>  
          step[rule_format, OF \<open>P (\<Xi>(0:= y))\<close>] unfolding powerset_def' subsetM_def s[rule_format] by simp
    qed 
  qed
  then show False
    using fin \<open>\<emptyset> \<epsilon> m\<close> by blast
qed

lemma cardinality_ex: "\<exists>! n. natM n \<and> x \<approx>\<^sub>M n"
proof (rule ex_ex1I)
  show "\<exists> n. natM n \<and> x \<approx>\<^sub>M n"
  proof (rule setind_SP[rule_format])
    show "SetProperty (\<lambda>a. \<exists>n. natM n \<and> a \<approx>\<^sub>M n)"
      unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+
    show "\<exists>n. natM n \<and> \<emptyset> \<approx>\<^sub>M n"
      using card_emp cardinality_def by blast
    show "\<exists>n. natM n \<and> setsucM x y \<approx>\<^sub>M n" if "\<exists>n. natM n \<and> x \<approx>\<^sub>M n" for x y
      using that card_setsuc setsuc_triv unfolding cardinality_def  by metis 
  qed
  show "natM n \<and> x \<approx>\<^sub>M n \<Longrightarrow> natM y \<and> x \<approx>\<^sub>M y \<Longrightarrow> n = y" for n x y
    using nat_equiv_unique set_equivalent_sym set_equivalent_trans by blast
qed

sublocale L_setext_empty_setsuc_setind
  by unfold_locales

end

subsection \<open>Dedekind finite\<close>

locale L_setext_empty_power_union_repl_dedekind = L_setext + L_empty + L_power + L_union + L_repl + L_dedekind

begin

sublocale L_setext_empty_power_union_repl
  by unfold_locales  

sublocale L_fin
proof (unfold_locales, rule notI)
  assume "\<exists>x. \<emptyset> \<epsilon> x \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> setsucM y y \<epsilon> x)"
  then obtain x' where x': "\<emptyset> \<epsilon> x'" "\<forall>y. y \<epsilon> x' \<longrightarrow> setsucM y y \<epsilon> x'"
    by blast
  define x where "x = separationM x' natM"
  from separ_def_SP[OF SP_nat]
  have x: "u \<epsilon> x \<longleftrightarrow> u \<epsilon> x' \<and> natM u" for u
    unfolding x_def. 
  have x_setsuc: "u \<epsilon> x \<longrightarrow> setsucM u u \<epsilon> x" for u
    using x'(2) nat_suc_nat[of u] unfolding x by blast 
  have "SetFormulaPredicate (\<lambda> \<Xi>. \<exists> v. \<Xi> 0 = \<langle>v,setsucM v v\<rangle>)"
    unfolding logsimps set_defs by (rule SFP_rules)+ 
  from sep[OF this, rule_format, of "x \<times>\<^sub>M x", simplified]
  obtain f where "u \<epsilon> f \<longleftrightarrow> (u \<epsilon> x \<times>\<^sub>M x  \<and> (\<exists>v. u = \<langle>v,setsucM v v\<rangle>))" for u
    by blast
  hence f: "u \<epsilon> f \<longleftrightarrow> (\<exists> v. v \<epsilon> x \<and> u = \<langle>v,setsucM v v\<rangle>)" for u
    using car_prod_def' x_setsuc by auto
  have "one_oneM f"
   by (rule one_oneI, unfold f x, blast, unfold ordered_pair_unique)  
    (use ord_pred_fun[OF natM_D natM_D] in blast)+ 
  have "domM f = x"
    unfolding setext[of _ x] f dom_def' by force 
  have "x \<approx>\<^sub>M rngM f"
    unfolding set_equivalent_def by (rule exI[of _ f]) (use \<open>one_oneM f\<close> \<open>domM f = x\<close> in blast)
  have "rngM f \<subset>\<^sub>M x"
  proof (rule proper_subsetI)
    show "rngM f \<subseteq>\<^sub>M x"
      unfolding subsetM_def rng_def' f ordered_pair_unique using x_setsuc by blast
    show "rngM f \<noteq> x"
      unfolding setext[of _ x] rng_def' not_all
    proof (rule exI[of _ \<emptyset>])
      have t: "\<emptyset> \<epsilon> x = True"
        by (simp add: x x'(1))
      have f: "(\<exists> v. \<langle>v,\<emptyset>\<rangle> \<epsilon> f) = False"
        unfolding f ordered_pair_unique setext[of \<emptyset>] binunion_def' singleton_def' by force
      show "(\<exists>v. \<langle>v,\<emptyset>\<rangle> \<epsilon> f) \<noteq> (\<emptyset> \<epsilon> x)"
        unfolding t f by blast
    qed
  qed
  from dedekind[unfolded dedekind_fin_def, rule_format, OF this] 
  show False
    using \<open>x \<approx>\<^sub>M rngM f\<close> by blast
qed

end
  
subsection \<open>Tarski finite\<close>

locale L_setext_empty_power_sep_setsuc_tarski = L_setext + L_empty + L_power + L_sep + L_setsuc + L_tarski

begin

sublocale L_setext_empty_power
  by unfold_locales

sublocale L_setext_empty_setsuc 
  by unfold_locales

text \<open>In a suitable context, the axiom of Tarski finitness yields the set induction schema.\<close>

sublocale L_setind
proof (unfold_locales, rule impI, rule impI, rule allI)
  fix P \<Xi> x
  assume set_p: "SetFormulaPredicate P" and
    step: "(\<forall>x y. P (\<Xi>(0 := x)) \<longrightarrow> P (\<Xi>(0 := setsucM x y)))" and
    "P (\<Xi>(0 := \<emptyset>))"
  show "P (\<Xi>(0 := x))"
  proof (rule ccontr)
    assume "\<not> P (\<Xi>(0 := x))"
    obtain z where z_def: "\<And> u. (u \<epsilon> z) \<longleftrightarrow> (u \<epsilon> (\<PP> x) \<and> P (\<Xi>(0 := u)))" 
      using sep[OF set_p, rule_format, of "\<PP> x"] by blast   
    have "z \<noteq> \<emptyset>" 
      using z_def \<open>P (\<Xi>(0 := \<emptyset>))\<close> empty_is_empty empty_is_subset subsetM_def powerset_def' by blast
    have "z \<subseteq>\<^sub>M \<PP> x"
      by (simp add: subsetM_def z_def)
    have neg: "\<exists> v. v \<epsilon> z \<and> u \<subset>\<^sub>M v" if "u \<epsilon> z" for u
    proof-
      obtain y where "\<not> y \<epsilon> u" and "y \<epsilon> x"
        using  \<open>\<not> P (\<Xi>(0 := x))\<close> \<open>u \<epsilon> z\<close>[unfolded z_def] setext[of u x] unfolding subsetM_def powerset_def' by blast
      have "(setsucM u y) \<epsilon> z"
        using \<open>y \<epsilon> x\<close> step[rule_format,of u y] powerset_def' subsetM_def setsuc_def' that z_def by auto
      moreover have "u \<subset>\<^sub>M (setsucM u y)" 
        unfolding proper_subsetM_def setext[of u] setsuc_def' 
        using \<open>\<not> y \<epsilon> u\<close>  by blast
      ultimately show ?thesis
        by blast
    qed
    show False
      using tarski[rule_format, of x, unfolded tarski_fin_def, rule_format, of z] \<open>z \<subseteq>\<^sub>M \<PP> x\<close> neg \<open>z \<noteq> \<emptyset>\<close> 
      unfolding subsetM_def powerset_def' z_def
      using \<open>P (\<Xi>(0 := \<emptyset>))\<close> empty_is_empty by blast   
  qed   
qed

sublocale L_setext_empty_setsuc_setind
  by unfold_locales 

text \<open>It follows in particular that union and replacement are provable in this context.\<close>

sublocale L_repl
  by unfold_locales

sublocale L_union
  by unfold_locales

end

subsection \<open>Set induction and regularity schema\<close>

text \<open>An apparently minor variation of the set induction schema, 
which nevertheless yields also the schema of regularity (i.e., epsilon induction). 
It is used in Pudlák and Sochor \<^cite>\<open>PudlakSochor1984\<close>.\<close>

locale L_setindregsch = set_signature +
  assumes setindregsch: "SetFormulaPredicate P \<Longrightarrow> 
    P(\<Xi>(0:= \<emptyset>)) \<longrightarrow> (\<forall> x y. P(\<Xi>(0:= x)) \<and> P(\<Xi>(0:= y)) \<longrightarrow> P(\<Xi>(0:= setsucM x y))) \<longrightarrow> (\<forall> x. P(\<Xi>(0:= x)))"

begin

lemma setindregsch_sp: assumes "SetProperty P" "P \<emptyset>" "\<forall> x y. P x \<and> P y \<longrightarrow> P (setsucM x y)"
  shows "\<forall> x. P x"
  using setindregsch[OF \<open>SetProperty P\<close>[unfolded SetProperty_def]] assms by force

lemma setindregsch_var: assumes "SetFormulaPredicate P" "P(\<Xi>(n:= \<emptyset>))" "\<forall> x y. P(\<Xi>(n:= x)) \<and> P(\<Xi>(n:= y)) 
  \<longrightarrow> P(\<Xi>(n:= setsucM x y))"
  shows "\<forall> x. P(\<Xi>(n:= x))"
proof
  fix x
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "P \<Xi> = P \<Xi>'" if "\<forall>i<m. \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  let ?m = "Suc (n + m)"  
  let ?f = "id(0 := ?m, n:= 0)"
  let ?Q = "\<lambda> X. (P (\<lambda> b. X (?f  b)))"
  let ?X = "\<Xi>(?m:= \<Xi> 0)" 
  have sfpq:  "SetFormulaPredicate ?Q"
    using transform_variables[OF \<open>SetFormulaPredicate P\<close>] by simp
  have small: "\<forall> i < m. (\<Xi>(n := u)) i = (?X (0 := u)) (?f i)" for u
    by auto
  have equiv: "(P (\<Xi>(n := u))) \<longleftrightarrow> (?Q (?X (0 := u)))" for u
    by (rule m[of "\<Xi>(n := u)" "\<lambda> b. (?X (0 := u))(?f b)"]) fact
  show "P (\<Xi>(n := x))"
    unfolding equiv
    by (rule setindregsch[rule_format, OF sfpq, of "\<Xi>(Suc (n + m) := \<Xi> 0)"], unfold equiv[symmetric])
     (use assms in blast)+    
qed  

\<comment> \<open>Induction schema for set formulas is a theorem.\<close>

sublocale L_setind
  by unfold_locales (use setindregsch in blast)

end

locale L_setext_empty_setsuc_setindregsch = L_setext + L_empty + L_setsuc + L_setindregsch 

begin
 
sublocale L_setext_empty_setsuc_setind
  by unfold_locales

lemma epsind_from_setindregsch_sp: assumes spp: "SetProperty P" and indp: "(\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> P y))  \<longrightarrow>  P x)"
  shows "\<forall> x. P x"
proof-
  let ?Q = "\<lambda> x. \<forall> u. (u \<epsilon> x \<longrightarrow> P u)"
  have "SetFormulaPredicate (\<lambda>\<Xi>. P (\<Xi> m))" for m
     using spp[unfolded SetProperty_def] by (rule transform_variables) 
   have "SetProperty ?Q" 
     unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+ fact
   have "\<forall> v w. ?Q v \<and> ?Q w \<longrightarrow> ?Q  (setsucM v w)"  \<comment>\<open>use \<open>?Q\<close> w and \<open>indp\<close> to show P w\<close>
     using indp unfolding setsuc_def' by presburger
   from setindregsch_sp[OF \<open>SetProperty ?Q\<close> _ this]
   have " \<forall> x. ?Q x " 
     by force
   then show " \<forall> x. P x "
     using indp by blast 
 qed

\<comment> \<open>Epsilon induction (and hence, regularity schema) is a theorem.\<close>

lemma epsind_from_setindregsch: assumes sfp: "SetFormulaPredicate P" and indp: "(\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> P(\<Xi>(0:=y))))  \<longrightarrow>  P(\<Xi>(0:=x)))"
  shows "\<forall> x. P(\<Xi>(0:=x))"
proof
  fix x
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'"
    by blast
  then have small: "P(\<Xi>(Suc m:=a, 0:= u)) = P(\<Xi>(0:= u))" for \<Xi> a u
    by simp
  let ?Q = "\<lambda> \<Xi>. \<forall> u. (u \<epsilon> (\<Xi> (Suc m)) \<longrightarrow> P(\<Xi>(0:=u)))"
  have sfpQ: "SetFormulaPredicate ?Q"
    by (rule SFP_all[of "\<lambda> \<Xi>. (\<Xi> 0) \<epsilon> (\<Xi> (m+1)) \<longrightarrow> P \<Xi>" 0, simplified])
    (unfold logsimps set_defs, (rule | fact)+)
  thm setindregsch_var[OF \<open>SetFormulaPredicate ?Q\<close>, of _ "Suc m", unfolded small, simplified]
  have "?Q (\<Xi> (0:=v))  \<and> ?Q (\<Xi> (0:=w)) \<longrightarrow> ?Q (\<Xi> (0:=(v\<union>\<^sub>M{w}\<^sub>M)))" for v w \<Xi> 
   \<comment>\<open>use ?Q w and indp to show P w\<close>
    unfolding setsuc_def' using indp[rule_format] by simp
  from setindregsch_var[OF \<open>SetFormulaPredicate ?Q\<close>, of _ "Suc m", unfolded small, simplified]
  have " ?Q (\<Xi>(Suc m:= x))"
    unfolding small fun_upd_same using indp by metis
  then show "P (\<Xi>(0 := x))"
     using indp unfolding small fun_upd_same by blast 
 qed

sublocale L_epsind
  by (unfold_locales) (use epsind_from_setindregsch in blast)

sublocale L_setext_empty_union_repl_pair_regsch
  by unfold_locales

end

subsection \<open>Summary of dependencies\<close>

theorem epsind_regsch_iff:
  "L_epsind mem \<longleftrightarrow> L_regsch mem"
proof
  assume "L_epsind mem"
  from L_epsind.epsind_regsch[OF this]
  show "L_regsch mem"
    by unfold_locales blast
next
  assume "L_regsch mem"
  from L_regsch.regsch_epsind[OF this]
  show "L_epsind mem"
    by unfold_locales
qed

text \<open>We give additional names to some important collections of axioms.
Here is a "canonical" axiomatization of the theory of hereditarily finite sets.\<close>

locale ZFfin =  L_setext + L_empty + L_power + L_union +  L_repl + L_fin + L_epsind

begin
sublocale L_setext_empty_power_union_repl_reg_fin
  by unfold_locales
sublocale L_regsch
  by unfold_locales
sublocale L_reg
  by unfold_locales
sublocale L_setsuc
  by unfold_locales
sublocale L_sep
  by unfold_locales
sublocale L_setind
  by unfold_locales
sublocale L_dedekind
  by unfold_locales
sublocale L_tarski
  by unfold_locales
end

text \<open>This is the list of axioms for sets from Vopěnka's book \<^cite>\<open>Vopenka1979\<close>.\<close>

locale ASTset = L_setext + L_empty + L_setsuc + L_setind + L_regsch

begin

text \<open>Vopěnka \<^cite>\<open>Vopenka1979\<close> shows that all axioms of @{term ZFfin} are provable in @{term ASTset}\<close>

sublocale ZFfin
proof-
  interpret L_setext_empty_setsuc_setind
    by unfold_locales
  interpret L_epsind
    by (simp add: L_regsch_axioms epsind_regsch_iff) 
  show "ZFfin (\<epsilon>)"
    by unfold_locales
qed

text \<open>The variation of set induction which combines it with regularity schema is provable from set induction schema and epsilon induction 
(i.e., regularity schema). Taken for granted in  \<^cite>\<open>PudlakSochor1984\<close>.\<close>

sublocale L_setindregsch
proof (unfold_locales, rule impI, rule impI, rule allI)
  fix P :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and \<Xi> and x
  let ?P = "\<lambda> y. P (\<Xi>(0 := y))"
  assume sfp: "SetFormulaPredicate P"
  show "?P x" if "?P \<emptyset>" and  step: "(\<forall>x y. ?P x \<and> ?P y \<longrightarrow> ?P (setsucM x y))"
  proof-
    \<comment>\<open>In order to complete the proof by \<open>\<epsilon>\<close>-induction, it is enough to show that all sets inherit the property \<open>?P\<close>. 
       Call this inheritance property \<open>Q\<close>\<close>
    let ?Q = "\<lambda> w. (\<forall> u. u \<epsilon> w \<longrightarrow> ?P u) \<longrightarrow> ?P w"
      \<comment>\<open>We show that all sets satisfy \<open>Q\<close> by set-induction.\<close>

\<comment> \<open>But first some work has to be done. Note that \<open>?Q\<close> depends on free variables present in \<open>P\<close>.
  We therefore have to reformulate \<open>?Q\<close> to reflect this. 
  We formulate \<open>Q\<close> as a property of a fresh variable \<open>\<Xi> (m+1)\<close>\<close>
    from bounded_free[OF sfp]
    obtain m where m: "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'" 
      by blast
    have fresh: " P (\<Xi>(m + k := a, 0 := b)) =  P (\<Xi>(0 := b))" for a b k \<Xi>
      \<comment> \<open>Indeed, \<open>P\<close> does not depend on any \<open>\<Xi> (m+k)\<close>\<close> 
      using m[rule_format, of "\<Xi>(m + k := a, 0 := b)" "\<Xi>(0 := b)"] by simp  

    let ?Q' = "\<lambda> \<Xi>. (\<forall> u. u \<epsilon> \<Xi> (m+1) \<longrightarrow> P (\<Xi>(0 := u))) \<longrightarrow> P (\<Xi>(0 := \<Xi> (m+1)))"
      \<comment> \<open>\<open>?Q' \<Xi>\<close> now says: \<open>x\<^sub>m\<^sub>+\<^sub>1\<close> inherits \<open>P\<close> from its elements\<close>
    have "SetFormulaPredicate ?Q'"
      \<comment> \<open>The technical part: showing that \<open>?Q'\<close> is set formula predicate\<close>
    proof-
      have "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>u. u \<epsilon> \<Xi> (Suc m) \<longrightarrow> P (\<Xi>(0 := u)))"
        by (rule SFP_all[of "\<lambda>\<Xi>. \<Xi> (m+2) \<epsilon> \<Xi> (Suc m) \<longrightarrow> P (\<Xi>(0 := \<Xi>(m+2)))" "m+2", 
              simplified fun_upd_same fun_upd_other, unfolded fresh])
          (unfold logsimps, rule+, fact) 
      show "SetFormulaPredicate ?Q'"
        unfolding logsimps by (rule SFP_rules)+ 
        (simp, fact, simp add: sfp update_variable)  
    qed
      \<comment>\<open>This yields the desired form of the induction in terms of \<open>?Q\<close>\<close>
    have Q_ind_rule: "?Q \<emptyset> \<Longrightarrow> (\<forall> x y. ?Q x \<longrightarrow> ?Q (setsucM x y)) \<Longrightarrow> \<forall> x. ?Q x"
      using 
         setind_var[rule_format, OF \<open>SetFormulaPredicate ?Q'\<close>, of \<Xi> "m+1"]
      unfolding fresh fun_upd_same by (rule, blast+) 

\<comment>\<open>Back to the main proof.\<close>
    have "\<forall> w. ?Q w"
    proof (rule Q_ind_rule)
      show "?Q \<emptyset>"
        using \<open>?P \<emptyset>\<close> by blast
          \<comment> \<open>the empty set inherits \<open>P\<close>, since it satisfies \<open>P\<close>\<close>
      show "\<forall> x y. ?Q x \<longrightarrow> ?Q (setsucM x y)"
      proof (rule allI, rule allI, rule impI, rule impI)
        fix x y
        assume \<open>?Q x\<close> and "\<forall>u. u \<epsilon> setsucM x y \<longrightarrow> ?P u" 
        hence "?P x" "?P y"
          using \<open>?Q x\<close> unfolding setsuc_def' by blast+
        thus "?P (setsucM x y)"
          using step by blast
      qed
    qed
    thus "?P x"
      using epsind[OF \<open>SetFormulaPredicate P\<close>] unfolding fun_upd_same fresh by metis
  qed
qed

end

text \<open>\<open>ZFfin\<close> and \<open>ASTset\<close> are two different axiomatizations of the same theory.\<close>

sublocale ASTset \<subseteq> ZFfin
  by unfold_locales
sublocale ZFfin \<subseteq> ASTset
  by (simp add: ASTset_def L_empty_axioms L_regsch_axioms L_setext_axioms L_setind_axioms L_setsuc_axioms)
  
text \<open>In the AST, set induction and epsilon induction (i.e., regularity schema) can be replaced by the variant \<open>setindregsch\<close>\<close>

theorem setindregsch_ast: "L_setext_empty_setsuc_setindregsch mem \<longleftrightarrow> ASTset mem"
proof
  assume "L_setext_empty_setsuc_setindregsch mem"
  then interpret  L_setext_empty_setsuc_setindregsch "mem".
  show "ASTset mem"
    by unfold_locales
next
  assume "ASTset mem"
  then interpret  ASTset "mem".
  show "L_setext_empty_setsuc_setindregsch mem"
    by unfold_locales
qed  

theorem zffin_ast: "ZFfin mem \<longleftrightarrow> ASTset mem"
proof
  assume "ZFfin mem"
  then interpret  ZFfin "mem".
  show "ASTset mem"
    by unfold_locales
next
  assume "ASTset mem"
  then interpret  ASTset "mem".
  show "ZFfin mem"
    by unfold_locales
qed  

text \<open>Ambivalence of the separation schema and the replacement schema.\<close>

theorem repl_implies_sep:
  shows "L_setext_empty_repl mem \<Longrightarrow> L_sep mem"
proof-
  assume "L_setext_empty_repl mem"
  then interpret L_setext_empty_repl "mem".
  show "L_sep mem"
    by unfold_locales
qed

text \<open>Under certain finiteness assumptions, separation entails replacement. See \<^cite>\<open>Behounek1998\<close> for details.\<close>

theorem sep_implies_repl:
  shows "L_setext_empty_power_sep_setsuc_tarski mem \<Longrightarrow> L_repl mem"
proof-
  assume "L_setext_empty_power_sep_setsuc_tarski mem"
  then interpret L_setext_empty_power_sep_setsuc_tarski "mem".
  show "L_repl mem"
    by unfold_locales
qed

text \<open>Entailment between different finiteness principles, in their natural contexts.\<close>

text \<open>The following is included in Vopěnka \<^cite>\<open>Vopenka1979\<close> by exploring the consequences of induction for set formulas.\<close>

theorem (in L_setext_empty_setsuc) 
  shows setind_implies_tarski: "L_setind (\<epsilon>) \<Longrightarrow> L_tarski (\<epsilon>)" and
        setind_implies_fin_by_setsuc: "L_setind (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)" and 
      setind_implies_dedekind_by_setsuc: "L_setind (\<epsilon>) \<Longrightarrow> L_dedekind (\<epsilon>)"  
proof-
  assume "L_setind (\<epsilon>)"
  then interpret L_setind
    by blast
  interpret L_setext_empty_setsuc_setind
    by unfold_locales 
  show "L_tarski (\<epsilon>)" "L_fin (\<epsilon>)" "L_dedekind (\<epsilon>)"
    by unfold_locales
qed    

theorem (in L_setext_empty_power_union_repl)
   dedekind_implies_fin: "L_dedekind (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)"
proof-
  assume "L_dedekind (\<epsilon>)"
  then interpret L_dedekind.
  interpret L_setext_empty_power_union_repl_dedekind
    by unfold_locales
  show "L_fin (\<epsilon>)"
    by (simp add: L_fin_axioms)
qed

text \<open>Equivalence of finiteness principles, in sufficiently strong common context.\<close>

theorem (in L_setext_empty_power_union_repl_reg)
        fin_implies_tarski: "L_fin (\<epsilon>) \<Longrightarrow> L_tarski (\<epsilon>)" and
        tarski_implies_fin: "L_tarski (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)" and
        fin_implies_setind: "L_fin (\<epsilon>) \<Longrightarrow> L_setind (\<epsilon>)" and
        setind_implies_fin: "L_setind (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)" and
        fin_implies_dedekind: "L_fin (\<epsilon>) \<Longrightarrow> L_dedekind (\<epsilon>)"
proof-
  assume "L_fin (\<epsilon>)"
  then interpret L_fin "(\<epsilon>)". 
  interpret L_setext_empty_power_union_repl_reg_fin "(\<epsilon>)"
     by unfold_locales 
  interpret L_setext_empty_setsuc_setind "(\<epsilon>)"
     by unfold_locales 
  show "L_tarski (\<epsilon>)" 
    by unfold_locales 
  show "L_dedekind (\<epsilon>)" 
    by unfold_locales 
  show "L_setind (\<epsilon>)" 
    by unfold_locales 
next
  assume "L_tarski (\<epsilon>)"
  then interpret L_tarski "(\<epsilon>)". 
  interpret L_setext_empty_power_sep_setsuc_tarski
     by unfold_locales 
  show "L_fin (\<epsilon>)" 
    by unfold_locales 
next
  assume "L_setind (\<epsilon>)" 
  then interpret L_setind "(\<epsilon>)"
    by blast
  interpret L_setsuc "(\<epsilon>)"
    by unfold_locales 
  interpret L_setext_empty_setsuc "(\<epsilon>)"
    by unfold_locales
  from setind_implies_tarski[OF \<open>L_setind (\<epsilon>)\<close>]  
  interpret L_tarski "(\<epsilon>)".
  interpret L_setext_empty_power_sep_setsuc_tarski "(\<epsilon>)"
     by unfold_locales 
  show "L_fin (\<epsilon>)"
    by unfold_locales 
qed

text \<open>The validity of the regularity schema/epsilon induction is closely related to the existence of a transitive superset
See also Proposition 5.4, Kaye and Wong \<^cite>\<open>KayeWong2007\<close>.
There, the equivalence of \<open>L_epsind\<close> and  \<open>L_ts\<close> is shown in the context of EST + regularity. 
Instead, we follow  Sochor  \<^cite>\<open>Sochor1979\<close> and \<^cite>\<open>Sochor1982\<close> 
in improving the claim by weakening both implications.  
\<close>

theorem  (in L_setext_sep_reg) ts_implies_epsind: 
  "L_ts (\<epsilon>) \<Longrightarrow> L_epsind (\<epsilon>)"
proof-
  assume "L_ts (\<epsilon>)"
  then interpret L_ts "(\<epsilon>)".
  interpret L_setext_sep_reg_ts
    by unfold_locales
  interpret L_regsch
    by unfold_locales
  show "L_epsind (\<epsilon>)"
    using L_epsind_def regsch_epsind by blast
qed

theorem  (in L_setext_empty_union_repl_pair) epsind_implies_ts: 
  "L_epsind (\<epsilon>) \<Longrightarrow> L_ts (\<epsilon>)"
proof-
  assume "L_epsind (\<epsilon>)"
  then interpret L_epsind "(\<epsilon>)".
  interpret L_setext_empty_union_repl_pair_regsch
    by unfold_locales  
  show "L_ts (\<epsilon>)"
    using L_ts_axioms.   
qed

text \<open>Consequently, in a sufficiently strong context we can verify the equivalence of axioms  A81 (regularity) + A82 (transitive superset) and A8 (schema of regularity)
from Sochor \<^cite>\<open>Sochor1979\<close>, p. 709.
\<close>

theorem  (in L_setext_empty_union_repl_pair) ts_reg_iff_regsch: 
  "L_ts (\<epsilon>) \<and> L_reg (\<epsilon>) \<longleftrightarrow> L_regsch (\<epsilon>)"
proof
  assume "L_regsch (\<epsilon>)"
  then interpret L_regsch "(\<epsilon>)".
  have "L_reg (\<epsilon>)"
    by (simp add: L_reg_axioms) 
  have "L_ts (\<epsilon>)"
    by (simp add: L_regsch_axioms epsind_regsch_iff epsind_implies_ts)
  then show "L_ts (\<epsilon>) \<and> L_reg (\<epsilon>)"
    using \<open>L_reg (\<epsilon>)\<close> by blast   
next
  assume "L_ts (\<epsilon>) \<and> L_reg (\<epsilon>)"
  then interpret L_ts "(\<epsilon>)" 
    by simp   
  interpret L_reg "(\<epsilon>)"
    using \<open>L_ts (\<epsilon>) \<and> L_reg (\<epsilon>)\<close> by simp
  interpret "L_setext_empty_repl"
    by unfold_locales
  interpret L_sep "(\<epsilon>)"
    using repl_implies_sep  by (simp add: L_sep_axioms) 
  interpret L_setext_sep_reg "(\<epsilon>)"
    by unfold_locales
  show "L_regsch (\<epsilon>)"
    using ts_implies_epsind L_ts_axioms unfolding epsind_regsch_iff.
qed

end
