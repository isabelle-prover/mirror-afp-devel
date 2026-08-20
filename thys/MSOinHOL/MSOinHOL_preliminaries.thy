theory MSOinHOL_preliminaries
  imports Main
begin

text \<open>Some global settings.\<close>

nitpick_params [user_axioms, expect = genuine]

text \<open>Declarations shared between the deep, maximal-shallow, and
  minimal-shallow embeddings of MSO in HOL.\<close>

typedecl D                                                       \<comment>\<open>Domain of individuals.\<close>
type_synonym R   = nat                                  \<comment>\<open>Binary relation symbols.\<close>
type_synonym V   = nat                              \<comment>\<open>First-order variable symbols.\<close>
type_synonym V2  = nat                              \<comment>\<open>Second-order variable symbols.\<close>
type_synonym \<R>   = "D \<Rightarrow> D \<Rightarrow> bool"            \<comment>\<open>Binary relations on individuals.\<close>
type_synonym \<I>   = "R \<Rightarrow> \<R>"                    \<comment>\<open>Interpretations of relation symbols.\<close>
type_synonym \<E>   = "V \<Rightarrow> D"                    \<comment>\<open>First-order variable assignments.\<close>
type_synonym \<G>   = "V2 \<Rightarrow> (D \<Rightarrow> bool)"    \<comment>\<open>Second-order variable assignments.\<close>
type_synonym \<D>   = "D \<Rightarrow> bool"                       \<comment>\<open>First-order domain restrictions.\<close>
type_synonym \<P>   = "(D \<Rightarrow> bool) \<Rightarrow> bool"       \<comment>\<open>Second-order domain restrictions.\<close>

text \<open>Pointwise update of first-order variable assignments.\<close>

definition EnvMod :: "\<E> \<Rightarrow> V \<Rightarrow> D \<Rightarrow> \<E>"  ("_[_ \<leftarrow> _]" [110,0,0] 110)
  where "g[x\<leftarrow>d] \<equiv> \<lambda>z. if z = x then d else g z"

text \<open>Pointwise update of second-order variable assignments
  (distinct notation, angle brackets).\<close>

definition SetMod :: "\<G> \<Rightarrow> V2 \<Rightarrow> (D \<Rightarrow> bool) \<Rightarrow> \<G>"
    ("_\<langle>_ \<leftarrow> _\<rangle>" [110,0,0] 110)
  where "G\<langle>X\<leftarrow>S\<rangle> \<equiv> \<lambda>Z. if Z = X then S else G Z"

text \<open>Standard lemmas about first-order variable-assignment update.\<close>

lemma L1 [simp]: "x \<noteq> y \<Longrightarrow> (g[y\<leftarrow>d]) x = g x"
  by (simp add: EnvMod_def)

lemma L2: "a \<noteq> c \<Longrightarrow> g[a\<leftarrow>d\<^sub>1][c\<leftarrow>d\<^sub>2] = g[c\<leftarrow>d\<^sub>2][a\<leftarrow>d\<^sub>1]"
  by (auto simp: EnvMod_def)

lemma L3 [simp]: "(g[a\<leftarrow>d]) a = d"
  by (simp add: EnvMod_def)

lemma L4 [simp]: "g[a\<leftarrow>d\<^sub>1][a\<leftarrow>d\<^sub>2] = g[a\<leftarrow>d\<^sub>2]"
  by (auto simp: EnvMod_def)

text \<open>Standard lemmas about second-order variable-assignment update.\<close>

lemma M1 [simp]: "X \<noteq> Y \<Longrightarrow> (G\<langle>Y\<leftarrow>S\<rangle>) X = G X"
  by (simp add: SetMod_def)

lemma M2: "A \<noteq> C \<Longrightarrow> G\<langle>A\<leftarrow>S\<^sub>1\<rangle>\<langle>C\<leftarrow>S\<^sub>2\<rangle> = G\<langle>C\<leftarrow>S\<^sub>2\<rangle>\<langle>A\<leftarrow>S\<^sub>1\<rangle>"
  by (auto simp: SetMod_def)

lemma M3 [simp]: "(G\<langle>A\<leftarrow>S\<rangle>) A = S"
  by (simp add: SetMod_def)

lemma M4 [simp]: "G\<langle>A\<leftarrow>S\<^sub>1\<rangle>\<langle>A\<leftarrow>S\<^sub>2\<rangle> = G\<langle>A\<leftarrow>S\<^sub>2\<rangle>"
  by (auto simp: SetMod_def)

text \<open>Bounded quantifiers: \<open>\<forall>x:D. \<phi>\<close> stands for \<open>\<forall>x. D x \<longrightarrow> \<phi> x\<close> and
  \<open>\<exists>x:D. \<phi>\<close> stands for \<open>\<exists>x. D x \<and> \<phi> x\<close>.\<close>

abbreviation "BAll D \<phi> \<equiv> \<forall>x. D x \<longrightarrow> \<phi> x"
syntax "BAll" :: "pttrn \<Rightarrow> logic \<Rightarrow> bool \<Rightarrow> bool"
    ("(3\<forall>(_/:_)./_)" [0,0,10] 10)
translations "\<forall>x:D. \<phi>" \<rightleftharpoons> "CONST BAll D (\<lambda>x. \<phi>)"

abbreviation "BEx D \<phi> \<equiv> \<exists>x. D x \<and> \<phi> x"
syntax "BEx" :: "pttrn \<Rightarrow> logic \<Rightarrow> bool \<Rightarrow> bool"
    ("(3\<exists>(_/:_)./_)" [0,0,10] 10)
translations "\<exists>x:D. \<phi>" \<rightleftharpoons> "CONST BEx D (\<lambda>x. \<phi>)"

text \<open>Set-as-predicate operations, range, and the universal domain
  (polymorphic; used for both sorts).\<close>

abbreviation "Into" (infix "into" 100)
  where "f into D \<equiv> \<forall>x. D (f x)"

abbreviation "Range"
  where "Range f \<equiv> \<lambda>x. \<exists>y. x = f y"

abbreviation "Onto" (infix "onto" 100)
  where "f onto D \<equiv> D = Range f"

abbreviation "Subset" (infix "\<^bold>\<subseteq>" 100)
  where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"

abbreviation "Union" (infixl "\<^bold>\<union>" 110)
  where "A \<^bold>\<union> B \<equiv> \<lambda>x. A x \<or> B x"

abbreviation "Univ"
  where "Univ \<equiv> \<lambda>x. True"

text \<open>Surjectivity onto the universal predicate coincides with HOL
  surjectivity.\<close>

lemma onto_Univ: "surj f = (f onto Univ)"
  by (auto simp: surj_def fun_eq_iff)

text \<open>Backward implication; useful for stating equivalences in two
  directions.\<close>

abbreviation Bimp (infixr "\<longleftarrow>" 50)
  where "\<phi> \<longleftarrow> \<psi> \<equiv> \<psi> \<longrightarrow> \<phi>"

end
