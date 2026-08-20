theory MSOinHOL_deep
  imports MSOinHOL_preliminaries
begin

text \<open>Deep embedding of monadic second-order logic (MSO) in HOL.\<close>

text \<open>Two binders: \<open>\<exists>\<^sup>d\<close> ranges over individuals;
  \<open>\<exists>\<^sup>d\<^sub>2\<close> ranges over monadic predicates.
  \<open>X\<^sup>d(x)\<close> is the monadic predication atom ``predicate \<open>X\<close>
  holds of individual \<open>x\<close>''.\<close>

datatype \<F> =
    AtmD R V V    ("_\<^sup>d'(_,_')")                       \<comment>\<open>relational atom \<open>r(x,y)\<close>\<close>
  | PrdD V2 V     ("_\<^sup>d'(_')")                         \<comment>\<open>monadic predication atom \<open>X(x)\<close>\<close>
  | NegD \<F>       ("\<not>\<^sup>d _" [58] 59)                    \<comment>\<open>negation\<close>
  | AndD \<F> \<F>     (infixr "\<and>\<^sup>d" 56)                 \<comment>\<open>conjunction\<close>
  | ExD V \<F>      ("\<exists>\<^sup>d_. _")                          \<comment>\<open>first-order existential\<close>
  | ExD2 V2 \<F>    ("\<exists>\<^sup>d\<^sub>2_. _")                          \<comment>\<open>second-order (monadic) existential\<close>

text \<open>Further connectives as derived definitions.\<close>

definition OrD (infixr "\<or>\<^sup>d" 54)
  where "\<phi> \<or>\<^sup>d \<psi> \<equiv> \<not>\<^sup>d(\<not>\<^sup>d\<phi> \<and>\<^sup>d \<not>\<^sup>d\<psi>)"

definition ImpD (infixr "\<supset>\<^sup>d" 55)
  where "\<phi> \<supset>\<^sup>d \<psi> \<equiv> \<not>\<^sup>d\<phi> \<or>\<^sup>d \<psi>"

definition IffD (infixr "\<longleftrightarrow>\<^sup>d" 54)
  where "\<phi> \<longleftrightarrow>\<^sup>d \<psi> \<equiv> (\<phi> \<supset>\<^sup>d \<psi>) \<and>\<^sup>d (\<psi> \<supset>\<^sup>d \<phi>)"

definition AllD ("\<forall>\<^sup>d_. _")
  where "\<forall>\<^sup>dx. \<phi> \<equiv> \<not>\<^sup>d(\<exists>\<^sup>dx. \<not>\<^sup>d\<phi>)"

definition AllD2 ("\<forall>\<^sup>d\<^sub>2_. _")
  where "\<forall>\<^sup>d\<^sub>2X. \<phi> \<equiv> \<not>\<^sup>d(\<exists>\<^sup>d\<^sub>2X. \<not>\<^sup>d\<phi>)"

text \<open>Relative truth in a model.  The first-order existential ranges over the
  individual domain \<open>D\<close>; the second-order existential ranges over the
  collection \<open>E\<close> of admissible monadic sets.\<close>

primrec RelativeTruthD :: "\<I> \<Rightarrow> \<D> \<Rightarrow> \<P> \<Rightarrow> \<E> \<Rightarrow> \<G> \<Rightarrow> \<F> \<Rightarrow> bool"
    ("\<langle>_,_,_\<rangle>,_,_ \<Turnstile>\<^sup>d _" [10,10,10,10,10] 100)
  where
    "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (r\<^sup>d(x,y)) = I r (g x) (g y)"
  | "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (X\<^sup>d(x)) = (G X) (g x)"
  | "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (\<not>\<^sup>d\<phi>) = (\<not> \<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  | "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (\<phi> \<and>\<^sup>d \<psi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi> \<and> \<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<psi>)"
  | "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (\<exists>\<^sup>dx. \<phi>) = (\<exists>d:D. \<langle>I,D,E\<rangle>,g[x\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>)"
  | "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (\<exists>\<^sup>d\<^sub>2X. \<phi>) = (\<exists>S:E. \<langle>I,D,E\<rangle>,g,G\<langle>X\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>)"

text \<open>Validity: true in every model, every domain-respecting first- and
  second-order assignment.\<close>

definition ValD ("\<Turnstile>\<^sup>d _" 9)
  where "\<Turnstile>\<^sup>d \<phi> \<equiv> \<forall>I D E g G. g into D \<longrightarrow> G into E \<longrightarrow> \<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>"

text \<open>Auxiliary ``full-domain'' notion of validity: assignments range over
  the full types (\<open>Univ\<close> on \<open>D\<close> and on \<open>D \<Rightarrow> bool\<close>).\<close>

definition ValD' ("\<Turnstile>\<^sup>d'' _" 9)
  where "\<Turnstile>\<^sup>d' \<phi> \<equiv> \<forall>I g G. \<langle>I,Univ,Univ\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>"

text \<open>General validity implies full-domain validity.\<close>

lemma Val: "\<Turnstile>\<^sup>d \<phi> \<Longrightarrow> \<Turnstile>\<^sup>d' \<phi>"
  using ValD'_def ValD_def by simp

text \<open>Bag of definitions for collective unfolding.\<close>

named_theorems DefD
lemmas [DefD] = OrD_def ImpD_def IffD_def AllD_def AllD2_def ValD_def ValD'_def

end
