theory MSOinHOL_shallow_minimal_locale
  imports MSOinHOL_preliminaries
begin

text \<open>Minimal (lightweight) shallow embedding of MSO in HOL, packaged as
  a locale.  Since MSO carries no world dependency, the formula type
  collapses to \<open>bool\<close>.\<close>

locale MinS =
  fixes II :: \<I> and gg :: \<E> and GG :: \<G>
begin

text \<open>Six primitive cases.  \<open>ExM\<close>, \<open>ExM2\<close> are HOL binders over the
  symbol types \<open>V\<close>, \<open>V2\<close>; atoms consult \<open>II\<close> via \<open>gg\<close>, and
  membership consults \<open>GG\<close> via \<open>gg\<close>.\<close>

definition AtmM :: "R \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" ("_\<^sup>m'(_,_')")
  where "r\<^sup>m(x,y) \<equiv> II r (gg x) (gg y)"

definition PrdM :: "V2 \<Rightarrow> V \<Rightarrow> bool" ("_\<^sup>m'(_')")
  where "X\<^sup>m(x) \<equiv> (GG X) (gg x)"

definition NegM :: "bool \<Rightarrow> bool" ("\<not>\<^sup>m _" [58] 59)
  where "\<not>\<^sup>m\<phi> \<equiv> \<not>\<phi>"

definition AndM :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<and>\<^sup>m" 56)
  where "\<phi> \<and>\<^sup>m \<psi> \<equiv> \<phi> \<and> \<psi>"

definition ExM :: "(V \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>\<^sup>m" 53)
  where "\<exists>\<^sup>md. \<Phi> d \<equiv> \<exists>d. \<Phi> d"

definition ExM2 :: "(V2 \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>\<^sup>m\<^sub>2" 53)
  where "\<exists>\<^sup>m\<^sub>2D. \<Phi> D \<equiv> \<exists>D. \<Phi> D"

text \<open>Derived connectives.\<close>

definition OrM :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<or>\<^sup>m" 54)
  where "\<phi> \<or>\<^sup>m \<psi> \<equiv> \<not>\<^sup>m(\<not>\<^sup>m\<phi> \<and>\<^sup>m \<not>\<^sup>m\<psi>)"

definition ImpM :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<supset>\<^sup>m" 55)
  where "\<phi> \<supset>\<^sup>m \<psi> \<equiv> \<not>\<^sup>m\<phi> \<or>\<^sup>m \<psi>"

definition IffM :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<longleftrightarrow>\<^sup>m" 54)
  where "\<phi> \<longleftrightarrow>\<^sup>m \<psi> \<equiv> (\<phi> \<supset>\<^sup>m \<psi>) \<and>\<^sup>m (\<psi> \<supset>\<^sup>m \<phi>)"

definition AllM :: "(V \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<^sup>m" 53)
  where "\<forall>\<^sup>md. \<Phi> d \<equiv> \<forall>d. \<Phi> d"

definition AllM2 :: "(V2 \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<^sup>m\<^sub>2" 53)
  where "\<forall>\<^sup>m\<^sub>2D. \<Phi> D \<equiv> \<forall>D. \<Phi> D"

text \<open>Relative truth and validity.  As the formula type is \<open>bool\<close>,
  validity is the identity.\<close>

definition ValM :: "bool \<Rightarrow> bool" ("\<Turnstile>\<^sup>m _" 9)
  where "\<Turnstile>\<^sup>m \<phi> \<equiv> \<phi>"

text \<open>Bag of definitions.\<close>

named_theorems DefM
lemmas DefM_defs [DefM] =
  AtmM_def PrdM_def NegM_def AndM_def ExM_def ExM2_def
  OrM_def ImpM_def IffM_def AllM_def AllM2_def ValM_def

end

end
