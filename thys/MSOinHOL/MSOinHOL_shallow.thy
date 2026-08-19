theory MSOinHOL_shallow
  imports MSOinHOL_preliminaries
begin

text \<open>Maximal (heavyweight) shallow embedding of MSO in HOL; MSO formulas
  are HOL terms of the following type \<open>\<sigma>\<close>.\<close>

type_synonym \<sigma> = "\<I> \<Rightarrow> \<D> \<Rightarrow> \<P> \<Rightarrow> \<E> \<Rightarrow> \<G> \<Rightarrow> bool"

text \<open>The six primitive cases.\<close>

definition AtmS :: "R \<Rightarrow> V \<Rightarrow> V \<Rightarrow> \<sigma>" ("_\<^sup>s'(_,_')")
  where "r\<^sup>s(x,y) \<equiv> \<lambda>I D E g G. I r (g x) (g y)"

definition PrdS :: "V2 \<Rightarrow> V \<Rightarrow> \<sigma>" ("_\<^sup>s'(_')")
  where "X\<^sup>s(x) \<equiv> \<lambda>I D E g G. (G X) (g x)"

definition NegS :: "\<sigma> \<Rightarrow> \<sigma>" ("\<not>\<^sup>s _" [58] 59)
  where "\<not>\<^sup>s\<phi> \<equiv> \<lambda>I D E g G. \<not> (\<phi> I D E g G)"

definition AndS :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<and>\<^sup>s" 56)
  where "\<phi> \<and>\<^sup>s \<psi> \<equiv> \<lambda>I D E g G. \<phi> I D E g G \<and> \<psi> I D E g G"

definition ExS :: "V \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<exists>\<^sup>s_. _" 53)
  where "\<exists>\<^sup>sx. \<phi> \<equiv> \<lambda>I D E g G. \<exists>d:D. \<phi> I D E (g[x\<leftarrow>d]) G"

definition ExS2 :: "V2 \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<exists>\<^sup>s\<^sub>2_. _" 53)
  where "\<exists>\<^sup>s\<^sub>2X. \<phi> \<equiv> \<lambda>I D E g G. \<exists>S:E. \<phi> I D E g (G\<langle>X\<leftarrow>S\<rangle>)"

text \<open>Derived connectives.\<close>

definition OrS :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<or>\<^sup>s" 54)
  where "\<phi> \<or>\<^sup>s \<psi> \<equiv> \<not>\<^sup>s(\<not>\<^sup>s\<phi> \<and>\<^sup>s \<not>\<^sup>s\<psi>)"

definition ImpS :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<supset>\<^sup>s" 55)
  where "\<phi> \<supset>\<^sup>s \<psi> \<equiv> \<not>\<^sup>s\<phi> \<or>\<^sup>s \<psi>"

definition IffS :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<longleftrightarrow>\<^sup>s" 54)
  where "\<phi> \<longleftrightarrow>\<^sup>s \<psi> \<equiv> (\<phi> \<supset>\<^sup>s \<psi>) \<and>\<^sup>s (\<psi> \<supset>\<^sup>s \<phi>)"

definition AllS :: "V \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<forall>\<^sup>s_. _" 53)
  where "\<forall>\<^sup>sx. \<phi> \<equiv> \<not>\<^sup>s(\<exists>\<^sup>sx. \<not>\<^sup>s\<phi>)"

definition AllS2 :: "V2 \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<forall>\<^sup>s\<^sub>2_. _" 53)
  where "\<forall>\<^sup>s\<^sub>2X. \<phi> \<equiv> \<not>\<^sup>s(\<exists>\<^sup>s\<^sub>2X. \<not>\<^sup>s\<phi>)"

text \<open>Relative truth and validity (mirroring the deep embedding).\<close>

definition RelTruthS :: "\<I> \<Rightarrow> \<D> \<Rightarrow> \<P> \<Rightarrow> \<E> \<Rightarrow> \<G> \<Rightarrow> \<sigma> \<Rightarrow> bool"
    ("\<langle>_,_,_\<rangle>,_,_ \<Turnstile>\<^sup>s _" [100,0,0,0,0] 100)
  where "\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>s \<phi> \<equiv> \<phi> I D E g G"

definition ValS :: "\<sigma> \<Rightarrow> bool" ("\<Turnstile>\<^sup>s _" 9)
  where "\<Turnstile>\<^sup>s \<phi> \<equiv> \<forall>I D E g G. g into D \<longrightarrow> G into E \<longrightarrow> \<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>s \<phi>"

text \<open>Auxiliary ``full-domain'' notion of validity: assignments range over
  the full types.\<close>

definition ValS' ("\<Turnstile>\<^sup>s'' _" 9)
  where "\<Turnstile>\<^sup>s' \<phi> \<equiv> \<forall>I g G. \<langle>I,Univ,Univ\<rangle>,g,G \<Turnstile>\<^sup>s \<phi>"

text \<open>General validity implies full-domain validity.\<close>

lemma Val_s: "\<Turnstile>\<^sup>s \<phi> \<Longrightarrow> \<Turnstile>\<^sup>s' \<phi>"
  using ValS'_def ValS_def by simp

text \<open>Bag of definitions.\<close>

named_theorems DefS
lemmas DefS_defs [DefS] =
  AtmS_def PrdS_def NegS_def AndS_def ExS_def ExS2_def
  OrS_def ImpS_def IffS_def AllS_def AllS2_def
  RelTruthS_def ValS_def ValS'_def

end
