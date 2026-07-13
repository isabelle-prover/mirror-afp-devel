theory MSOinHOL_shallow_minimal_elementary
  imports
    MSOinHOL_faithfulness_locale
    MSOinHOL_lowenheim_skolem
begin

text \<open>Extra simp rules for @{term DpToShS} (derived quantifiers and
  connectives).\<close>

lemma (in MinS) DpToShS_All [simp]:
  "\<lparr>\<forall>\<^sup>dx. \<phi>\<rparr> = (\<forall>\<^sup>md. \<lparr>[x \<leftarrow>\<^sub>r d](\<phi>)\<rparr>)"
  unfolding DefD DefM by (simp add: ExM_def NegM_def ren_subst_def)

lemma (in MinS) DpToShS_All2 [simp]:
  "\<lparr>\<forall>\<^sup>d\<^sub>2x. \<phi>\<rparr> = (\<forall>\<^sup>m\<^sub>2d. \<lparr>[x \<leftarrow>\<^sub>r\<^sub>2 d](\<phi>)\<rparr>)"
  unfolding DefD DefM using MinS.FaithfulMDlem by auto

lemma (in MinS) DpToShS_Equiv [simp]:
  "\<lparr>\<phi> \<longleftrightarrow>\<^sup>d \<psi>\<rparr> = (\<lparr>\<phi>\<rparr> \<longleftrightarrow>\<^sup>m \<lparr>\<psi>\<rparr>)"
  unfolding DefD DefM by (simp add: AndM_def NegM_def)

lemma (in MinS) DpToShS_Imp [simp]:
  "\<lparr>\<phi> \<supset>\<^sup>d \<psi>\<rparr> = (\<lparr>\<phi>\<rparr> \<supset>\<^sup>m \<lparr>\<psi>\<rparr>)"
  unfolding DefD DefM by (simp add: AndM_def NegM_def)

text \<open>Elementary constants-only presentation: @{text II}, @{text gg},
  @{text GG} chosen so that the global interpretation is a
  @{text MinS_ES_Univ} (existence via @{text Deep'_to_MinS}).\<close>

consts II :: \<I>  gg :: \<E>  GG :: \<G>

specification (II gg GG) ES_Univ: "MinS_ES_Univ II gg GG"
  by (meson Deep'_to_MinS RelativeTruthD.simps ValD'_def)

global_interpretation MinS_ES_Univ II gg GG
  using ES_Univ by auto

notation AtmM    ("_\<^sup>m'(_,_')")
    and PrdM    ("_\<^sup>m'(_')")
    and NegM    ("\<not>\<^sup>m _" [58] 59)
    and AndM    (infixr "\<and>\<^sup>m" 56)
    and ExM     (binder "\<exists>\<^sup>m" 53)
    and ExM2    (binder "\<exists>\<^sup>m\<^sub>2" 53)
    and OrM     (infixr "\<or>\<^sup>m" 54)
    and ImpM    (infixr "\<supset>\<^sup>m" 55)
    and IffM    (infixr "\<longleftrightarrow>\<^sup>m" 54)
    and AllM    (binder "\<forall>\<^sup>m" 53)
    and AllM2   (binder "\<forall>\<^sup>m\<^sub>2" 53)
    and ValM    ("\<Turnstile>\<^sup>m _" 9)
    and DpToShM ("\<lparr>_\<rparr>")

text \<open>Faithfulness under universal carriers.\<close>

lemma FaithfulMD_ES: "(\<Turnstile>\<^sup>m \<lparr>\<phi>\<rparr>) = \<langle>II,Univ,Univ\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>"
  using FaithfulMD \<N>_valid_ES_Univ by blast

text \<open>Inheritance: standard validity transfers to minimal validity.\<close>

lemma ValidM_if_ValidD': "(\<Turnstile>\<^sup>d' \<phi>) \<Longrightarrow> (\<Turnstile>\<^sup>m \<lparr>\<phi>\<rparr>)"
  by (metis MinS_ES_Univ_axioms Deep'_to_MinS)

end
