theory MSOinHOL_shallow_minimal
  imports MSOinHOL_faithfulness_locale
begin

text \<open>Constants-only presentation: a global interpretation of the minimal
  shallow embedding.\<close>

consts II :: \<I>  gg :: \<E>  GG :: \<G>

global_interpretation MinS II gg GG .

text \<open>Re-introduce the locale-internal notation at the global level.\<close>

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

end
