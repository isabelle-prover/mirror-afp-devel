(*  Title:       CoreC++
    ID:          $Id: TypeRel.thy,v 1.6 2006-10-23 14:58:31 fhaftmann Exp $
    Author:      Tobias Nipkow, Daniel Wasserrab 
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Extracted from the Jinja theory Common/TypeRel.thy by Tobias Nipkow 
*)


header {* \isaheader{The subtype relation} *}

theory TypeRel imports SubObj begin


consts
  widen   :: "prog \<Rightarrow> (ty \<times> ty) set"  -- "widening"

syntax (xsymbols)
  widen   :: "prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)

translations
  "P \<turnstile> T \<le> T'"  ==  "(T,T') \<in> widen P"

abbreviation (xsymbols)
  widens :: "prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70)
  "widens P Ts Ts' \<equiv> list_all2 (fun_of (widen P)) Ts Ts'"

inductive "widen P"
intros
  widen_refl[iff]: "P \<turnstile> T \<le> T"
  widen_subcls:    "P \<turnstile> Path C to D unique \<Longrightarrow> P \<turnstile> Class C \<le> Class D"
  widen_null[iff]: "P \<turnstile> NT \<le> Class C"

lemma [iff]: "(P \<turnstile> T \<le> Void) = (T = Void)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> T \<le> Boolean) = (T = Boolean)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> T \<le> Integer) = (T = Integer)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> Void \<le> T) = (T = Void)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> Boolean \<le> T) = (T = Boolean)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> Integer \<le> T) = (T = Integer)"
by (auto elim: widen.elims)


lemma [iff]: "(P \<turnstile> T \<le> NT) = (T = NT)"

apply(cases T) apply auto
apply (ind_cases "P \<turnstile> T \<le> T'")
apply auto
done


lemmas widens_refl [iff] = rel_list_all2_refl [OF widen_refl]
lemmas widens_Cons [iff] = rel_list_all2_Cons1 [of "widen P", standard]

end
