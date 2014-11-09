section {* Type Application *}

theory TypeApp
imports HOLCF
begin

subsection {* Class of type constructors *}

text {* In HOLCF, the type @{typ "udom defl"} consists of deflations
over the universal domain---each value of type @{typ "udom defl"}
represents a bifinite domain. In turn, values of the continuous
function type @{typ "udom defl \<rightarrow> udom defl"} represent functions from
domains to domains, i.e.~type constructors. *}

text {* Class @{text tycon}, defined below, will be populated with
dummy types: For example, if the type @{text foo} is an instance of
class @{text tycon}, then users will never deal with any values @{text
"x::foo"} in practice. Such types are only used with the overloaded
constant @{text tc}, which associates each type @{text "'a::tycon"}
with a value of type @{typ "udom defl \<rightarrow> udom defl"}. \medskip *}

class tycon =
  fixes tc :: "('a::type) itself \<Rightarrow> udom defl \<rightarrow> udom defl"

text {* Type @{typ "'a itself"} is defined in Isabelle's meta-logic;
it is inhabited by a single value, written @{term "TYPE('a)"}. We
define the syntax @{text "TC('a)"} to abbreviate @{text "tc
TYPE('a)"}. \medskip *}

syntax  "_TC" :: "type \<Rightarrow> logic"  ("(1TC/(1'(_')))")

translations "TC('a)" \<rightleftharpoons> "CONST tc TYPE('a)"


subsection {* Type constructor for type application *}

text {* We now define a binary type constructor that models type
application: Type @{text "('a, 't) app"} is the result of applying the
type constructor @{text 't} (from class @{text tycon}) to the type
argument @{text 'a} (from class @{text domain}). *}

text {* We define type @{text "('a, 't) app"} using @{text domaindef},
a low-level type-definition command provided by HOLCF (similar to
@{text typedef} in Isabelle/HOL) that defines a new domain type
represented by the given deflation. Note that in HOLCF, @{text
"DEFL('a)"} is an abbreviation for @{text "defl TYPE('a)"}, where
@{text "defl :: ('a::domain) itself \<Rightarrow> udom defl"} is an overloaded
function from the @{text domain} type class that yields the deflation
representing the given type. \medskip *}

domaindef ('a,'t) app = "TC('t::tycon)\<cdot>DEFL('a::domain)"

text {* We define the infix syntax @{text "'a\<cdot>'t"} for the type @{text
"('a,'t) app"}. Note that for consistency with Isabelle's existing
type syntax, we have used postfix order for type application: type
argument on the left, type constructor on the right. \medskip *}

type_notation app ("(_\<cdot>_)" [999,1000] 999)

text {* The @{text domaindef} command generates the theorem @{text
DEFL_app}: @{thm DEFL_app [where 'a="'a::domain" and 't="'t::tycon"]},
which we can use to derive other useful lemmas. \medskip *}

lemma TC_DEFL: "TC('t::tycon)\<cdot>DEFL('a) = DEFL('a\<cdot>'t)"
by (rule DEFL_app [symmetric])

lemma DEFL_app_mono [simp, intro]:
  "DEFL('a) \<sqsubseteq> DEFL('b) \<Longrightarrow> DEFL('a\<cdot>'t::tycon) \<sqsubseteq> DEFL('b\<cdot>'t)"
 apply (simp add: DEFL_app)
 apply (erule monofun_cfun_arg)
done

end
