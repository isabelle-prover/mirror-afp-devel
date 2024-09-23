theory SyntaxTweaks 
imports Main
begin

syntax (implnl output)
  "\<Longrightarrow>" :: "prop \<Rightarrow> prop \<Rightarrow> prop" (\<open>_ //\<Longrightarrow> _\<close> [0,1] 1)

notation (holimplnl output)
"implies" (\<open>(2_ \<longrightarrow>// _)\<close> [0,1] 1)
notation (holimplnl output)
"conj" (\<open>_ \<and>/ _\<close> [34,35]35)
  

syntax (letnl output)
  "_binds"      :: "[letbind, letbinds] => letbinds"     (\<open>_;//_\<close>)
text \<open>Theorems as inference rules, usepackage mathpartir\<close>

syntax (eqindent output) "op =" ::"['a, 'a] => bool"               ( \<open>(2_ =/ _)\<close> [49,50]50)

(* LOGIC *)
syntax (latex output)
  If            :: "[bool, 'a, 'a] => 'a"
  (\<open>(\<^latex>\<open>\holkeyword{\<close>if\<^latex>\<open>}\<close>(_)/ \<^latex>\<open>\holkeyword{\<close>then\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\holkeyword{\<close>else\<^latex>\<open>}\<close> (_))\<close> 10)

  "_Let"        :: "[letbinds, 'a] => 'a"
  (\<open>(\<^latex>\<open>\holkeyword{\<close>let\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\holkeyword{\<close>in\<^latex>\<open>}\<close> (_))\<close> 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  (\<open>(\<^latex>\<open>\holkeyword{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\holkeyword{\<close>of\<^latex>\<open>}\<close>/ _)\<close> 10)

notation (Rule output)
  Pure.imp  (\<open>\<^latex>\<open>\mbox{}\inferrule{\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\mbox{\<close>_\<^latex>\<open>}}\<close>\<close>)

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>\mbox{}\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\mbox{\<close>_\<^latex>\<open>}}\<close>\<close>)

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\\\<close>/ _\<close>)

  "_asm" :: "prop \<Rightarrow> asms" (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close>\<close>)


notation (Axiom output)
  "Trueprop"  (\<open>\<^latex>\<open>\mbox{}\inferrule{\mbox{}}{\mbox{\<close>_\<^latex>\<open>}}\<close>\<close>)

syntax (IfThen output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _/ \<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)

  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _ /\<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close> /\<^latex>\<open>{\normalsize \,\<close>and\<^latex>\<open>\,}\<close>/ _\<close>)
  "_asm" :: "prop \<Rightarrow> asms" (\<open>\<^latex>\<open>\mbox{\<close>_\<^latex>\<open>}\<close>\<close>)

syntax (IfThenNoBox output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _/ \<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>\,}\<close>/ _.\<close>)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  (\<open>\<^latex>\<open>{\normalsize{}\<close>If\<^latex>\<open>\,}\<close> _ /\<^latex>\<open>{\normalsize \,\<close>then\<^latex>\<open>:\,}\<close>/ _.\<close>)
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" (\<open>_ /\<^latex>\<open>{\normalsize \,\<close>and\<^latex>\<open>\,}\<close>/ _\<close>)
  "_asm" :: "prop \<Rightarrow> asms" (\<open>_\<close>)


text \<open>power\<close>
syntax (latex output)
  power :: "['a::power, nat] => 'a"           (\<open>_\<^bsup>_\<^esup>\<close> [1000,0]80)

(* empty set *)
syntax (latex output)
  "_emptyset" :: "'a set"              (\<open>\<emptyset>\<close>)
translations
  "_emptyset"      <= "{}"

text \<open>insert\<close>
translations 
(*
  "{x} \<union> A" <= "insert x A"
*)
  "{x,y}" <= "{x} \<union> {y}"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"
  "{x}" <= "{x} \<union> {}"


syntax (latex output)
 Cons :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"    (infixr \<open>\<cdot>\<close> 65)

syntax (latex output)
 "Some" :: "'a \<Rightarrow> 'a option" (\<open>(\<lfloor>_\<rfloor>)\<close>)
 "None" :: "'a option" (\<open>\<bottom>\<close>)

text \<open>lesser indentation as default\<close>
syntax (latex output)
  "ALL "        :: "[idts, bool] => bool"                (\<open>(2\<forall>_./ _)\<close> [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                (\<open>(2\<exists>_./ _)\<close> [0, 10] 10)

text \<open>space around \<in>\<close>
syntax (latex output)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      (\<open>(3\<forall>_\<^latex>\<open>\,\<close>\<in>_./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      (\<open>(3\<exists>_\<^latex>\<open>\,\<close>\<in>_./ _)\<close> [0, 0, 10] 10)

text \<open>compact line breaking for some infix operators\<close>
term "HOL.conj"
notation (compact output)
"conj" (\<open>_ \<and>/ _\<close> [34,35]35)
notation (compact output)
"append" (\<open>_ @/ _\<close> [64,65]65)

text \<open>force a newline after definition equation\<close>
syntax (defnl output)
  "=="       :: "[prop, prop] => prop"                (\<open>(2_ \<equiv>// _)\<close> [1,2] 2) 
syntax (defeqnl output)
  "=="       :: "[prop, prop] => prop"                (\<open>(2_ =// _)\<close> [1,2] 2) 
syntax (eqnl output)
  "op ="       :: "['a, 'a] => bool"                     (\<open>(2_ =// _)\<close> [1,2] 2) 
syntax (latex output)
  "=="       :: "[prop, prop] => prop"                (\<open>(2_ \<equiv>/ _)\<close> [1,2] 2) 

text \<open>New-line after assumptions\<close>
syntax (asmnl output)
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  (\<open>_; // _\<close>)

text \<open>uncurry functions\<close>
syntax (uncurry output)
"_cargs" :: "'a \<Rightarrow> cargs \<Rightarrow> cargs" (\<open>_, _\<close>)
"_applC" :: "[('b => 'a), cargs] => logic" (\<open>(1_/(1'(_')))\<close> [1000, 0] 1000)

text \<open>but keep curried notation for constructors\<close>
syntax (uncurry output)
"_cargs_curry":: "'a \<Rightarrow> cargs \<Rightarrow> cargs" (\<open>_ _\<close> [1000,1000] 1000)
"_applC_curry":: "[('b => 'a), cargs] => logic" (\<open>(1_/ _)\<close> [1000, 1000] 999)



text \<open>`dot'-selector notation for records\<close>
syntax (latex output)
"_rec_sel" :: "'r \<Rightarrow> id \<Rightarrow> 'a" (\<open>_._\<close> [1000,1000]1000)


text \<open>invisible binder in case we want to force "bound"-markup\<close>
consts Bind:: "('a \<Rightarrow> 'b) \<Rightarrow> 'c" (binder \<open>Bind \<close> 10)
translations
  "f" <= "Bind x. f"


(* length *)
notation (latex output)
  length  (\<open>|_|\<close>)

(* Optional values *)
notation (latex output)
  None (\<open>\<bottom>\<close>)

notation (latex output)
  Some (\<open>\<lfloor>_\<rfloor>\<close>)

(* nth *)
notation (latex output)
  nth  (\<open>_\<^latex>\<open>\ensuremath{_{[\<close>_\<^latex>\<open>]}}\<close>\<close> [1000,0] 1000)

end
