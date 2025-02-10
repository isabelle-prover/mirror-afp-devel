section \<open>Axioms of complements\<close>

theory Axioms_Complement
  imports Laws With_Type.With_Type
begin

typedecl ('a, 'b) complement_domain
instance complement_domain :: (domain, domain) domain..
typedecl ('a, 'b) complement_domain_simple
instance complement_domain_simple :: (domain, domain) domain..

setup \<open> (* Supporting with-type for the dummy class `domain` *)
With_Type.add_with_type_info_global {
  class = \<^class>\<open>domain\<close>,
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_type\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_type\<close>,
  with_type_wellformed = @{thm with_type_wellformed_type},
  param_names = [],
  transfer = NONE,
  rep_rel_itself = NONE
}\<close>

class domain_with_simple_complement = domain

\<comment> \<open>We need that there is at least one object in our category. We call is \<^term>\<open>some_domain\<close>.\<close>
typedecl some_domain
instance some_domain :: domain_with_simple_complement ..

axiomatization where 
  complement_exists_simple: \<open>register F \<Longrightarrow> \<exists>G :: ('a, 'b) complement_domain_simple update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
    for F :: \<open>'a::domain update \<Rightarrow> 'b::domain_with_simple_complement update\<close>

(* Short for "complement domain carrier" *)
axiomatization cdc :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> ('a,'b) complement_domain set\<close> where 
  complement_exists: \<open>register F \<Longrightarrow> let 'c::domain = cdc F in
                      \<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
    for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>

axiomatization where complement_unique: \<open>compatible F G \<Longrightarrow> iso_register (F;G) \<Longrightarrow> compatible F H \<Longrightarrow> iso_register (F;H)
          \<Longrightarrow> equivalent_registers G H\<close> 
    for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close> and G :: \<open>'g::domain update \<Rightarrow> 'b update\<close> and H :: \<open>'h::domain update \<Rightarrow> 'b update\<close>

end
