section \<open>Axioms of complements\<close>

theory Axioms_Complement
  imports Laws
begin

typedecl ('a, 'b) complement_domain
instance complement_domain :: (domain, domain) domain..

\<comment> \<open>We need that there is at least one object in our category. We call is \<^term>\<open>some_domain\<close>.\<close>
typedecl some_domain
instance some_domain :: domain..

axiomatization where 
  complement_exists: \<open>register F \<Longrightarrow> \<exists>G :: ('a, 'b) complement_domain update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close> for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>

axiomatization where complement_unique: \<open>compatible F G \<Longrightarrow> iso_register (F;G) \<Longrightarrow> compatible F H \<Longrightarrow> iso_register (F;H)
          \<Longrightarrow> equivalent_registers G H\<close> 
    for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close> and G :: \<open>'g::domain update \<Rightarrow> 'b update\<close> and H :: \<open>'h::domain update \<Rightarrow> 'b update\<close>

end
