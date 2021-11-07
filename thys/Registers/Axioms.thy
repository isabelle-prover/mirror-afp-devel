section \<open>Axioms of registers\<close>

theory Axioms
  imports Main
begin

class domain
instance prod :: (domain,domain) domain
  by intro_classes

typedecl 'a update
axiomatization comp_update :: "'a::domain update \<Rightarrow> 'a update \<Rightarrow> 'a update" where
  comp_update_assoc: "comp_update (comp_update a b) c = comp_update a (comp_update b c)"
axiomatization id_update :: "'a::domain update" where
  id_update_left: "comp_update id_update a = a" and
  id_update_right: "comp_update a id_update = a"

axiomatization preregister :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> bool\<close>
axiomatization where
  comp_preregister: "preregister F \<Longrightarrow> preregister G \<Longrightarrow> preregister (G \<circ> F)" and
  id_preregister: \<open>preregister id\<close>
for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close> and G :: \<open>'b update \<Rightarrow> 'c::domain update\<close>

axiomatization where
  preregister_mult_right: \<open>preregister (\<lambda>a. comp_update a z)\<close> and
  preregister_mult_left: \<open>preregister (\<lambda>a. comp_update z a)\<close>
    for z :: "'a::domain update"

axiomatization tensor_update :: \<open>'a::domain update \<Rightarrow> 'b::domain update \<Rightarrow> ('a\<times>'b) update\<close> 
  where tensor_extensionality: "preregister F \<Longrightarrow> preregister G \<Longrightarrow> (\<And>a b. F (tensor_update a b) = G (tensor_update a b)) \<Longrightarrow> F = G"
  for F G :: \<open>('a\<times>'b) update \<Rightarrow> 'c::domain update\<close>

axiomatization where tensor_update_mult: \<open>comp_update (tensor_update a c) (tensor_update b d) = tensor_update (comp_update a b) (comp_update c d)\<close>
  for a b :: \<open>'a::domain update\<close> and c d :: \<open>'b::domain update\<close>

axiomatization register :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close>
axiomatization where
  register_preregister: "register F \<Longrightarrow> preregister F" and
  register_comp: "register F \<Longrightarrow> register G \<Longrightarrow> register (G \<circ> F)"  and
  register_mult: "register F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)" and
  register_of_id: \<open>register F \<Longrightarrow> F id_update = id_update\<close> and
  register_id: \<open>register (id :: 'a update \<Rightarrow> 'a update)\<close>
for F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'b update \<Rightarrow> 'c::domain update" 

axiomatization where register_tensor_left: \<open>register (\<lambda>a. tensor_update a id_update)\<close>
axiomatization where register_tensor_right: \<open>register (\<lambda>a. tensor_update id_update a)\<close>

axiomatization register_pair ::
  \<open>('a::domain update \<Rightarrow> 'c::domain update) \<Rightarrow> ('b::domain update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  register_pair_is_register: \<open>register F \<Longrightarrow> register G \<Longrightarrow> (\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a))
       \<Longrightarrow> register (register_pair F G)\<close> and
  register_pair_apply: \<open>register F \<Longrightarrow> register G \<Longrightarrow> (\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a))
       \<Longrightarrow> (register_pair F G) (tensor_update a b) = comp_update (F a) (G b)\<close>

end
