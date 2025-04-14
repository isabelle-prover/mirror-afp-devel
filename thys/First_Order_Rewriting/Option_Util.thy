subsection\<open>Option Type\<close>

theory Option_Util
  imports Main
begin

primrec option_to_list :: "'a option \<Rightarrow> 'a list"
  where
    "option_to_list (Some a) = [a]" |
    "option_to_list None = []"

lemma set_option_to_list_sound [simp]:
  "set (option_to_list t) = set_option t"
  by (induct t) auto

fun fun_of_map :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)" where 
  "fun_of_map m d a = (case m a of Some b \<Rightarrow> b | None \<Rightarrow> d)"

end