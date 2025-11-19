theory Option_Extra \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports Main
begin

abbreviation get_or :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "\<And>a default. get_or a default \<equiv> case a of None \<Rightarrow> default | Some a \<Rightarrow> a"

end
