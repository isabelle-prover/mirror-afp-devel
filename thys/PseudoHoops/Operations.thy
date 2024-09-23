section\<open>Operations\<close>

theory Operations
imports Main
begin

class left_imp = 
  fixes imp_l :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>l\<rightarrow>\<close> 65)

class right_imp = 
  fixes imp_r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>r\<rightarrow>\<close> 65)

class left_uminus =
  fixes uminus_l :: "'a => 'a"  (\<open>-l _\<close> [81] 80)

class right_uminus =
  fixes uminus_r :: "'a => 'a"  (\<open>-r _\<close> [81] 80)

end
