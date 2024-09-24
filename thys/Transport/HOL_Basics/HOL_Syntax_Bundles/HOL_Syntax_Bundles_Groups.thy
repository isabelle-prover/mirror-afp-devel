\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Group Syntax\<close>
theory HOL_Syntax_Bundles_Groups
  imports HOL.Groups
begin

bundle HOL_groups_syntax
begin
notation Groups.zero (\<open>0\<close>)
notation Groups.one (\<open>1\<close>)
notation Groups.plus (infixl \<open>+\<close> 65)
notation Groups.minus (infixl \<open>-\<close> 65)
notation Groups.uminus (\<open>- _\<close> [81] 80)
notation Groups.times (infixl \<open>*\<close> 70)
notation abs (\<open>\<bar>_\<bar>\<close>)
end
bundle no_HOL_groups_syntax
begin
no_notation Groups.zero (\<open>0\<close>)
no_notation Groups.one (\<open>1\<close>)
no_notation Groups.plus (infixl \<open>+\<close> 65)
no_notation Groups.minus (infixl \<open>-\<close> 65)
no_notation Groups.uminus (\<open>- _\<close> [81] 80)
no_notation Groups.times (infixl \<open>*\<close> 70)
no_notation abs (\<open>\<bar>_\<bar>\<close>)
end


end