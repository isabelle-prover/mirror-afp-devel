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

end