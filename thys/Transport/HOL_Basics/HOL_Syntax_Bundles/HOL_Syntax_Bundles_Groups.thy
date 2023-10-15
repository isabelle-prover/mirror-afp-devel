\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Group Syntax\<close>
theory HOL_Syntax_Bundles_Groups
  imports HOL.Groups
begin

bundle HOL_groups_syntax
begin
notation Groups.zero ("0")
notation Groups.one ("1")
notation Groups.plus (infixl "+" 65)
notation Groups.minus (infixl "-" 65)
notation Groups.uminus ("- _" [81] 80)
notation Groups.times (infixl "*" 70)
notation abs ("\<bar>_\<bar>")
end
bundle no_HOL_groups_syntax
begin
no_notation Groups.zero ("0")
no_notation Groups.one ("1")
no_notation Groups.plus (infixl "+" 65)
no_notation Groups.minus (infixl "-" 65)
no_notation Groups.uminus ("- _" [81] 80)
no_notation Groups.times (infixl "*" 70)
no_notation abs ("\<bar>_\<bar>")
end


end