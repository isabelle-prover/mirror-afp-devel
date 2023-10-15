\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Relation Syntax\<close>
theory HOL_Syntax_Bundles_Relations
  imports HOL.Relation
begin

bundle HOL_relation_syntax
begin
notation relcomp (infixr "O" 75)
notation relcompp (infixr "OO" 75)
notation converse ("(_\<inverse>)" [1000] 999)
notation conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)
notation (ASCII)
  converse  ("(_^-1)" [1000] 999) and
  conversep ("(_^--1)" [1000] 1000)
end
bundle no_HOL_relation_syntax
begin
no_notation relcomp (infixr "O" 75)
no_notation relcompp (infixr "OO" 75)
no_notation converse ("(_\<inverse>)" [1000] 999)
no_notation conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)
no_notation (ASCII)
  converse  ("(_^-1)" [1000] 999) and
  conversep ("(_^--1)" [1000] 1000)
end


end