\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Relation Syntax\<close>
theory HOL_Syntax_Bundles_Relations
  imports HOL.Relation
begin

bundle HOL_relation_syntax
begin
notation relcomp (infixr \<open>O\<close> 75)
notation relcompp (infixr \<open>OO\<close> 75)
notation converse (\<open>(_\<inverse>)\<close> [1000] 999)
notation conversep  (\<open>(_\<inverse>\<inverse>)\<close> [1000] 1000)
notation (ASCII)
  converse  (\<open>(_^-1)\<close> [1000] 999) and
  conversep (\<open>(_^--1)\<close> [1000] 1000)
end
bundle no_HOL_relation_syntax
begin
no_notation relcomp (infixr \<open>O\<close> 75)
no_notation relcompp (infixr \<open>OO\<close> 75)
no_notation converse (\<open>(_\<inverse>)\<close> [1000] 999)
no_notation conversep  (\<open>(_\<inverse>\<inverse>)\<close> [1000] 1000)
no_notation (ASCII)
  converse  (\<open>(_^-1)\<close> [1000] 999) and
  conversep (\<open>(_^--1)\<close> [1000] 1000)
end


end