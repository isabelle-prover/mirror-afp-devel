\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Relation Syntax\<close>
theory HOL_Syntax_Bundles_Relations
  imports HOL.Relation
begin

bundle HOL_relation_syntax
begin
notation relcomp (infixr \<open>O\<close> 75)
notation relcompp (infixr \<open>OO\<close> 75)
notation converse (\<open>(\<open>notation=\<open>postfix -1\<close>\<close>_\<inverse>)\<close> [1000] 999)
notation conversep  (\<open>(\<open>notation=\<open>postfix -1-1\<close>\<close>_\<inverse>\<inverse>)\<close> [1000] 1000)
notation (ASCII)
  converse  (\<open>(\<open>notation=\<open>postfix -1\<close>\<close>_^-1)\<close> [1000] 999) and
  conversep (\<open>(\<open>notation=\<open>postfix -1-1\<close>\<close>_^--1)\<close> [1000] 1000)
end

end