\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>HOL Syntax Bundles\<close>
subsection \<open>Basic Syntax\<close>
theory HOL_Syntax_Bundles_Base
  imports HOL_Basics_Base
begin

bundle HOL_ascii_syntax
begin
notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)
syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
end
bundle no_HOL_ascii_syntax
begin
no_notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)
no_syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
end


end