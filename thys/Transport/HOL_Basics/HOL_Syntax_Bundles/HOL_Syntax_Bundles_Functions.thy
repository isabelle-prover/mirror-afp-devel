\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Function Syntax\<close>
theory HOL_Syntax_Bundles_Functions
  imports HOL.Fun
begin

bundle HOL_function_syntax
begin
notation comp (infixl "\<circ>" 55)
end
bundle no_HOL_function_syntax
begin
no_notation comp (infixl "\<circ>" 55)
end


end