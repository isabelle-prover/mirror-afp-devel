\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lattice Syntax\<close>
theory HOL_Syntax_Bundles_Lattices
  imports
    HOL.Lattices
begin

bundle lattice_syntax \<comment> \<open>copied from theory Main\<close>
begin
notation
  bot ("\<bottom>")
  and top ("\<top>")
  and inf (infixl "\<sqinter>" 70)
  and sup (infixl "\<squnion>" 65)
end
bundle no_lattice_syntax
begin
no_notation
  bot ("\<bottom>")
  and top ("\<top>")
  and inf (infixl "\<sqinter>" 70)
  and sup (infixl "\<squnion>" 65)
end

unbundle lattice_syntax


end