\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lattice Syntax\<close>
theory HOL_Syntax_Bundles_Lattices
  imports
    HOL.Lattices
begin

bundle lattice_syntax \<comment> \<open>copied from theory Main\<close>
begin
notation
  bot (\<open>\<bottom>\<close>)
  and top (\<open>\<top>\<close>)
  and inf (infixl \<open>\<sqinter>\<close> 70)
  and sup (infixl \<open>\<squnion>\<close> 65)
end

unbundle lattice_syntax

end