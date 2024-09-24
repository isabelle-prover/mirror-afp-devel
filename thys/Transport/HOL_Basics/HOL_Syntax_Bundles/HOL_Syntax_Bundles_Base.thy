\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>HOL Syntax Bundles\<close>
subsection \<open>Basic Syntax\<close>
theory HOL_Syntax_Bundles_Base
  imports HOL_Basics_Base
begin

bundle HOL_ascii_syntax
begin
notation (ASCII)
  Not (\<open>~ _\<close> [40] 40) and
  conj (infixr \<open>&\<close> 35) and
  disj (infixr \<open>|\<close> 30) and
  implies (infixr \<open>-->\<close> 25) and
  not_equal (infixl \<open>~=\<close> 50)
syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" (\<open>(let (_)/ in (_))\<close> 10)
end
bundle no_HOL_ascii_syntax
begin
no_notation (ASCII)
  Not (\<open>~ _\<close> [40] 40) and
  conj (infixr \<open>&\<close> 35) and
  disj (infixr \<open>|\<close> 30) and
  implies (infixr \<open>-->\<close> 25) and
  not_equal (infixl \<open>~=\<close> 50)
no_syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" (\<open>(let (_)/ in (_))\<close> 10)
end


end