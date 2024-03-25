section \<open>Quad Tree Basics\<close>

theory Quad_Base
imports "HOL-Library.Tree" (* only for \<open>height\<close> *)
begin

datatype 'a qtree = L 'a | Q "'a qtree" "'a qtree" "'a qtree" "'a qtree"

instantiation qtree :: (type)height
begin

fun height_qtree :: "'a qtree \<Rightarrow> nat" where
"height (L _) = 0" |
"height (Q t0 t1 t2 t3) =
  Max {height t0, height t1, height t2, height t3} + 1"

instance ..

end

end
