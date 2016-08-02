theory Lorenz_Parallel
imports Lorenz_Approximation
begin

subsection \<open>Parallelization in Isabelle\<close>

lemma "set (concat (Parallel.map (\<lambda>(i, j). the_res (lorenz_irects 8 8 i j)) (take 4 INITIALS0))) \<subseteq>
  set (map (\<lambda>(i, j). [i, j, 6912]) INITIALS)"
  by eval

end
