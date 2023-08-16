section \<open> Polygonal Number Theorem \<close>
subsection \<open> Gauss's Theorem on Triangular Numbers\<close>
text \<open>We show Gauss's theorem which states that every non-negative integer is the sum of three triangles, using the Three Squares Theorem AFP entry \cite{Three_Squares-AFP}. This corresponds to Theorem 1.8 in \cite{nathanson1996}.\<close>

theory Polygonal_Number_Theorem_Gauss
  imports Polygonal_Number_Theorem_Lemmas
begin

text\<open>The following is the formula for the $k$-th polygonal number of order $m+2$.\<close>

definition polygonal_number :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "polygonal_number m k = m*k*(k-1) div 2 + k"

text\<open>When $m = 1$, the polygonal numbers have order 3 and the formula represents triangular numbers. 
Gauss showed that all natural numbers can be written as the sum of three triangular numbers. 
In other words, the triangular numbers form an additive basis of order 3 of the natural numbers.\<close>

theorem Gauss_Sum_of_Three_Triangles:
  fixes n :: nat
  shows "\<exists> x y z. n = polygonal_number 1 x + polygonal_number 1 y + polygonal_number 1 z"

proof -
  have "(8 * n + 3) mod 8 = 3" by auto
  then obtain a b c where 0: "odd a \<and> odd b \<and> odd c \<and> 8 * n + 3 = a^2 + b^2 + c^2"
    using odd_three_squares_using_mod_eight by presburger
  then obtain x y z where "a = 2 * x + 1 \<and> b = 2 * y + 1 \<and> c = 2 * z + 1" by (meson oddE)
  hence "8 * n + 3 = (2 * x + 1)^2 + (2 * y + 1)^2 + (2 * z + 1)^2"
    using 0 by auto
  hence "n = (x * x + x + y * y + y + z * z + z) div 2"
    by (auto simp add: power2_eq_square)
  hence n_expr:"n = (x * (x + 1) + y * (y + 1) + z * (z + 1)) div 2"
    by (metis (no_types, lifting) arithmetic_simps(79) nat_arith.add1 nat_distrib(2))

  have triangle_identity: "polygonal_number 1 k = k*(k+1) div 2" for k
  proof -
    have "k*(k-1)+2*k = k*k+k" by (simp add: right_diff_distrib')
    hence "k*(k-1) div 2 + k = (k*k+k) div 2"
      by (metis Groups.add_ac(2) bot_nat_0.not_eq_extremum div_mult_self2 pos2)
    thus ?thesis using polygonal_number_def by simp
  qed
  from n_expr triangle_identity show ?thesis 
    by (metis div_plus_div_distrib_dvd_right even_mult_iff odd_even_add odd_one)
qed
end