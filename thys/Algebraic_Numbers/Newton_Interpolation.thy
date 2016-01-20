(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Newton Interpolation\<close>

text \<open>We implemented Newton interpolation, i.e., a method to interpolate a polynomial $p$
  from a list of points $(x_1,p(x_1)), (x_2, p(x_2)), \ldots$. The interpolation algorithm 
  currently has no soundness properties but can be used as a fast interpolation oracle.

  It remains as future work to prove correctness of the algorithm.\<close>
theory Newton_Interpolation
imports 
  Polynomial
  Lagrange_Interpolation
begin

context
fixes 
  ty :: "'a :: field itself"
  and x :: "nat \<Rightarrow> 'a"
  and f :: "nat \<Rightarrow> 'a"
  and xs :: "'a list"
  and fs :: "'a list"
begin

private function xij_f :: "nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "xij_f i j = (if i < j then (xij_f (i + 1) j - xij_f i (j - 1)) / (x j - x i) else f i)"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,j). j - i)", auto)

private fun combine_rows :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "combine_rows [] fj xj xis = [fj]"
| "combine_rows (xi_j1 # x_j1s) fj xj (xi # xis) = (let 
    x_js = combine_rows x_j1s fj xj xis;
    new = (hd x_js - xi_j1) / (xj - xi)
    in new # x_js)"
    

private fun newton_coefficients_main :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "newton_coefficients_main [fj] xjs = [[fj]]"
| "newton_coefficients_main (fj # fjs) (xj # xjs) = (
    let rec = newton_coefficients_main fjs xjs; row = hd rec;
      new_row = combine_rows row fj xj xs
    in new_row # rec)"
| "newton_coefficients_main _ _ = []"

private definition c :: "nat \<Rightarrow> 'a" where
  "c i = xij_f 0 i"

private fun newton_coefficients :: "nat \<Rightarrow> 'a list" where
  "newton_coefficients n = map hd (newton_coefficients_main (rev fs) (rev xs))"

private fun b :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "b 0 n = [:c n:]"
| "b (Suc j) i = b j (i + 1) * [: - x i, 1 :] + [:c i:]"

private fun newton_composition :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a poly" where
  "newton_composition [cn] xis = [:cn:]"
| "newton_composition (ci # cs) (xi # xis) = newton_composition cs xis * [:- xi, 1:] + [:ci:]"
| "newton_composition _ _ = 0"

definition newton_poly :: "nat \<Rightarrow> 'a poly" where
  "newton_poly n = b n 0"

definition newton_poly_impl :: "nat \<Rightarrow> 'a poly" where
  "newton_poly_impl n = newton_composition (rev (newton_coefficients n)) xs"
end

definition newton_interpolation_poly :: "('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "newton_interpolation_poly x_fs = (let n = length x_fs - 1;
    xs = map fst x_fs; fs = map snd x_fs in
    newton_poly_impl xs fs n)"

end