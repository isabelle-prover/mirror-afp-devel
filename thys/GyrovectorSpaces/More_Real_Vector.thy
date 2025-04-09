theory More_Real_Vector
  imports Main "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces
begin

lemma (in real_vector) inner_eq_1:
  assumes "norm a = 1" "norm b = 1" "inner a b = 1"
  shows "a = b"
proof-
  have "(norm (a - b))\<^sup>2 = inner (a - b) (a - b)"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> = inner a a - 2 * (inner a b) + inner b b"
    by (simp add: inner_commute inner_diff_right)
  also have "... = 0"
    using assms
    by (simp add: norm_eq_sqrt_inner)
  finally have "norm (a - b) = 0"
    by simp
  thus "a = b"
    by simp
qed

end