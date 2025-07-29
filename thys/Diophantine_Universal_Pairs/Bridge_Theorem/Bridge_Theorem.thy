theory Bridge_Theorem
  imports Bridge_Theorem_Rev
begin

theorem (in bridge_variables) theorem_II:
  fixes b Y X g :: int
  assumes "b \<ge> 0" and "Y \<ge> b \<and> Y \<ge> 2^8" and "X \<ge> 3*b" and "g \<ge> 1"
  shows "statement2 b Y X g = statement1 b Y X"
    and "statement2a b Y X g = statement1 b Y X"
  using theorem_II_1_3[of b Y X g] theorem_II_3_2[of b Y X g] theorem_II_2_1[of b Y X g] assms by argo+

(* The following theorems are for exposition only. *)

definition (in bridge_variables) bridge_relations
  where "bridge_relations k l w h x y b g Y X \<equiv>
    is_square (D l w h g Y X * F l w h x g Y X * I l w h x y g Y X)
    \<and> is_square ((U l X Y^4*V w g Y^2-4)*J k l w g Y X^2+4)
    \<and> S l w g Y X dvd T l w h g Y X b 
    \<and> ((4*g*(C l w h g Y X)-4*g*l*Y*(J k l w g Y X))^2 < (J k l w g Y X)^2)"

theorem (in bridge_variables) bridge_theorem_simplified:
  fixes b Y X g :: int
  assumes "b \<ge> 0" and "Y \<ge> b" and "Y \<ge> 2^8" and "X \<ge> 3*b" and "g \<ge> 1"
  shows "(is_power2 b \<and> Y dvd int (2 * nat X choose nat X))
        = (\<exists>h k l w x y :: int. bridge_relations k l w h x y b g Y X
                                \<and> (h\<ge>b)\<and>(k\<ge>b)\<and>(l\<ge>b)\<and>(w\<ge>b)\<and>(x\<ge>b)\<and>(y\<ge>b))"
  unfolding bridge_relations_def J_def
  using assms theorem_II(2) statement1_def
        statement2a_def[unfolded d2a_def d2b_def d2c_def d2e_def L_def]
  by (auto simp: mult.assoc)

end
