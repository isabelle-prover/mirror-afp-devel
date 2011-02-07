theory K_L_Spark_User
imports K_L_Spark_Specification K_L_Spark_Declaration

begin



lemma goal6'1:
  fixes j::int
  assumes H1: "0 <= j"
  assumes H2: "j <= 15"
  shows "0 = k_l' j"
  using assms by (simp add: K_def)

lemma goal7'1:
  fixes j::int
  assumes H1: "16 <= j"
  assumes H2: "j <= 31"
  shows "1518500249 = k_l' j"
proof -
  from H1 have "16 <= nat j" by simp
  moreover from H2 have "nat j <= 31" by simp
  ultimately show ?thesis by (simp add: K_def)
qed

lemma goal8'1: 
  assumes H1: " (32 :: int) <= j'' "
  assumes H2: " j'' <= (47 :: int) "
  shows " (1859775393 :: int) = k_l' j'' "
proof -
  from H1 have "32 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 47" by simp
  ultimately show ?thesis by (simp add: K_def)
qed

lemma goal9'1: 
  assumes H1: " (48 :: int) <= j'' "
  assumes H2: " j'' <= (63 :: int) "
  shows " (2400959708 :: int) = k_l' j'' " (is "?C1")
proof -
  from H1 have "48 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 63" by simp
  ultimately show ?thesis by (simp add: K_def)
qed

lemma goal10'1: 
  assumes H2: " j'' <= (79 :: int) "
  assumes H6: " (63 :: int) < j'' "
  shows " (2840853838 :: int) = k_l' j'' " (is "?C1")
proof -
  from H6 have "64 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 79" by simp
  ultimately show ?thesis by (simp add: K_def)
qed

lemmas userlemmas =
  goal6'1
  goal7'1
  goal8'1
  goal9'1
  goal10'1
end
