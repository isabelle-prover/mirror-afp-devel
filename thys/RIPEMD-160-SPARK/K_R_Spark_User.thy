theory K_R_Spark_User
imports K_R_Spark_Specification K_R_Spark_Declaration

begin



lemma goal6'1: 
  assumes H1: " (0 :: int) <= j'' "
  assumes H2: " j'' <= (15 :: int) "
  shows " (1352829926 :: int) = k_r' j'' " (is "?C1")
  using assms by (simp add: K'_def)

lemma goal7'1: 
  assumes H1: " (16 :: int) <= j'' "
  assumes H2: " j'' <= (31 :: int) "
  shows " (1548603684 :: int) = k_r' j'' " (is "?C1")
proof-
  from H1 have "16 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 31" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed

lemma goal8'1: 
  assumes H1: " (32 :: int) <= j'' "
  assumes H2: " j'' <= (47 :: int) "
  shows " (1836072691 :: int) = k_r' j'' " (is "?C1")
proof -
  from H1 have "32 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 47" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed


lemma goal9'1: 
  assumes H1: " (48 :: int) <= j'' "
  assumes H2: " j'' <= (63 :: int) "
  shows " (2053994217 :: int) = k_r' j'' " (is "?C1")
proof -
  from H1 have "48 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 63" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed


lemma goal10'1: 
  assumes H2: " j'' <= (79 :: int) "
  assumes H6: " (63 :: int) < j'' "
  shows " (0 :: int) = k_r' j'' " (is "?C1")
proof -
  from H6 have "64 <= nat j''" by simp
  moreover from H2 have "nat j'' <= 79" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed


lemmas userlemmas =
  goal6'1
  goal7'1
  goal8'1
  goal9'1
  goal10'1
end
