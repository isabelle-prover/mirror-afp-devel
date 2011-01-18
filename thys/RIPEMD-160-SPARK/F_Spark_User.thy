theory F_Spark_User
imports F_Spark_Specification F_Spark_Declaration

begin

lemma goal2'1:
  shows "0 <= bit__or' (bit__and' x'' y'') (bit__and' (4294967295 - x'') z'')"
  by (rule WordDefinition.uint_0)

lemma goal2'2:
  shows "bit__or' (bit__and' x'' y'') (bit__and' (4294967295 - x'') z'') <= 4294967295"
  by (simp add: bwsimps int_word_uint)

lemma goal3'1:
  shows "0 <= bit__xor' (bit__or' x'' (4294967295 - y'')) z''"
  by (rule WordDefinition.uint_0)

lemma goal3'2:
  shows "bit__xor' (bit__or' x'' (4294967295 - y'')) z'' <= 4294967295"
  by (simp add: bwsimps int_word_uint)

lemma goal4'1:
  shows "0 <= bit__or' (bit__and' x'' z'' ) (bit__and' y'' (4294967295 - z''))"
  by simp

lemma goal4'2:
  shows "bit__or' (bit__and' x'' z'' ) (bit__and' y'' (4294967295 - z'')) <= 4294967295"
  by (simp add: bwsimps int_word_uint)

lemma goal5'1:
  shows "0 <= bit__xor' x'' (bit__or' y'' (4294967295 - z''))"
  by simp

lemma goal5'2:
  shows "bit__xor' x'' (bit__or' y'' (4294967295 - z'')) <= 4294967295"
  by (simp add: bwsimps int_word_uint)

lemma goal6'1:
  assumes H8: "j'' <= (15 :: int) "
  shows " bit__xor' x'' (bit__xor' y'' z'') = f' j'' x'' y'' z''"
proof -
  from H8 have "nat j'' <= 15" by simp
  thus ?thesis
    by (simp add: f_def)
qed

lemma goal7'1:
  assumes H7: "(16 :: int) <= j''"
  assumes H8: "j'' <= (31 :: int)"
  shows "bit__or' (bit__and' x'' y'') (bit__and' (4294967295 - x'') z'') = f' j'' x'' y'' z''"
proof -
  from H7 have "16 <= nat j''" by simp
  moreover from H8 have "nat j'' <= 31" by simp
  ultimately show ?thesis
    by (simp add: f_def)
qed

lemma goal8'1:
  assumes H7: "32 <= j''"
  assumes H8: "j'' <= 47"
  shows "bit__xor' (bit__or' x'' (4294967295 - y'')) z'' = f' j'' x'' y'' z''"
proof -
  from H7 have "32 <= nat j''" by simp
  moreover from H8 have "nat j'' <= 47" by simp
  ultimately show ?thesis by (simp add: f_def)
qed

lemma goal9'1: 
  assumes H7: "48 <= j''"
  assumes H8: "j'' <= 63"
  shows "bit__or' (bit__and' x'' z'') (bit__and' y'' (4294967295 - z'')) = f' j'' x'' y'' z''"
proof -
  from H7 have "48 <= nat j''" by simp
  moreover from H8 have   "nat j'' <= 63" by simp
  ultimately show ?thesis by (simp add: f_def)
qed

lemma goal10'1:
  assumes H2: "j'' <= 79"
  assumes H12: "63 < j''"
  shows "bit__xor' x'' (bit__or' y'' (4294967295 - z'')) = f' j'' x'' y'' z''"
proof -
  from H2 have "nat j'' <= 79" by simp
  moreover from H12 have "64 <= nat j''" by simp
  ultimately show ?thesis by (simp add: f_def)
qed

lemmas userlemmas =
  goal2'1
  goal2'2
  goal3'1
  goal3'2
  goal4'1
  goal4'2
  goal5'1
  goal5'2
  goal6'1
  goal7'1
  goal8'1
  goal9'1
  goal10'1

end
