section \<open>Testing for Integrality and Conversion to Integers\<close>

theory Is_Int_To_Int
  imports 
    Polynomial_Interpolation.Is_Rat_To_Rat
begin

lemma inv_of_rat: "inv of_rat (of_rat x) = x"
  by (meson injI inv_f_eq of_rat_eq_iff)

lemma of_rat_Ints_iff: "((of_rat x :: 'a :: field_char_0) \<in> \<int>) = (x \<in> \<int>)" 
  by (metis Ints_cases Ints_of_int inv_of_rat of_rat_of_int_eq)

lemma is_int_code[code_unfold]:
  shows "(x \<in> \<int>) = (is_rat x \<and> is_int_rat (to_rat x))"
proof -
  have "x \<in> \<int> \<longleftrightarrow> x \<in> \<rat> \<and> x \<in> \<int>"
    by (metis Ints_cases Rats_of_int)
  also have "\<dots> = (is_rat x \<and> is_int_rat (to_rat x))" 
  proof (simp, intro conj_cong[OF refl])
    assume "x \<in> \<rat>" 
    then obtain y where x: "x = of_rat y" unfolding Rats_def by auto
    show "(x \<in> \<int>) = (to_rat x \<in> \<int>)" unfolding x
      by (simp add: of_rat_Ints_iff)
  qed
  finally show ?thesis .
qed

definition to_int :: "'a :: is_rat \<Rightarrow> int" where 
  "to_int x = int_of_rat (to_rat x)" 

lemma of_int_to_int: "x \<in> \<int> \<Longrightarrow> of_int (to_int x) = x" 
  by (metis Ints_cases int_of_rat(1) of_rat_of_int_eq to_int_def to_rat_of_rat)

lemma to_int_of_int: "to_int (of_int x) = x"
  by (metis int_of_rat(1) of_rat_of_int_eq to_int_def to_rat_of_rat)

lemma to_rat_complex_of_real[simp]: "to_rat (complex_of_real x) = to_rat x"
  by (metis Re_complex_of_real complex_of_real_of_rat of_rat_to_rat to_rat to_rat_of_rat)

lemma to_int_complex_of_real[simp]: "to_int (complex_of_real x) = to_int x"
  by (simp add: to_int_def)

end
