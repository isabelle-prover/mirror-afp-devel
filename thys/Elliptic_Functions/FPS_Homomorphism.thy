theory FPS_Homomorphism
  imports "HOL-Computational_Algebra.Formal_Laurent_Series" "Polynomial_Interpolation.Ring_Hom"
begin

interpretation fps_to_fls: comm_ring_hom "fps_to_fls :: 'a :: comm_ring_1 fps \<Rightarrow> 'a fls"
  by standard (auto simp: fls_times_fps_to_fls)

interpretation fps_to_fls: inj_idom_hom "fps_to_fls :: 'a :: idom fps \<Rightarrow> 'a fls"
  by standard auto

interpretation fps_const: comm_ring_hom "fps_const :: 'a :: comm_ring_1 \<Rightarrow> 'a fps"
  by standard auto

interpretation fps_const: inj_idom_hom "fps_const :: 'a :: idom \<Rightarrow> 'a fps"
  by standard auto

interpretation fls_const: comm_ring_hom "fls_const :: 'a :: comm_ring_1 \<Rightarrow> 'a fls"
  by standard (auto simp: fls_plus_const)

interpretation fls_const: inj_idom_hom "fls_const :: 'a :: idom \<Rightarrow> 'a fls"
  by standard auto

interpretation fls_const: field_hom "fls_const :: 'a :: field \<Rightarrow> 'a fls"
  by standard auto

interpretation fls_const: field_char_0_hom "fls_const :: 'a :: field_char_0 \<Rightarrow> 'a fls"
  by standard auto


locale fps_homomorphism =
  fixes f :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"
  assumes f_0: "f 0 = 0"
  assumes f_1: "f 1 = 1"
  assumes f_add: "f (x + y) = f x + f y"
  assumes f_mult: "f (x * y) = f x * f y"
begin

lemma f_sum: "f (\<Sum>x\<in>A. g x) = (\<Sum>x\<in>A. f (g x))"
  by (induction A rule: infinite_finite_induct) (simp_all add: f_0 f_add)

lemma f_prod: "f (\<Prod>x\<in>A. g x) = (\<Prod>x\<in>A. f (g x))"
  by (induction A rule: infinite_finite_induct) (simp_all add: f_1 f_mult)

lemma f_sum_list: "f (sum_list xs) = sum_list (map f xs)"
  by (induction xs) (simp_all add: f_0 f_add)

lemma f_prod_list: "f (prod_list xs) = prod_list (map f xs)"
  by (induction xs) (simp_all add: f_1 f_mult)

lemma f_power: "f (x ^ n) = f x ^ n"
  using f_prod[of "\<lambda>_. x" "{..<n}"] by simp

lemmas f_simps = f_0 f_1 f_add f_mult f_sum f_prod f_power

definition fps :: "'a fps \<Rightarrow> 'b fps" where
  "fps F = Abs_fps (\<lambda>n. f (fps_nth F n))"

lemma fps_nth [simp]: "fps_nth (fps F) n = f (fps_nth F n)"
  by (simp add: fps_def)

lemma Abs_fps [simp]: "fps (Abs_fps g) = Abs_fps (\<lambda>n. f (g n))"
  by (simp add: fps_eq_iff)

lemma fps_0 [simp]: "fps 0 = 0"
  and fps_1 [simp]: "fps 1 = 1"
  and fps_const [simp]: "fps (fps_const c) = fps_const (f c)"
  and fps_add [simp]: "fps (F + G) = fps F + fps G"
  and fps_mult [simp]: "fps (F * G) = fps F * fps G"
  and fps_shift [simp]: "fps (fps_shift n F) = fps_shift n (fps F)"
  by (simp_all add: fps_eq_iff f_simps fps_mult_nth)

lemma fps_sum: "fps (\<Sum>x\<in>A. g x) = (\<Sum>x\<in>A. fps (g x))"
  by (induction A rule: infinite_finite_induct) (simp_all add: f_0 f_add)

lemma fps_prod: "fps (\<Prod>x\<in>A. g x) = (\<Prod>x\<in>A. fps (g x))"
  by (induction A rule: infinite_finite_induct) (simp_all add: f_1 f_mult)

lemma fps_sum_list: "fps (sum_list xs) = sum_list (map fps xs)"
  by (induction xs) (simp_all add: f_0 f_add)

lemma fps_prod_list: "fps (prod_list xs) = prod_list (map fps xs)"
  by (induction xs) (simp_all add: f_1 f_mult)

lemma fps_power [simp]: "fps (x ^ n) = fps x ^ n"
  using fps_prod[of "\<lambda>_. x" "{..<n}"] by simp

lemma fps_of_nat [simp]: "fps (of_nat n) = of_nat n"
  by (induction n) (simp_all add: f_simps)

lemma fps_numeral [simp]: "fps (numeral num) = numeral num"
  by (subst (1 2) of_nat_numeral [symmetric]) (rule fps_of_nat)


end

locale fps_homomorphism_ring =
  fps_homomorphism f for f :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
begin

lemma fps_minus [simp]: "fps (-x) = -fps x"
proof -
  have "0 = x + (-x)"
    by simp
  also have "fps \<dots> = fps x + fps (-x)"
    by (subst fps_add) auto
  finally show ?thesis
    by (simp add: algebra_simps add_eq_0_iff)
qed

lemma fps_diff [simp]: "fps (F - G) = fps F - fps G"
proof -
  have "fps (F - G) = fps (F + -G)"
    by simp
  thus ?thesis
    unfolding fps_add by simp
qed

lemma fps_of_int [simp]: "fps (of_int m) = of_int m"
  using fps_of_nat[of "nat m"] fps_minus[of "of_nat (nat (-m))"] fps_of_nat[of "nat (-m)"]
  by (cases "m \<ge> 0") (simp_all del: fps_minus fps_of_nat)

end
  
interpretation of_nat: fps_homomorphism of_nat
  by standard auto

interpretation of_nat_fps: comm_semiring_hom "of_nat.fps"
  by standard auto

interpretation of_nat_fps: inj_semiring_hom "of_nat.fps :: nat fps \<Rightarrow> 'a :: {comm_semiring_1, semiring_char_0} fps"
  by standard (auto simp: fps_eq_iff)


interpretation of_int: fps_homomorphism of_int
  by standard auto

interpretation of_int: fps_homomorphism_ring of_int
  by standard auto

interpretation of_int_fps: comm_ring_hom "of_int.fps"
  by standard auto

interpretation of_int_fps: inj_idom_hom "of_int.fps :: int fps \<Rightarrow> 'a :: {idom, ring_char_0} fps"
  by standard (auto simp: fps_eq_iff)

end