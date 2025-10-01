theory J3_Relations
  imports J3_Polynomial "../Coding/Utils"
begin

subsection \<open>Properties of the $J_3$ polynomial\<close>

context section5_given
begin

text \<open>Helper lemmas\<close>

lemma cpx_sqrt_of_square:
  "cpx_sqrt (k^2) = of_int (abs k)"
proof -
  have "k^2\<ge>0" by simp
  hence "cpx_sqrt (k^2) = sqrt (of_int (k^2))" unfolding cpx_sqrt_def by simp
  also have "... = of_int (abs k)"
    by (metis of_int_abs of_int_mult of_real_of_int_eq power2_eq_square real_sqrt_abs2)
  finally show ?thesis by blast
qed

lemma sqrt_is_int_iff_square:
  "(\<exists>k::int. cpx_sqrt n = of_int k) \<longleftrightarrow> (\<exists>a. n = a^2)"
proof -
  have 0: "(\<exists>a. n = a^2) \<Longrightarrow> (\<exists>k::int. cpx_sqrt n = of_int k)"
  proof -
    assume "\<exists>a. n = a^2"
    then obtain a where a_def: "n=a^2" by blast
    hence "n\<ge>0" by force
    hence "cpx_sqrt n = of_int (abs a)" using cpx_sqrt_of_square a_def by blast
    thus "\<exists>k::int. cpx_sqrt n = of_int k" by simp
  qed
  have "(\<exists>k::int. cpx_sqrt n = of_int k) \<Longrightarrow> (\<exists>a. n = a^2)"
  proof -
    assume "\<exists>k::int. cpx_sqrt n = of_int k"
    then obtain k where k_def: "cpx_sqrt n = of_int k" by blast
    hence 1: "Im (cpx_sqrt n) = 0" by simp
    have "n<0 \<Longrightarrow> False"
    proof -
      assume assm: "n<0"
      hence "cpx_sqrt n = \<i> * sqrt (-n)" unfolding cpx_sqrt_def by simp
      hence "Im (cpx_sqrt n) \<noteq> 0" using assm by force
      thus "False" using 1 by simp
    qed
    hence "n\<ge>0" by force
    hence "complex_of_real (sqrt n) = of_int k" using k_def unfolding cpx_sqrt_def by simp
    hence "k^2 = n" by (metis k_def of_int_eq_iff of_int_power square_sqrt)
    thus "\<exists>a. n = a^2" by blast
  qed
  thus ?thesis using 0 by blast
qed

abbreviation divd (infixl "divd" 70) where "(divd) \<equiv> Rings.divide_class.divide" 

lemma square_odd_mult_prime: 
  assumes "b\<ge>0"
  shows "\<not>is_square b \<Longrightarrow> \<exists>p. prime p \<and> odd(multiplicity p b)"
proof (cases "b=0")
  case True
  then show "\<not>is_square b \<Longrightarrow> \<exists>p. prime p \<and> odd(multiplicity p b)" unfolding is_square_def by simp
next
  case False
  hence hyp: "b>0" using assms by simp
  have "(\<forall>p. prime p \<longrightarrow> even(multiplicity p b)) \<Longrightarrow> is_square b" 
  proof -
    assume assm: "(\<forall>p. prime p \<longrightarrow> even(multiplicity p b))"
    define S where "S = prime_factors b"
    define a where "a = (\<Prod>p\<in>S. p^(multiplicity p b divd 2))"
    hence "a^2 = (\<Prod>p\<in>S. (p^(multiplicity p b divd 2))^2)" unfolding a_def
      using prod_power_distrib by blast
    also have "... = (\<Prod>p\<in>S. (p^(multiplicity p b divd 2 * 2)))"
      by (simp add: power_mult)
    also have "... = (\<Prod>p\<in>S. (p^(multiplicity p b)))" using S_def assm
      by (metis (no_types, lifting) dvd_div_mult_self in_prime_factors_imp_prime prod.cong)
    also have "... = b"
      using S_def assms prime_factorization_int hyp by presburger
    finally show ?thesis unfolding is_square_def by blast
  qed
  thus "\<not>is_square b \<Longrightarrow> \<exists>p. prime p \<and> odd(multiplicity p b)" by blast
qed

lemma square_even_multiplicity: "prime p \<and> is_square a \<Longrightarrow> even (multiplicity p a)"
proof -
  assume assm: "prime p \<and> is_square a"
  then obtain b where "a = b^2" unfolding is_square_def by blast
  hence "multiplicity p a = 2 * multiplicity p b" using assm
    by (metis mult_0_right multiplicity_zero prime_elem_multiplicity_power_distrib prime_imp_prime_elem zero_power2)
  thus "even (multiplicity p a)" by simp
qed

text \<open>J3 correctly encodes the three squares\<close>

lemma J3_encodes_three_squares: 
  fixes a1::int and a2::int and a3::int
  defines "f \<equiv> (\<lambda>y. (\<lambda>_. 0)(0:=y, 1:=a1, 2:=a2, 3:=a3))"
  shows "(is_square a1 \<and> is_square a2 \<and> is_square a3) \<longleftrightarrow> (\<exists>y::int. insertion (f y) J3 = 0)"
proof -
  (* Direct implication *)

  have dir_imp: "(is_square a1 \<and> is_square a2 \<and> is_square a3) \<Longrightarrow> (\<exists>y::int. insertion (f y) J3 = 0)"
  proof -
    assume assm: "(is_square a1 \<and> is_square a2 \<and> is_square a3)"
    then obtain k1::int and k2::int and k3::int
      where a1_sq: "a1 = k1^2" and a2_sq: "a2 = k2^2" and a3_sq: "a3 = k3^2"
      unfolding is_square_def by blast
    define X3::int where "X3 = 1 + a1^2 + a2^2 + a3^2"
    define y::int where "y = abs k1 + abs k2 * X3 + abs k3 * X3^2"
    define \<epsilon>::"int\<times>int\<times>int" where "\<epsilon> = (-1, -1, -1)"
    have eps: "\<epsilon>\<in>{-1, 1::int}\<times>{-1, 1::int}\<times>{-1, 1::int}" unfolding \<epsilon>_def by blast
    have X3_prop: "X3 = 1 + (f y 1)^2 + (f y 2)^2 + (f y 3)^2" using f_def X3_def by force 
    have "of_int((f y) 0) + fst3 \<epsilon> * cpx_sqrt((f y) 1) + snd3 \<epsilon> * cpx_sqrt((f y) 2) * of_int X3
        + trd3 \<epsilon> * cpx_sqrt((f y) 3) * of_int(X3^2)
      = of_int y - cpx_sqrt a1 - cpx_sqrt a2 * of_int X3 - cpx_sqrt a3 * of_int(X3^2)"
      unfolding \<epsilon>_def f_def by simp
    also have "... = of_int (abs k1 + abs k2 * X3 + abs k3 * X3^2)
        - of_int (abs k1) - of_int (abs k2) * of_int X3 - of_int (abs k3) * of_int(X3^2)"
      unfolding y_def a1_sq a2_sq a3_sq using cpx_sqrt_of_square by presburger
    also have "... = 0" using of_int_add of_int_mult by simp
    finally have "insertion (f y) J3 = 0" using J3_cancels_iff eps
      using X3_prop \<E>_def by blast
    thus "\<exists>y::int. insertion (f y) J3 = 0" by blast
  qed

  (* Reciprocal implication *)

  have "(\<exists>y::int. insertion (f y) J3 = 0) \<and> \<not> (is_square a1 \<and> is_square a2 \<and> is_square a3) \<Longrightarrow> False"
  proof -
    assume assm: "(\<exists>y::int. insertion (f y) J3 = 0) \<and> \<not> (is_square a1 \<and> is_square a2 \<and> is_square a3)"
    then obtain y where J3_eq_0: "insertion (f y) J3 = 0" by blast
    define A::"nat\<Rightarrow>int" where "A = (\<lambda>k. f y k)" (* so that A 1 = a1 for example *)
    define X3 where "X3 \<equiv> 1 + (f y 1)^2 + (f y 2)^2 + (f y 3)^2"
    obtain \<epsilon>::"int\<times>int\<times>int"
      where \<epsilon>_prop: "\<epsilon>\<in>{-1,1::int}\<times>{-1,1::int}\<times>{-1,1::int}"
      and "of_int(f y 0) + fst3 \<epsilon> * cpx_sqrt(f y 1) + snd3 \<epsilon> * cpx_sqrt(f y 2) * of_int(X3)
        + trd3 \<epsilon> * cpx_sqrt(f y 3) * of_int (X3^2) = 0"
      using J3_eq_0 J3_cancels_iff[of "f y"] X3_def \<E>_def by blast
    hence fact_0: "of_int y + fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)
        + trd3 \<epsilon> * cpx_sqrt a3 * of_int (X3^2) = 0" using f_def by force
    hence "of_int y + fun3 \<epsilon> 1 * cpx_sqrt a1 + fun3 \<epsilon> 2 * cpx_sqrt a2 * of_int(X3)
        + fun3 \<epsilon> 3 * cpx_sqrt a3 * of_int (X3^2) = 0"
      using fact_0 fun3_1_eq_fst3 fun3_2_eq_snd3 fun3_3_eq_trd3 by metis
    hence "0 = of_int y + fun3 \<epsilon> 1 * cpx_sqrt (A 1) * of_int (X3^(1-1))
                    + fun3 \<epsilon> 2 * cpx_sqrt (A 2) * of_int(X3^(2-1))
                    + fun3 \<epsilon> 3 * cpx_sqrt (A 3) * of_int (X3^(3-1))"
      unfolding f_def A_def by fastforce
    also have "... = of_int y +(\<Sum>j\<in>{1,2,3}. fun3 \<epsilon> j * cpx_sqrt(A j) * of_int (X3^(j-1)))"
      by simp
    finally have fact_0_sum: 
          "0 = of_int y +(\<Sum>j\<in>{1,2,3}. fun3 \<epsilon> j * cpx_sqrt(A j) * of_int (X3^(j-1)))" by blast
    have X3_pos: "X3\<ge>1" unfolding X3_def by simp

    (* Proof that a1, a2, a3 \<ge> 0  *)

    have abs_sqrt_Le_X3: "n\<in>{a1, a2, a3} \<Longrightarrow> abs(Im(cpx_sqrt n)) \<le> X3-1" for n
    proof -
      assume assm: "n\<in>{a1, a2, a3}"
      have "abs(Im(cpx_sqrt n)) \<le> cmod (cpx_sqrt n)" by (simp add: abs_Im_le_cmod)
      also have "... = abs (sqrt n)"
        unfolding cpx_sqrt_def by (simp add: norm_mult real_sqrt_minus)
      also have "... = sqrt(abs n)" 
        by (metis of_int_abs real_sqrt_abs2 real_sqrt_mult)
      also have "... \<le> abs n" using sqrt_int_smaller
        using abs_ge_zero by blast
      also have "... = abs (sqrt (n^2))" by force
      also have "... \<le> abs (n^2)" using sqrt_int_smaller
        by (smt (verit, ccfv_SIG) of_int_nonneg real_sqrt_ge_zero zero_le_power2)
      also have "... \<le> X3-1" unfolding X3_def f_def apply simp using assm by fastforce
      finally show ?thesis by simp
    qed
    have "a3<0 \<Longrightarrow> False"
    proof -
      assume assm: "a3<0"
      hence sqrt3:"cpx_sqrt a3 = \<i> * sqrt (-a3)" unfolding cpx_sqrt_def by simp
      have sqBe1: "abs(sqrt(-a3)) \<ge> 1" using assm by simp
      have "0 = Im (of_int y + fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)
        + trd3 \<epsilon> * cpx_sqrt a3 * of_int (X3^2))" using fact_0 by simp
      also have "... = Im(fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)
        + trd3 \<epsilon> * of_int (X3^2) * cpx_sqrt a3)" by force
      also have "... = Im(fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3))
        + trd3 \<epsilon> * of_int (X3^2) * sqrt(-a3)" using sqrt3 by force
      finally have 0: "0 \<ge> - (abs(Im(fst3 \<epsilon> * cpx_sqrt a1)) + abs(Im(snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3))))
        + abs (trd3 \<epsilon> * X3^2 * sqrt(-a3))" by force 
      
      have "abs(Im(fst3 \<epsilon> * cpx_sqrt a1)) + abs(Im(snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)))
       = abs(Im(cpx_sqrt a1)) + abs(Im (cpx_sqrt a2)) * abs (of_int(X3))"
        using \<epsilon>_prop(1) abs_mult by force
      also have "... \<le> of_int (X3 - 1) + of_int (X3 -1) * abs(of_int X3)" using abs_sqrt_Le_X3
        by (smt (verit, best) insertCI mult_right_mono)
      also have "... = X3-1 + (X3-1)*X3" using X3_pos of_int_add of_int_mult by force
      also have "... = X3^2-1" by algebra
      finally have 1: "abs(Im(fst3 \<epsilon> * cpx_sqrt a1)) + abs(Im(snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)))
                      \<le> X3^2-1" by blast

      have "abs (trd3 \<epsilon> * X3^2 * sqrt(-a3)) = abs (of_int (trd3 \<epsilon>)) * abs (of_int (X3^2)) * abs (sqrt(-a3))"
        using abs_mult of_int_mult by metis
      also have "... = X3^2 * abs (sqrt(-a3))"
        using \<epsilon>_prop(1) by fastforce
      also have "... \<ge> X3^2" using sqBe1 mult_left_mono[of 1 "abs( sqrt(-a3))" "X3^2"] by force
      finally have "0 \<ge> -(X3^2-1) + X3^2" using 0 1 by force
      thus "False" by simp
    qed
    hence a3_pos: "a3\<ge>0" by fastforce
    have "a2<0 \<Longrightarrow> False"
    proof -
      assume assm: "a2<0"
      hence sqrt2:"cpx_sqrt a2 = \<i> * sqrt (-a2)" unfolding cpx_sqrt_def by simp
      have sqBe1: "abs(sqrt(-a2)) \<ge> 1" using assm by simp
      have "0 = Im (of_int y + fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)
        + trd3 \<epsilon> * cpx_sqrt a3 * of_int (X3^2))" using fact_0 by simp
      also have "... = Im(fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3))"
        using a3_pos cpx_sqrt_def by force
      also have "... = Im(fst3 \<epsilon> * cpx_sqrt a1) + snd3 \<epsilon> * sqrt (-a2) * of_int(X3)"
        using sqrt2 by force
      finally have 0: "0 \<ge> - abs(Im(fst3 \<epsilon> * cpx_sqrt a1)) + abs(snd3 \<epsilon> * X3 * sqrt (-a2))"
        by (smt (verit, del_insts) mult.assoc mult.commute of_int_mult)
      
      have "abs(Im(fst3 \<epsilon> * cpx_sqrt a1)) = abs(Im(cpx_sqrt a1))"
        using \<epsilon>_prop(1) abs_mult by force
      also have "... \<le> of_int (X3 - 1)" using abs_sqrt_Le_X3
        by (smt (verit, best) insertCI mult_right_mono)
      finally have 1: "abs(Im(fst3 \<epsilon> * cpx_sqrt a1)) \<le> X3-1" by blast

      have "abs (snd3 \<epsilon> * X3 * sqrt(-a2)) = abs (of_int (snd3 \<epsilon>)) * abs (of_int (X3)) * abs (sqrt(-a2))"
        using abs_mult of_int_mult by metis
      also have "... = X3 * abs (sqrt(-a2))" using \<epsilon>_prop(1) X3_pos by fastforce
      also have "... \<ge> X3" using sqBe1 X3_pos mult_left_mono by force
      finally have "0 \<ge> -(X3-1) + X3" using 0 1 by force
      thus "False" by simp
    qed
    hence a2_pos: "a2\<ge>0" by fastforce
    have "a1<0 \<Longrightarrow> False"
    proof -
      assume assm: "a1<0"
      hence sqrt1:"cpx_sqrt a1 = \<i> * sqrt (-a1)" unfolding cpx_sqrt_def by simp
      have sqBe1: "abs(sqrt(-a1)) \<ge> 1" using assm by simp
      have "0 = Im (of_int y + fst3 \<epsilon> * cpx_sqrt a1 + snd3 \<epsilon> * cpx_sqrt a2 * of_int(X3)
        + trd3 \<epsilon> * cpx_sqrt a3 * of_int (X3^2))" using fact_0 by simp
      also have "... = Im(fst3 \<epsilon> * cpx_sqrt a1)"
        using a3_pos a2_pos cpx_sqrt_def by force
      also have "... = fst3 \<epsilon> * sqrt (-a1)" using sqrt1 by simp
      finally show "False" using assm \<epsilon>_prop(1) by force
    qed
    hence a1_pos: "a1\<ge>0" by fastforce

    (* Writing equality with the two big sums *)

    define k::nat where "k = (if \<not>is_square a3 then 3 else
                        (if \<not>is_square a2 then 2 else 1))"
    hence k123: "k\<in>{1,2,3}" by simp
    consider (3) "\<not>is_square a3" | (2) "is_square a3 \<and> \<not>is_square a2"
           | (1) "is_square a3 \<and> is_square a2" by blast
    hence Ak_bigger_not_sq: "\<not>is_square (A k) \<and> (\<forall>j\<in>{k+1..3}. is_square (A j))"
    proof (cases)
      case 3 then show ?thesis using k_def A_def f_def by simp
    next
      case 2 then show ?thesis using k_def A_def f_def by simp
    next
      case 1 then show ?thesis using assm k_def A_def f_def by simp
    qed
    have A_pos: "j\<in>{1,2,3} \<Longrightarrow> A j \<ge> 0" for j
      using a1_pos a2_pos a3_pos unfolding A_def f_def by fastforce
    obtain p::int where p_prime: "prime p" and p_mult: "odd(multiplicity p (A k))"
      using square_odd_mult_prime Ak_bigger_not_sq A_pos[of k] k123 by blast
    have sqrtpA: "sqrt(A j) = sqrt(p) *  sqrt(A j/p)" for j using real_sqrt_mult[of "real_of_int p"]
      by (metis mult.commute nonzero_divide_eq_eq not_prime_0 of_int_0_eq_iff p_prime)
    define Se where "Se = {x\<in>{1,2,3}. even(multiplicity p (A x))}"
    define So where "So = {x\<in>{1,2,3}. odd(multiplicity p (A x))}"
    have disj_Se_So: "Se\<inter>So = {} \<and> Se\<union>So = {1,2,3}" using Se_def So_def by fast
    hence eq_two_sums: "0 = of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * cpx_sqrt(A j) * of_int (X3^(j-1)))
                       + (\<Sum>j\<in>So. fun3 \<epsilon> j * cpx_sqrt(A j) * of_int (X3^(j-1)))"
      using fact_0_sum sum.union_disjoint
      by (smt (verit, best) add.commute finite.emptyI finite_Un finite_insert group_cancel.add2)
    also have "... = of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * complex_of_real (sqrt(A j)) * of_int (X3^(j-1)))
                       + (\<Sum>j\<in>So. fun3 \<epsilon> j * complex_of_real (sqrt(A j)) * of_int (X3^(j-1)))"
      using A_pos unfolding Se_def So_def cpx_sqrt_def by force
    also have "... =  of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))
                               + (\<Sum>j\<in>So. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))"
      using of_real_mult of_real_add by force
    also have eq_sum_random1: "... = of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))
                              + (\<Sum>j\<in>So.  sqrt(p) * fun3 \<epsilon> j *  sqrt(A j/p) * of_int (X3^(j-1)))"
      using sqrtpA by (simp add:algebra_simps)
    also have eq_sum_random2: "... = of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))
                         + sqrt (p) * (\<Sum>j\<in>So. fun3 \<epsilon> j *  sqrt(A j/p) * of_int (X3^(j-1)))"
      using sum_distrib_left[of "sqrt (real_of_int p)" "(\<lambda>j. real_of_int (fun3 \<epsilon> j) *
         sqrt (real_of_int (A j) / real_of_int p) * real_of_int (X3 ^ (j - 1)))" So]
      by (metis (no_types, lifting) mult.assoc sum.cong)
    finally have fact_0_sum_real:
          "0 =  of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))
                         + sqrt (p) * (\<Sum>j\<in>So. fun3 \<epsilon> j * sqrt(A j/p) * of_int (X3^(j-1)))"
      using of_real_eq_0_iff by fastforce

    (* 2-dimensional vector space arguments *)

    obtain b1::int where b1_def: "a1 = b1 * p^(multiplicity p a1)"
      by (metis dvd_div_mult_self multiplicity_dvd)
    obtain b2::int where b2_def: "a2 = b2 * p^(multiplicity p a2)"
      by (metis dvd_div_mult_self multiplicity_dvd)
    obtain b3::int where b3_def: "a3 = b3 * p^(multiplicity p a3)"
      by (metis dvd_div_mult_self multiplicity_dvd)
    have b1_pos: "b1\<ge>0" using b1_def a1_pos
      by (smt (verit) p_prime prime_gt_0_int zero_le_mult_iff zero_less_power)
    have b2_pos: "b2\<ge>0" using b2_def a2_pos
      by (smt (verit) p_prime prime_gt_0_int zero_le_mult_iff zero_less_power)
    have b3_pos: "b3\<ge>0" using b3_def a3_pos
      by (smt (verit) p_prime prime_gt_0_int zero_le_mult_iff zero_less_power)
    define B::"nat\<Rightarrow>int" where "B = (\<lambda>_. 0)(1:=b1, 2:=b2, 3:=b3)"
    hence B_prop: "j\<in>{1,2,3} \<Longrightarrow> A j = B j * p^(multiplicity p (A j))" for j
      unfolding A_def B_def f_def using b1_def b2_def b3_def by fastforce
    have B_pos: "j\<in>{1,2,3} \<Longrightarrow> B j \<ge> 0" for j using B_def b1_pos b2_pos b3_pos by fastforce
    have pnB0:"p^n>0" for n by (simp add: p_prime prime_gt_0_int)
    hence "even n \<Longrightarrow> sqrt(p^n) = p^(n divd 2)" for n
      by (simp add: p_prime prime_ge_0_int real_sqrt_power real_sqrt_power_even)
    hence "\<forall>j\<in>Se. sqrt(p^(multiplicity p (A j))) = p^((multiplicity p (A j)) divd 2)"
      using Se_def by blast
    hence sqrtAj: "\<forall>j\<in>Se. sqrt (A j) = sqrt(B j) * p^(multiplicity p (A j) divd 2)"
      using B_prop real_sqrt_mult by (metis (no_types, lifting) Se_def mem_Collect_eq of_int_mult)
    have sqrtBj_field: "\<forall>j\<in>{1,2,3}. sqrt(B j) \<in> field([B 1, B 2, B 3])"
      using cpx_sqrt_def sqrt_in_field B_pos
      by (metis insert_iff list.simps(15) singletonD)
    hence "\<forall>j\<in>Se. sqrt(A j) \<in> field [B 1, B 2, B 3]"
      using int_in_field field_add_mult sqrtAj
      by (metis UnCI disj_Se_So of_real_mult of_real_of_int_eq)
    hence Se_field: "\<forall>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)) \<in> field [B 1, B 2, B 3]"
      using int_in_field field_add_mult by (metis of_real_mult of_real_of_int_eq)

    have "odd n \<Longrightarrow> sqrt(p^n) = sqrt p * p^(n divd 2)" for n
      using pnB0 by (smt (z3) Suc_eq_plus1 odd_two_times_div_two_succ of_int_nonneg of_int_power
          p_prime power.simps(2) power_mult prime_ge_0_int real_sqrt_abs real_sqrt_power)
    hence "j\<in>So \<Longrightarrow> sqrt(p^(multiplicity p (A j))) = sqrt p * p^((multiplicity p (A j)) divd 2)" for j
      using So_def by blast
    hence "j\<in>So \<Longrightarrow> sqrt (A j) = sqrt(B j) * sqrt p * p^(multiplicity p (A j) divd 2)" for j
      using B_prop real_sqrt_mult
      by (metis (no_types, lifting) UnCI disj_Se_So mult.assoc of_int_mult)
    hence "j\<in>So \<Longrightarrow> sqrt (A j/p) = sqrt(B j) * p^(multiplicity p (A j) divd 2)" for j
      using real_sqrt_mult p_prime real_sqrt_divide by force
    hence So_field: "j\<in>So \<Longrightarrow> sqrt(A j/p) \<in> field [B 1, B 2, B 3]" for j
      using int_in_field field_add_mult sqrtBj_field
      by (metis (no_types, lifting) So_def mem_Collect_eq of_real_mult of_real_of_int_eq)
    hence So_field: "\<forall>j\<in>So. fun3 \<epsilon> j * sqrt(A j/p) * of_int (X3^(j-1)) \<in> field [B 1, B 2, B 3]"
      using int_in_field field_add_mult by (metis of_real_mult of_real_of_int_eq)

    define sum_Se where "sum_Se = of_int y + (\<Sum>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))"
    define sum_So where "sum_So = (\<Sum>j\<in>So. fun3 \<epsilon> j * sqrt(A j/p) * of_int (X3^(j-1)))"
    have fact_0bis: "sum_Se + sqrt p * sum_So = 0"
      unfolding sum_Se_def sum_So_def using fact_0_sum_real by presburger
    have "(\<Sum>j\<in>Se. complex_of_real(fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))) \<in> field [B 1, B 2, B 3]"
      using Se_field field_sum
      by (metis (no_types, lifting) disj_Se_So finite.emptyI finite.insertI finite_Un)
    hence "(\<Sum>j\<in>Se. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1))) \<in> field [B 1, B 2, B 3]"
      using of_real_add by force
    hence sum_Se_field: "sum_Se \<in> field [B 1, B 2, B 3]"
      unfolding sum_Se_def using int_in_field field_add_mult
      by (metis (no_types, lifting) of_real_add of_real_of_int_eq)
    have "(\<Sum>j\<in>So. complex_of_real(fun3 \<epsilon> j * sqrt(A j/p) * of_int (X3^(j-1)))) \<in> field [B 1, B 2, B 3]"
      using So_field field_sum
      by (metis (no_types, lifting) disj_Se_So finite.emptyI finite.insertI finite_Un)
    hence sum_So_field: "sum_So \<in> field [B 1, B 2, B 3]"
      unfolding sum_So_def using of_real_add by force

    obtain B_no_0 where B_no_0_prop: "set B_no_0 = set [B 1, B 2, B 3] - {0} \<and> field B_no_0 = field [B 1, B 2, B 3]"
      using field_remove_zeros by blast

    have "sum_So \<noteq> 0 \<Longrightarrow> False"
    proof -
      assume "sum_So \<noteq> 0"
      hence "sqrt p = -sum_Se / sum_So"
        using fact_0bis by (smt (verit, best) nonzero_divide_eq_eq)
      hence sqrtp_in: "sqrt p \<in> field [B 1, B 2, B 3]" using sum_So_field sum_Se_field
        by (metis field_inv_div field_opp of_real_divide of_real_minus)

      have "\<forall>j\<in>{1,2,3}. multiplicity p (A j) = multiplicity p (B j) + multiplicity p (A j)"
        using B_prop
        by (metis add_cancel_left_left multiplicity_prime_power multiplicity_zero not_prime_0 p_prime power_not_zero prime_elem_multiplicity_mult_distrib prime_imp_prime_elem)
      hence "\<forall>j\<in>{1,2,3}. multiplicity p (B j) = 0" by simp
      hence "\<forall>j\<in>{1,2,3}. B j \<noteq> 0 \<longrightarrow> \<not>p dvd (B j)" using prime_elem_multiplicity_eq_zero_iff
        using p_prime by blast
      hence "\<forall>b\<in>set B_no_0.  \<not>p dvd b" using B_no_0_prop by force
      hence "cpx_sqrt p \<notin> field B_no_0" using root_p_not_in_field_extension p_prime by simp
      hence "sqrt p \<notin> field [B 1, B 2, B 3]" using B_no_0_prop unfolding cpx_sqrt_def
        by (metis p_prime prime_ge_0_int)
      thus "False" using sqrtp_in by blast
    qed
    hence "sum_So = 0" by blast
    hence "sqrt p * sum_So = 0" by simp
    hence "(\<Sum>j\<in>So. sqrt p * fun3 \<epsilon> j * sqrt(A j/p) * of_int (X3^(j-1))) = 0"
      unfolding sum_So_def by (smt (verit) Re_complex_of_real eq_sum_random2)
    hence sum_So_0: "(\<Sum>j\<in>So. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1))) = 0"
      by (smt (verit, best) Re_complex_of_real eq_sum_random1)

    have "{k+1..3} \<subseteq> Se" using Ak_bigger_not_sq square_even_multiplicity[of p] p_prime
      unfolding Se_def by fastforce
    hence "\<forall>j\<in>So. j\<in>{1,2,3} \<and> j\<notin>{k+1..3}" using disj_Se_So by blast
    hence So_Le_k: "So \<subseteq> {1..k}" by fastforce
    hence So_L_k: "So-{k} \<subseteq> {1..k-1}" by fastforce
    hence So_k_un_disj: "(So-{k}) \<union> ({1..k-1}-(So-{k})) = {1..k-1} \<and> (So-{k}) \<inter> ({1..k-1}-(So-{k})) = {}"
      by blast
    have fin_So_k: "finite (So-{k}) \<and> finite ({1..k-1}-(So-{k}))" using So_L_k
      by (meson finite_Diff finite_atLeastAtMost finite_subset)
      
      

    have fin_So: "finite So" unfolding So_def by simp
    have So_123: "So\<subseteq>{1,2,3}" using So_def by fast
    hence So_k_123: "So-{k}\<subseteq>{1,2,3}" by blast
    have tok_123: "{1..k-1}\<subseteq>{1,2,3}" using k123 by force
    have k_in_So:  "k\<in>So" unfolding So_def using k123 p_mult by blast
    hence "(\<Sum>j\<in>So. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))
        = (\<Sum>j\<in>So-{k}. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))
          + fun3 \<epsilon> k * sqrt(A k) * of_int (X3^(k-1))"
      using fin_So by (simp add: sum.remove)
    hence "fun3 \<epsilon> k * sqrt(A k) * of_int (X3^(k-1))
        = - (\<Sum>j\<in>So-{k}. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))"
      using sum_So_0 by simp
    hence "abs (fun3 \<epsilon> k * sqrt(A k) * of_int (X3^(k-1)))
      = abs (\<Sum>j\<in>So-{k}. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))"
      by simp
    hence eq0_abs: "abs (of_int (fun3 \<epsilon> k)) * abs (sqrt(A k) * of_int (X3^(k-1)))
      = abs (\<Sum>j\<in>So-{k}. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))"
      using abs_mult[of "of_int (fun3 \<epsilon> k)" "sqrt(A k) * of_int (X3^(k-1))"] by argo
    have fun3_eps_1: "\<forall>j\<in>{1,2,3}. fun3 \<epsilon> j\<in>{-1, 1}" using \<epsilon>_prop k123 by fastforce
    hence fun3_epsk_1: "fun3 \<epsilon> k\<in>{-1, 1}" using k123 by blast
    have abs_fun3: "\<forall>j\<in>So-{k}. abs(fun3 \<epsilon> j) = 1" using So_k_123 fun3_eps_1 by force
    have abs_sqrt_X3: "\<forall>j\<in>{1,2,3}. abs (sqrt(A j) * of_int (X3^(j-1))) = sqrt(A j) * X3^(j-1)"
      using abs_mult A_pos X3_pos by simp
    hence random_eq: "abs (sqrt(A k) * of_int (X3^(k-1))) = sqrt(A k) * X3^(k-1)" using k123 by blast
    hence "sqrt(A k) * of_int (X3^(k-1))
      = abs (\<Sum>j\<in>So-{k}. fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1)))"
      using eq0_abs fun3_epsk_1 by force
    also have "... \<le> (\<Sum>j\<in>So-{k}. abs (fun3 \<epsilon> j * sqrt(A j) * of_int (X3^(j-1))))"
      by blast
    also have "... = (\<Sum>j\<in>So-{k}. abs (fun3 \<epsilon> j) * abs(sqrt(A j) * of_int (X3^(j-1))))"
      using abs_mult by (metis (no_types, opaque_lifting) mult.commute mult.left_commute of_int_abs)
    also have "... = (\<Sum>j\<in>So-{k}. abs (sqrt(A j) * of_int (X3^(j-1))))"
      using abs_fun3 by force
    also have "... \<le> (\<Sum>j\<in>So-{k}. abs (sqrt(A j) * of_int (X3^(j-1))))
             + (\<Sum>j\<in>{1..k-1}-(So-{k}). abs (sqrt(A j) * of_int (X3^(j-1))))"
      by force
    also have "... = (\<Sum>j\<in>{1..k-1}. abs (sqrt(A j) * of_int (X3^(j-1))))"
      using So_k_un_disj fin_So_k sum.union_disjoint by (smt (verit, best))
    also have "... = (\<Sum>j\<in>{1..k-1}. sqrt(A j) * of_int (X3^(j-1)))"
      using abs_sqrt_X3 tok_123 by (meson subsetD sum.cong)
    also have "... \<le> (\<Sum>j\<in>{1..k-1}. sqrt(A j) * of_int (X3^(k-2)))"
    proof -
      have "\<forall>j\<in>{0..k-2}. X3^j \<le> X3^(k-2)" using X3_pos
        by (meson atLeastAtMost_iff power_increasing)
      hence "\<forall>j\<in>{1..k-1}. X3^(j-1) \<le> X3^(k-2)" by fastforce
      hence "\<forall>j\<in>{1..k-1}. sqrt (A j) * X3^(j-1) \<le> sqrt(A j) *X3^(k-2)" using A_pos tok_123
        by (meson mult_left_mono of_int_le_iff of_int_nonneg real_sqrt_ge_zero subsetD)
      thus ?thesis by (meson sum_mono)
    qed
    also have "... = (\<Sum>j\<in>{1..k-1}. sqrt(A j)) * X3^(k-2)" using sum_distrib_right by metis
    finally have ineq1: "sqrt (real_of_int (A k)) * real_of_int (X3 ^ (k - 1))
        \<le> (\<Sum>j = 1..k - 1. sqrt (real_of_int (A j))) * real_of_int (X3 ^ (k - 2))"
      by simp
    have "sqrt (A k) * of_int(X3) \<le> (\<Sum>j = 1..k - 1. sqrt (real_of_int (A j)))"
    proof (cases "k=1")
      case True
      then show ?thesis using ineq1 random_eq by simp
    next
      case False
      hence k_23: "k\<in>{2,3}" using k123 by blast
      hence "1+(k-2) = k-1" by force
      hence "X3 ^ (k - 1) = X3 * X3 ^ (k - 2)"
        by (metis power_add power_one_right)
      hence "real_of_int (X3 ^ (k - 1)) = X3 * real_of_int (X3 ^ (k - 2))" by simp
      hence "sqrt (A k) * of_int(X3) * of_int (X3 ^ (k - 2))
      \<le> (\<Sum>j = 1..k - 1. sqrt (real_of_int (A j))) * of_int (X3 ^ (k - 2))" using ineq1 by simp
      then show ?thesis using X3_pos by simp
    qed
    also have "... \<le> (\<Sum>j = 1..k - 1. abs (sqrt (A j)))"
      by (simp add: sum_mono)
    also have "... \<le> (\<Sum>j = 1..k - 1. abs (sqrt (A j))) +(\<Sum>j = k..3. abs (sqrt (A j)))" by force
    also have "... \<le> (\<Sum>j\<in>{1,2,3}. abs (sqrt (A j)))"
    proof -
      have "{1..k-1}\<union>{k..3} = {1,2,3} \<and> {1..k-1}\<inter>{k..3} = {}" using k123 by fastforce
      thus ?thesis by (smt (verit, best) finite_atLeastAtMost sum.union_disjoint)
    qed
    also have "... \<le> (\<Sum>j\<in>{1,2,3}. A j)"
      by (smt (verit, best) A_pos of_int_nonneg of_int_sum real_sqrt_ge_0_iff sqrt_int_smaller sum_mono)
    also have "... \<le> (\<Sum>j\<in>{1,2,3}. A j^2)" using A_pos
    proof -
      have "(m::int)\<ge>0 \<Longrightarrow> m\<le>m^2" for m
        by (meson of_int_power_le_of_int_cancel_iff sqrt_int_smaller sqrt_le_D)
      thus ?thesis using A_pos by (meson of_int_le_iff sum_mono)
    qed
    also have "... < 1 + (A 1)^2 + (A 2)^2 + (A 3)^2" by simp
    also have "... \<le> X3" using X3_def A_def by blast
    finally have "sqrt (A k) < 1" using X3_pos by simp
    hence "A k = 0" using A_pos k123 by force 
    thus False using Ak_bigger_not_sq using is_square_def by force
  qed
  thus ?thesis using dir_imp by blast
qed

end 

end
