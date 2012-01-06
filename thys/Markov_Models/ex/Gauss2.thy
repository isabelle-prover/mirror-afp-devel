(*  Gauss-Jordan elimination for matrices represented as functions
      (extension to completeness)
    Author: Tobias Nipkow
*)
header {* Gauss-Jordan elimination algorithm (completeness) *}
theory Gauss2
  imports "../../Gauss-Jordan-Elim-Fun/Gauss_Jordan_Elim_Fun"
begin

definition solution2 :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where "solution2 A m n x = (\<forall>i<m. (\<Sum> j=0..<m. A i j * x j) = A i n)"

definition "usolution A m n x \<longleftrightarrow>
  solution2 A m n x \<and> (\<forall>y. solution2 A m n y \<longrightarrow> (\<forall>j<m. y j = x j))"

lemma non_null_if_pivot:
  assumes "usolution A m n x" and "q < m" shows "\<exists>p<m. A p q \<noteq> 0"
proof(rule ccontr)
  assume "\<not>(\<exists>p<m. A p q \<noteq> 0)"
  hence 1: "\<And>p. p<m \<Longrightarrow> A p q = 0" by simp
  { fix y assume 2: "\<forall>j. j\<noteq>q \<longrightarrow> y j = x j"
    { fix i assume "i<m"
      with assms(1) have "A i n = (\<Sum>j = 0..<m. A i j * x j)"
        by (auto simp: solution2_def usolution_def)
      with 1[OF `i<m`] 2
      have "(\<Sum>j = 0..<m. A i j * y j) = A i n"
        by (auto intro!: setsum_cong)
    }
    hence "solution2 A m n y" by(simp add: solution2_def)
  }
  hence "solution2 A m n (x(q:=0))" and "solution2 A m n (x(q:=1))" by auto
  with assms(1) zero_neq_one `q < m`
  show False
    by (simp add: usolution_def)
       (metis fun_upd_same zero_neq_one)
qed

lemma lem1:
  fixes f :: "'a \<Rightarrow> 'b::field"
  shows "(\<Sum>x\<in>A. f x * (a * g x)) = a * (\<Sum>x\<in>A. f x * g x)"
  by (simp add: setsum_right_distrib field_simps)

lemma lem2:
  fixes f :: "'a \<Rightarrow> 'b::field"
  shows "(\<Sum>x\<in>A. f x * (g x * a)) = a * (\<Sum>x\<in>A. f x * g x)"
  by (simp add: setsum_right_distrib field_simps)

subsection{* Complete *}

lemma gauss_jordan_complete:
  "m \<le> n \<Longrightarrow> usolution A m n x \<Longrightarrow> \<exists>B. gauss_jordan A m = Some B"
proof(induction m arbitrary: A)
  case 0 show ?case by simp
next
  case (Suc m A)
  from `Suc m \<le> n` have "m\<le>n" and "m<Suc m" by arith+
  from non_null_if_pivot[OF Suc.prems(2) `m<Suc m`]
  obtain p' where "p'<Suc m" and "A p' m \<noteq> 0" by blast
  hence "dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] \<noteq> []"
    by (simp add: dropWhile_eq_Nil_conv)
       (metis atLeast0LessThan lessThan_iff linorder_neqE_nat not_less_eq)
  then obtain p xs where 1: "dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] = p#xs"
    by (metis list.exhaust)
  from this have "p\<le>m" "A p m \<noteq> 0"
    by (simp_all add: dropWhile_eq_Cons_conv del: upt_Suc)
       (metis set_upt atLeast0AtMost atLeastLessThanSuc_atLeastAtMost atMost_iff in_set_conv_decomp)
  then have p: "p < Suc m" "A p m \<noteq> 0"
    by auto
  let ?Ap' = "(\<lambda>j. A p j / A p m)"
  let ?A' = "(\<lambda>i. if i=p then ?Ap' else (\<lambda>j. A i j - A i m * ?Ap' j))"
  let ?A = "Fun.swap p m ?A'"
  have A: "solution2 A (Suc m) n x" using Suc.prems(2) by(simp add: usolution_def)
  { fix i assume le_m: "p < Suc m" "i < Suc m" "A p m \<noteq> 0"
    have "(\<Sum>j = 0..<m. (A i j - A i m * A p j / A p m) * x j) =
      ((\<Sum>j = 0..<Suc m. A i j * x j) - A i m * x m) -
      ((\<Sum>j = 0..<Suc m. A p j * x j) - A p m * x m) * A i m / A p m"
      by (simp add: field_simps setsum_subtractf setsum_divide_distrib
                    setsum_right_distrib)
    also have "\<dots> = A i n - A p n * A i m / A p m"
      using A le_m
      by (simp add: solution2_def field_simps del: setsum_op_ivl_Suc)
    finally have "(\<Sum>j = 0..<m. (A i j - A i m * A p j / A p m) * x j) =
      A i n - A p n * A i m / A p m" . }
  then have "solution2 ?A m n x" using p
    by (auto simp add: solution2_def swap_def field_simps)
  moreover
  { fix y assume a: "solution2 ?A m n y"
    let ?y = "y(m := A p n / A p m - (\<Sum>j = 0..<m. A p j * y j) / A p m)"
    have "solution2 A (Suc m) n ?y" unfolding solution2_def
    proof safe
      fix i assume "i < Suc m"
      show "(\<Sum>j=0..<Suc m. A i j * ?y j) = A i n"
      proof (cases "i = p")
        assume "i = p" with p show ?thesis by (simp add: field_simps)
      next
        assume "i \<noteq> p"
        show ?thesis
        proof (cases "i = m")
          assume "i = m"
          with p `i \<noteq> p` have "p < m" by simp
          with a[unfolded solution2_def, THEN spec, of p] p(2)
          have "A p m * (A m m * A p n + A p m * (\<Sum>j = 0..<m. y j * A m j)) = A p m * (A m n * A p m + A m m * (\<Sum>j = 0..<m. y j * A p j))"
            by (simp add: swap_def field_simps setsum_subtractf lem1 lem2 setsum_divide_distrib[symmetric]
                     split: if_splits)
          with `A p m \<noteq> 0` show ?thesis unfolding `i = m`
            by simp (simp add: field_simps)
        next
          assume "i \<noteq> m"
          then have "i < m" using `i < Suc m` by simp
          with a[unfolded solution2_def, THEN spec, of i] p(2)
          have "A p m * (A i m * A p n + A p m * (\<Sum>j = 0..<m. y j * A i j)) = A p m * (A i n * A p m + A i m * (\<Sum>j = 0..<m. y j * A p j))"
            by (simp add: swap_def field_simps setsum_subtractf lem1 lem2 setsum_divide_distrib[symmetric]
                     split: if_splits)
          with `A p m \<noteq> 0` show ?thesis
            by simp (simp add: field_simps)
        qed
      qed
    qed
    with `usolution A (Suc m) n x`
    have "\<forall>j<Suc m. ?y j = x j" by (simp add: usolution_def)
    hence "\<forall>j<m. y j = x j"
      by simp (metis less_SucI nat_neq_iff)
  } ultimately have "usolution ?A m n x" by(simp add: usolution_def)
  from Suc.IH[OF `m\<le>n` this] 1 show ?case by(simp)
qed

end
