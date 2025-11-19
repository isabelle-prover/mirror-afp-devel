theory Notation
  imports Polynomials.More_MPoly_Type Complex_Main "HOL-Library.Rewrite"
begin

section \<open>Multivariate Polynomials\<close>

subsection \<open>Elementary properties\<close>

subsubsection \<open>Notation\<close>

notation smult (infixl "*\<^sub>s" 70)

definition max_coeff :: "'a::{zero,abs,linorder} mpoly \<Rightarrow> 'a" where
  "max_coeff P \<equiv> Max (abs ` MPoly_Type.coeffs P)"

lemma coeffs_empty_iff: "coeffs P = {} \<longleftrightarrow> P = 0"
proof 
  assume "coeffs P = {}" thus "P = 0"
    unfolding coeffs_def 
    by simp (metis emptyE equals0I in_keys_lookup_in_range keys_eq_empty mapping_of_inject 
             zero_mpoly.rep_eq)
next
  assume "P = 0" thus "coeffs P = {}"
    by (simp add: coeffs.abs_eq zero_mpoly.abs_eq)
qed

lemma coeff_minus: "coeff p m - coeff q m = coeff (p-q) m"
  by (simp add: coeff_def lookup_minus minus_mpoly.rep_eq)

definition nth0 :: "'a::zero list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!\<^sub>0" 100) where
  "xs !\<^sub>0 i = (xs ! i when i < length xs)"

lemma nth0_nth : "i < length xs \<Longrightarrow> xs !\<^sub>0 i = xs ! i"
  unfolding nth0_def by auto

lemma nth0_0: "i \<ge> length xs \<Longrightarrow> xs !\<^sub>0 i = 0"
  unfolding nth0_def by auto

lemma nth0_Cons: "(x # xs') !\<^sub>0 i = (case i of 0 \<Rightarrow> x | Suc i' \<Rightarrow> xs' !\<^sub>0 i')"
  unfolding nth0_def nth_Cons by (cases i; auto)

lemma nth0_Cons_0 [simp, code]: "(x # xs) !\<^sub>0 0 = x"
  unfolding nth0_def by auto

lemma nth0_Cons_Suc [simp, code]: "(x # xs) !\<^sub>0 (Suc n) = xs !\<^sub>0 n"
  unfolding nth0_def by auto

lemma nth0_finite[simp]: "finite {i. xs !\<^sub>0 i \<noteq> 0}"
  unfolding nth0_def by auto

lemma nth0_inj: "length xs = length ys \<Longrightarrow> (!\<^sub>0) xs = (!\<^sub>0) ys \<Longrightarrow> xs = ys"
proof -
  have aux:
    "length xs = n \<Longrightarrow> length ys = n \<Longrightarrow> (!\<^sub>0) xs = (!\<^sub>0) ys \<Longrightarrow> xs = ys" for n
  proof (induction n arbitrary: xs ys)
    case 0
    thus ?case by auto
  next
    case (Suc n)
    from Suc obtain x xs' where xs_def: "xs = x # xs'" by (metis Suc_length_conv)
    from Suc obtain y ys' where ys_def: "ys = y # ys'" by (metis Suc_length_conv)
    have 0: "x = y" using Suc unfolding xs_def ys_def nth0_Cons
      by (metis nat.case(1))
    have 1: "length xs' = n" "length ys' = n" using xs_def ys_def Suc by auto
    have 2: "(!\<^sub>0) xs' = (!\<^sub>0) ys'" using Suc
      unfolding xs_def ys_def nth0_Cons
      by (simp; metis nth0_nth nth_equalityI nat.case(2))
    from 1 2 have 3: "xs' = ys'" using Suc by auto
    from 0 3 show ?case unfolding xs_def ys_def by auto
  qed
  assume "length xs = length ys" "(!\<^sub>0) xs = (!\<^sub>0) ys"
  thus ?thesis using aux by auto
qed

lemma nth0_sum_list: "sum_list i = (\<Sum>v | i !\<^sub>0 v \<noteq> 0. i !\<^sub>0 v)"
proof (induction i)
  case Nil
  thus ?case unfolding nth0_def by auto
next
  case (Cons a i)
  have 0: "(\<Sum>v | i !\<^sub>0 v \<noteq> 0. i !\<^sub>0 v) =
    (\<Sum>v\<in>Suc ` {v. i !\<^sub>0 v \<noteq> 0}. i !\<^sub>0 (v - 1))"
    by (metis (no_types, lifting) add_diff_cancel_left' inj_Suc plus_1_eq_Suc
      sum.reindex_cong)
  show ?case proof cases
    assume 1: "a = 0"
    have 2: "{v. v \<noteq> 0 \<and> (v \<noteq> 0 \<longrightarrow> i !\<^sub>0 (v - 1) \<noteq> 0)} \<inter> - {0} =
      Suc ` {v. i !\<^sub>0 v \<noteq> 0}" unfolding image_def by auto
    show ?case using nth0_finite[of "a # i"] Cons 0 1 2
      unfolding nth0_Cons Nitpick.case_nat_unfold by (simp add: sum.If_cases)
  next
    assume 3: "a \<noteq> 0"
    have 4: "{v. v \<noteq> 0 \<longrightarrow> i !\<^sub>0 (v - 1) \<noteq> 0} \<inter> - {0} =
      Suc ` {v. i !\<^sub>0 v \<noteq> 0}" unfolding image_def by auto
    show ?case using nth0_finite[of "a # i"] Cons 0 3 4
      unfolding nth0_Cons Nitpick.case_nat_unfold by (simp add: sum.If_cases)
  qed
qed

lemma lookup_Abs_poly_mapping_nth0[simp]:
  "lookup (Abs_poly_mapping ((!\<^sub>0) xs)) = (!\<^sub>0) xs"
  by auto

lemma Abs_poly_mapping_nth0_single[simp]:
  "Abs_poly_mapping ((!\<^sub>0) [x]) = Poly_Mapping.single 0 x"
  unfolding Poly_Mapping.single_def nth0_def
  by (simp; metis (mono_tags, opaque_lifting) nth_Cons_0 when_simps(2))

lemma Abs_poly_mapping_nth0_append_single[simp]:
  "Abs_poly_mapping ((!\<^sub>0) (xs @ [x])) =
    Abs_poly_mapping ((!\<^sub>0) xs) + Poly_Mapping.single (length xs) x"
  unfolding Poly_Mapping.single_def plus_poly_mapping_def
    nth0_def nth_append when_def
  by (simp; rule cong[of Abs_poly_mapping, OF refl]; rule; simp)

lemma Sum_any_rev_image:
  assumes "finite {x. f x \<noteq> 0}"
  shows "Sum_any (\<lambda>m. Sum_any (\<lambda>x. f x when g x = m)) = Sum_any f"
proof -
  have 0: "(\<Sum>x | (f x when g x = m) \<noteq> 0. f x when g x = m) =
    (\<Sum>x | f x \<noteq> 0. f x when g x = m)" for m
    apply (rule sum.mono_neutral_left)
    using assms apply auto
    done

  have 1: "(\<Sum>x | f x \<noteq> 0. f x when g x = m) \<noteq> 0 \<Longrightarrow> (\<exists>x\<in>{x. f x \<noteq> 0}. g x = m)" for m
    by (meson sum.neutral when_neq_zero)

  have "Sum_any (\<lambda>m. Sum_any (\<lambda>x. f x when g x = m)) =
    (\<Sum>m | (\<Sum>x | f x \<noteq> 0. f x when g x = m) \<noteq> 0. \<Sum>x | f x \<noteq> 0. f x when g x = m)"
    unfolding Sum_any.expand_set 0 ..
  also have "... = (\<Sum>m\<in>g ` {x. f x \<noteq> 0}. \<Sum>x | f x \<noteq> 0. f x when g x = m)"
    apply (rule sum.mono_neutral_left)
    subgoal using assms by simp
    subgoal using 1 by blast
    subgoal by auto
    done
  also have "... = (\<Sum>m\<in>g ` {x. f x \<noteq> 0}. sum f {x \<in> {x. f x \<noteq> 0}. g x = m})"
    apply (rule arg_cong2[of _ _ _ _ sum, OF _ refl])
    apply (rule HOL.ext)
    apply (rule sum.mono_neutral_cong)
    subgoal using assms by simp
    subgoal using assms by simp
    subgoal by simp
    subgoal by auto
    subgoal by simp
    done
  also have "... = sum f {x. f x \<noteq> 0}"
    using sum.image_gen[OF assms, of f, symmetric] .
  also have "... = Sum_any f"
    unfolding Sum_any.expand_set ..
  finally show ?thesis .
qed

lemma Sum_any_rev_image_add:
  assumes "finite {(m\<^sub>1, m\<^sub>2). f m\<^sub>1 m\<^sub>2 \<noteq> 0}"
  shows "Sum_any (\<lambda>m. (Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. f m\<^sub>1 m\<^sub>2 when m = m\<^sub>1 + m\<^sub>2)))) 
  = Sum_any (\<lambda>m\<^sub>1. (Sum_any (\<lambda>m\<^sub>2. f m\<^sub>1 m\<^sub>2)))"
proof -
  have "finite (fst ` {(m\<^sub>1, m\<^sub>2). f m\<^sub>1 m\<^sub>2 \<noteq> 0})"
    by (rule finite_imageI[OF assms])
  hence 0: "finite {m\<^sub>1. \<exists>m\<^sub>2. f m\<^sub>1 m\<^sub>2 \<noteq> 0}"
    unfolding image_def by auto
  have "finite (snd ` {(m\<^sub>1, m\<^sub>2). f m\<^sub>1 m\<^sub>2 \<noteq> 0})"
    by (rule finite_imageI[OF assms])
  hence 1: "finite {m\<^sub>2. \<exists>m\<^sub>1. f m\<^sub>1 m\<^sub>2 \<noteq> 0}"
    unfolding image_def by auto

  have "finite ({m\<^sub>1. \<exists>m\<^sub>2. f m\<^sub>1 m\<^sub>2 \<noteq> 0} \<times> {m\<^sub>2. \<exists>m\<^sub>1. f m\<^sub>1 m\<^sub>2 \<noteq> 0})"
    using 0 1 by simp
  hence 3: "finite {(m\<^sub>1, m\<^sub>2). (\<exists>m\<^sub>1. f m\<^sub>1 m\<^sub>2 \<noteq> 0) \<and> (\<exists>m\<^sub>2. f m\<^sub>1 m\<^sub>2 \<noteq> 0)}" (is "finite ?C")
    apply (rule back_subst)
    apply (rule arg_cong[of _ _ finite])
    apply auto
    done

  have "Sum_any (\<lambda>m. (Sum_any (\<lambda>m\<^sub>1. Sum_any (\<lambda>m\<^sub>2. f m\<^sub>1 m\<^sub>2 when m = m\<^sub>1 + m\<^sub>2)))) = 
    Sum_any (\<lambda>m. Sum_any (\<lambda>(m\<^sub>1, m\<^sub>2). f m\<^sub>1 m\<^sub>2 when m = m\<^sub>1 + m\<^sub>2))"
    apply (rule arg_cong[of _ _ Sum_any])
    apply (rule ext)
    apply (rule Sum_any.cartesian_product[of ?C])
    subgoal using 3 .
    subgoal by auto
    done
  also have "... = Sum_any (\<lambda>(m\<^sub>1, m\<^sub>2). f m\<^sub>1 m\<^sub>2)"
    apply (subst Sum_any_rev_image[of "\<lambda>(m\<^sub>1, m\<^sub>2). f m\<^sub>1 m\<^sub>2" "\<lambda>(m\<^sub>1, m\<^sub>2). m\<^sub>1 + m\<^sub>2", symmetric])
    subgoal using assms by (metis (mono_tags, lifting) Collect_cong split_def)
    subgoal
      apply (rule arg_cong[of _ _ Sum_any])
      apply (rule ext)
      apply (rule arg_cong[of _ _ Sum_any])
      apply (rule ext)
      by (smt (verit, best) case_prod_unfold)
    done
  also have "... = Sum_any (\<lambda>m\<^sub>1. (Sum_any (\<lambda>m\<^sub>2. f m\<^sub>1 m\<^sub>2)))"
    apply (rule Sum_any.cartesian_product[of ?C, symmetric])
    subgoal using 3 .
    subgoal by auto
    done
  finally show ?thesis .
qed

lemma of_int_Sum_any:
  fixes f :: "'b \<Rightarrow> int"
  assumes "finite {a. f a \<noteq> 0}"
  shows "(of_int :: int \<Rightarrow> 'a::ring_1) (Sum_any f) = Sum_any (of_int \<circ> f)"
proof -
  have "of_int (sum f {a. f a \<noteq> 0}) = sum ((of_int :: int \<Rightarrow> 'a) \<circ> f) {a. f a \<noteq> 0}"
    by simp
  also have "... = sum ((of_int :: int \<Rightarrow> 'a) \<circ> f) {a. (of_int \<circ> f) a \<noteq> (0 :: 'a)}"
    apply (rule sum.mono_neutral_right)
    subgoal using assms by simp
    subgoal using Collect_mono_iff by fastforce
    subgoal by auto
    done
  finally show ?thesis
    unfolding Sum_any.expand_set
    .
qed

lemma of_int_Prod_any:
  fixes f :: "'b \<Rightarrow> int"
  assumes "finite {a. f a \<noteq> 1}"
  shows "(of_int :: int \<Rightarrow> 'a::comm_ring_1) (Prod_any f) = Prod_any (of_int \<circ> f)"
proof -
  have "of_int (prod f {a. f a \<noteq> 1}) = prod ((of_int :: int \<Rightarrow> 'a) \<circ> f) {a. f a \<noteq> 1}"
    by simp
  also have "... = prod ((of_int :: int \<Rightarrow> 'a) \<circ> f) {a. (of_int \<circ> f) a \<noteq> (1 :: 'a)}"
    apply (rule prod.mono_neutral_right)
    subgoal using assms by simp
    subgoal using Collect_mono_iff by fastforce
    subgoal by auto
    done
  finally show ?thesis
    unfolding Prod_any.expand_set
    .
qed

subsubsection \<open>The constant polynomial\<close>

lemma Const_zero: "Const 0 = 0"
  by (simp add: Const.abs_eq Const\<^sub>0_zero zero_mpoly_def)
lemma Const_one: "Const 1 = 1"
  by (simp add: Const.abs_eq Const\<^sub>0_one one_mpoly.abs_eq)
lemma Const_add: "Const a + Const b = Const (a + b)"
  using  Const\<^sub>0_def monom.abs_eq monom_add by (metis Const.abs_eq)
lemma Const_mult: "Const a * Const b = Const (a * b)"
  using  Const\<^sub>0_def monom.abs_eq mult_monom Const.abs_eq by (metis add_0)
lemma Const_power: "Const c ^ i = Const (c ^ i)"
  by (induct i; auto simp add: Const_mult Const_one)
lemma Const_sub: "Const a - Const b = Const (a - b)"
  by (metis Const.abs_eq Const\<^sub>0_def monom.abs_eq monom_diff)

lemma Const_when: "Const (a when P) = (Const a when P)"
  using Const_zero fun_when by auto

lemma coeff_Const_zero: "MPoly_Type.coeff (Const c) 0 = c"
  unfolding MPoly_Type.coeff_def Const.rep_eq Const\<^sub>0_def lookup_single
  by simp

lemma Const_sum_Any: "Const (Sum_any f) = Sum_any (Const \<circ> f)"
proof -
  have 0: "{a. Const (f a) \<noteq> 0} = {a. f a \<noteq> 0}"
    by (metis Const_zero coeff_Const_zero)
  show ?thesis
    unfolding Sum_any.expand_set comp_def 0
    apply (rule infinite_finite_induct)
    apply (auto simp add: Const_zero Const_add[symmetric])
    done
qed

lemma Const_numeral: "Const (numeral x) = numeral x"
  unfolding Const.abs_eq
  apply (simp add: Const\<^sub>0_numeral)
  by (metis monom.abs_eq monom_numeral single_numeral)

lemma union_subset:
  fixes A :: "'a set"
    and B :: "'b set"
    and f :: "'a \<Rightarrow> 'b set"
  assumes "\<And>x. f x \<subseteq> B"
  shows "\<Union> (f`A) \<subseteq> B"
  using assms by auto

lemma of_nat_Const: "of_nat n = Const (int n)"
proof (induction n)
  case 0 show ?case by (simp add: Const_def Const\<^sub>0_def zero_mpoly_def)
next 
  case (Suc n)
  have "of_nat (Suc n) = 1 + of_nat n" by (simp add: algebra_simps)
  also have "... = 1 + Const (int n)" by (simp add: Suc.IH)
  also have "... = Const 1 + Const (int n)" by (simp add: Const_one)
  also have "... = Const (1 + int n)" by (simp add: Const_add)
  finally show ?case by (simp add: algebra_simps)
qed

lemma of_int_Const: "of_int x = Const x"
  using of_nat_Const Const_sub
  by (metis int_diff_cases of_int_diff of_int_of_nat_eq)

subsubsection \<open>Finite sums and products\<close>

lemma add_to_finite_sum:
  fixes f::"'b::comm_monoid_add\<Rightarrow>'a::comm_monoid_add" and g::"'c\<Rightarrow>'b"
  assumes "\<And>x y. f (x+y) = f x + f y" and "f 0 = 0"
  shows "finite S \<Longrightarrow> (\<Sum>x\<in>S. f (g x)) = f(\<Sum>x\<in>S. g x)"
proof (induction "card S" arbitrary:S)
  case 0
  then show ?case using assms(2) by force
next
  case (Suc n)
  then obtain y where y_prop: "y\<in>S" by fastforce
  define S' where "S' = S - {y}"
  hence card_S':"card S' = n" using Suc by (simp add: y_prop)
  have disj_un_S: "S = S'\<union>{y} \<and> S'\<inter>{y}={}\<and>finite S" using y_prop S'_def Suc by force
  hence "(\<Sum>x\<in>S. f (g x)) = (\<Sum>x\<in>S'. f (g x)) + (\<Sum>x\<in>{y}. f (g x))"
    by (meson finite_Un sum.union_disjoint)
  also have "... = f(\<Sum>x\<in>S'. g x) + f (g y)" using Suc(1)[of "S'"] card_S'
    by (metis S'_def add.commute calculation disj_un_S finite_Un sum.remove y_prop)
  also have "... = f((\<Sum>x\<in>S'. g x) + g y)" using assms by simp
  also have "... = f(\<Sum>x\<in>S. g x)" using disj_un_S
    by (metis S'_def add.commute sum.remove y_prop)
  finally show "(\<Sum>x\<in>S. f (g x)) = f (sum g S)" by blast
qed

lemma mult_to_finite_prod:
  fixes f::"'b::comm_monoid_mult\<Rightarrow>'a::comm_monoid_mult" and g::"'c\<Rightarrow>'b"
  assumes "\<And>x y. f (x*y) = f x * f y" and "f 1 = 1"
  shows "finite S \<Longrightarrow> (\<Prod>x\<in>S. f (g x)) = f(\<Prod>x\<in>S. g x)"
proof (induction "card S" arbitrary:S)
  case 0
  then show ?case using assms(2) by force
next
  case (Suc n)
  then obtain y where y_prop: "y\<in>S" by fastforce
  define S' where "S' = S - {y}"
  hence card_S':"card S' = n" using Suc by (simp add: y_prop)
  have disj_un_S: "S = S'\<union>{y} \<and> S'\<inter>{y}={}\<and>finite S" using y_prop S'_def Suc by force
  hence "(\<Prod>x\<in>S. f (g x)) = (\<Prod>x\<in>S'. f (g x)) * (\<Prod>x\<in>{y}. f (g x))"
    by (meson finite_Un prod.union_disjoint)
  also have "... = f(\<Prod>x\<in>S'. g x) * f (g y)" using Suc(1)[of "S'"] card_S'
    by (metis S'_def calculation disj_un_S finite_Un mult.commute prod.remove y_prop)
  also have "... = f((\<Prod>x\<in>S'. g x) * g y)" using assms by simp
  also have "... = f(\<Prod>x\<in>S. g x)" using disj_un_S
    by (metis S'_def mult.commute prod.remove y_prop)
  finally show "(\<Prod>x\<in>S. f (g x)) = f (prod g S)" by blast
qed

lemma nat_sum_distrib:
  fixes f::"nat\<Rightarrow>int"
  assumes S_fin: "finite S" and nonneg: "\<And>i. i\<in>S \<Longrightarrow> f i \<ge> 0"
  shows "nat (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. nat (f i))"
using assms proof (induct rule:finite_induct[OF S_fin])
  case 1 thus ?case by simp
next
  case (2 x S)
  have "nat (sum f (insert x S)) = nat (sum f S + f x)"
    using 2 by simp
  also have "... = nat (sum f S) + nat (f x)"
    using 2 nat_add_distrib sum_nonneg by blast 
  also have "... = (\<Sum>i\<in>insert x S. nat (f i))"
    using 2 by auto
  finally show ?case .
qed  

subsubsection \<open>Insertion\<close>

named_theorems insertion_simps "Lemmas about insertion"

lemma pow_when: "b \<noteq> 0 \<Longrightarrow> a ^ (b when P) = (if P then a ^ b else 1)"
  by simp

declare insertion_add[simp, insertion_simps]
declare insertion_mult[simp, insertion_simps]

lemma insertion_Var[simp, insertion_simps]: "insertion f (Var n) = f n"
  apply (simp add: insertion_def insertion_aux_def insertion_fun_def Var_def
    MPoly_inverse Var\<^sub>0_def)
  apply (simp add: Poly_Mapping.lookup_single when_mult pow_when)
  done

lemma insertion_Const[simp, insertion_simps]: "insertion f (Const c) = c"
  apply (simp add: insertion_def insertion_aux_def insertion_fun_def Const_def
    MPoly_inverse Const\<^sub>0_def)
  apply (simp add: Poly_Mapping.lookup_single when_mult)
  done

lemma insertion_numeral[simp, insertion_simps]: "insertion f (numeral n) = numeral n"
  by (metis insertion_single monom_numeral mult.right_neutral power_0 single_zero)

lemma Sum_any_neg:
  fixes f :: "_ \<Rightarrow> 'a::ring_1"
  shows "Sum_any (\<lambda>a. - f a) = - Sum_any (\<lambda>a. f a)"
proof cases
  assume "finite {a. f a \<noteq> 0}"
  thus ?thesis
    apply (subst (1 2) mult_minus1[symmetric])
    apply (metis Sum_any_right_distrib)
    done
next
  assume "infinite {a. f a \<noteq> 0}"
  thus ?thesis by auto
qed

lemma insertion_neg[simp, insertion_simps]:
  fixes f :: "_ \<Rightarrow> 'a::comm_ring_1"
  shows "insertion f (- p) = - insertion f p"
  by (metis insertion_add insertion_zero neg_eq_iff_add_eq_0)

lemma insertion_diff[simp, insertion_simps]:
  fixes f :: "_ \<Rightarrow> 'a::comm_ring_1"
  shows "insertion f (p - q) = insertion f p - insertion f q"
  by (metis eq_diff_eq insertion_add)

lemma insertion_of_int[simp, insertion_simps]: 
  fixes f::"nat \<Rightarrow> int" and c::int
  shows "insertion f (of_int c) = c"
  by (simp add: of_int_Const)

lemma insertion_of_nat[simp, insertion_simps]: 
  fixes f::"nat \<Rightarrow> int" and n::nat
  shows "insertion f (of_nat n) = int n"
  by (simp add: of_nat_Const)

lemma insertion_pow[simp, insertion_simps]: "insertion f (P^n) = (insertion f P)^n"
  by (induct n) simp_all
  
lemma insertion_sum[simp, insertion_simps]:
  "finite S \<Longrightarrow> insertion f (\<Sum>i\<in>S. P i) = (\<Sum>i\<in>S. insertion f (P i))"
  using add_to_finite_sum insertion_add insertion_zero
  by (metis (no_types, lifting) sum.cong) 

lemma insertion_prod[simp, insertion_simps]:
  "finite S \<Longrightarrow> insertion f (\<Prod>i\<in>S. P i) = (\<Prod>i\<in>S. insertion f (P i))"
  using mult_to_finite_prod insertion_mult insertion_one 
  by (metis (no_types, lifting) prod.cong)

lemma insertion_monom[simp, insertion_simps]:
  "insertion f (monom m a) = a * (\<Prod>x. f x ^ lookup m x)"
  unfolding insertion.rep_eq insertion_aux.rep_eq insertion_fun_def
  unfolding mapping_of_monom lookup_single
  unfolding when_mult Sum_any_when_equal'
  ..

lemma insertion_of_int_times : "insertion f (of_int n * P) = n * insertion f P"
  by simp


lemma pow_positive:
  fixes a :: "'a::idom"
  assumes "a \<noteq> 0"
  assumes "n > 0"
  shows "a ^ n \<noteq> 0"
  apply (induction rule: nat_induct_non_zero[OF assms(2)])
  unfolding power_Suc2 using assms(1)
  by auto


text \<open>One more typeclasses\<close>

instance mpoly :: (semiring_no_zero_divisors) semiring_no_zero_divisors
  by intro_classes (transfer, simp)


end