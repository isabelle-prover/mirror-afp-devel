(* Author: Alexander Maletzky *)

section \<open>Utilities\<close>

theory Utils
  imports Main
begin

subsection \<open>Lists\<close>

lemma map_upt: "map (\<lambda>i. f (xs ! i)) [0..<length xs] = map f xs"
  by (simp add: nth_equalityI)

lemma map_upt_zip:
  assumes "length xs = length ys"
  shows "map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys] = map (\<lambda>(x, y). f x y) (zip xs ys)" (is "?l = ?r")
proof -
  have len_l: "length ?l = length ys" by simp
  from assms have len_r: "length ?r = length ys" by simp
  show ?thesis
  proof (simp only: list_eq_iff_nth_eq len_l len_r, rule, rule, intro allI impI)
    fix i
    assume "i < length ys"
    hence "i < length ?l" and "i < length ?r" by (simp_all only: len_l len_r)
    thus "map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys] ! i = map (\<lambda>(x, y). f x y) (zip xs ys) ! i"
      by simp
  qed
qed

subsection \<open>Sums and Products\<close>

lemma additive_implies_homogenous:
  assumes "\<And>x y. f (x + y) = f x + ((f (y::'a::monoid_add))::'b::cancel_comm_monoid_add)"
  shows "f 0 = 0"
proof -
  have "f (0 + 0) = f 0 + f 0" by (rule assms)
  hence "f 0 = f 0 + f 0" by simp
  thus "f 0 = 0" by simp
qed

lemma fun_sum_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
  shows "f (sum g A) = (\<Sum>a\<in>A. f (g a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    thus ?case by (simp add: assms(1))
  next
    case step: (insert a A)
    show ?case by (simp add: sum.insert[OF step(1) step(2)] assms(2) step(3))
  qed
next
  case False
  thus ?thesis by (simp add: assms(1))
qed

lemma fun_sum_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + ((f y)::'a::cancel_comm_monoid_add)"
  shows "f (sum g A) = (\<Sum>a\<in>A. f (g a))"
  by (rule fun_sum_commute, rule additive_implies_homogenous, fact+)

lemma fun_sum_list_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
  shows "f (sum_list xs) = sum_list (map f xs)"
proof (induct xs)
  case Nil
  thus ?case by (simp add: assms(1))
next
  case (Cons x xs)
  thus ?case by (simp add: assms(2))
qed

lemma fun_sum_list_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + ((f y)::'a::cancel_comm_monoid_add)"
  shows "f (sum_list xs) = sum_list (map f xs)"
  by (rule fun_sum_list_commute, rule additive_implies_homogenous, fact+)

lemma sum_set_upt_eq_sum_list: "(\<Sum>i = m..<n. f i) = (\<Sum>i\<leftarrow>[m..<n]. f i)"
  using sum_set_upt_conv_sum_list_nat by auto

lemma sum_list_upt: "(\<Sum>i\<leftarrow>[0..<(length xs)]. f (xs ! i)) = (\<Sum>x\<leftarrow>xs. f x)"
  by (simp only: map_upt)

lemma sum_list_upt_zip:
  assumes "length xs = length ys"
  shows "(\<Sum>i\<leftarrow>[0..<(length ys)]. f (xs ! i) (ys ! i)) = (\<Sum>(x, y)\<leftarrow>(zip xs ys). f x y)"
  by (simp only: map_upt_zip[OF assms])

lemma sum_list_zeroI:
  assumes "set xs \<subseteq> {0}"
  shows "sum_list xs = 0"
  using assms by (induct xs, auto)

lemma fun_prod_commute:
  assumes "f 1 = 1" and "\<And>x y. f (x * y) = f x * f y"
  shows "f (prod g A) = (\<Prod>a\<in>A. f (g a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    thus ?case by (simp add: assms(1))
  next
    case step: (insert a A)
    show ?case by (simp add: prod.insert[OF step(1) step(2)] assms(2) step(3))
  qed
next
  case False
  thus ?thesis by (simp add: assms(1))
qed

end (* theory *)
