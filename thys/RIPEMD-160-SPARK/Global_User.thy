section "Arrays in SPARK vs Lists in Isabelle"
theory Global_User
imports Main
begin

subsection "Functions vs Lists"

text{* Arrays defined in SPARK are represented as functions in
Isabelle. In the specification, it is more convenient to use
lists. Therefore it is a common task to prove equivalences like
$\forall i \leq \mathsf{length}\ l.\ l\ !\ i = f\ i$, where $l$ is the
list specified in Isabelle and $f$ the function corresponding to the
array defined in SPARK. *}

text{* Constructing a function from a list makes things easier for the
simplifier, otherwise the definition of the list would need to be
unfolded $(\mathsf{length}\ l)$ times what yields to
efficiency-problems.*}

primrec list_to_fun where
  "list_to_fun [] _ (f::int \<Rightarrow> int) = f"
| "list_to_fun (a # xs) i f = (list_to_fun xs (i + 1) f) (i := (int a))"

lemma nth_list_to_fun_eq_aux:
  assumes "i_0 <= i" and "i < length l + i_0"
  shows "int (l ! (i - i_0)) = (list_to_fun l (int i_0) f) (int i)"
  using assms
proof (induct l arbitrary: i i_0)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  moreover have aux: "1 + int i_0 = int i_0 + 1" by simp
  ultimately show ?case by (simp add: nth_Cons' aux)
qed

lemma nth_list_to_fun_eq:
  assumes "0 <= i" and "i < length l"
  shows "int (l ! i) = (list_to_fun l 0 f) (int i)"
proof -
  have "int (l ! (i - 0)) =
    (list_to_fun l (int 0) f) (int i)"
    by (rule nth_list_to_fun_eq_aux) (simp_all add: assms)
  thus ?thesis by simp
qed

text {* A tail-recursive definition makes it even more efficient. *}

primrec list_to_fun_eff where
  "list_to_fun_eff [] _ (f::int \<Rightarrow> int) = f"
| "list_to_fun_eff (a # xs) i f = list_to_fun_eff xs (i + 1) (f(i := (int a)))"

lemma list_to_fun_id:
  assumes "i_0 > i"
  shows "list_to_fun_eff l (int i_0) f (int i) = f (int i)"
using assms
proof (induct l arbitrary: i_0 f)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  have I: "int i_0 + 1 = int (i_0 + 1)" by simp
  from Cons(2) have L: "i < i_0 + 1" by simp
  with Cons have
    "list_to_fun_eff xs (int i_0 + 1) (f(int i_0 := int a)) (int i) = f (int i)"
    unfolding I Cons(1)[OF L] by simp
  thus ?case by simp
qed

lemma nth_list_to_fun_eff_eq_aux:
  assumes "i_0 <= i" and "i < length l + i_0"
  shows "int (l ! (i - i_0)) = (list_to_fun_eff l (int i_0) f) (int i)"
  using assms
proof (induct l arbitrary: i f i_0)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  have I: "int i_0 + 1 = int (i_0 + 1)" by simp
  {
    assume "i = i_0"
    moreover
    have "i_0 + 1 > i_0" by simp
    have
      "int a = list_to_fun_eff xs (int i_0 + 1) (f(int i_0 := int a)) (int i_0)"
      unfolding I list_to_fun_id[OF `i_0 + 1 > i_0`] by simp
    ultimately have ?case by (simp add: nth_Cons')
  }
  moreover
  {
    assume "i \<noteq> i_0"
    moreover
    hence H: "i_0 + 1 <= i" using Cons by simp
    have H': "i < length xs + (i_0 + 1)" using Cons (3) by simp
    have "int (xs ! (i - Suc i_0)) =
      list_to_fun_eff xs (int i_0 + 1) (f(int i_0 := int a)) (int i)"
      unfolding I Cons(1)[OF H H', symmetric] by simp
    ultimately have ?case using Cons(2) by (simp add: nth_Cons')
  }
  ultimately show ?case by blast
qed

lemma nth_list_to_fun_eff_eq:
  assumes "0 <= i" and "i < length l"
  shows "int (l ! i) = (list_to_fun_eff l 0 f) (int i)"
proof -
  have "int (l ! (i - 0)) =
    (list_to_fun_eff l (int 0) f) (int i)"
    by (rule nth_list_to_fun_eff_eq_aux) (simp_all add: assms)
  thus ?thesis by simp
qed


subsection{* Maximum Element of Lists *}

text{* The following lemmas help the simplifier to prove properties
about maximal elements of a list. It is easier to calculate the
maximum element of a list in an efficient way (using fold) and prove
the correctness of this calculation. *}

lemma fold_max_leq:
  fixes i j :: nat
  assumes "i <= j"
  shows "foldl max i l <= foldl max j l"
using assms
by (induct l arbitrary: i j) simp_all

lemma fold_max_lower:
  fixes i :: nat
  shows "i <= foldl max i l"
proof (induct l arbitrary: i)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "i <= x")
    case True
    moreover have "x <= foldl max x xs" using Cons .
    ultimately show ?thesis by simp
  next
    case False
    thus ?thesis using Cons by (simp add: max_def)
  qed
qed

lemma list_max:
  fixes l::"nat list"
  fixes i::"nat"
  assumes "0 <= l ! i"
  assumes "0 <= i"
  assumes "i < length l"
  shows "l ! i <= foldl max 0 l"
  using assms
proof (induct l arbitrary: i)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case (Suc j)
    note Cons(1)
    moreover have "0 <= xs ! (i - 1)" using Suc Cons by simp
    moreover have "0 <= i - 1" using Cons by simp
    moreover have "i - 1 < length xs" using Suc Cons by simp
    ultimately
    have "xs ! (i - 1) <= foldl max 0 xs" .
    moreover have "(x#xs) ! i = xs ! (i - 1)"
      using Suc Cons by simp
    moreover have "foldl max 0 xs <= foldl max (max 0 x) xs"
      by (rule fold_max_leq) simp
    ultimately
    show ?thesis by simp
  next
    case 0
    moreover have H: "(max 0 x) \<le> foldl max (max 0 x) xs" using fold_max_lower
      by simp
    ultimately show ?thesis
      by (cases "0 <= x") simp_all
  qed
qed

lemma list_max_int:
  assumes "l ! nat j \<le> foldl max 0 l"
  assumes "foldl max 0 l = nat U"
  assumes "0 <= j"
  assumes "0 <= U"
  shows "int (l ! nat j) \<le> U"
  using assms by simp


end
