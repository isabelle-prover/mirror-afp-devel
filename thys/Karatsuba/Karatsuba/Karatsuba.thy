section "Karatsuba Multiplication"

theory Karatsuba
imports "../Binary_Representations/Nat_LSBF" "../Binary_Representations/Int_LSBF" "../Estimation_Method"
begin

text "This theory contains an implementation of the Karatsuba Multiplication on type @{type nat_lsbf}."

definition abs_diff :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"abs_diff x y = (x -\<^sub>n y) +\<^sub>n (y -\<^sub>n x)"

lemma abs_diff_correct: "int (to_nat (abs_diff x y)) = abs (int (to_nat x) - int (to_nat y))"
  unfolding abs_diff_def by (simp add: add_nat_correct subtract_nat_correct)

lemma abs_diff_length: "length (abs_diff xs ys) \<le> max (length xs) (length ys)"
proof (cases "compare_nat xs ys")
  case True
  then have "xs -\<^sub>n ys = []" by (simp add: subtract_nat_def)
  then have "abs_diff xs ys = ys -\<^sub>n xs" by (simp add: abs_diff_def add_nat_def)
  then show ?thesis using length_subtract_nat_le[of ys xs] by simp
next
  case False
  then have "ys \<le>\<^sub>n xs" by (simp only: compare_nat_correct)
  then have "ys -\<^sub>n xs = []" by (simp add: subtract_nat_def)
  then have "abs_diff xs ys = xs -\<^sub>n ys" by (simp add: abs_diff_def add_nat_com add_nat_def)
  then show ?thesis using length_subtract_nat_le[of xs ys] by simp
qed

text "For small inputs, implementations of Karatsuba Multiplication usually switch to grid
multiplication. The threshold does not matter for the asymptotic running time, hence we will just
arbitrarily choose @{term \<open>42::nat\<close>}."

definition karatsuba_lower_bound :: nat where
"karatsuba_lower_bound \<equiv> 42"

lemma karatsuba_lower_bound_requirement:
  "karatsuba_lower_bound \<ge> 1"
  unfolding karatsuba_lower_bound_def by simp

text "A first version of the algorithm assumes the input numbers have a length which is a power of 2.
The function @{term karatsuba_on_power_of_2_length} takes the specified length as additional first
argument."

fun karatsuba_on_power_of_2_length :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"karatsuba_on_power_of_2_length k x y =
(if k \<le> karatsuba_lower_bound
then x *\<^sub>n y
else let
    (x0, x1) = split x;
    (y0, y1) = split y;
    k_div_2 = (k div 2);
    prod0 = karatsuba_on_power_of_2_length k_div_2 x0 y0;
    prod1 = karatsuba_on_power_of_2_length k_div_2 x1 y1;
    prod2 = karatsuba_on_power_of_2_length k_div_2
      (fill k_div_2 (abs_diff x0 x1))
      (fill k_div_2 (abs_diff y0 y1));
    add01 = prod0 +\<^sub>n prod1;
    r = (if (x1 \<le>\<^sub>n x0) = (y1 \<le>\<^sub>n y0)
        then add01 -\<^sub>n prod2
        else add01 +\<^sub>n prod2)
  in prod0 +\<^sub>n (r >>\<^sub>n k_div_2) +\<^sub>n (prod1 >>\<^sub>n k))"

declare karatsuba_on_power_of_2_length.simps[simp del]

locale karatsuba_context =
  fixes k l :: nat
  fixes x y :: nat_lsbf
  assumes k_power_of_2: "k = 2 ^ l"
  assumes length_x: "length x = k"
  assumes length_y: "length y = k"
  assumes recursion_condition: "\<not> k \<le> karatsuba_lower_bound"
begin

definition x0 where "x0 = fst (split x)"
definition x1 where "x1 = snd (split x)"
definition y0 where "y0 = fst (split y)"
definition y1 where "y1 = snd (split y)"
definition k_div_2 where "k_div_2 = k div 2"
definition prod0 where "prod0 = karatsuba_on_power_of_2_length k_div_2 x0 y0"
definition prod1 where "prod1 = karatsuba_on_power_of_2_length k_div_2 x1 y1"
definition prod2 where "prod2 = karatsuba_on_power_of_2_length k_div_2
      (fill k_div_2 (abs_diff x0 x1))
      (fill k_div_2 (abs_diff y0 y1))"
definition add01 where "add01 = prod0 +\<^sub>n prod1"
definition r where "r = (if (x1 \<le>\<^sub>n x0) = (y1 \<le>\<^sub>n y0)
        then add01 -\<^sub>n prod2
        else add01 +\<^sub>n prod2)"

lemma split_x: "split x = (x0, x1)" using x0_def x1_def by simp
lemma split_y: "split y = (y0, y1)" using y0_def y1_def by simp

lemmas defs1 = split_x split_y
lemmas defs2 = prod0_def prod1_def prod2_def k_div_2_def add01_def r_def

lemma recursive: "karatsuba_on_power_of_2_length k x y =
  prod0 +\<^sub>n (r >>\<^sub>n k_div_2) +\<^sub>n (prod1 >>\<^sub>n k)"
  unfolding karatsuba_on_power_of_2_length.simps[of k x y]
  using defs1 defs2 recursion_condition
  by (simp only: if_False Let_def case_prod_conv)

lemma l_ge_1: "l \<ge> 1"
  using karatsuba_lower_bound_requirement recursion_condition k_power_of_2
  by (cases l; simp)

lemma k_even: "k mod 2 = 0"
  using k_power_of_2 l_ge_1 by simp

lemma k_div_2: "k_div_2 = 2 ^ (l - 1)"
  unfolding k_div_2_def using k_power_of_2 l_ge_1 by (simp add: power_diff)

lemma k_div_2_less_k: "k_div_2 < k"
  unfolding k_div_2_def using k_power_of_2 by simp

lemma length_x_split: "length x0 = k_div_2" "length x1 = k_div_2"
  unfolding k_div_2_def using k_even length_split[OF _ split_x] length_x by argo+

lemma length_y_split: "length y0 = k_div_2" "length y1 = k_div_2"
  unfolding k_div_2_def using k_even length_split[OF _ split_y] length_y by argo+

lemma length_abs_diff_x0_x1: "length (abs_diff x0 x1) \<le> k_div_2"
  using abs_diff_length[of x0 x1] length_x_split by simp
lemma length_fill_abs_diff_x0_x1: "length (fill k_div_2 (abs_diff x0 x1)) = k_div_2"
  by (intro length_fill length_abs_diff_x0_x1)

lemma length_abs_diff_y0_y1: "length (abs_diff y0 y1) \<le> k_div_2"
  using abs_diff_length[of y0 y1] length_y_split by simp
lemma length_fill_abs_diff_y0_y1: "length (fill k_div_2 (abs_diff y0 y1)) = k_div_2"
  by (intro length_fill length_abs_diff_y0_y1)

lemmas IH_prems1 = recursion_condition split_x[symmetric] refl split_y[symmetric] refl k_div_2_def
    k_div_2 length_x_split(1) length_y_split(1)

lemmas IH_prems2 = recursion_condition split_x[symmetric] refl split_y[symmetric] refl k_div_2_def
    prod0_def k_div_2 length_x_split(2) length_y_split(2)

lemmas IH_prems3 = recursion_condition split_x[symmetric] refl split_y[symmetric] refl k_div_2_def
    prod0_def prod1_def k_div_2 length_fill_abs_diff_x0_x1 length_fill_abs_diff_y0_y1

end

lemma karatsuba_on_power_of_2_length_correct:
  assumes "k = 2 ^ l"
  assumes "length x = k" "length y = k"
  shows "to_nat (karatsuba_on_power_of_2_length k x y) = to_nat x * to_nat y"
using assms proof (induction k x y arbitrary: l rule: karatsuba_on_power_of_2_length.induct)
  case (1 k x y l)
  show ?case
  proof (cases "k \<le> karatsuba_lower_bound")
    case True
    then show ?thesis
      unfolding karatsuba_on_power_of_2_length.simps[of k x y]
      by (simp add: grid_mul_nat_correct)
  next
    case False
    then interpret r: karatsuba_context k l x y using "1.prems"
      by (unfold_locales; simp)
    from r.l_ge_1 obtain l' where "l = Suc l'"
      by (metis less_eqE plus_1_eq_Suc)
    then have "k div 2 = 2 ^ l'" using \<open>k = 2 ^ l\<close> by simp

    have to_nat_x: "to_nat x = to_nat r.x0 + 2 ^ (k div 2) * to_nat r.x1"
      unfolding r.k_div_2_def[symmetric]
      using app_split[OF r.split_x] to_nat_app[of r.x0 r.x1] r.length_x_split by algebra

    have to_nat_y: "to_nat y = to_nat r.y0 + 2 ^ (k div 2) * to_nat r.y1"
      unfolding r.k_div_2_def[symmetric]
      using app_split[OF r.split_y] to_nat_app[of r.y0 r.y1] r.length_y_split by algebra

    have 4: "to_nat r.prod0 = to_nat r.x0 * to_nat r.y0"
      unfolding r.prod0_def
      by (intro 1(1)[OF r.IH_prems1])
    have 5: "to_nat r.prod1 = to_nat r.x1 * to_nat r.y1"
      unfolding r.prod1_def
      by (intro 1(2)[OF r.IH_prems2])
    have "to_nat r.prod2 = to_nat (fill r.k_div_2 (abs_diff r.x0 r.x1)) * to_nat (fill r.k_div_2 (abs_diff r.y0 r.y1))"
      unfolding r.prod2_def
      by (intro 1(3)[OF r.IH_prems3])
    hence "int (to_nat r.prod2) = abs (int (to_nat r.x0) - int (to_nat r.x1)) * abs (int (to_nat r.y0) - int (to_nat r.y1))"
      using abs_diff_correct by simp
    then have "int (to_nat r.prod2) = abs ((int (to_nat r.x0) - int (to_nat r.x1)) * (int (to_nat r.y0) - int (to_nat r.y1)))"
      by (subst abs_mult, assumption)
    then have 6: "(if (compare_nat r.x1 r.x0) = (compare_nat r.y1 r.y0) then int (to_nat r.prod2) else - int (to_nat r.prod2)) = (int (to_nat r.x0) - int (to_nat r.x1)) * (int (to_nat r.y0) - int (to_nat r.y1))"
      apply (cases "to_nat r.x0 \<ge> to_nat r.x1"; cases "to_nat r.y0 \<ge> to_nat r.y1")
      by (simp_all add: compare_nat_correct mult_nonneg_nonpos mult_nonneg_nonpos2 mult_nonpos_nonpos)

    have 7: "int (to_nat r.r) = int (to_nat r.x0) * int (to_nat r.y1) + int (to_nat r.x1) * int (to_nat r.y0)"
    proof (cases "(r.x1 \<le>\<^sub>n r.x0) = (r.y1 \<le>\<^sub>n r.y0)")
      case True
      then have int_p: "int (to_nat r.r) = int (to_nat r.prod0 + to_nat r.prod1 - to_nat r.prod2)"
        unfolding r.r_def r.add01_def
        by (simp add: subtract_nat_correct add_nat_correct)
      have int_prod2: "int (to_nat r.prod2) = (int (to_nat r.x0) - int (to_nat r.x1)) * (int (to_nat r.y0) - int (to_nat r.y1))"
        using 6 True by simp
      have "- (int (to_nat r.x0) * int (to_nat r.y1)) \<le> int (to_nat r.x1) * int (to_nat r.y0)"
        apply (intro order.trans[of "- (int (to_nat r.x0) * int (to_nat r.y1))" 0 "int (to_nat r.x1) * int (to_nat r.y0)"])
        by simp_all
      then have "to_nat r.prod0 + to_nat r.prod1 \<ge> to_nat r.prod2"
        apply (intro iffD1[OF zle_int])
        by (simp add: 4 5 int_prod2 left_diff_distrib right_diff_distrib)
      then have "int (to_nat r.r) = int (to_nat r.prod0) + int (to_nat r.prod1) - int (to_nat r.prod2)"
        using int_p by simp
      then show ?thesis using int_prod2 by (simp add: left_diff_distrib right_diff_distrib 4 5)
    next
      case False
      then have "int (to_nat r.r) = int (to_nat r.prod0) + int (to_nat r.prod1) + int (to_nat r.prod2)"
        unfolding r.r_def
        by (simp add: add_nat_correct r.add01_def)
      moreover from False 6 have "- int (to_nat r.prod2) = (int (to_nat r.x0) - int (to_nat r.x1)) * (int (to_nat r.y0) - int (to_nat r.y1))"
        by simp
      then have "int (to_nat r.prod2) = - (int (to_nat r.x0) - int (to_nat r.x1)) * (int (to_nat r.y0) - int (to_nat r.y1))"
        by linarith
      ultimately show ?thesis by (simp add: 4 5 left_diff_distrib right_diff_distrib)
    qed

    (* the main proof *)
    from r.recursive have "int (to_nat (karatsuba_on_power_of_2_length k x y)) =
      int (to_nat (r.prod0 +\<^sub>n (r.r >>\<^sub>n r.k_div_2) +\<^sub>n (r.prod1 >>\<^sub>n k)))" by simp
    also have "... = int (to_nat r.prod0) + int (to_nat (shift_right r.k_div_2 r.r)) + int (to_nat (shift_right k r.prod1))"
      by (simp add: add_nat_correct)
    also have "... = int (to_nat r.prod0) + int (2 ^ (k div 2) * to_nat r.r) + int (2 ^ k * to_nat r.prod1)"
      by (simp only: to_nat_shift_right r.k_div_2_def)
    also have "... = int (to_nat r.prod0) + 2 ^ (k div 2) * int (to_nat r.r) + 2 ^ k * int (to_nat r.prod1)"
      by simp
    also have "... = int (to_nat r.x0) * int (to_nat r.y0) + 2 ^ (k div 2) * (int (to_nat r.x0) * int (to_nat r.y1) + int (to_nat r.x1) * int (to_nat r.y0)) + 2 ^ k * int (to_nat r.x1) * int (to_nat r.y1)"
      using 7 4 5
      by simp
    also have "... = (int (to_nat r.x0) + 2 ^ (k div 2) * (int (to_nat r.x1)))
      * (int (to_nat r.y0) + 2 ^ (k div 2) * (int (to_nat r.y1)))"
    proof -
      have "2 * (k div 2) = k"
        using r.k_even by force
      have "(int (to_nat r.x0) + 2 ^ (k div 2) * (int (to_nat r.x1)))
          * (int (to_nat r.y0) + 2 ^ (k div 2) * (int (to_nat r.y1)))
        = int (to_nat r.x0) * int (to_nat r.y0)
          + (2::int) ^ (k div 2) * (int (to_nat r.x1)) * (int (to_nat r.y0))
          + (int (to_nat r.x0)) * 2 ^ (k div 2) * (int (to_nat r.y1))
          + (2::int) ^ (k div 2) * (int (to_nat r.x1)) * 2 ^ (k div 2) * (int (to_nat r.y1))"
        using distrib_left[of "(int (to_nat r.x0) + 2 ^ (k div 2) * (int (to_nat r.x1)))" "int (to_nat r.y0)" "2 ^ (k div 2) * (int (to_nat r.y1))"]
        by (simp add: ring_class.ring_distribs(2))
      also have "... = int (to_nat r.x0) * int (to_nat r.y0)
          + (2::int) ^ (k div 2) * (int (to_nat r.x1)) * (int (to_nat r.y0))
          + (int (to_nat r.x0)) * 2 ^ (k div 2) * (int (to_nat r.y1))
          + ((2::int) ^ (k div 2) * 2 ^ (k div 2)) * (int (to_nat r.x1)) * (int (to_nat r.y1))"
        by simp
      also have "(2::int) ^ (k div 2) * 2 ^ (k div 2) = 2 ^ k"
        using power_add[of "2::int" "k div 2" "k div 2", symmetric]
        using \<open>2 * (k div 2) = k\<close>
        by simp
      finally have "(int (to_nat r.x0) + 2 ^ (k div 2) * (int (to_nat r.x1)))
          * (int (to_nat r.y0) + 2 ^ (k div 2) * (int (to_nat r.y1)))
        = int (to_nat r.x0) * int (to_nat r.y0)
          + 2 ^ (k div 2) * (int (to_nat r.x1)) * (int (to_nat r.y0))
          + (int (to_nat r.x0)) * 2 ^ (k div 2) * (int (to_nat r.y1))
          + (2::int) ^ k * (int (to_nat r.x1)) * (int (to_nat r.y1))" by simp
      also have "... = int (to_nat r.x0) * int (to_nat r.y0)
          + ((2::int) ^ (k div 2) * (int (to_nat r.x1)) * (int (to_nat r.y0))
          + (2::int) ^ (k div 2) * (int (to_nat r.x0)) * (int (to_nat r.y1)))
          + (2::int) ^ k * (int (to_nat r.x1)) * (int (to_nat r.y1))"
        by simp
      also have "... = int (to_nat r.x0) * int (to_nat r.y0)
          + (2::int) ^ (k div 2) * (int (to_nat r.x1) * int (to_nat r.y0) + int (to_nat r.x0) * int (to_nat r.y1))
          + (2::int) ^ k * (int (to_nat r.x1)) * (int (to_nat r.y1))"
        using distrib_left[of "(2::int) ^ (k div 2)"] by simp
      finally show ?thesis by simp
    qed
    also have "... = int (to_nat x) * int (to_nat y)"
      by (simp add: to_nat_x to_nat_y)
    finally have "int (to_nat (karatsuba_on_power_of_2_length k x y)) = int (to_nat x * to_nat y)"
      by simp
    thus ?thesis by presburger
  qed
qed

function len_kar_bound where
"len_kar_bound l = (if 2 ^ l \<le> karatsuba_lower_bound then 2 * karatsuba_lower_bound else 2 ^ l + len_kar_bound (l - 1) + 4)"
  by pat_completeness auto
termination
  apply (relation "Wellfounded.measure (\<lambda>l. l)")
  subgoal by simp
  subgoal for l
    using karatsuba_lower_bound_requirement by (cases l; simp)
  done

declare len_kar_bound.simps[simp del]

lemma length_karatsuba_on_power_of_2_aux:
  assumes "k = 2 ^ l"
  assumes "length x = k" "length y = k"
  shows "length (karatsuba_on_power_of_2_length k x y) \<le> len_kar_bound l"
  using assms proof (induction k x y arbitrary: l rule: karatsuba_on_power_of_2_length.induct)
  case (1 k x y)
  then show ?case
  proof (cases "k \<le> karatsuba_lower_bound")
    case True
    then have "karatsuba_on_power_of_2_length k x y = grid_mul_nat x y"
      unfolding karatsuba_on_power_of_2_length.simps[of k x y] by argo
    also have "length ... \<le> length x + length y"
      by (rule length_grid_mul_nat)
    also have "... = 2 * k" using 1 by linarith
    also have "... \<le> len_kar_bound l"
      unfolding len_kar_bound.simps[of l] using "1.prems" True by simp
    finally show ?thesis .
  next
    case False
    then interpret r: karatsuba_context k l x y using "1.prems" by unfold_locales simp_all
    from r.recursive have "length (karatsuba_on_power_of_2_length k x y) =
      length (r.prod0 +\<^sub>n (r.r >>\<^sub>n r.k_div_2) +\<^sub>n
      (r.prod1 >>\<^sub>n k))"
      by argo
    also have "... \<le> max (max (length r.prod0)
            (2 ^ (l - 1) +
             max (max (length r.prod0) (length r.prod1) + 1) (length r.prod2) + 1) + 1)
       (k + length r.prod1) + 1"
      unfolding r.r_def r.add01_def
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: length_add_nat_upper)
      unfolding length_shift_right r.k_div_2 if_distrib[of length]
      apply (estimation estimate: if_le_max)
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: length_subtract_nat_le)
      apply (estimation estimate: length_add_nat_upper)
      by simp
    also have "... \<le> max (max (len_kar_bound (l - 1))
          (2 ^ (l - 1) +
           max (max (len_kar_bound (l - 1)) (len_kar_bound (l - 1)) + 1)
            (len_kar_bound (l - 1)) + 1) + 1)
     (k + len_kar_bound (l - 1)) + 1"
      unfolding r.prod0_def r.prod1_def r.prod2_def
      apply (estimation estimate: "1.IH"(1)[OF r.IH_prems1])
      apply (estimation estimate: "1.IH"(2)[OF r.IH_prems2])
      apply (estimation estimate: "1.IH"(3)[OF r.IH_prems3])
      by (rule order.refl)
    also have "... = max (2 ^ (l - 1) + len_kar_bound (l - 1) + 3)
     (2 ^ l + len_kar_bound (l - 1)) + 1"
      unfolding max.idem r.k_power_of_2 by (simp del: One_nat_def)
    also have "... \<le> (2 ^ l + len_kar_bound (l - 1) + 3) + 1"
      apply (intro add_mono order.refl)
      apply (intro max.boundedI)
      subgoal
        apply (intro add_mono order.refl) by simp
      subgoal by simp
      done
    also have "... = len_kar_bound l"
      unfolding len_kar_bound.simps[of l] using False r.k_power_of_2 by simp
    finally show ?thesis .
  qed
qed

lemma len_kar_bound_le: "len_kar_bound l \<le> 6 * 2 ^ l + 2 * karatsuba_lower_bound"
proof (induction l rule: less_induct)
  case (less l)
  then show ?case
  proof (cases "2 ^ l \<le> karatsuba_lower_bound")
    case True
    then show ?thesis
      unfolding len_kar_bound.simps[of l] by simp
  next
    case False
    then have "l - 1 < l" using karatsuba_lower_bound_requirement by (cases l; simp)
    then have "l > 0" by simp
    from False have "len_kar_bound l = 2 ^ l + len_kar_bound (l - 1) + 4"
      unfolding len_kar_bound.simps[of l] by argo
    also have "... \<le> 2 ^ l + (6 * 2 ^ (l - 1) + 2 * karatsuba_lower_bound) + 4"
      using less[OF \<open>l - 1 < l\<close>] by simp
    also have "... = 2 * (2 ^ (l - 1)) + (6 * 2 ^ (l - 1) + 2 * karatsuba_lower_bound) + 4"
      unfolding power_Suc[symmetric] Suc_diff_1[OF \<open>l > 0\<close>] by (rule refl)
    also have "... = 8 * 2 ^ (l - 1) + 4 + 2 * karatsuba_lower_bound" by simp
    also have "... \<le> 8 * 2 ^ (l - 1) + 4 * 2 ^ (l - 1) + 2 * karatsuba_lower_bound" by simp
    also have "... = 12 * 2 ^ (l - 1) + 2 * karatsuba_lower_bound" by simp
    also have "... = 6 * 2 ^ l + 2 * karatsuba_lower_bound"
      using Suc_diff_1[OF \<open>l > 0\<close>, symmetric] power_Suc[of "2::nat" "l - 1"] by simp
    finally show ?thesis .
  qed
qed

text "The following is a pretty crude estimate for the length of the result of our Karatsuba
implementation, but it suffices for our purposes."

lemma length_karatsuba_on_power_of_2_length_le:
  assumes "k = 2 ^ l"
  assumes "length x = k" "length y = k"
  shows "length (karatsuba_on_power_of_2_length k x y) \<le> 6 * k + 2 * karatsuba_lower_bound"
  using order.trans[OF length_karatsuba_on_power_of_2_aux[OF assms] len_kar_bound_le]
  unfolding assms .

text "In order to multiply two integers of arbitrary length using Karatsuba multiplication, the
input numbers can just be zero-padded."

fun karatsuba_mul_nat :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"karatsuba_mul_nat x y = (let k = next_power_of_2 (max (length x) (length y)) in
  karatsuba_on_power_of_2_length k (fill k x) (fill k y))"

text "We verify the correctness of Karatsuba multiplication:"

theorem karatsuba_mul_nat_correct: "to_nat (karatsuba_mul_nat x y) = to_nat x * to_nat y"
proof -
  define k where "k = next_power_of_2 (max (length x) (length y))"
  then obtain l where "k = 2 ^ l" using next_power_of_2_is_power_of_2 by blast
  have 1: "to_nat (fill k x) = to_nat x" "to_nat (fill k y) = to_nat y" by simp_all
  have "k \<ge> length x" "k \<ge> length y"
    using next_power_of_2_lower_bound[of "max (length x) (length y)"] k_def
    by simp_all
  hence "length (fill k x) = k" "length (fill k y) = k" using length_fill by simp_all
  show ?thesis unfolding k_def[symmetric] karatsuba_lower_bound_def
    using karatsuba_on_power_of_2_length_correct[OF \<open>k = 2 ^ l\<close> \<open>length (fill k x) = k\<close> \<open>length (fill k y) = k\<close>]
    by (simp only: karatsuba_mul_nat.simps Let_def k_def[symmetric] to_nat_fill)
qed

lemma length_karatsuba_mul_nat_le: "length (karatsuba_mul_nat x y) \<le> 12 * max (length x) (length y) + (6 + 2 * karatsuba_lower_bound)"
proof -
  let ?m = "max (length x) (length y)"
  define k where "k = next_power_of_2 ?m"
  then obtain l where "k = 2 ^ l" using next_power_of_2_is_power_of_2 by auto
  from k_def have "?m \<le> k" using next_power_of_2_lower_bound by simp
  from k_def have "karatsuba_mul_nat x y = karatsuba_on_power_of_2_length k (fill k x) (fill k y)"
    unfolding karatsuba_mul_nat.simps Let_def by argo
  also have "length ... \<le> 6 * k + 2 * karatsuba_lower_bound"
    apply (intro length_karatsuba_on_power_of_2_length_le[OF \<open>k = 2 ^ l\<close>] length_fill)
    subgoal using \<open>?m \<le> k\<close> by simp
    subgoal using \<open>?m \<le> k\<close> by simp
    done
  also have "... \<le> 6 * (2 * ?m + 1) + 2 * karatsuba_lower_bound"
    apply (intro add_mono mult_le_mono order.refl)
    unfolding k_def by (rule next_power_of_2_upper_bound')
  also have "... = 12 * ?m + (6 + 2 * karatsuba_lower_bound)"
    by simp
  finally show ?thesis .
qed

text "Formally, we only implemented Karatsuba multiplication on natural numbers (not all integers).
However, this does not really matter, as the multiplication can just be lifted to the integers.
This lifting has already been done on other types, but for the sake of completeness we will just add
it here as well:"

fun karatsuba_mul_int where
"karatsuba_mul_int x y = nat_mul_to_int_mul karatsuba_mul_nat x y"

corollary karatsuba_mul_int_correct:
"to_int (karatsuba_mul_int x y) = to_int x * to_int y"
  using nat_mul_to_int_mul_correct[of karatsuba_mul_nat] karatsuba_mul_nat_correct
  by (metis karatsuba_mul_int.simps surj_pair)

end