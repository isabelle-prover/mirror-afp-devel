section "Running Time of Karatsuba Multiplication"

theory "Karatsuba_TM"
  imports Karatsuba "../Binary_Representations/Nat_LSBF_TM"
    "../Estimation_Method"
begin

text "This theory contains a time monad version of Karatsuba multiplication, which is used to
verify the asymptotic running time of $\\mathcal{O}\\left(n ^ {\\log_2 3}\\right)$."

definition abs_diff_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"abs_diff_tm xs ys =1 do {
  r1 \<leftarrow> xs -\<^sub>n\<^sub>t ys;
  r2 \<leftarrow> ys -\<^sub>n\<^sub>t xs;
  r1 +\<^sub>n\<^sub>t r2
}"

lemma val_abs_diff_tm[simp, val_simp]: "val (abs_diff_tm xs ys) = abs_diff xs ys"
  by (simp add: abs_diff_tm_def abs_diff_def)

lemma time_abs_diff_tm_le: "time (abs_diff_tm xs ys) \<le> 62 * max (length xs) (length ys) + 100"
proof -
  have "time (abs_diff_tm xs ys) \<le> time (xs -\<^sub>n\<^sub>t ys) + time (ys -\<^sub>n\<^sub>t xs) +
       time ((xs -\<^sub>n ys) +\<^sub>n\<^sub>t (ys -\<^sub>n xs)) + 1"
    by (simp add: abs_diff_tm_def)
  also have "... \<le> 62 * max (length xs) (length ys) + 100"
  apply (estimation estimate: time_subtract_nat_tm_le)
  apply (estimation estimate: time_subtract_nat_tm_le)
  apply (estimation estimate: time_add_nat_tm_le)
  using length_subtract_nat_le[of xs ys] length_subtract_nat_le[of ys xs]
  by linarith
  finally show ?thesis .
qed

context karatsuba_context
begin

definition fill_abs_diff_x where "fill_abs_diff_x = fill k_div_2 (abs_diff x0 x1)"
definition fill_abs_diff_y where "fill_abs_diff_y = fill k_div_2 (abs_diff y0 y1)"
definition sgnx where "sgnx = (x1 \<le>\<^sub>n x0)"
definition sgny where "sgny = (y1 \<le>\<^sub>n y0)"
definition sgnxy where "sgnxy = (sgnx = sgny)"
definition r' where "r' = (if sgnxy then add01 -\<^sub>n prod2 else add01 +\<^sub>n prod2)"
definition sr where "sr = r >>\<^sub>n k_div_2"
definition add0sr where "add0sr = prod0 +\<^sub>n sr"
definition s1 where  "s1 = prod1 >>\<^sub>n k"

lemma r_r': "r = r'"
  unfolding r_def r'_def sgnxy_def sgnx_def sgny_def by argo

lemmas defs3 = fill_abs_diff_x_def fill_abs_diff_y_def sgnx_def sgny_def sgnxy_def r_r' r'_def sr_def add0sr_def s1_def

end

lemma add_nat_carry_aux:
  assumes "length x \<le> k"
  assumes "length y \<le> k"
  assumes "length (x +\<^sub>n y) = k + 1"
  shows "max (length x) (length y) = k" "Nat_LSBF.to_nat x + Nat_LSBF.to_nat y \<ge> 2 ^ k"
proof -
  have "length x = k \<or> length y = k"
  proof (rule ccontr)
    assume "\<not> (length x = k \<or> length y = k)"
    then have "max (length x) (length y) < k" using assms by simp
    then have "length (add_nat x y) < k + 1" using length_add_nat_upper[of x y] by linarith
    then show False using assms by simp
  qed
  then show "max (length x) (length y) = k" using assms by linarith
  then obtain z where "add_nat x y = z @ [True]"
    using add_nat_last_bit_True assms by blast
  from this[symmetric] have "Nat_LSBF.to_nat x + Nat_LSBF.to_nat y \<ge> 2 ^ length z"
    using add_nat_correct[of x y] to_nat_length_lower_bound[of z] by argo
  also have "2 ^ length z = 2 ^ k" using \<open>add_nat x y = z @ [True]\<close> assms by simp
  finally show "Nat_LSBF.to_nat x + Nat_LSBF.to_nat y \<ge> 2 ^ k" by simp
qed

context begin

private fun f where
"f k = (if k \<le> karatsuba_lower_bound then 2 * k else f (k div 2) + k + 4)"

declare f.simps[simp del]

private lemma f_linear: "f k \<le> 6 * k"
  apply (induction k rule: f.induct)
  subgoal for k
    apply (cases "k \<le> karatsuba_lower_bound")
    subgoal by (simp add: f.simps[of k])
    subgoal premises prems
    proof (cases "k \<ge> 5")
      case True
      then show ?thesis using prems unfolding f.simps[of k] by simp
    next
      case False
      then consider "k = 2" | "k = 3" | "k = 4" using prems karatsuba_lower_bound_requirement by linarith
      then show ?thesis using prems unfolding f.simps[of k] by fastforce
    qed
    done
  done

private lemma f_bound:
  assumes "k = 2 ^ l"
  assumes "length x = k"
  assumes "length y = k"
  shows "length (karatsuba_on_power_of_2_length k x y) \<le> f k"
  using assms
proof (induction k x y arbitrary: l rule: karatsuba_on_power_of_2_length.induct)
  case (1 k x y)
  show ?case
  proof (cases "k \<le> karatsuba_lower_bound")
    case True
    then show ?thesis unfolding karatsuba_on_power_of_2_length.simps[of k x y]
      using length_grid_mul_nat[of x y] "1.prems" f.simps[of k] by simp
  next
    case False
    then interpret r : karatsuba_context k l x y
      using "1.prems" by (unfold_locales; simp)
    have len0: "length r.prod0 \<le> f (k div 2)"
      unfolding r.prod0_def r.k_div_2_def[symmetric]
      by (intro 1(1)[OF r.IH_prems1])
    have len1: "length r.prod1 \<le> f (k div 2)"
      unfolding r.prod1_def r.k_div_2_def[symmetric]
      by (intro 1(2)[OF r.IH_prems2])
    have len2: "length r.prod2 \<le> f (k div 2)"
      unfolding r.prod2_def r.k_div_2_def[symmetric]
      by (intro 1(3)[OF r.IH_prems3])

    have len_p01: "length (r.prod0 +\<^sub>n r.prod1) \<le> f (k div 2) + 1"
      using length_add_nat_upper[of r.prod0 r.prod1] len0 len1 by linarith
    then have "length (r.prod0 +\<^sub>n r.prod1 +\<^sub>n r.prod2) \<le> f (k div 2) + 2"
      using length_add_nat_upper[of "r.prod0 +\<^sub>n r.prod1" r.prod2] len2 by linarith
    moreover have "length (r.prod0 +\<^sub>n r.prod1 -\<^sub>n r.prod2) \<le> f (k div 2) + 1"
      using length_subtract_nat_le[of "r.prod0 +\<^sub>n r.prod1" r.prod2] len_p01 len2
      by linarith
    ultimately have lenif: "length (if r.sgnxy then r.prod0 +\<^sub>n r.prod1 -\<^sub>n r.prod2
            else r.prod0 +\<^sub>n r.prod1 +\<^sub>n r.prod2) \<le> f (k div 2) + 2" (is "length ?if \<le> _")
      by simp

    have "length (karatsuba_on_power_of_2_length k x y) \<le> max (r.k_div_2 + f (k div 2)) (k + f (k div 2)) + 4"
      unfolding r.recursive
      apply (estimation estimate: length_add_nat_upper)
      apply (subst length_shift_right)
      apply (estimation estimate: length_add_nat_upper)
      apply (subst length_shift_right)
      unfolding r.r_def r.add01_def
      apply (subst if_distrib[of length])
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: length_subtract_nat_le)
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: len0)
      apply (estimation estimate: len1)
      apply (estimation estimate: len2)
      by auto
    also have "... = k + f (k div 2) + 4"
      using r.k_div_2_less_k by simp
    finally show ?thesis unfolding f.simps[of k] using False by simp
  qed
qed

lemma length_karatsuba_on_power_of_2_length:
  assumes "k = 2 ^ l"
  assumes "length x = k"
  assumes "length y = k"
  shows "length (karatsuba_on_power_of_2_length k x y) \<le> 6 * k"
  using f_bound[OF assms] f_linear[of k] by simp

end

function karatsuba_on_power_of_2_length_tm :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"karatsuba_on_power_of_2_length_tm k xs ys =1 do {
  b \<leftarrow> k \<le>\<^sub>t karatsuba_lower_bound;
  (if b then grid_mul_nat_tm xs ys else do {
    (x0, x1) \<leftarrow> split_tm xs;
    (y0, y1) \<leftarrow> split_tm ys;
    k_div_2 \<leftarrow> k div\<^sub>t 2;
    prod0 \<leftarrow> karatsuba_on_power_of_2_length_tm k_div_2 x0 y0;
    prod1 \<leftarrow> karatsuba_on_power_of_2_length_tm k_div_2 x1 y1;
    abs_diff_x \<leftarrow> (abs_diff_tm x0 x1 \<bind> fill_tm k_div_2);
    abs_diff_y \<leftarrow> (abs_diff_tm y0 y1 \<bind> fill_tm k_div_2);
    prod2 \<leftarrow> karatsuba_on_power_of_2_length_tm k_div_2 abs_diff_x abs_diff_y;
    sgnx \<leftarrow> x1 \<le>\<^sub>n\<^sub>t x0;
    sgny \<leftarrow> y1 \<le>\<^sub>n\<^sub>t y0;
    sgnxy \<leftarrow> sgnx =\<^sub>t sgny;
    \<comment> \<open>construct return value\<close>
    add01 \<leftarrow> prod0 +\<^sub>n\<^sub>t prod1;
    r \<leftarrow> (if sgnxy then add01 -\<^sub>n\<^sub>t prod2 else add01 +\<^sub>n\<^sub>t prod2);
    sr \<leftarrow> r >>\<^sub>n\<^sub>t k_div_2;
    add0sr \<leftarrow> prod0 +\<^sub>n\<^sub>t sr;
    s1 \<leftarrow> prod1 >>\<^sub>n\<^sub>t k;
    add0sr +\<^sub>n\<^sub>t s1
  })
}"
  by pat_completeness simp
termination
  by (relation "Wellfounded.measure (\<lambda>p. size (fst p))") simp_all

declare karatsuba_on_power_of_2_length_tm.simps[simp del]

lemma val_karatsuba_on_power_of_2_length_tm[simp, val_simp]:
  assumes "k = 2 ^ l"
  assumes "length xs = k" "length ys = k"
  shows "val (karatsuba_on_power_of_2_length_tm k xs ys) = karatsuba_on_power_of_2_length k xs ys"
using assms proof (induction k arbitrary: l xs ys rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k \<le> karatsuba_lower_bound")
    case True
    then show ?thesis
      unfolding karatsuba_on_power_of_2_length_tm.simps[of k xs ys]
      karatsuba_on_power_of_2_length.simps[of k xs ys]
      val_bind_tm val_less_eq_nat_tm val_simps val_grid_mul_nat_tm
      by simp
  next
    case False
    interpret r: karatsuba_context k l xs ys
      using less False by unfold_locales simp_all
    have val0: "val (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x0 r.y0) = r.prod0"
      unfolding r.prod0_def
      by (intro less.IH[OF r.k_div_2_less_k r.k_div_2 r.length_x_split(1) r.length_y_split(1)])
    have val1: "val (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x1 r.y1) = r.prod1"
      unfolding r.prod1_def
      by (intro less.IH[OF r.k_div_2_less_k r.k_div_2 r.length_x_split(2) r.length_y_split(2)])
    have val2: "val (karatsuba_on_power_of_2_length_tm r.k_div_2 r.fill_abs_diff_x r.fill_abs_diff_y) = r.prod2"
      unfolding r.prod2_def r.fill_abs_diff_x_def[symmetric] r.fill_abs_diff_y_def[symmetric]
      apply (intro less.IH[OF r.k_div_2_less_k r.k_div_2])
      subgoal unfolding r.fill_abs_diff_x_def by (rule r.length_fill_abs_diff_x0_x1)
      subgoal unfolding r.fill_abs_diff_y_def by (rule r.length_fill_abs_diff_y0_y1)
      done
    have "val (karatsuba_on_power_of_2_length_tm k xs ys) = r.add0sr +\<^sub>n r.s1"
      unfolding karatsuba_on_power_of_2_length_tm.simps[of k xs ys]
      val_bind_tm val_less_eq_nat_tm val_simps val_split_tm r.split_x r.split_y
      val_divide_nat_tm val_abs_diff_tm val_fill_tm r.k_div_2_def[symmetric]
      val_compare_nat_tm val_subtract_nat_tm val_add_nat_tm val_equal_bool_tm val_shift_right_tm
      Let_def Product_Type.prod.case r.defs2[symmetric] r.defs3[symmetric] val0 val1 val2
      using False by argo
    also have "... = karatsuba_on_power_of_2_length k xs ys"
      using r.recursive
      unfolding karatsuba_on_power_of_2_length.simps[of k xs ys]
      Let_def r.split_x r.split_y Product_Type.prod.case r.defs2[symmetric] r.defs3[symmetric] by argo
    finally show ?thesis .
  qed
qed

fun h where
"h k = (if k \<le> karatsuba_lower_bound then 2 * k + 8 * k * k + 3
    else 407 + 224 * k + 3 * h (k div 2))"
declare h.simps[simp del]

lemma time_karatsuba_on_power_of_2_length_tm_le_h:
  assumes "k = 2 ^ l"
  assumes "length xs = k" "length ys = k"
  shows "time (karatsuba_on_power_of_2_length_tm k xs ys) \<le> h k"
using assms proof (induction k arbitrary: xs ys l rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k \<le> karatsuba_lower_bound")
    case True
    then have "time (karatsuba_on_power_of_2_length_tm k xs ys) \<le>
      2 * k + 8 * length xs * max (length xs) (length ys) + 3"
      unfolding karatsuba_on_power_of_2_length_tm.simps[of k xs ys]
      apply (simp add: time_less_eq_nat_tm)
      apply (subst Suc_eq_plus1)+
      apply (estimation estimate: time_grid_mul_nat_tm_le)
      apply (rule order.refl)
      done
    also have "... = 2 * k + 8 * k * k + 3" unfolding less(3) less(4) by simp
    finally show ?thesis unfolding h.simps[of k] using True by simp
  next
    case False
    then interpret r: karatsuba_context k l xs ys
      by (unfold_locales; simp add: less)
    have val0: "val (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x0 r.y0) = r.prod0"
      unfolding r.prod0_def
      by (intro val_karatsuba_on_power_of_2_length_tm[OF r.k_div_2 r.length_x_split(1) r.length_y_split(1)])
    have val1: "val (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x1 r.y1) = r.prod1"
      unfolding r.prod1_def
      by (intro val_karatsuba_on_power_of_2_length_tm[OF r.k_div_2 r.length_x_split(2) r.length_y_split(2)])
    have val2: "val (karatsuba_on_power_of_2_length_tm r.k_div_2 r.fill_abs_diff_x r.fill_abs_diff_y) = r.prod2"
      unfolding r.prod2_def r.fill_abs_diff_x_def[symmetric] r.fill_abs_diff_y_def[symmetric]
      apply (intro val_karatsuba_on_power_of_2_length_tm[OF r.k_div_2])
      subgoal unfolding r.fill_abs_diff_x_def by (rule r.length_fill_abs_diff_x0_x1)
      subgoal unfolding r.fill_abs_diff_y_def by (rule r.length_fill_abs_diff_y0_y1)
      done

    have len0: "length (r.prod0) \<le> 3 * k"
      unfolding r.prod0_def
      apply (estimation estimate: length_karatsuba_on_power_of_2_length[OF r.k_div_2 r.length_x_split(1) r.length_y_split(1)])
      unfolding r.k_div_2_def
      by simp
    have len1: "length (r.prod1) \<le> 3 * k"
      unfolding r.prod1_def
      apply (estimation estimate: length_karatsuba_on_power_of_2_length[OF r.k_div_2 r.length_x_split(2) r.length_y_split(2)])
      unfolding r.k_div_2_def
      by simp
    have len2: "length (r.prod2) \<le> 3 * k"
      unfolding r.prod2_def
      apply (estimation estimate: length_karatsuba_on_power_of_2_length[OF r.k_div_2 r.length_fill_abs_diff_x0_x1 r.length_fill_abs_diff_y0_y1])
      unfolding r.k_div_2_def
      by simp

    have len01: "length r.add01 \<le> 3 * k + 1"
      unfolding r.add01_def
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: len0)
      apply (estimation estimate: len1)
      by simp
    have lenr: "length r.r \<le> 3 * k + 2"
      unfolding r.r_def if_distrib[of length]
      apply (estimation estimate: length_subtract_nat_le)
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: len01)
      apply (estimation estimate: len2)
      by simp
    have lensr: "length r.sr \<le> r.k_div_2 + 3 * k + 2"
      unfolding r.sr_def
      apply (subst length_shift_right)
      apply (estimation estimate: lenr)
      by simp
    have len0sr: "length r.add0sr \<le> r.k_div_2 + 3 * k + 3"
      unfolding r.add0sr_def
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: len0)
      apply (estimation estimate: lensr)
      by simp
    have lens1: "length r.s1 \<le> 4 * k"
      unfolding r.s1_def
      apply (subst length_shift_right)
      apply (estimation estimate: len1)
      by simp

    have time0: "time (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x0 r.y0) \<le> h r.k_div_2"
      by (intro less.IH[OF r.k_div_2_less_k r.k_div_2 r.length_x_split(1) r.length_y_split(1)])
    have time1: "time (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x1 r.y1) \<le> h r.k_div_2"
      by (intro less.IH[OF r.k_div_2_less_k r.k_div_2 r.length_x_split(2) r.length_y_split(2)])
    have time2: "time (karatsuba_on_power_of_2_length_tm r.k_div_2 r.fill_abs_diff_x r.fill_abs_diff_y) \<le> h r.k_div_2"
      apply (intro less.IH[OF r.k_div_2_less_k r.k_div_2])
      subgoal unfolding r.fill_abs_diff_x_def using r.length_fill_abs_diff_x0_x1 by assumption
      subgoal unfolding r.fill_abs_diff_y_def using r.length_fill_abs_diff_y0_y1 by assumption
      done

    have "time (karatsuba_on_power_of_2_length_tm k xs ys) =
        time (k \<le>\<^sub>t karatsuba_lower_bound) +
        time (split_tm xs) +
        time (split_tm ys) +
        time (k div\<^sub>t 2) +
        time (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x0 r.y0) +
        time (karatsuba_on_power_of_2_length_tm r.k_div_2 r.x1 r.y1) +
        time (abs_diff_tm r.x0 r.x1) + time (fill_tm r.k_div_2 (abs_diff r.x0 r.x1)) +
        time (abs_diff_tm r.y0 r.y1) + time (fill_tm r.k_div_2 (abs_diff r.y0 r.y1)) +
        time (karatsuba_on_power_of_2_length_tm r.k_div_2 r.fill_abs_diff_x r.fill_abs_diff_y) +
        time (r.x1 \<le>\<^sub>n\<^sub>t r.x0) +
        time (r.y1 \<le>\<^sub>n\<^sub>t r.y0) +
        time (r.sgnx =\<^sub>t r.sgny) +
        time (add_nat_tm r.prod0 r.prod1) +
        (if r.sgnxy then time (r.add01 -\<^sub>n\<^sub>t r.prod2)
                   else time (r.add01 +\<^sub>n\<^sub>t r.prod2)) +
        time (r.r >>\<^sub>n\<^sub>t r.k_div_2) +
        time (r.prod0 +\<^sub>n\<^sub>t r.sr) +
        time (r.prod1 >>\<^sub>n\<^sub>t k) +
        time (r.add0sr +\<^sub>n\<^sub>t r.s1) + 1"
      unfolding karatsuba_on_power_of_2_length_tm.simps[of k xs ys]
      tm_time_simps if_distrib[of time] val_less_eq_nat_tm val_split_tm r.defs1
      Product_Type.prod.case val_divide_nat_tm r.defs2[symmetric] r.defs3[symmetric]
      val_abs_diff_tm val_simps val_fill_tm val_karatsuba_on_power_of_2_length_tm
      val_compare_nat_tm Let_def val0 val1 val2 val_add_nat_tm val_equal_bool_tm
      val_subtract_nat_tm
      by (auto simp: False r.defs2[symmetric] r.defs3[symmetric])
    also have "... \<le> 2 * k + 2 +
        (10 * k + 16) + (10 * k + 16) +
        (8 * k + 11) +
        h (k div 2) +
        h (k div 2) +
        (31 * k + 100) +
        (2 * k + 5) +
        (31 * k + 100) +
        (2 * k + 5) +
        h (k div 2) +
        (7 * k + 23) +
        (7 * k + 23) +
        2 +
        (6 * k + 3) +
        (90 * k + 78) +
        (k + 3) +
        (7 * k + 7) +
        (2 * k + 3) +
        (8 * k + 9) +
        1"
      apply (intro add_mono)
      subgoal by (estimation estimate: time_less_eq_nat_tm_le) simp
      subgoal by (estimation estimate: time_split_tm_le) (simp add: less)
      subgoal by (estimation estimate: time_split_tm_le) (simp add: less)
      subgoal by (estimation estimate: time_divide_nat_tm_le) simp
      subgoal by (estimation estimate: time0) (simp add: r.k_div_2_def)
      subgoal by (estimation estimate: time1) (simp add: r.k_div_2_def)
      subgoal apply (estimation estimate: time_abs_diff_tm_le) unfolding r.length_x_split r.k_div_2_def by simp
      subgoal apply (estimation estimate: time_fill_tm_le) using r.length_abs_diff_x0_x1 r.k_div_2_def by simp
      subgoal apply (estimation estimate: time_abs_diff_tm_le) unfolding r.length_y_split r.k_div_2_def by simp
      subgoal apply (estimation estimate: time_fill_tm_le) using r.length_abs_diff_y0_y1 r.k_div_2_def by simp
      subgoal by (estimation estimate: time2) (simp add: r.k_div_2_def)
      subgoal apply (estimation estimate: time_compare_nat_tm_le) using r.length_x_split r.k_div_2_def by simp
      subgoal apply (estimation estimate: time_compare_nat_tm_le) using r.length_y_split r.k_div_2_def by simp
      subgoal using time_equal_bool_tm_le by simp
      subgoal
        apply (estimation estimate: time_add_nat_tm_le)
        apply (estimation estimate: len0)
        apply (estimation estimate: len1)
        by simp
      subgoal
        apply (estimation estimate: time_subtract_nat_tm_le)
        apply (estimation estimate: time_add_nat_tm_le)
        apply (estimation estimate: len01)
        apply (estimation estimate: len2)
        by simp
      subgoal using r.k_div_2_def by simp
      subgoal
        apply (estimation estimate: time_add_nat_tm_le)
        apply (estimation estimate: len0)
        apply (estimation estimate: lensr)
        using r.k_div_2_def by simp
      subgoal by simp
      subgoal
        apply (estimation estimate: time_add_nat_tm_le)
        apply (estimation estimate: len0sr)
        apply (estimation estimate: lens1)
        using r.k_div_2_less_k by presburger
      subgoal by simp
      done
    also have "... = 407 + 224 * k + 3 * h (k div 2)"
      by simp
    finally show ?thesis unfolding h.simps[of k] using False by simp
  qed
qed

lemma n_div_2: "n div 2 = nat \<lfloor>real n / 2\<rfloor>"
  by linarith

function h_real :: "nat \<Rightarrow> real" where
"x \<le> karatsuba_lower_bound \<Longrightarrow> h_real x = 8 * x * x + 2 * x + 3"
| "x > karatsuba_lower_bound \<Longrightarrow> h_real x = 407 + 224 * x + 3 * h_real (nat (\<lfloor>real x / 2\<rfloor>))"
  by force simp_all
termination
  by (relation "Wellfounded.measure (\<lambda>x. x)") (simp_all add: n_div_2[symmetric])

lemma h_h_real: "real (h k) = h_real k"
  apply (induction k rule: h.induct)
  subgoal for k
    apply (cases "k \<le> karatsuba_lower_bound")
    by (simp_all add: h_real.simps[of k] h.simps[of k] n_div_2 del: h_real.simps)
  done

lemma h_real_bigo: "h_real \<in> O(\<lambda>n. real n powr log 2 3)"
  by (master_theorem 1 p': 1) (auto simp: powr_divide)

definition karatsuba_mul_nat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"karatsuba_mul_nat_tm xs ys =1 do {
  lenx \<leftarrow> length_tm xs;
  leny \<leftarrow> length_tm ys;
  k \<leftarrow> max_nat_tm lenx leny \<bind> next_power_of_2_tm;
  fillx \<leftarrow> fill_tm k xs;
  filly \<leftarrow> fill_tm k ys;
  karatsuba_on_power_of_2_length_tm k fillx filly
}"

lemma val_karatsuba_mul_nat_tm[simp, val_simp]: "val (karatsuba_mul_nat_tm xs ys) = karatsuba_mul_nat xs ys"
proof -
  define k where "k = next_power_of_2 (max (length xs) (length ys))"
  then obtain l where "k = 2 ^ l" using  next_power_of_2_is_power_of_2 by auto
  have "val (karatsuba_on_power_of_2_length_tm k (fill k xs) (fill k ys)) =
      karatsuba_on_power_of_2_length k (fill k xs) (fill k ys)"
    apply (intro val_karatsuba_on_power_of_2_length_tm[OF \<open>k = 2 ^ l\<close>])
    unfolding k_def using next_power_of_2_lower_bound[of "max (length xs) (length ys)"] by auto
  then show ?thesis
    unfolding karatsuba_mul_nat_tm_def karatsuba_mul_nat.simps val_simp Let_def k_def .
qed

definition time_karatsuba_mul_nat_bound where
  "time_karatsuba_mul_nat_bound m = 53 + 218 * (next_power_of_2 m) + h (next_power_of_2 m)"

text "The following two lemmas are one way to formally express the more informal statement
''Karatsuba Multiplication needs $\\mathcal{O}\\left(n ^ {\\log_2 3}\\right)$ bit operations for
input numbers of length $n$''."

theorem time_karatsuba_mul_nat_tm_le:
  assumes "max (length xs) (length ys) = m"
  shows "time (karatsuba_mul_nat_tm xs ys) \<le> time_karatsuba_mul_nat_bound m"
proof -
  define k where "k = next_power_of_2 m"
  then obtain l where "k = 2 ^ l" using next_power_of_2_is_power_of_2 by auto
  have lens: "length xs \<le> k" "length ys \<le> k"
    using assms next_power_of_2_lower_bound[of m] k_def by simp_all
  have "time (karatsuba_mul_nat_tm xs ys) =
    time (length_tm xs) +
    time (length_tm ys) +
    time (max_nat_tm (length xs) (length ys)) +
    time (next_power_of_2_tm (max (length xs) (length ys))) +
    time (fill_tm k xs) +
    time (fill_tm k ys) +
    time (karatsuba_on_power_of_2_length_tm k (fill k xs) (fill k ys)) + 1"
  unfolding karatsuba_mul_nat_tm_def tm_time_simps val_simp Let_def
    assms k_def[symmetric] by presburger
  also have "... \<le>
    (k + 1) + (k + 1) + (2 * k + 3) +
    (208 * k + 37) +
    (3 * k + 5) +
    (3 * k + 5) +
    h k +
    1"
    apply (intro add_mono order.refl)
    subgoal by (simp add: lens)
    subgoal by (simp add: lens)
    subgoal apply (estimation estimate: time_max_nat_tm_le) using lens by simp
    subgoal apply (estimation estimate: time_next_power_of_2_tm_le) using lens by simp
    subgoal apply (estimation estimate: time_fill_tm_le) using lens by simp
    subgoal apply (estimation estimate: time_fill_tm_le) using lens by simp
    subgoal apply (intro time_karatsuba_on_power_of_2_length_tm_le_h[OF \<open>k = 2 ^ l\<close>]) using lens
      by auto
    done
  also have "... = 53 + 218 * k + h k" by simp
  finally show ?thesis unfolding k_def time_karatsuba_mul_nat_bound_def[symmetric] .
qed

theorem time_karatsuba_mul_nat_bound_bigo: "time_karatsuba_mul_nat_bound \<in> O(\<lambda>m. m powr log 2 3)"
proof -
  define t where "t = (\<lambda>m. real (53 + 218 * m + h m))"
  then have "time_karatsuba_mul_nat_bound = t \<circ> next_power_of_2"
    unfolding time_karatsuba_mul_nat_bound_def by auto
  also have "... \<in> O(\<lambda>m. m powr log 2 3)"
    apply (intro powr_bigo_linear_index_transformation)
    subgoal
    proof -
      have "(\<lambda>x. real (next_power_of_2 x)) \<in> O(\<lambda>x. real (2 * x + 1))"
        apply (intro landau_mono_always)
        using next_power_of_2_upper_bound' real_mono by simp_all
      moreover have "(\<lambda>x. real (2 * x + 1)) \<in> O(real)" by auto
      ultimately show "(\<lambda>x. real (next_power_of_2 x)) \<in> O(real)"
        using landau_o.big.trans by blast
    qed
    subgoal unfolding t_def real_linear real_multiplicative h_h_real
      apply (intro sum_in_bigo)
      subgoal by auto
      subgoal by auto
      subgoal using h_real_bigo .
      done
    subgoal by auto
    done
  finally show ?thesis .
qed

end