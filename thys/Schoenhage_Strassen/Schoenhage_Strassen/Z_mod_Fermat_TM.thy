theory "Z_mod_Fermat_TM"
imports
  Z_mod_Fermat
  Z_mod_power_of_2_TM
  "../Preliminaries/Schoenhage_Strassen_Runtime_Preliminaries"
begin

fun evens_odds_tm :: "bool \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"evens_odds_tm b [] =1 return []"
| "evens_odds_tm True (x # xs) =1 do {
    rs \<leftarrow> evens_odds_tm False xs;
    return (x # rs)
  }"
| "evens_odds_tm False (x # xs) =1 evens_odds_tm True xs"

lemma val_evens_odds_tm[simp, val_simp]: "val (evens_odds_tm b xs) = evens_odds b xs"
  by (induction b xs rule: evens_odds_tm.induct; simp)

lemma time_evens_odds_tm_le: "time (evens_odds_tm b xs) \<le> length xs + 1"
  by (induction b xs rule: evens_odds_tm.induct; simp)

context int_lsbf_fermat
begin

definition multiply_with_power_of_2_tm :: "nat_lsbf \<Rightarrow> nat \<Rightarrow> nat_lsbf tm" where
"multiply_with_power_of_2_tm xs m =1 rotate_right_tm m xs"

lemma val_multiply_with_power_of_2_tm[simp, val_simp]:
  "val (multiply_with_power_of_2_tm xs m) = multiply_with_power_of_2 xs m"
  unfolding multiply_with_power_of_2_tm_def multiply_with_power_of_2_def by simp

lemma time_multiply_with_power_of_2_tm_le:
"time (multiply_with_power_of_2_tm xs m) \<le> 24 + 26 * max m (length xs)"
  unfolding multiply_with_power_of_2_tm_def tm_time_simps
  by (estimation estimate: time_rotate_right_tm_le) simp

definition divide_by_power_of_2_tm :: "nat_lsbf \<Rightarrow> nat \<Rightarrow> nat_lsbf tm" where
"divide_by_power_of_2_tm xs m =1 rotate_left_tm m xs"

lemma val_divide_by_power_of_2_tm[simp, val_simp]:
  "val (divide_by_power_of_2_tm xs m) = divide_by_power_of_2 xs m"
  unfolding divide_by_power_of_2_tm_def divide_by_power_of_2_def by simp

lemma time_divide_by_power_of_2_tm_le:
"time (divide_by_power_of_2_tm xs m) \<le> 24 + 26 * max m (length xs)"
  unfolding divide_by_power_of_2_tm_def tm_time_simps
  by (estimation estimate: time_rotate_left_tm_le) simp

definition add_fermat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"add_fermat_tm xs ys =1 do {
  zs \<leftarrow> xs +\<^sub>n\<^sub>t ys;
  lenzs \<leftarrow> length_tm zs;
  k1 \<leftarrow> k +\<^sub>t 1;
  powk \<leftarrow> 2 ^\<^sub>t k1;
  powk1 \<leftarrow> powk +\<^sub>t 1;
  b \<leftarrow> lenzs =\<^sub>t powk1;
  if b then do {
    zsr \<leftarrow> butlast_tm zs;
    inc_nat_tm zsr
  } else return zs
}"

lemma val_add_fermat_tm[simp, val_simp]: "val (add_fermat_tm xs ys) = add_fermat xs ys"
  unfolding add_fermat_tm_def add_fermat_def by (simp add: Let_def)

lemma time_add_fermat_tm_le: "time (add_fermat_tm xs ys) \<le> 13 + 7 * max (length xs) (length ys) + 28 * 2 ^ k"
proof -
  define m where "m = max (length xs) (length ys)"
  have "time (add_fermat_tm xs ys) =
    time (xs +\<^sub>n\<^sub>t ys) +
    time (length_tm (add_nat xs ys)) +
    time (k +\<^sub>t 1) +
    time (2 ^\<^sub>t (k + 1)) +
    time (2 ^ (k + 1) +\<^sub>t 1) +
    time (length (xs +\<^sub>n ys) =\<^sub>t 2 ^ (k + 1) + 1) +
    (if length (xs +\<^sub>n ys) = 2 ^ (k + 1) + 1
    then time (butlast_tm (xs +\<^sub>n ys)) +
         time (inc_nat_tm (butlast (xs +\<^sub>n ys)))
    else 0) + 1"
    unfolding add_fermat_tm_def tm_time_simps val_add_nat_tm val_plus_nat_tm
    val_power_nat_tm val_length_tm val_equal_nat_tm val_butlast_tm by simp
  also have "... \<le>
    (2 * m + 3) +
    (m + 2) +
    (2 ^ Suc k) +
    12 * 2 ^ Suc k +
    (2 ^ Suc k + 1) +
    (m + 2) +
    (3 * m + 4) + 1"
    apply (intro add_mono order.refl)
    subgoal apply (estimation estimate: time_add_nat_tm_le) unfolding m_def by simp
    subgoal
      unfolding time_length_tm
      apply (estimation estimate: length_add_nat_upper) unfolding m_def by simp
    subgoal using less_exp[of "Suc k"] by auto
    subgoal apply (estimation estimate: time_power_nat_tm_2_le) by simp
    subgoal by simp
    subgoal unfolding time_equal_nat_tm
      apply (estimation estimate: length_add_nat_upper)
      unfolding m_def[symmetric] by simp
    subgoal
      apply (estimation estimate: time_butlast_tm_le)
      apply (estimation estimate: time_inc_nat_tm_le)
      apply (intro if_leqI)
      subgoal
        apply (subst length_butlast)
        apply (estimation estimate: length_add_nat_upper)
        subgoal using length_add_nat_upper[of xs ys] by simp
        subgoal unfolding m_def[symmetric] by simp
        done
      subgoal by simp
      done
    done
  also have "... = 13 + 7 * m + 28 * 2 ^ k" by simp
  finally show ?thesis unfolding m_def .
qed

definition subtract_fermat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"subtract_fermat_tm xs ys =1 do {
  powk \<leftarrow> 2 ^\<^sub>t k;
  minusy \<leftarrow> multiply_with_power_of_2_tm ys powk;
  add_fermat_tm xs minusy
}"

lemma val_subtract_fermat_tm[simp, val_simp]: "val (subtract_fermat_tm xs ys) = subtract_fermat xs ys"
  unfolding subtract_fermat_tm_def subtract_fermat_def by simp

lemma time_subtract_fermat_tm_le: "time (subtract_fermat_tm xs ys) \<le>
  38 + 66 * 2 ^ k + 26 * length ys + 7 * max (length xs) (length ys)"
  unfolding subtract_fermat_tm_def tm_time_simps val_power_nat_tm
  val_multiply_with_power_of_2_tm
  apply (estimation estimate: time_power_nat_tm_2_le)
  apply (estimation estimate: time_multiply_with_power_of_2_tm_le)
  apply (estimation estimate: time_add_fermat_tm_le)
  apply (subst length_multiply_with_power_of_2)
  apply (estimation estimate: Nat_max_le_sum[of "2 ^ k"])
  by simp

definition reduce_tm :: "nat_lsbf \<Rightarrow> nat_lsbf tm" where
"reduce_tm xs =1 do {
  (ys, zs) \<leftarrow> split_tm xs;
  b \<leftarrow> zs \<le>\<^sub>n\<^sub>t ys;
  if b then ys -\<^sub>n\<^sub>t zs
  else do {
    kpow \<leftarrow> 2 ^\<^sub>t k;
    kpow1 \<leftarrow> kpow -\<^sub>t 1;
    zeros \<leftarrow> replicate_tm kpow1 False;
    a1 \<leftarrow> zeros @\<^sub>t [True];
    s \<leftarrow> (True # a1) +\<^sub>n\<^sub>t ys;
    s -\<^sub>n\<^sub>t zs
  }
}"

lemma val_reduce_tm[simp, val_simp]: "val (reduce_tm xs) = reduce xs"
  unfolding reduce_tm_def reduce_def by (simp split: prod.splits)

lemma time_reduce_tm_le: "time (reduce_tm xs) \<le> 155 + 85 * length xs + 46 * 2 ^ k"
proof -
  obtain ys zs where split_xs: "split xs = (ys, zs)" by fastforce
  note lens = length_split_le[OF split_xs]
  define b where "b = compare_nat zs ys"
  define kpow1 :: nat where "kpow1 = 2 ^ k - 1"
  define zeros where "zeros = replicate kpow1 False"
  define a1 where "a1 = zeros @ [True]"
  define s where "s = add_nat (True # a1) ys"

  note defs = b_def kpow1_def zeros_def a1_def s_def

  have len_a1: "length a1 = 2 ^ k"
    unfolding a1_def zeros_def kpow1_def by simp
  have len_s_le: "length s \<le> 2 ^ k + length xs + 2"
    unfolding s_def
    apply (estimation estimate: length_add_nat_upper)
    apply (estimation estimate: Nat_max_le_sum)
    apply (estimation estimate: lens(1))
    using len_a1 by simp

  have "time (reduce_tm xs) =
    time (split_tm xs) +
    time (zs \<le>\<^sub>n\<^sub>t ys) +
    (if b then time (ys -\<^sub>n\<^sub>t zs)
    else time (2 ^\<^sub>t k) +
      time ((2 ^ k) -\<^sub>t 1) +
      time (replicate_tm kpow1 False) +
      time (zeros @\<^sub>t [True]) +
      time ((True # a1) +\<^sub>n\<^sub>t ys) +
      time (s -\<^sub>n\<^sub>t zs)) + 1"
    unfolding reduce_tm_def tm_time_simps val_split_tm split_xs
    Product_Type.prod.case val_compare_nat_tm val_power_nat_tm val_replicate_tm
    val_minus_nat_tm val_append_tm val_add_nat_tm defs[symmetric] by simp
  also have "... \<le>
    (10 * length xs + 16) + (13 * length xs + 23) +
    (if b then (30 * length xs + 48)
    else 12 * 2 ^ k +
      2 +
      2 ^ k +
      2 ^ k +
      (2 * 2 ^ k + 2 * length xs + 5) +
      (30 * 2 ^ k + 60 * length xs + 108)) + 1"
    apply (intro add_mono if_prop_cong[where P = "(\<le>)"] order.refl refl)
    subgoal using time_split_tm_le by simp
    subgoal
      apply (estimation estimate: time_compare_nat_tm_le) using lens by simp
    subgoal
      apply (estimation estimate: time_subtract_nat_tm_le) using lens by simp
    subgoal using time_power_nat_tm_2_le by simp
    subgoal by simp
    subgoal unfolding time_replicate_tm kpow1_def by simp
    subgoal by (simp add: zeros_def kpow1_def)
    subgoal
      apply (estimation estimate: time_add_nat_tm_le)
      apply (estimation estimate: Nat_max_le_sum)
      apply (estimation estimate: lens(1))
      using len_a1 by simp
    subgoal
      apply (estimation estimate: time_subtract_nat_tm_le)
      apply (estimation estimate: Nat_max_le_sum)
      apply (estimation estimate: len_s_le)
      apply (estimation estimate: lens(2))
      by simp
    done
  also have "... \<le> 155 + 85 * length xs + 46 * 2 ^ k"
    by simp
  finally show ?thesis .
qed

function (domintros) from_nat_lsbf_tm :: "nat_lsbf \<Rightarrow> nat_lsbf tm" where
"from_nat_lsbf_tm xs =1 do {
  k1 \<leftarrow> k +\<^sub>t 1;
  powk \<leftarrow> 2 ^\<^sub>t k1;
  lenxs \<leftarrow> length_tm xs;
  b \<leftarrow> lenxs \<le>\<^sub>t powk;
  if b then fill_tm powk xs else do {
    xs1 \<leftarrow> take_tm powk xs;
    xs2 \<leftarrow> drop_tm powk xs;
    a \<leftarrow> xs1 +\<^sub>n\<^sub>t xs2;
    from_nat_lsbf_tm a
  }
}"
  by pat_completeness auto
termination
  apply (intro allI)
  subgoal for xs
    apply (induction xs rule: from_nat_lsbf.induct)
    subgoal for xs
      using from_nat_lsbf_tm.domintros[of xs] from_nat_lsbf_dom_termination
      by simp
    done
  done

declare from_nat_lsbf_tm.simps[simp del]

lemma val_from_nat_lsbf_tm[simp, val_simp]: "val (from_nat_lsbf_tm xs) = from_nat_lsbf xs"
proof (induction xs rule: from_nat_lsbf.induct)
  case (1 xs)
  then show ?case
    unfolding from_nat_lsbf_tm.simps[of xs] val_simps from_nat_lsbf.simps[of xs]
    unfolding Let_def by simp
qed

abbreviation e :: nat where "e \<equiv> 2 ^ (k + 1)"
lemma e_ge_1: "e \<ge> 1" by simp
lemma e_ge_2: "e \<ge> 2" by simp
lemma e_ge_4: "k > 0 \<Longrightarrow> e \<ge> 4" using power_increasing[of 2 "k + 1" "2::nat"] by simp

lemma time_from_nat_lsbf_tm_le_aux:
  assumes "xs' = add_nat (take e xs) (drop e xs)"
  shows "time (from_nat_lsbf_tm xs) \<le> 18 * e + 4 * length xs + 9 +
     (if length xs \<le> e then 0 else time (from_nat_lsbf_tm xs')) "
using assms proof (induction xs rule: from_nat_lsbf.induct)
  case (1 xs)

  have "time (from_nat_lsbf_tm xs) = time (k +\<^sub>t 1) +
    time (2 ^\<^sub>t (k + 1)) +
    time (length_tm xs) +
    time (length xs \<le>\<^sub>t e) +
    (if length xs \<le> e then time (fill_tm e xs)
    else time (take_tm e xs) +
      time (drop_tm e xs) +
      time (take e xs +\<^sub>n\<^sub>t drop e xs) +
      time (from_nat_lsbf_tm xs')) + 1"
    unfolding from_nat_lsbf_tm.simps[of xs] tm_time_simps val_simp 1(2)[symmetric]
    by simp
  also have "... \<le> e +
    (12 * e) +
    (length xs + 1) +
    (2 * e + 2) +
    (if length xs \<le> e then 3 * (e + length xs) + 5
    else (e + 1) +
      (e + 1) +
      (2 * length xs + 3) +
      time (from_nat_lsbf_tm xs')) + 1"
    apply (intro add_mono order.refl if_prop_cong[where P = "(\<le>)"] refl)
    subgoal unfolding time_plus_nat_tm 1(2) using less_exp[of "k + 1"] by simp
    subgoal unfolding 1(2) by (rule time_power_nat_tm_2_le)
    subgoal by simp
    subgoal apply (estimation estimate: time_less_eq_nat_tm_le) by simp
    subgoal apply (estimation estimate: time_fill_tm_le) by simp
    subgoal apply (estimation estimate: time_take_tm_le) by simp
    subgoal apply (estimation estimate: time_drop_tm_le) by simp
    subgoal apply (estimation estimate: time_add_nat_tm_le) by simp
    done
  also have "... = 15 * e + length xs + 4 +
    (if length xs \<le> e then 3 * e + 3 * length xs + 5
    else 2 * e + 2 * length xs + 5 +
      time (from_nat_lsbf_tm xs'))"
    by simp
  also have "... \<le> 18 * e + 4 * length xs + 9 +
      (if length xs \<le> e then 0 else time (from_nat_lsbf_tm xs'))"
    by (cases "length xs \<le> e"; simp)
  finally show ?case .
qed

lemma time_from_nat_lsbf_tm_le_aux':
  assumes "xs' = add_nat (take e xs) (drop e xs)"
  shows "time (from_nat_lsbf_tm xs) \<le> 66 * e + 4 * length xs + 35 +
      (if length xs \<le> e + 1 then 0 else time (from_nat_lsbf_tm xs'))"
proof -
  consider "length xs \<le> e" | "length xs = e + 1" | "length xs \<ge> e + 2"
    by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using time_from_nat_lsbf_tm_le_aux[OF assms] by simp
  next
    case 2
    consider ("2_1") "length xs' \<le> e" | ("2_2") "xs' = replicate e False @ [True]"
      using add_take_drop_carry_aux[OF assms 2 e_ge_1] by argo
    then show ?thesis
    proof cases
      case "2_1"
      then have "time (from_nat_lsbf_tm xs') \<le> 22 * e + 9"
        using time_from_nat_lsbf_tm_le_aux[OF refl, of xs']
        by simp
      then have "time (from_nat_lsbf_tm xs) \<le> 44 * e + 22"
        using time_from_nat_lsbf_tm_le_aux[OF assms] 2
        by simp
      then show ?thesis by simp
    next
      case "2_2"
      then have len_xs': "length xs' = e + 1" by simp
      define xs'' where "xs'' = add_nat (take e xs') (drop e xs')"
      from "2_2" have "take e xs' = replicate e False" "drop e xs' = [True]" by simp_all
      then have "xs'' = True # replicate (e - 1) False"
        unfolding add_nat_def xs''_def using add_carry.simps
        by (metis Suc_eq_plus1 Suc_le_D add_carry_True_inc_nat diff_Suc_1 inc_nat.simps(1) inc_nat.simps(2) le_refl replicate_Suc self_le_ge2_pow)
      then have len_xs'': "length xs'' = e" using e_ge_1 by simp
      then have "time (from_nat_lsbf_tm xs'') \<le> 22 * e + 9"
        using time_from_nat_lsbf_tm_le_aux[OF refl, of xs''] by simp
      then have "time (from_nat_lsbf_tm xs') \<le> 44 * e + 22"
        using time_from_nat_lsbf_tm_le_aux[OF xs''_def] len_xs'
        by simp
      then have "time (from_nat_lsbf_tm xs) \<le> 66 * e + 35"
        using time_from_nat_lsbf_tm_le_aux[OF assms] 2
        by simp
      then show ?thesis by simp
    qed
  next
    case 3
    then show ?thesis
      using time_from_nat_lsbf_tm_le_aux[OF assms] by simp
  qed
qed

function time_from_nat_lsbf_tm_bound where
"time_from_nat_lsbf_tm_bound l = 88 * e + 4 * l + 48 +
    (if l \<le> 2 * e then 0 else time_from_nat_lsbf_tm_bound (l - (e - 1)))"
  by pat_completeness auto
termination
  apply (relation "Wellfounded.measure id")
  subgoal by simp
  subgoal for l unfolding in_measure id_def using e_ge_2 by linarith
  done
declare time_from_nat_lsbf_tm_bound.simps[simp del]

lemma time_from_nat_lsbf_tm_le_bound:
  assumes "length xs \<le> l"
  shows "time (from_nat_lsbf_tm xs) \<le> time_from_nat_lsbf_tm_bound l"
using assms proof (induction l arbitrary: xs rule: time_from_nat_lsbf_tm_bound.induct)
  case (1 l)
  consider "length xs \<le> e + 1" | "length xs \<ge> e + 2 \<and> length xs \<le> 2 * e" | "length xs > 2 * e"
    by linarith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      unfolding time_from_nat_lsbf_tm_bound.simps[of l]
      using time_from_nat_lsbf_tm_le_aux'[OF refl, of xs]
      by simp
  next
    case 2
    define xs' where "xs' = add_nat (take e xs) (drop e xs)"
    have "length xs' \<le> e + 1"
      unfolding xs'_def
      apply (estimation estimate: length_add_nat_upper)  
      using 2 by auto
    then have "time (from_nat_lsbf_tm xs') \<le> 70 * e + 39"
      using time_from_nat_lsbf_tm_le_aux'[OF refl, of xs'] by auto
    then have "time (from_nat_lsbf_tm xs) \<le> 88 * e + 4 * length xs + 48"
      using time_from_nat_lsbf_tm_le_aux[OF xs'_def] 2 by auto
    then show ?thesis
      unfolding time_from_nat_lsbf_tm_bound.simps[of l] using 2 1 by linarith
  next
    case 3
    define xs' where "xs' = add_nat (take e xs) (drop e xs)"
    have "length (take e xs) = e" "length (drop e xs) = length xs - e"
      using 3 by simp_all
    then have "max (length (take e xs)) (length (drop e xs)) = length xs - e"
      using 3 by linarith
    then have "length xs' \<le> length xs - e + 1"
      unfolding xs'_def
      using length_add_nat_upper[of "take e xs" "drop e xs"] by argo
    then have len_xs': "length xs' \<le> l - (e - 1)" using "1.prems" e_ge_1 3 by linarith
    
    have ih: "time (from_nat_lsbf_tm xs') \<le> time_from_nat_lsbf_tm_bound (l - (e - 1))"
      apply (intro "1.IH")
      subgoal using "1.prems" 3 by linarith
      subgoal by (fact len_xs')
      done
    then have "time (from_nat_lsbf_tm xs) \<le> 18 * e + 4 * length xs + 9 +
        time_from_nat_lsbf_tm_bound (l - (e - 1))"
      using time_from_nat_lsbf_tm_le_aux[OF xs'_def] 3 by simp
    then show ?thesis
      unfolding time_from_nat_lsbf_tm_bound.simps[of l]
      using 3 "1.prems" by simp
  qed
qed

lemma time_from_nat_lsbf_tm_bound_closed:
  assumes "x \<le> 2 * e"
  assumes "x \<ge> e + 2"
  shows "time_from_nat_lsbf_tm_bound (x + l * (e - 1)) =
    (l + 1) * (88 * e + 4 * x + 48) + 4 * (\<Sum> {0..l}) * (e - 1)"
proof (induction l)
  case 0
  then show ?case
    unfolding time_from_nat_lsbf_tm_bound.simps[of "x + 0 * (e - 1)"]
    using assms by simp
next
  case (Suc l)
  have "x + Suc l * (e - 1) > 2 * e"
    using assms e_ge_1 by simp
  then have "time_from_nat_lsbf_tm_bound (x + Suc l * (e - 1)) =
    88 * e + 4 * (x + Suc l * (e - 1)) + 48 +
    time_from_nat_lsbf_tm_bound (x + Suc l * (e - 1) - (e - 1))" (is "_ = ?t + ?r")
    unfolding time_from_nat_lsbf_tm_bound.simps[of "x + Suc l * (e - 1)"]
    apply (intro_cong "[cong_tag_2 (+)]" more: refl)
    using iffD2[OF not_le] by metis
  also have "?r = time_from_nat_lsbf_tm_bound (x + l * (e - 1))"
    apply (intro arg_cong[where f = time_from_nat_lsbf_tm_bound])
    using assms by simp
  also have "... = (l + 1) * (88 * e + 4 * x + 48) + 4 * (\<Sum> {0..l}) * (e - 1)"
    (is "... = ?r'")
    by (rule Suc.IH)
  also have "?t + ?r' = (Suc l + 1) * (88 * e + 4 * x + 48) + 4 * \<Sum> {0..Suc l} * (e - 1)"
    by (simp add: add_mult_distrib)
  finally show ?case .
qed

lemma time_from_nat_lsbf_tm_le:
  assumes "e \<ge> 4"
  assumes "length xs \<le> c * e"
  shows "time (from_nat_lsbf_tm xs) \<le> (288 * c + 144) + (96 + 192 * c + 8 * c * c) * e"
proof (cases "length xs \<le> 2 * e")
  case True
  have "time (from_nat_lsbf_tm xs) \<le> time_from_nat_lsbf_tm_bound (length xs)"
    by (intro time_from_nat_lsbf_tm_le_bound order.refl)
  also have "... = 88 * e + 4 * length xs + 48"
    unfolding time_from_nat_lsbf_tm_bound.simps[of "length xs"]
    using True by simp
  also have "... \<le> 96 * e + 48"
    using True by auto
  also have "... \<le> (96 + 192 * c + 8 * c * c) * e + (288 * c + 144)"
    apply (intro add_mono mult_le_mono order.refl)
    by simp_all
  finally show ?thesis by simp
next
  case False
  define x' where "x' = length xs mod (e - 1)"
  define y' where "y' = length xs div (e - 1)"
  from x'_def y'_def have len_xs': "length xs = y' * (e - 1) + x'" by presburger
  from False have "length xs \<ge> 2 * (e - 1)" by simp
  then have "y' \<ge> 2" unfolding y'_def
    by (metis add_gr_0 e_ge_1 even_power gcd_nat.eq_iff le_neq_implies_less less_eq_div_iff_mult_less_eq odd_one odd_pos zero_less_diff)
  define x where "x = (if x' \<le> 2 then x' + 2 * (e - 1) else x' + (e - 1))"
  define y where "y = (if x' \<le> 2 then y' - 2 else y' - 1)"
  have len_xs: "length xs = x + y * (e - 1)"
    unfolding len_xs'
    apply (cases "x' \<le> 2")
    subgoal unfolding x_def y_def using \<open>y' \<ge> 2\<close> by (simp add: diff_mult_distrib)
    subgoal premises prems
    proof -
      have "y' * (e - 1) + x' = (y' - 1 + 1) * (e - 1) + x'"
        using \<open>y' \<ge> 2\<close> by simp
      also have "... = x' + (e - 1) + (y' - 1) * (e - 1)"
        by (simp only: add_mult_distrib)
      also have "... = x + y * (e - 1)"
        unfolding x_def y_def using prems by simp
      finally show ?thesis .
    qed
    done
  have x_lower: "x \<ge> e + 2"
  proof (cases "x' \<le> 2")
    case True
    then show ?thesis unfolding x_def using assms by simp
  next
    case False
    then show ?thesis unfolding x_def by simp
  qed
  have "e - 1 > 0" using e_ge_2 by linarith
  have x'_upper: "x' < e - 1"
    using x'_def pos_mod_bound[of \<open>e - 1\<close>] \<open>e - 1 > 0\<close> less_eq_Suc_le mod_less_divisor by blast
  have x_upper: "x \<le> 2 * e"
  proof (cases "x' \<le> 2")
    case True
    then show ?thesis unfolding x_def using x'_upper by simp
  next
    case False
    then show ?thesis unfolding x_def using x'_upper by simp
  qed
  have "y \<le> y'" unfolding y_def using \<open>y' \<ge> 2\<close> by simp
  also have "... \<le> (c * e) div (e - 1)"
    unfolding y'_def using assms(2) div_le_mono by simp
  also have "... = (c * ((e - 1) + 1)) div (e - 1)"
    using e_ge_1 by simp
  also have "... = c + c div (e - 1)"
    unfolding add_mult_distrib2 using div_mult_self3[of "e - 1" c c]
    using \<open>0 < e - 1\<close> by simp
  also have "... \<le> 2 * c" using div_le_dividend by simp
  finally have "y \<le> 2 * c" .
  have "y * (e - 1) \<le> y' * (e - 1)"
    unfolding y_def using \<open>y' \<ge> 2\<close> by simp
  also have "... \<le> length xs" unfolding y'_def by simp
  finally have ye_le: "y * (e - 1) \<le> length xs" .
  have "time (from_nat_lsbf_tm xs) \<le> time_from_nat_lsbf_tm_bound (length xs)"
    by (intro time_from_nat_lsbf_tm_le_bound order.refl)
  also have "... = (y + 1) * (88 * e + 4 * x + 48) + 4 * \<Sum> {(0::nat)..y} * (e - 1)"
    unfolding len_xs
    by (intro time_from_nat_lsbf_tm_bound_closed x_lower x_upper)
  also have "... \<le> (y + 1) * (88 * e + 4 * x + 48) + 4 * y * y * (e - 1)"
    using euler_sum_bound[of y] atMost_atLeast0[of y] by simp
  also have "... \<le> (y + 1) * (96 * e + 48) + 4 * y * y * (e - 1)"
    by (estimation estimate: x_upper, simp)
  also have "... = (y + 1) * (96 * (e - 1) + 144) + 4 * y * y * (e - 1)"
    using e_ge_1 by (simp add: diff_mult_distrib2 add.commute)
  also have "... = 96 * (e - 1) + 144 * (y + 1) + 96 * y * (e - 1) + 4 * y * y * (e - 1)"
    by (simp add: add_mult_distrib2)
  also have "... = 96 * (e - 1) + 144 * y + 144 + (96 + 4 * y) * (y * (e - 1))"
    by (simp add: add_mult_distrib)
  also have "... \<le> 96 * length xs + 144 * (2 * c) + 144 + (96 + 4 * (2 * c)) * length xs"
    apply (intro add_mono order.refl mult_le_mono ye_le \<open>y \<le> 2 * c\<close>)
    subgoal using False by simp
    done
  also have "... = (288 * c + 144) + (192 + 8 * c) * length xs"
    by (simp add: add_mult_distrib)
  also have "... \<le> (288 * c + 144) + (192 * c + 8 * c * c) * e"
    apply (estimation estimate: assms(2))
    by (simp add: add_mult_distrib)
  also have "... \<le> (288 * c + 144) + (96 + 192 * c + 8 * c * c) * e"
    by (intro add_mono mult_le_mono order.refl; simp)
  finally show ?thesis .
qed

fun fft_combine_b_c_aux_tm where
"fft_combine_b_c_aux_tm f g l (revs, s) [] [] =1 rev_tm revs"
| "fft_combine_b_c_aux_tm f g l (revs, s) (b # bs) (c # cs) =1 do {
    c_shifted \<leftarrow> g c s;
    r \<leftarrow> f b c_shifted;
    s_new \<leftarrow> s +\<^sub>t l;
    k1 \<leftarrow> k +\<^sub>t 1;
    powk1 \<leftarrow> 2 ^\<^sub>t k1;
    s_new_mod \<leftarrow> s_new mod\<^sub>t powk1;
    fft_combine_b_c_aux_tm f g l (r # revs, s_new_mod) bs cs
  }"
| "fft_combine_b_c_aux_tm _ _ _ _ _ _ = undefined"

lemma val_fft_combine_b_c_aux_tm[simp, val_simp]:
  assumes "length bs = length cs"
  shows "val (fft_combine_b_c_aux_tm f g l (revs, s) bs cs) =
    fft_combine_b_c_aux (\<lambda>x y. val (f x y)) (\<lambda>x y. val (g x y)) l (revs, s) bs cs"
  using assms apply (induction bs arbitrary: cs revs s)
  subgoal for cs revs s by (cases cs; simp)
  subgoal for b bs cs revs s by (cases cs; simp)
  done

lemma time_fft_combine_b_c_aux_tm_le:
  assumes "length bs = length cs"
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> length b = e"
  assumes "\<And>c. c \<in> set cs \<Longrightarrow> length c = e"
  assumes "\<And>xs ys. time (f xs ys) \<le> 38 + 66 * 2 ^ k + 26 * length ys + 7 * max (length xs) (length ys)"
  assumes "s < e"
  assumes "g = multiply_with_power_of_2_tm \<or> g = divide_by_power_of_2_tm"
  shows "time (fft_combine_b_c_aux_tm f g l (revs, s) bs cs) \<le> length revs + 3 + length bs * (72 + 116 * e + 8 * l)"
  using assms
proof (induction bs arbitrary: revs s cs)
  case Nil
  then have "cs = []" by simp
  then have "time (fft_combine_b_c_aux_tm f g l (revs, s) [] cs) = length revs + 3" by simp
  then show ?case by simp
next
  case (Cons b bs)
  from Cons.prems have len_b: "length b = e" by simp
  from Cons.prems(1) obtain c cs' where "cs = c # cs'" by (metis length_Suc_conv)
  with Cons.prems have len_c: "length c = e" by simp
  have sl_less: "(s + l) mod e < e" using e_ge_1 mod_less_divisor[OF iffD2[OF less_eq_Suc_le, of 0 e]] by simp
  have ih: "time (fft_combine_b_c_aux_tm f g l (revs', s') bs cs') \<le>
      length revs' + 3 + length bs * (72 + 116 * e + 8 * l)"
    if "s' < e" for revs' s'
    apply (intro Cons.IH)
    subgoal using Cons.prems \<open>cs = c # cs'\<close> by simp
    subgoal using Cons.prems by simp
    subgoal using Cons.prems \<open>cs = c # cs'\<close> by simp
    subgoal by (rule Cons.prems)
    subgoal by (fact that)
    subgoal by (rule Cons.prems)
    done
  have val_gcs: "val (g c s) = multiply_with_power_of_2 c s \<or> val (g c s) = divide_by_power_of_2 c s"
    using Cons.prems by fastforce
  from \<open>cs = c # cs'\<close> have "time (fft_combine_b_c_aux_tm f g l (revs, s) (b # bs) cs) =
      time (g c s) +
      time (f b (val (g c s))) +
      time (2 ^\<^sub>t (k + 1)) +
      time ((s + l) mod\<^sub>t e) +
      time (fft_combine_b_c_aux_tm f g l (val (f b (val (g c s))) # revs, (s + l) mod e) bs cs') +
      s + k + 3"
    by (simp del: One_nat_def)
  also have "... \<le>
      (24 + 26 * max s (length c)) +
      (38 + 33 * e + 26 * length c + 7 * max (length b) (length c)) +
      12 * e + (8 * (s + l) + 2 * e + 7) +
      (length revs + 4 + length bs * (72 + 116 * e + 8 * l)) + s + k + 3" (is "... \<le> ?t + k + 3")
    apply (intro add_mono order.refl)
    subgoal
      using time_multiply_with_power_of_2_tm_le[of c s]
      using time_divide_by_power_of_2_tm_le[of c s]
      using Cons.prems by fastforce
    subgoal
      using val_gcs Cons.prems(4)[of b "val (g c s)"]
      using length_multiply_with_power_of_2[of c s] length_divide_by_power_of_2[of c s]
      by auto
    subgoal by (rule time_power_nat_tm_2_le)
    subgoal by (rule time_mod_nat_tm_le)
    subgoal apply (estimation estimate: ih[OF sl_less]) by simp
    done
  also have "?t + k + 3 = ?t + (k + 3)" by (rule add.assoc[of ?t k 3])
  also have "... \<le> ?t + e + 2"
    using less_exp[of k] iffD1[OF less_eq_Suc_le, OF less_exp[of k]] by simp
  also have "?t + e + 2 = 75 + 107 * e + 9 * s + 8 * l + length revs + length bs * (72 + 116 * e + 8 * l)"
    unfolding len_b len_c using \<open>s < e\<close> by simp
  also have "... \<le> 75 + 116 * e + 8 * l + length revs + length bs * (72 + 116 * e + 8 * l)"
    using \<open>s < e\<close> by simp
  also have "... = length revs + 3 + length (b # bs) * (72 + 116 * e + 8 * l)"
    by simp
  finally show ?case .
qed

fun fft_ifft_combine_b_c_add_tm :: "bool \<Rightarrow> nat \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list tm" where
"fft_ifft_combine_b_c_add_tm True l bs cs =1 fft_combine_b_c_aux_tm add_fermat_tm divide_by_power_of_2_tm l ([], 0) bs cs"
| "fft_ifft_combine_b_c_add_tm False l bs cs =1 fft_combine_b_c_aux_tm add_fermat_tm multiply_with_power_of_2_tm l ([], 0) bs cs"

fun fft_ifft_combine_b_c_subtract_tm :: "bool \<Rightarrow> nat \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list tm" where
"fft_ifft_combine_b_c_subtract_tm True l bs cs =1 fft_combine_b_c_aux_tm subtract_fermat_tm divide_by_power_of_2_tm l ([], 0) bs cs"
| "fft_ifft_combine_b_c_subtract_tm False l bs cs =1 fft_combine_b_c_aux_tm subtract_fermat_tm multiply_with_power_of_2_tm l ([], 0) bs cs"

lemma val_fft_ifft_combine_b_c_add_tm[simp, val_simp]:
  assumes "length bs = length cs"
  shows "val (fft_ifft_combine_b_c_add_tm it l bs cs) = fft_ifft_combine_b_c_add it l bs cs"
  by (cases it; simp add: assms)

lemma val_fft_ifft_combine_b_c_subtract_tm[simp, val_simp]:
  assumes "length bs = length cs"
  shows "val (fft_ifft_combine_b_c_subtract_tm it l bs cs) = fft_ifft_combine_b_c_subtract it l bs cs"
  by (cases it; simp add: assms)

lemma time_fft_combine_b_c_add_tm_le:
  assumes "length bs = length cs"
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> length b = e"
  assumes "\<And>c. c \<in> set cs \<Longrightarrow> length c = e"
  shows "time (fft_ifft_combine_b_c_add_tm it l bs cs) \<le> 4 + length bs * (72 + 116 * e + 8 * l)"
proof -
  have
    "time (fft_combine_b_c_aux_tm add_fermat_tm g l ([], 0) bs cs)
      \<le> length ([] :: nat_lsbf list) + 3 + length bs * (72 + 116 * e + 8 * l)"
    if "g = multiply_with_power_of_2_tm \<or> g = divide_by_power_of_2_tm" for g
    apply (intro time_fft_combine_b_c_aux_tm_le)
    subgoal by (intro assms)
    subgoal using assms by simp
    subgoal using assms by simp
    subgoal by (estimation estimate: time_add_fermat_tm_le; simp)
    subgoal using e_ge_1 by simp
    subgoal using that .
    done
  then show ?thesis by (cases it; simp)
qed

lemma time_fft_combine_b_c_subtract_tm_le:
  assumes "length bs = length cs"
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> length b = e"
  assumes "\<And>c. c \<in> set cs \<Longrightarrow> length c = e"
  shows "time (fft_ifft_combine_b_c_subtract_tm it l bs cs) \<le> 4 + length bs * (72 + 116 * e + 8 * l)"
proof -
  have
    "time (fft_combine_b_c_aux_tm subtract_fermat_tm g l ([], 0) bs cs)
      \<le> length ([] :: nat_lsbf list) + 3 + length bs * (72 + 116 * e + 8 * l)"
    if "g = multiply_with_power_of_2_tm \<or> g = divide_by_power_of_2_tm" for g
    apply (intro time_fft_combine_b_c_aux_tm_le)
    subgoal by (intro assms)
    subgoal using assms by simp
    subgoal using assms by simp
    subgoal by (estimation estimate: time_subtract_fermat_tm_le; simp)
    subgoal using e_ge_1 by simp
    subgoal using that .
    done
  then show ?thesis by (cases it; simp)
qed

fun fft_ifft_tm where
"fft_ifft_tm it l [] =1 return []"
| "fft_ifft_tm it l [x] =1 return [x]"
| "fft_ifft_tm it l [x, y] =1 do {
    r1 \<leftarrow> add_fermat_tm x y;
    r2 \<leftarrow> subtract_fermat_tm x y;
    return [r1, r2]
  }"
| "fft_ifft_tm it l a =1 do {
    nums1 \<leftarrow> evens_odds_tm True a;
    nums2 \<leftarrow> evens_odds_tm False a;
    b \<leftarrow> fft_ifft_tm it (2 * l) nums1;
    c \<leftarrow> fft_ifft_tm it (2 * l) nums2;
    g \<leftarrow> fft_ifft_combine_b_c_add_tm it l b c;
    h \<leftarrow> fft_ifft_combine_b_c_subtract_tm it l b c;
    g @\<^sub>t h
  }"

lemma val_fft_ifft_tm[simp, val_simp]: "length a = 2 ^ m \<Longrightarrow> val (fft_ifft_tm it l a) = fft_ifft it l a"
proof (induction it l a arbitrary: m rule: fft_ifft.induct)
  case (1 it l)
  then show ?case by simp
next
  case (2 it l x)
  then show ?case by simp
next
  case (3 it l x y)
  then show ?case by simp
next
  case (4 it l a1 a2 a3 as)
  interpret fft_context k it l m a1 a2 a3 as
    apply unfold_locales using 4 by simp
  obtain m' where "m = Suc (Suc m')" using nat_le_iff_add e_ge_2 by auto
  have len_eo: "length (evens_odds b local.a) = 2 ^ Suc m'" for b
    apply (cases b)
    subgoal using length_evens_odds(1)[of local.a] "4.prems" unfolding a_def[symmetric] \<open>m = Suc (Suc m')\<close>
      by simp
    subgoal using length_evens_odds(2)[of local.a] "4.prems" unfolding a_def[symmetric] \<open>m = Suc (Suc m')\<close>
      by simp
    done
  have len_eq: "length (fft_ifft it (2 * l) (evens_odds True local.a)) = length (fft_ifft it (2 * l) (evens_odds False local.a))"
    using length_fft_ifft[OF len_eo] by simp

  have ih1: "val (fft_ifft_tm it (2 * l) (evens_odds True local.a)) = fft_ifft it (2 * l) (evens_odds True local.a)"
    using len_eo by (intro "4.IH"[OF _ refl], subst a_def[symmetric], intro refl, fastforce)
  have ih2: "val (fft_ifft_tm it (2 * l) (evens_odds False local.a)) = fft_ifft it (2 * l) (evens_odds False local.a)"
    by (intro "4.IH"(2)[OF refl _ refl len_eo], subst a_def[symmetric], rule refl)
  
  show ?case unfolding fft_ifft_tm.simps fft_ifft.simps unfolding a_def[symmetric]
    unfolding Let_def val_simp ih1 ih2
    unfolding val_fft_ifft_combine_b_c_add_tm[OF len_eq] val_fft_ifft_combine_b_c_subtract_tm[OF len_eq]
    by (rule refl)
qed

lemma time_fft_ifft_tm_le_aux:
  assumes "\<And>x. x \<in> set a \<Longrightarrow> length x = e"
  assumes "length a = 2 ^ m"
  shows "time (fft_ifft_tm it l a) \<le> 2 ^ (m - 1) * (52 + 87 * e) + (m - 1) * 2 ^ m * (76 + 116 * e) + (\<Sum>i \<leftarrow> [0..<m-1]. 2 ^ i) * (8 * 2 ^ m * l + 13)"
using assms proof (induction it l a arbitrary: m rule: fft_ifft.induct)
  case (1 it l)
  then show ?case by simp
next
  case (2 it l x)
  then show ?case by simp
next
  case (3 it l x y)
  have "time (fft_ifft_tm it l [x, y]) \<le> 52 + 87 * e"
    unfolding fft_ifft_tm.simps tm_time_simps
    apply (estimation estimate: time_add_fermat_tm_le)
    apply (estimation estimate: time_subtract_fermat_tm_le)
    by (simp add: 3)
  also have "... \<le> 2 ^ (m - Suc 0) * (52 + 87 * e)" by simp
  finally show ?case by simp
next
  case (4 it l a1 a2 a3 as)
  interpret fft_context k it l m a1 a2 a3 as
    apply unfold_locales using 4 by simp
  obtain m' where "m = Suc (Suc m')" using nat_le_iff_add e_ge_2 by auto
  then have "Suc m' = m - 1" by simp
  have len_eo: "length (evens_odds b local.a) = 2 ^ Suc m'" for b
    apply (cases b)
    subgoal using length_evens_odds(1)[of local.a] length_a \<open>m = Suc (Suc m')\<close>
      by simp
    subgoal using length_evens_odds(2)[of local.a] length_a \<open>m = Suc (Suc m')\<close>
      by simp
    done
  have len_eo_nth: "length x = e" if "x \<in> set (evens_odds b local.a)" for b x
    using set_evens_odds[of b local.a] that "4.prems" unfolding a_def[symmetric] by auto
  define ih_bound where "ih_bound = 2 ^ (Suc m' - 1) * (52 + 87 * e) + (Suc m' - 1) * 2 ^ Suc m' * (76 + 116 * e) +
      (\<Sum>i \<leftarrow> [0..<Suc m' - 1]. 2 ^ i) * (8 * 2 ^ Suc m' * (2 * l) + 13)"
  have ih1: "time (fft_ifft_tm it (2 * l) nums1) \<le> ih_bound"
    unfolding a_def nums1_def ih_bound_def
    apply (intro "4.IH"(1)[OF refl refl, of "Suc m'"])
    subgoal for x unfolding a_def[symmetric] using len_eo_nth by simp
    subgoal unfolding a_def[symmetric] by (rule len_eo)
    done
  have ih2: "time (fft_ifft_tm it (2 * l) nums2) \<le> ih_bound"
    unfolding a_def nums2_def ih_bound_def
    apply (intro "4.IH"(2)[OF refl refl refl, of "Suc m'"])
    subgoal for x unfolding a_def[symmetric] using len_eo_nth by simp
    subgoal unfolding a_def[symmetric] by (rule len_eo)
    done

  have val_fft1: "val (fft_ifft_tm it (2 * l) nums1) = fft_ifft it (2 * l) nums1"
    apply (intro val_fft_ifft_tm[of _ "Suc m'"])
    unfolding nums1_def by (rule len_eo)
  have val_fft2: "val (fft_ifft_tm it (2 * l) nums2) = fft_ifft it (2 * l) nums2"
    apply (intro val_fft_ifft_tm[of _ "Suc m'"])
    unfolding nums2_def by (rule len_eo)
  from length_b length_c have len_bc: "length b = length c" by simp
  have val_add: "val (fft_ifft_combine_b_c_add_tm it l b c) = fft_ifft_combine_b_c_add it l b c"
    by (rule val_fft_ifft_combine_b_c_add_tm[OF len_bc])
  have val_sub: "val (fft_ifft_combine_b_c_subtract_tm it l b c) = fft_ifft_combine_b_c_subtract it l b c"
    by (rule val_fft_ifft_combine_b_c_subtract_tm[OF len_bc])

  have nums_carrier: "set nums1 \<subseteq> fermat_non_unique_carrier" "set nums2 \<subseteq> fermat_non_unique_carrier"
    using "4.prems" unfolding a_def[symmetric] nums1_def nums2_def using set_evens_odds by fast+

  have b_carrier: "set b \<subseteq> fermat_non_unique_carrier"
    unfolding b_def apply (intro fft_ifft_carrier nums_carrier) unfolding nums1_def len_eo by fast
  have c_carrier: "set c \<subseteq> fermat_non_unique_carrier"
    unfolding c_def apply (intro fft_ifft_carrier nums_carrier) unfolding nums2_def len_eo by fast

  have "time (fft_ifft_tm it l (a1 # a2 # a3 # as)) =
      time (evens_odds_tm True local.a) +
      time (evens_odds_tm False local.a) +
      time (fft_ifft_tm it (2 * l) nums1) +
      time (fft_ifft_tm it (2 * l) nums2) +
      time (fft_ifft_combine_b_c_add_tm it l b c) +
      time (fft_ifft_combine_b_c_subtract_tm it l b c) +
      time (g @\<^sub>t h) + 1"
    unfolding fft_ifft_tm.simps tm_time_simps val_evens_odds_tm
    unfolding defs[symmetric] val_fft1 val_fft2 val_add val_sub
    by simp
  also have "... \<le>
      (length local.a + 1) +
      (length local.a + 1) +
      ih_bound +
      ih_bound +
      (4 + length b * (72 + 116 * e + 8 * l)) +
      (4 + length b * (72 + 116 * e + 8 * l)) +
      (length g + 1) + 1"
    apply (intro add_mono order.refl)
    subgoal by (rule time_evens_odds_tm_le)
    subgoal by (rule time_evens_odds_tm_le)
    subgoal using ih1 .
    subgoal using ih2 .
    subgoal
      apply (intro time_fft_combine_b_c_add_tm_le[OF len_bc])
      subgoal using b_carrier unfolding fermat_non_unique_carrier_def by auto
      subgoal using c_carrier unfolding fermat_non_unique_carrier_def by auto
      done
    subgoal
      apply (intro time_fft_combine_b_c_subtract_tm_le[OF len_bc])
      subgoal using b_carrier unfolding fermat_non_unique_carrier_def by auto
      subgoal using c_carrier unfolding fermat_non_unique_carrier_def by auto
      done
    subgoal by simp
    done
  also have "... = 2 * length local.a + 2 * ih_bound + (2 * length b) * (72 + 116 * e + 8 * l) + length g + 12"
    by simp
  also have "... = 5 * 2 ^ Suc m' + 2 * ih_bound + 2 * 2 ^ Suc m' * (72 + 116 * e + 8 * l) + 12"
    unfolding length_a length_b length_g \<open>m = Suc (Suc m')\<close> by simp
  also have "... \<le> 8 * 2 ^ Suc m' + 2 * ih_bound + 2 * 2 ^ Suc m' * (72 + 116 * e + 8 * l) + 13"
    by simp
  also have "... = 2 * ih_bound + 2 ^ m * (76 + 116 * e + 8 * l) + 13"
    unfolding \<open>m = Suc (Suc m')\<close> by (simp add: add_mult_distrib2)
  also have "... = 2 * ih_bound + 2 ^ m * (76 + 116 * e) + 8 * 2 ^ m * l + 13"
    by (simp add: add_mult_distrib2)
  also have "... = (2 * 2 ^ (Suc m' - 1)) * (52 + 87 * e) +
      (Suc m' - 1) * (2 * 2 ^ Suc m') * (76 + 116 * e) +
      2 * (\<Sum>i \<leftarrow> [0..<Suc m' - 1]. 2 ^ i) * (8 * 2 ^ Suc m' * (2 * l) + 13) +
      2 ^ m * (76 + 116 * e) + 8 * 2 ^ m * l + 13"
    unfolding ih_bound_def by simp
  also have "... = 2 ^ (m - 1) * (52 + 87 * e) +
      (Suc m' - 1) * 2 ^ m * (76 + 116 * e) +
      2 * (\<Sum>i \<leftarrow> [0..<Suc m' - 1]. 2 ^ i) * (8 * 2 ^ m * l + 13) +
      2 ^ m * (76 + 116 * e) + 8 * 2 ^ m * l + 13"
    apply (intro arg_cong2[where f = "(+)"] refl)
    subgoal unfolding \<open>m = Suc (Suc m')\<close> by simp
    subgoal unfolding \<open>m = Suc (Suc m')\<close> by simp
    subgoal unfolding \<open>m = Suc (Suc m')\<close> by simp
    done
  also have "... = 2 ^ (m - 1) * (52 + 87 * e) +
      ((Suc m' - 1) + 1) * 2 ^ m * (76 + 116 * e) +
      (2 * (\<Sum>i \<leftarrow> [0..<Suc m' - 1]. 2 ^ i) + 1) * (8 * 2 ^ m * l + 13)"
    by (simp add: add_mult_distrib)
  also have "... = 2 ^ (m - 1) * (52 + 87 * e) +
      (m - 1) * 2 ^ m * (76 + 116 * e) +
      (\<Sum>i \<leftarrow> [0..<Suc m']. 2 ^ i) * (8 * 2 ^ m * l + 13)"
    apply (intro arg_cong2[where f = "(+)"] arg_cong2[where f = "(*)"] refl)
    subgoal unfolding \<open>m = Suc (Suc m')\<close> by simp
    subgoal unfolding sum_list_const_mult[symmetric] power_Suc[symmetric]
      unfolding sum_list_split_0 sum_list_index_trafo[of "power 2" Suc "[0..<Suc m' - 1]"] map_Suc_upt
      by simp
    done
  finally show ?case unfolding \<open>Suc m' = m - 1\<close> .
qed

lemma time_fft_ifft_tm_le:
  assumes "\<And>x. x \<in> set a \<Longrightarrow> length x = e"
  assumes "length a = 2 ^ m"
  shows "time (fft_ifft_tm it l a) \<le> 2 ^ m * (65 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m)"
proof -
  from time_fft_ifft_tm_le_aux[OF assms]
  have "time (fft_ifft_tm it l a) \<le> 2 ^ (m - 1) * (52 + 87 * e) + (m - 1) * 2 ^ m * (76 + 116 * e) + (\<Sum>i \<leftarrow> [0..<m-1]. 2 ^ i) * (8 * 2 ^ m * l + 13)"
    by simp
  also have "... \<le> 2 ^ m * (52 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (2 ^ (m - 1) - 1) * (8 * 2 ^ m * l + 13)"
    apply (intro add_mono mult_le_mono order.refl)
    subgoal by simp
    subgoal by simp
    subgoal using geo_sum_nat[of 2 "m - 1"] by simp
    done
  also have "... \<le> 2 ^ m * (52 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + 2 ^ m * (8 * 2 ^ m * l + 13)"
    apply (intro add_mono mult_le_mono order.refl)
    by (meson diff_le_self le_trans one_le_numeral power_increasing)
  also have "... = 2 ^ m * (65 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m)"
    by (simp add: add_mult_distrib2 power_add[symmetric])
  finally show ?thesis .
qed

fun fft_tm where
"fft_tm l a =1 fft_ifft_tm False l a"
fun ifft_tm where
"ifft_tm l a =1 fft_ifft_tm True l a"

lemma val_fft_tm[simp, val_simp]: "length a = 2 ^ m \<Longrightarrow> val (fft_tm l a) = fft l a"
  by simp
lemma val_ifft_tm[simp, val_simp]: "length a = 2 ^ m \<Longrightarrow> val (ifft_tm l a) = ifft l a"
  by simp


lemma time_fft_tm_le:
  assumes "\<And>x. x \<in> set a \<Longrightarrow> length x = e"
  assumes "length a = 2 ^ m"
  shows "time (fft_tm l a) \<le> 2 ^ m * (66 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m)"
proof -
  have "time (fft_tm l a) = 1 + time (fft_ifft_tm False l a)"
    by simp
  also have "... \<le> 1 + (2 ^ m * (65 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m))"
    by (intro add_mono order.refl time_fft_ifft_tm_le assms; assumption)
  also have "... \<le> 2 ^ m + (2 ^ m * (65 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m))"
    by (intro add_mono order.refl; simp)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma time_ifft_tm_le:
  assumes "\<And>x. x \<in> set a \<Longrightarrow> length x = e"
  assumes "length a = 2 ^ m"
  shows "time (ifft_tm l a) \<le> 2 ^ m * (66 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m)"
proof -
  have "time (ifft_tm l a) = 1 + time (fft_ifft_tm True l a)"
    by simp
  also have "... \<le> 1 + (2 ^ m * (65 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m))"
    by (intro add_mono order.refl time_fft_ifft_tm_le assms; assumption)
  also have "... \<le> 2 ^ m + (2 ^ m * (65 + 87 * e) + m * 2 ^ m * (76 + 116 * e) + (8 * l) * 2 ^ (2 * m))"
    by (intro add_mono order.refl; simp)
  finally show ?thesis by (simp add: algebra_simps)
qed

end

end