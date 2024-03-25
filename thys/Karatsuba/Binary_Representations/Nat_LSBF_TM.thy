section "Running time of @{text Nat_LSBF}"

theory "Nat_LSBF_TM"
  imports Nat_LSBF "../Karatsuba_Runtime_Lemmas" "../Main_TM" "../Estimation_Method"
begin

subsection "Truncating and filling"

fun truncate_reversed_tm :: "nat_lsbf \<Rightarrow> nat_lsbf tm" where
"truncate_reversed_tm [] =1 return []"
| "truncate_reversed_tm (x # xs) =1 (if x then return (x # xs) else truncate_reversed_tm xs)"

lemma val_truncate_reversed_tm[simp, val_simp]: "val (truncate_reversed_tm xs) = truncate_reversed xs"
  by (induction xs rule: truncate_reversed_tm.induct) simp_all

lemma time_truncate_reversed_tm_le: "time (truncate_reversed_tm xs) \<le> length xs + 1"
  by (induction xs rule: truncate_reversed_tm.induct) simp_all

definition truncate_tm :: "nat_lsbf \<Rightarrow> nat_lsbf tm" where
"truncate_tm xs =1 do {
  rev_xs \<leftarrow> rev_tm xs;
  truncate_rev_xs \<leftarrow> truncate_reversed_tm rev_xs;
  rev_tm truncate_rev_xs
}"

lemma val_truncate_tm[simp, val_simp]: "val (truncate_tm xs) = truncate xs"
  by (simp add: truncate_tm_def Nat_LSBF.truncate_def)

lemma time_truncate_tm_le: "time (truncate_tm xs) \<le> 3 * length xs + 6"
  using add_mono[OF time_truncate_reversed_tm_le[of "rev xs"] truncate_reversed_length_ineq[of "rev xs"]]
  by (simp add: truncate_tm_def)

definition fill_tm :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"fill_tm n xs =1 do {
  k \<leftarrow> length_tm xs;
  l \<leftarrow> n -\<^sub>t k;
  zeros \<leftarrow> replicate_tm l False;
  xs @\<^sub>t zeros
}"

lemma val_fill_tm[simp, val_simp]: "val (fill_tm n xs) = fill n xs"
  by (simp add: fill_tm_def fill_def)

lemma com_f_of_min_max: "f a b = f b a \<Longrightarrow> f (min a b) (max a b) = f a b"
  by (cases "a \<le> b"; simp add: max_def min_def)
lemma add_min_max: "min (a::'a:: ordered_ab_semigroup_add) b + max a b = a + b"
  by (intro com_f_of_min_max add.commute)

lemma time_fill_tm: "time (fill_tm n xs) = 2 * length xs + n + 5"
  by (simp add: fill_tm_def time_replicate_tm add_min_max)

lemma time_fill_tm_le: "time (fill_tm n xs) \<le> 3 * max n (length xs) + 5"
  unfolding time_fill_tm by simp

subsection "Right-shifts"

definition shift_right_tm :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"shift_right_tm n xs =1 do {
  r \<leftarrow> replicate_tm n False;
  r @\<^sub>t xs
}"

lemma val_shift_right_tm[simp, val_simp]: "val (shift_right_tm n xs) = xs >>\<^sub>n n"
  by (simp add: shift_right_tm_def shift_right_def)

lemma time_shift_right_tm[simp]: "time (shift_right_tm n xs) = 2 * n + 3"
  by (simp add: shift_right_tm_def time_replicate_tm)

subsection "Subdividing lists"

subsubsection "Splitting a list in two blocks"

definition split_at_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) tm" where
"split_at_tm k xs =1 do {
  xs1 \<leftarrow> take_tm k xs;
  xs2 \<leftarrow> drop_tm k xs;
  return (xs1, xs2)
}"

lemma val_split_at_tm[simp, val_simp]: "val (split_at_tm k xs) = split_at k xs"
  unfolding split_at_tm_def by simp

lemma time_split_at_tm: "time (split_at_tm k xs) = 2 * min k (length xs) + 3"
  unfolding split_at_tm_def tm_time_simps time_take_tm time_drop_tm by simp

definition split_tm :: "nat_lsbf \<Rightarrow> (nat_lsbf \<times> nat_lsbf) tm" where
"split_tm xs =1 do {
  n \<leftarrow> length_tm xs;
  n_div_2 \<leftarrow> n div\<^sub>t 2;
  split_at_tm n_div_2 xs
}"

lemma val_split_tm[simp, val_simp]: "val (split_tm xs) = split xs"
  by (simp add: split_tm_def split_def Let_def)

lemma time_split_tm_le: "time (split_tm xs) \<le> 10 * length xs + 16"
  using time_divide_nat_tm_le[of "length xs" 2]
  by (simp add: split_tm_def time_split_at_tm)

subsubsection "Splitting a list in multiple blocks"

fun subdivide_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list tm" where
"subdivide_tm 0 xs =1 undefined"
| "subdivide_tm n [] =1 return []"
| "subdivide_tm n xs =1 do {
    r \<leftarrow> take_tm n xs;
    s \<leftarrow> drop_tm n xs;
    rs \<leftarrow> subdivide_tm n s;
    return (r # rs)
  }"

lemma val_subdivide_tm[simp, val_simp]: "n > 0 \<Longrightarrow> val (subdivide_tm n xs) = subdivide n xs"
  by (induction n xs rule: subdivide.induct) simp_all

lemma time_subdivide_tm_le_aux:
  assumes "n > 0"
  shows "time (subdivide_tm n xs) \<le> k * (2 * n + 3) + time (subdivide_tm n (drop (k * n) xs))"
proof (induction k arbitrary: xs)
  case (Suc k)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a l)
    then have "time (subdivide_tm n (a # l)) \<le> 2 * n + 3 + time (subdivide_tm n (drop n (a # l)))"
      using gr0_implies_Suc[OF assms] by (auto simp: time_take_tm time_drop_tm)
    also have "... \<le> 2 * n + 3 + (k * (2 * n + 3) + time (subdivide_tm n (drop (k * n) (drop n (a # l)))))"
      by (intro add_mono order.refl Suc)
    also have "... = Suc k * (2 * n + 3) + time (subdivide_tm n (drop (Suc k * n) (a # l)))"
      by (simp add: add.commute)
    finally show ?thesis using Cons by simp
  qed
qed simp

lemma time_subdivide_tm_le:
  fixes xs :: "'a list"
  assumes "n > 0"
  shows "time (subdivide_tm n xs) \<le> 5 * length xs + 2 * n + 4"
proof -
  define k where "k = length xs div n + 1"
  then have "k * n \<ge> length xs" using assms
    by (meson div_less_iff_less_mult less_add_one order_less_imp_le)
  then have drop_Nil: "drop (k * n) xs = []" by simp
  have "time (subdivide_tm n xs) \<le> k * (2 * n + 3) + time (subdivide_tm n ([] :: 'a list))"
    using time_subdivide_tm_le_aux[OF assms, of xs k] unfolding drop_Nil .
  also have "... = k * (2 * n + 3) + 1" using gr0_implies_Suc[OF assms] by auto
  also have "... = (2 * n * (length xs div n) + 2 * n) + 3 * (length xs div n) + 4"
    unfolding k_def by (simp add: add_mult_distrib2)
  also have "... \<le> 5 * length xs + 2 * n + 4"
    using times_div_less_eq_dividend[of n "length xs"] div_le_dividend[of "length xs" n] by linarith
  finally show ?thesis .
qed

subsection "The @{const bitsize} function"

fun bitsize_tm :: "nat \<Rightarrow> nat tm" where
"bitsize_tm 0 =1 return 0"
| "bitsize_tm n =1 do {
    n_div_2 \<leftarrow> n div\<^sub>t 2;
    r \<leftarrow> bitsize_tm n_div_2;
    1 +\<^sub>t r
  }"

lemma val_bitsize_tm[simp, val_simp]: "val (bitsize_tm n) = bitsize n"
  by (induction n rule: bitsize_tm.induct) simp_all

fun time_bitsize_tm_bound :: "nat \<Rightarrow> nat" where
"time_bitsize_tm_bound 0 = 1"
| "time_bitsize_tm_bound n = 14 + 8 * n + time_bitsize_tm_bound (n div 2)"

lemma time_bitsize_tm_aux:
  "time (bitsize_tm n) \<le> time_bitsize_tm_bound n"
  apply (induction n rule: bitsize_tm.induct)
  subgoal by simp
  subgoal for n using time_divide_nat_tm_le[of "Suc n" 2] by simp
  done

lemma time_bitsize_tm_aux2: "time_bitsize_tm_bound n \<le> (2 * 8 + 4 * 14) * n + 23"
  apply (intro div_2_recursion_linear)
  using less_iff_Suc_add by auto

lemma time_bitsize_tm_le: "time (bitsize_tm n) \<le> 72 * n + 23"
  using order.trans[OF time_bitsize_tm_aux time_bitsize_tm_aux2] by simp

subsubsection "The @{const is_power_of_2} function"

fun is_power_of_2_tm :: "nat \<Rightarrow> bool tm" where
"is_power_of_2_tm 0 =1 return False"
| "is_power_of_2_tm (Suc 0) =1 return True"
| "is_power_of_2_tm n =1 do {
    n_mod_2 \<leftarrow> n mod\<^sub>t 2;
    n_div_2 \<leftarrow> n div\<^sub>t 2;
    c1 \<leftarrow> n_mod_2 =\<^sub>t 0;
    c2 \<leftarrow> is_power_of_2_tm n_div_2;
    c1 \<and>\<^sub>t c2
  }"

lemma val_is_power_of_2_tm[simp, val_simp]: "val (is_power_of_2_tm n) = is_power_of_2 n"
  by (induction n rule: is_power_of_2_tm.induct) simp_all

lemma time_is_power_of_2_tm_le: "time (is_power_of_2_tm n) \<le> 114 * n + 1"
proof -
  have "time (is_power_of_2_tm n) \<le> (2 * 25 + 4 * 16) * n + 1"
    apply (intro div_2_recursion_linear)
    subgoal by simp
    subgoal by simp
    subgoal premises prems for n
    proof -
      from prems obtain n' where "n = Suc (Suc n')"
        by (metis Suc_diff_1 Suc_diff_Suc order_less_trans zero_less_one)
      
      then have "time (is_power_of_2_tm n) =
          time (n mod\<^sub>t 2) +
          time (n div\<^sub>t 2) +
          time (is_power_of_2_tm (n div 2)) + 3"
        by (simp add: time_equal_nat_tm)
      also have "... \<le> 16 * n + time (is_power_of_2_tm (n div 2)) + 25"
        apply (estimation estimate: time_mod_nat_tm_le)
        apply (estimation estimate: time_divide_nat_tm_le)
        apply simp
        done
      finally show ?thesis by simp
    qed
    done
  then show ?thesis by simp
qed

definition next_power_of_2_tm :: "nat \<Rightarrow> nat tm" where
"next_power_of_2_tm n =1 do {
  b \<leftarrow> is_power_of_2_tm n;
  if b then return n else do {
    r \<leftarrow> bitsize_tm n;
    2 ^\<^sub>t r
  }
}"

lemma val_next_power_of_2_tm[simp, val_simp]: "val (next_power_of_2_tm n) = next_power_of_2 n"
  by (simp add: next_power_of_2_tm_def)

lemma time_next_power_of_2_tm_le: "time (next_power_of_2_tm n) \<le> 208 * n + 37"
proof (cases "is_power_of_2 n")
  case True
  then show ?thesis
    using time_is_power_of_2_tm_le[of n]
    by (simp add: next_power_of_2_tm_def)
next
  case False
  then have "time (next_power_of_2_tm n) =
      time (is_power_of_2_tm n) +
      time (bitsize_tm n) +
      time (power_nat_tm 2 (bitsize n)) + 1"
    by (simp add: next_power_of_2_tm_def)
  also have "... \<le> 186 * n + 6 * 2 ^ (bitsize n) + 5 * bitsize n + 26"
    apply (estimation estimate: time_is_power_of_2_tm_le)
    apply (estimation estimate: time_bitsize_tm_le)
    apply (estimation estimate: time_power_nat_tm_le)
    by simp
  also have "... \<le> 186 * n + 11 * 2 ^ (bitsize n) + 26"
    by simp
  also have "... \<le> 208 * n + 37"
    by (estimation estimate: two_pow_bitsize_bound) simp
  finally show ?thesis .
qed

subsection "Addition"

fun bit_add_carry_tm :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) tm" where
"bit_add_carry_tm False False False =1 return (False, False)"
| "bit_add_carry_tm False False True =1 return (True, False)"
| "bit_add_carry_tm False True False =1 return (True, False)"
| "bit_add_carry_tm False True True =1 return (False, True)"
| "bit_add_carry_tm True False False =1 return (True, False)"
| "bit_add_carry_tm True False True =1 return (False, True)"
| "bit_add_carry_tm True True False =1 return (False, True)"
| "bit_add_carry_tm True True True =1 return (True, True)"

lemma val_bit_add_carry_tm[simp, val_simp]: "val (bit_add_carry_tm x y z) = bit_add_carry x y z"
  by (induction x y z rule: bit_add_carry_tm.induct; simp)
lemma time_bit_add_carry_tm[simp]: "time (bit_add_carry_tm x y z) = 1"
  by (induction x y z rule: bit_add_carry_tm.induct; simp)

fun inc_nat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf tm" where
"inc_nat_tm [] =1 return [True]"
| "inc_nat_tm (False # xs) =1 return (True # xs)"
| "inc_nat_tm (True # xs) =1 do {
    r \<leftarrow> inc_nat_tm xs;
    return (False # r)
  }"

lemma val_inc_nat_tm[simp, val_simp]: "val (inc_nat_tm xs) = inc_nat xs"
  by (induction xs rule: inc_nat_tm.induct) simp_all

lemma time_inc_nat_tm_le: "time (inc_nat_tm xs) \<le> length xs + 1"
  by (induction xs rule: inc_nat_tm.induct) simp_all

fun add_carry_tm :: "bool \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"add_carry_tm False [] y =1 return y"
| "add_carry_tm False (x # xs) [] =1 return (x # xs)"
| "add_carry_tm True [] y =1 do {
    r \<leftarrow> inc_nat_tm y;
    return r
  }"
| "add_carry_tm True (x # xs) [] =1 do {
    r \<leftarrow> inc_nat_tm (x # xs);
    return r
  }"
| "add_carry_tm c (x # xs) (y # ys) =1 do {
    (a, b) \<leftarrow> bit_add_carry_tm c x y;
    r \<leftarrow> add_carry_tm b xs ys;
    return (a # r)
  }"

lemma val_add_carry_tm[simp, val_simp]: "val (add_carry_tm c xs ys) = add_carry c xs ys"
  by (induction c xs ys rule: add_carry_tm.induct) (simp_all split: prod.splits)

lemma time_add_carry_tm_le: "time (add_carry_tm c xs ys) \<le> 2 *  max (length xs) (length ys) + 2"
proof (induction c xs ys rule: add_carry_tm.induct)
  case (3 y)
  then show ?case using time_inc_nat_tm_le[of y] by simp
next
  case (4 x xs)
  then show ?case using time_inc_nat_tm_le[of "x # xs"] by simp
qed (simp_all split: prod.splits)

definition add_nat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"add_nat_tm xs ys =1 do {
  r \<leftarrow> add_carry_tm False xs ys;
  return r
}"

lemma val_add_nat_tm[simp, val_simp]: "val (add_nat_tm xs ys) = xs +\<^sub>n ys"
  by (simp add: add_nat_tm_def add_nat_def)

lemma time_add_nat_tm_le: "time (add_nat_tm xs ys) \<le> 2 * max (length xs) (length ys) + 3"
  using time_add_carry_tm_le[of _ xs ys] by (simp add: add_nat_tm_def)

subsection "Comparison and subtraction"

fun compare_nat_same_length_reversed_tm :: "bool list \<Rightarrow> bool list \<Rightarrow> bool tm" where
"compare_nat_same_length_reversed_tm [] [] =1 return True"
| "compare_nat_same_length_reversed_tm (False # xs) (False # ys) =1 compare_nat_same_length_reversed_tm xs ys"
| "compare_nat_same_length_reversed_tm (True # xs) (False # ys) =1 return False"
| "compare_nat_same_length_reversed_tm (False # xs) (True # ys) =1 return True"
| "compare_nat_same_length_reversed_tm (True # xs) (True # ys) =1 compare_nat_same_length_reversed_tm xs ys"
| "compare_nat_same_length_reversed_tm _ _ =1 undefined"

lemma val_compare_nat_same_length_reversed_tm[simp, val_simp]:
  assumes "length xs = length ys"
  shows "val (compare_nat_same_length_reversed_tm xs ys) = compare_nat_same_length_reversed xs ys"
  using assms by (induction xs ys rule: compare_nat_same_length_reversed_tm.induct) simp_all

lemma time_compare_nat_same_length_reversed_tm_le:
  "length xs = length ys \<Longrightarrow> time (compare_nat_same_length_reversed_tm xs ys) \<le> length xs + 1"
  by (induction xs ys rule: compare_nat_same_length_reversed_tm.induct) simp_all

fun compare_nat_same_length_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> bool tm" where
"compare_nat_same_length_tm xs ys =1 do {
  rev_xs \<leftarrow> rev_tm xs;
  rev_ys \<leftarrow> rev_tm ys;
  compare_nat_same_length_reversed_tm rev_xs rev_ys
}"

lemma val_compare_nat_same_length_tm[simp, val_simp]:
  assumes "length xs = length ys"
  shows "val (compare_nat_same_length_tm xs ys) = compare_nat_same_length xs ys"
  using assms by simp

lemma time_compare_nat_same_length_tm_le:
  "length xs = length ys \<Longrightarrow> time (compare_nat_same_length_tm xs ys) \<le> 3 * length xs + 6"
  using time_compare_nat_same_length_reversed_tm_le[of "rev xs" "rev ys"]
  by simp

definition make_same_length_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> (nat_lsbf \<times> nat_lsbf) tm" where
"make_same_length_tm xs ys =1 do {
  len_xs \<leftarrow> length_tm xs;
  len_ys \<leftarrow> length_tm ys;
  n \<leftarrow> max_nat_tm len_xs len_ys;
  fill_xs \<leftarrow> fill_tm n xs;
  fill_ys \<leftarrow> fill_tm n ys;
  return (fill_xs, fill_ys)
}"

lemma val_make_same_length_tm[simp, val_simp]: "val (make_same_length_tm xs ys) = make_same_length xs ys"
  by (simp add: make_same_length_tm_def make_same_length_def del: max_nat_tm.simps)

lemma time_make_same_length_tm_le: "time (make_same_length_tm xs ys) \<le> 10 * max (length xs) (length ys) + 16"
proof -
  have "time (make_same_length_tm xs ys) = 13 + 3 * length xs + 3 * length ys +
    (time (max_nat_tm (length xs) (length ys)) + 2 * max (length xs) (length ys))"
    by (simp add: make_same_length_tm_def time_fill_tm del: max_nat_tm.simps)
  also have "... \<le> 10 * max (length xs) (length ys) + 16"
    using time_max_nat_tm_le[of "length xs" "length ys"] by simp
  finally show ?thesis .
qed

definition compare_nat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> bool tm" where
"compare_nat_tm xs ys =1 do {
  (fill_xs, fill_ys) \<leftarrow> make_same_length_tm xs ys;
  compare_nat_same_length_tm fill_xs fill_ys
}"

lemma val_compare_nat_tm[simp, val_simp]: "val (compare_nat_tm xs ys) = (xs \<le>\<^sub>n ys)"
  using make_same_length_correct[where xs = xs and ys = ys]
  by (simp add: compare_nat_tm_def compare_nat_def del: compare_nat_same_length_tm.simps compare_nat_same_length.simps split: prod.splits)

lemma time_compare_nat_tm_le: "time (compare_nat_tm xs ys) \<le> 13 * max (length xs) (length ys) + 23"
proof -
  obtain fill_xs fill_ys where fills_defs: "make_same_length xs ys = (fill_xs, fill_ys)" by fastforce
  then have "time (compare_nat_tm xs ys) = time (make_same_length_tm xs ys) +
      time (compare_nat_same_length_tm fill_xs fill_ys) + 1"
    by (simp add: compare_nat_tm_def del: compare_nat_same_length_tm.simps)
  also have "... \<le> (10 * max (length xs) (length ys) + 16) +
      (3 * max (length xs) (length ys) + 6) + 1"
    apply (intro add_mono order.refl time_make_same_length_tm_le)
    using time_compare_nat_same_length_tm_le[of fill_xs fill_ys]
    using make_same_length_correct[OF fills_defs[symmetric]] by argo
  finally show ?thesis by simp
qed

definition subtract_nat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"subtract_nat_tm xs ys =1 do {
  b \<leftarrow> compare_nat_tm xs ys;
  if b then return [] else do {
    (fill_xs, fill_ys) \<leftarrow> make_same_length_tm xs ys;
    fill_ys_comp \<leftarrow> map_tm Not_tm fill_ys;
    a \<leftarrow> add_carry_tm True fill_xs fill_ys_comp;
    butlast_tm a
  }
}"

lemma val_subtract_nat_tm[simp, val_simp]: "val (subtract_nat_tm xs ys) = xs -\<^sub>n ys"
  by (simp add: subtract_nat_tm_def subtract_nat_def Let_def split: prod.splits)

lemma time_map_tm_Not_tm: "time (map_tm Not_tm xs) = 2 * length xs + 1"
  using time_map_tm_constant[of xs Not_tm 1] by simp

lemma time_subtract_nat_tm_le: "time (subtract_nat_tm xs ys) \<le> 30 * max (length xs) (length ys) + 48"
proof -
  obtain x1 x2 where x12: "make_same_length xs ys = (x1, x2)" by fastforce
  note x12_simps = make_same_length_correct[OF x12[symmetric]]
  then have max12: "max (length x1) (length x2) = max (length xs) (length ys)"
    by simp
  show ?thesis
  proof (cases "compare_nat xs ys")
    case True
    then show ?thesis
      using time_compare_nat_tm_le[of xs ys]
      by (simp add: subtract_nat_tm_def)
  next
    case False
    then have "time (subtract_nat_tm xs ys) =
        Suc (time (compare_nat_tm xs ys) +
             (time (make_same_length_tm xs ys) +
              (time (map_tm Not_tm x2) +
               (time (add_carry_tm True x1 (map Not x2)) +
                (time (butlast_tm (add_carry True x1 (map Not x2))))))))"
      by (simp add: subtract_nat_tm_def x12)
    also have "... \<le> 30 * max (length xs) (length ys) + 48"
      apply (subst Suc_eq_plus1)
      apply (estimation estimate: time_compare_nat_tm_le)
      apply (estimation estimate: time_make_same_length_tm_le)
      apply (subst time_map_tm_Not_tm)
      apply (estimation estimate: time_add_carry_tm_le)
      apply (estimation estimate: time_butlast_tm_le)
      apply (estimation estimate: time_inc_nat_tm_le)
      apply (estimation estimate: length_add_carry_upper)
      apply (subst length_map)+
      apply (subst max12)+
      apply (subst x12_simps)+
      apply simp
      done
    finally show ?thesis .
  qed
qed

subsection "(Grid) Multiplication"

fun grid_mul_nat_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"grid_mul_nat_tm [] ys =1 return []"
| "grid_mul_nat_tm (False # xs) ys =1 do {
    r \<leftarrow> grid_mul_nat_tm xs ys;
    return (False # r)
  }"
| "grid_mul_nat_tm (True # xs) ys =1 do {
    r \<leftarrow> grid_mul_nat_tm xs ys;
    add_nat_tm (False # r) ys
  }"

lemma val_grid_mul_nat_tm[simp, val_simp]: "val (grid_mul_nat_tm xs ys) = xs *\<^sub>n ys"
  by (induction xs ys rule: grid_mul_nat_tm.induct) simp_all

lemma euler_sum_bound: "\<Sum> {..(n::nat)} \<le> n * n"
  by (induction n) simp_all

lemma time_grid_mul_nat_tm_le:
  "time (grid_mul_nat_tm xs ys) \<le> 8 * length xs * max (length xs) (length ys) + 1"
proof -
  have "time (grid_mul_nat_tm xs ys) \<le> 2 * (\<Sum> {..length xs}) + length xs * (2 * length ys + 4) + 1"
  proof (induction xs ys rule: grid_mul_nat_tm.induct)
    case (1 ys)
    then show ?case by simp
  next
    case (2 xs ys)
    then show ?case by simp
  next
    case (3 xs ys)
    then have "time (grid_mul_nat_tm (True # xs) ys) \<le>
        time (grid_mul_nat_tm xs ys) +
        time (add_nat_tm (False # grid_mul_nat xs ys) ys) + 1" (is "?l \<le> ?i + _ + 1")
      by simp
    also have "... \<le> ?i + 2 * max (1 + length (grid_mul_nat xs ys)) (length ys) + 4"
      by (estimation estimate: time_add_nat_tm_le) simp
    also have "... \<le> ?i + 2 * (length xs + length ys + 1) + 4"
      apply (estimation estimate: length_grid_mul_nat[of xs ys])
      by (simp_all add: length_grid_mul_nat)
    also have "... = ?i + 2 * (length (True # xs)) + 2 * length ys + 4"
      by simp
    also have "... \<le> 2 * (\<Sum> {..length (True # xs)}) + length (True # xs) * (2 * length ys + 4) + 1"
      using 3 by simp
    finally show ?case .
  qed
  also have "... \<le> 2 * length xs * length xs + 2 * length xs * length ys + 4 * length xs + 1"
    by (estimation estimate: euler_sum_bound) (simp add: distrib_left)
  also have "... \<le> 6 * length xs * length xs + 2 * length xs * length ys + 1"
    by (simp add: leI)
  also have "... \<le> 8 * length xs * max (length xs) (length ys) + 1"
    by (simp add: add.commute add_mult_distrib nat_mult_max_right)
  finally show ?thesis .
qed

subsection "Syntax bundles"

abbreviation shift_right_tm_flip where "shift_right_tm_flip xs n \<equiv> shift_right_tm n xs"

bundle nat_lsbf_tm_syntax
begin
  notation add_nat_tm (infixl "+\<^sub>n\<^sub>t" 65)
  notation compare_nat_tm (infixl "\<le>\<^sub>n\<^sub>t" 50)
  notation subtract_nat_tm (infixl "-\<^sub>n\<^sub>t" 65)
  notation grid_mul_nat_tm (infixl "*\<^sub>n\<^sub>t" 70)
  notation shift_right_tm_flip (infixl ">>\<^sub>n\<^sub>t" 55)
end

bundle no_nat_lsbf_tm_syntax
begin
  no_notation add_nat_tm (infixl "+\<^sub>n\<^sub>t" 65)
  no_notation compare_nat_tm (infixl "\<le>\<^sub>n\<^sub>t" 50)
  no_notation subtract_nat_tm (infixl "-\<^sub>n\<^sub>t" 65)
  no_notation grid_mul_nat_tm (infixl "*\<^sub>n\<^sub>t" 70)
  no_notation shift_right_tm_flip (infixl ">>\<^sub>n\<^sub>t" 55)
end

unbundle nat_lsbf_tm_syntax

end