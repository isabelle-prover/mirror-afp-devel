theory Main_TM
  imports Main Time_Monad_Extended Estimation_Method
begin

section "Running Time Formalization for some functions available in @{theory Main}"

subsection "Functions on @{type bool}"

subsubsection "Not"

fun Not_tm :: "bool \<Rightarrow> bool tm" where
"Not_tm True =1 return False"
| "Not_tm False =1 return True"

lemma val_Not_tm[simp, val_simp]: "val (Not_tm x) = Not x"
  by (cases x; simp)

lemma time_Not_tm[simp]: "time (Not_tm x) = 1"
  by (cases x; simp)

subsubsection "disj / conj"

definition disj_tm where "disj_tm x y =1 return (x \<or> y)"
definition conj_tm where "conj_tm x y =1 return (x \<and> y)"

lemma val_disj_tm[simp, val_simp]: "val (disj_tm x y) = (x \<or> y)"
  by (simp add: disj_tm_def)
lemma time_disj_tm[simp]: "time (disj_tm x y) = 1"
  by (simp add: disj_tm_def)
lemma val_conj_tm[simp, val_simp]: "val (conj_tm x y) = (x \<and> y)"
  by (simp add: conj_tm_def)
lemma time_conj_tm[simp]: "time (conj_tm x y) = 1"
  by (simp add: conj_tm_def)

subsubsection "equal"

fun equal_bool_tm :: "bool \<Rightarrow> bool \<Rightarrow> bool tm" where
"equal_bool_tm True p =1 return p"
| "equal_bool_tm False p =1 Not_tm p"

lemma val_equal_bool_tm[simp, val_simp]: "val (equal_bool_tm x y) = (x = y)"
  by (cases x; simp)

lemma time_equal_bool_tm_le: "time (equal_bool_tm x y) \<le> 2"
  by (cases x; simp)

subsection "Functions involving pairs"

subsubsection "@{const fst} / @{const snd}"

fun fst_tm :: "'a \<times> 'b \<Rightarrow> 'a tm" where
"fst_tm (x, y) =1 return x"
fun snd_tm :: "'a \<times> 'b \<Rightarrow> 'b tm" where
"snd_tm (x, y) =1 return y"

lemma val_fst_tm[simp, val_simp]: "val (fst_tm p) = fst p"
  by (subst prod.collapse[symmetric], unfold fst_tm.simps, simp)
lemma time_fst_tm[simp]: "time (fst_tm p) = 1"
  by (subst prod.collapse[symmetric], unfold fst_tm.simps, simp)
lemma val_snd_tm[simp, val_simp]: "val (snd_tm p) = snd p"
  by (subst prod.collapse[symmetric], unfold snd_tm.simps, simp)
lemma time_snd_tm[simp]: "time (snd_tm p) = 1"
  by (subst prod.collapse[symmetric], unfold snd_tm.simps, simp)

subsection "Functions on @{type nat}"

subsubsection "@{const plus}"

fun plus_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"plus_nat_tm (Suc m) n =1 plus_nat_tm m (Suc n)"
| "plus_nat_tm 0 n =1 return n"

lemma val_plus_nat_tm[simp, val_simp]: "val (plus_nat_tm m n) = m + n"
  by (induction m n rule: plus_nat_tm.induct) simp_all

lemma time_plus_nat_tm[simp]: "time (plus_nat_tm m n) = m + 1"
  by (induction m n rule: plus_nat_tm.induct) simp_all

subsubsection "@{const times}"

fun times_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"times_nat_tm 0 n =1 return 0"
| "times_nat_tm (Suc m) n =1 do {
    r \<leftarrow> times_nat_tm m n;
    plus_nat_tm n r
  }"

lemma val_times_nat_tm[simp]: "val (times_nat_tm m n) = m * n"
  by (induction m n rule: times_nat_tm.induct) simp_all

lemma time_times_nat_tm[simp]: "time (times_nat_tm m n) = m * (n + 2) + 1"
  by (induction m n rule: times_nat_tm.induct) simp_all

subsubsection "@{const power}"

fun power_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"power_nat_tm a 0 =1 return 1"
| "power_nat_tm a (Suc n) =1 do {
    r \<leftarrow> power_nat_tm a n;
    times_nat_tm a r
  }"

lemma val_power_nat_tm[simp, val_simp]: "val (power_nat_tm a n) = a ^ n"
  by (induction a n rule: power_nat_tm.induct) simp_all

lemma time_power_nat_tm_aux0: "time (power_nat_tm 0 n) = 2 * n + 1"
  by (induction n) simp_all

lemma time_power_nat_tm_aux1: "time (power_nat_tm 1 n) = 5 * n + 1"
  by (induction n) simp_all

lemma time_power_nat_tm_aux2:
  assumes "m \<ge> 2"
  shows "time (power_nat_tm m n) \<le> (2 * n + m ^ n) * m + 2 * n + 1"
proof (induction n)
  case 0
  then have "time (power_nat_tm m 0) = 1" by simp
  then show ?case by simp
next
  case (Suc n)
  have "time (power_nat_tm m (Suc n)) \<le> time (power_nat_tm m n) + (m ^ n + 2) * m + 2"
    by simp
  also have "... \<le> (2 * n + m ^ n) * m + 2 * n + 1 + (m ^ n + 2) * m + 2"
    using Suc by simp
  also have "... = (2 * n + m ^ n) * m + (m ^ n + 2) * m + 2 * Suc n + 1"
    by simp
  also have "... = (2 * Suc n + 2 * m ^ n) * m + 2 * Suc n + 1"
    using add_mult_distrib by simp
  also have "... \<le> (2 * Suc n + m ^ Suc n) * m + 2 * Suc n + 1"
    using assms by simp
  finally show ?case .
qed

lemma time_power_nat_tm_le: "time (power_nat_tm m n) \<le> 3 * m ^ Suc n + 5 * n + 1"
proof -
  consider "m = 0" | "m = 1" | "m \<ge> 2" by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using time_power_nat_tm_aux0[of n] by simp
  next
    case 2
    then show ?thesis using time_power_nat_tm_aux1[of n] by simp
  next
    case 3
    then have "2 ^ n \<le> m ^ n" using power_mono by fast
    moreover have "n < 2 ^ n" by simp
    ultimately have n_le_m_pow_n: "n \<le> m ^ n" by linarith
    have "time (power_nat_tm m n) \<le> (2 * m ^ n + m ^ n) * m + 2 * n + 1"
      apply (estimation estimate: time_power_nat_tm_aux2[OF 3, of n])
      using n_le_m_pow_n by simp
    also have "... = 3 * m ^ Suc n + 2 * n + 1" by simp
    finally show ?thesis by simp
  qed
qed

lemma time_power_nat_tm_2_le: "time (power_nat_tm 2 n) \<le> 12 * 2 ^ n"
proof -
  have "time (power_nat_tm 2 n) \<le> 3 * 2 ^ Suc n + 5 * n + 1"
    by (fact time_power_nat_tm_le)
  also have "... \<le> 3 * 2 ^ Suc n + 5 * 2 ^ n + 2 ^ n"
    apply (intro add_mono mult_le_mono order.refl)
    using less_exp[of n] by simp_all
  finally show ?thesis by simp
qed

subsubsection "@{const minus}"

fun minus_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"minus_nat_tm m 0 =1 return m"
| "minus_nat_tm 0 m =1 return 0"
| "minus_nat_tm (Suc m) (Suc n) =1 minus_nat_tm m n"

lemma val_minus_nat_tm[simp, val_simp]: "val (minus_nat_tm m n) = m - n"
  by (induction m n rule: minus_nat_tm.induct) simp_all

lemma time_minus_nat_tm[simp]: "time (minus_nat_tm m n) = min m n + 1"
  by (induction m n rule: minus_nat_tm.induct) simp_all

subsubsection "@{const less} / @{const less_eq}"

fun less_eq_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> bool tm" and less_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> bool tm" where
"less_eq_nat_tm (Suc m) n =1 less_nat_tm m n"
| "less_eq_nat_tm 0 n =1 return True"
| "less_nat_tm m (Suc n) =1 less_eq_nat_tm m n"
| "less_nat_tm m 0 =1 return False"

lemma val_less_eq_nat_tm[simp, val_simp]: "(val (less_eq_nat_tm n m) = (n \<le> m))"
  and val_less_nat_tm[simp, val_simp]: "(val (less_nat_tm m n) = (m < n))"
  by (induction m and n rule: less_eq_nat_tm_less_nat_tm.induct) auto

lemma time_less_eq_nat_tm_aux: "time (less_eq_nat_tm (m + k) (n + k)) = 2 * k + time (less_eq_nat_tm m n)"
  by (induction k) simp_all
lemma time_less_nat_tm_aux: "time (less_nat_tm (m + k) (n + k)) = 2 * k + time (less_nat_tm m n)"
  by (induction k) simp_all

lemma time_less_eq_nat_tm: "time (less_eq_nat_tm n m) = 2 * min n m + 1 + of_bool (m < n)"
proof (cases "m < n")
  case True
  then obtain k where "n = m + Suc k" by (metis add_Suc_right less_natE)
  then have "time (less_eq_nat_tm n m) = 2 * m + 2"
    using time_less_eq_nat_tm_aux[of "Suc k" m 0] by (simp add: add.commute)
  then show ?thesis using True by simp
next
  case False
  then obtain k where "m = n + k" using nat_le_iff_add[of n m] by auto
  then have "time (less_eq_nat_tm n m) = 2 * n + 1"
    using time_less_eq_nat_tm_aux[of 0 n k] by (simp add: add.commute)
  then show ?thesis using False by simp
qed
lemma time_less_nat_tm: "time (less_nat_tm m n) = 2 * min m n + 1 + of_bool (m < n)"
proof (cases "m < n")
  case True
  then obtain k where "n = m + Suc k" by (metis add_Suc_right less_natE)
  then have "time (less_nat_tm m n) = 2 * m + 2"
    using time_less_nat_tm_aux[of 0 m "Suc k"] by (simp add: add.commute)
  then show ?thesis using True by simp
next
  case False
  then obtain k where "m = n + k" using nat_le_iff_add[of n m] by auto
  then have "time (less_nat_tm m n) = 2 * n + 1"
    using time_less_nat_tm_aux[of k n 0] by (simp add: add.commute)
  then show ?thesis using False by simp
qed

lemma time_less_eq_nat_tm_le: "time (less_eq_nat_tm n m) \<le> 2 * min n m + 2"
  by (simp add: time_less_eq_nat_tm)
lemma time_less_nat_tm_le: "time (less_nat_tm m n) \<le> 2 * min m n + 2"
  by (simp add: time_less_nat_tm)

subsubsection "@{const HOL.eq}"

fun equal_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> bool tm" where
"equal_nat_tm 0 0 =1 return True"
| "equal_nat_tm (Suc x) 0 =1 return False"
| "equal_nat_tm 0 (Suc y) =1 return False"
| "equal_nat_tm (Suc x) (Suc y) =1 equal_nat_tm x y"

lemma val_equal_nat_tm[simp, val_simp]: "val (equal_nat_tm x y) = (x = y)"
  by (induction x y rule: equal_nat_tm.induct) simp_all

lemma time_equal_nat_tm: "time (equal_nat_tm x y) = min x y + 1"
  by (induction x y rule: equal_nat_tm.induct) simp_all

subsubsection "@{const max}"

fun max_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"max_nat_tm x y =1 do {
  b \<leftarrow> less_eq_nat_tm x y;
  if b then return y else return x
}"

lemma val_max_nat_tm[simp, val_simp]: "val (max_nat_tm x y) = max x y"
  by simp

lemma time_max_nat_tm: "time (max_nat_tm x y) = 2 * min x y + 2 + of_bool (y < x)"
  by (simp add: time_less_eq_nat_tm)

lemma time_max_nat_tm_le: "time (max_nat_tm x y) \<le> 2 * min x y + 3"
  unfolding time_max_nat_tm by simp

subsubsection "@{const divide} / @{const modulo}"

fun divmod_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) tm" where
"divmod_nat_tm m n =1 do {
  n0 \<leftarrow> equal_nat_tm n 0;
  m_lt_n \<leftarrow> less_nat_tm m n;
  b \<leftarrow> disj_tm n0 m_lt_n;
  if b then return (0, m) else do {
    m_minus_n \<leftarrow> minus_nat_tm m n;
    (q, r) \<leftarrow> divmod_nat_tm m_minus_n n;
    return (Suc q, r)
  }
}"
declare divmod_nat_tm.simps[simp del]

lemma val_divmod_nat_tm[simp, val_simp]: "val (divmod_nat_tm m n) = Euclidean_Rings.divmod_nat m n"
proof (induction m n rule: divmod_nat_tm.induct)
  case (1 m n)
  show ?case
  proof (cases "n = 0 \<or> m < n")
    case True
    then show ?thesis unfolding divmod_nat_tm.simps[of m n] by (simp add: Euclidean_Rings.divmod_nat_if)
  next
    case False
    then have "val (divmod_nat_tm m n) = (let (q, r) = val (divmod_nat_tm (m - n) n) in (Suc q, r))"
      unfolding divmod_nat_tm.simps[of m n]
      by (simp add: Let_def split: prod.splits)
    also have "... = (let (q, r) = Euclidean_Rings.divmod_nat (m - n) n in (Suc q, r))"
      using 1 False by simp
    also have "... = Euclidean_Rings.divmod_nat m n"
      unfolding Euclidean_Rings.divmod_nat_if[of m n]
      by (simp add: False split: prod.splits)
    finally show ?thesis .
  qed
qed

lemma time_divmod_nat_tm_aux:
  assumes "r < n"
  assumes "n > 0"
  shows "time (divmod_nat_tm (n * k + r) n) = 5 * k + 3 * n * k + time (divmod_nat_tm r n)"
  using assms
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    unfolding divmod_nat_tm.simps[of "n * (Suc k) + r" n]
    by (simp add: time_equal_nat_tm time_less_nat_tm split: prod.splits)
qed


lemma time_divmod_nat_tm_le: "time (divmod_nat_tm m n) \<le> 8 * m + 2 * n + 5"
proof (cases "n = 0 \<or> m < n")
  case True
  have "time (divmod_nat_tm m n) = time (equal_nat_tm n 0) + time (less_nat_tm m n) + 2"
    unfolding divmod_nat_tm.simps[of m n]
    by (simp add: True)
  also have "... \<le> 2 * min m n + 5"
    apply (subst time_equal_nat_tm)
    apply (estimation estimate: time_less_nat_tm_le)
    by simp
  finally show ?thesis by simp
next
  case False
  define k r where "k = m div n" "r = m mod n"
  then have krn: "m = n * k + r" by simp
  from k_r_def have "r < n" using False by simp
  have "time (divmod_nat_tm m n) = 5 * k + 3 * n * k + time (divmod_nat_tm r n)"
    apply (subst krn, intro time_divmod_nat_tm_aux, intro \<open>r < n\<close>)
    using False by simp
  also have "time (divmod_nat_tm r n) = time (equal_nat_tm n 0) + time (less_nat_tm r n) + 2"
    unfolding divmod_nat_tm.simps[of r n]
    by (simp add: \<open>r < n\<close>)
  also have "... \<le> 2 * min r n + 5"
    apply (subst time_equal_nat_tm)
    apply (estimation estimate: time_less_nat_tm_le)
    by simp
  finally have "time (divmod_nat_tm m n) \<le> 5 * k + 3 * n * k + 2 * n + 5"
    by simp
  also have "... \<le> 5 * k + 3 * m + 2 * n + 5"
    using k_r_def by simp
  also have "... \<le> 8 * m + 2 * n + 5"
    using k_r_def by simp
  finally show ?thesis .
qed

definition divide_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"divide_nat_tm m n =1 divmod_nat_tm m n \<bind> fst_tm"

lemma val_divide_nat_tm[simp, val_simp]: "val (divide_nat_tm m n) = m div n"
  by (simp add: divide_nat_tm_def Euclidean_Rings.divmod_nat_def)

lemma time_divide_nat_tm_le: "time (divide_nat_tm m n) \<le> 8 * m + 2 * n + 7"
  using time_divmod_nat_tm_le[of m n] by (simp add: divide_nat_tm_def)

definition mod_nat_tm :: "nat \<Rightarrow> nat \<Rightarrow> nat tm" where
"mod_nat_tm m n =1 divmod_nat_tm m n \<bind> snd_tm"

lemma val_mod_nat_tm[simp, val_simp]: "val (mod_nat_tm m n) = m mod n"
  by (simp add: mod_nat_tm_def Euclidean_Rings.divmod_nat_def)

lemma time_mod_nat_tm_le: "time (mod_nat_tm m n) \<le> 8 * m + 2 * n + 7"
  using time_divmod_nat_tm_le[of m n] by (simp add: mod_nat_tm_def)

definition dvd_tm where "dvd_tm a b =1 do {
  b_mod_a \<leftarrow> mod_nat_tm b a;
  equal_nat_tm b_mod_a 0
}"

subsubsection "@{const dvd}"

lemma val_dvd_tm[simp, val_simp]: "val (dvd_tm a b) = (a dvd b)"
  unfolding dvd_tm_def dvd_eq_mod_eq_0 by simp

lemma time_dvd_tm_le: "time (dvd_tm a b) \<le> 8 * b + 2 * a + 9"
  unfolding dvd_tm_def tm_time_simps val_mod_nat_tm time_equal_nat_tm
  using time_mod_nat_tm_le[of b a] by simp

subsubsection "@{const even} / @{const odd}"

definition even_tm where "even_tm a = dvd_tm 2 a"

lemma val_even_tm[simp, val_simp]: "val (even_tm a) = even a"
  unfolding even_tm_def by simp

lemma time_even_tm_le: "time (even_tm a) \<le> 8 * a + 13"
  unfolding even_tm_def tm_time_simps
  using time_dvd_tm_le[of 2 a] by simp

definition odd_tm where "odd_tm a = dvd_tm 2 a \<bind> Not_tm"

lemma val_odd_tm[simp, val_simp]: "val (odd_tm a) = odd a"
  unfolding odd_tm_def by simp

lemma time_odd_tm_le: "time (odd_tm a) \<le> 8 * a + 14"
  unfolding odd_tm_def tm_time_simps
  using time_dvd_tm_le[of 2 a] by simp

subsection "List functions"

subsubsection "@{const take}"

fun take_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"take_tm n [] =1 return []"
| "take_tm n (x # xs) =1 (case n of 0 \<Rightarrow> return [] | Suc m \<Rightarrow>
  do {
    r \<leftarrow> take_tm m xs;
    return (x # r)
  })"

lemma val_take_tm[simp, val_simp]: "val (take_tm n xs) = take n xs"
  by (induction n xs rule: take_tm.induct) (simp_all split: nat.splits)

lemma time_take_tm: "time (take_tm n xs) = min n (length xs) + 1"
  by (induction n xs rule: take_tm.induct) (simp_all split: nat.splits)

lemma time_take_tm_le: "time (take_tm n xs) \<le> n + 1"
  by (simp add: time_take_tm)

subsubsection "@{const drop}"

fun drop_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"drop_tm n [] =1 return []"
| "drop_tm n (x # xs) =1 (case n of 0 \<Rightarrow> return (x # xs) | Suc m \<Rightarrow>
    do {
      r \<leftarrow> drop_tm m xs;
      return r
    })"

lemma val_drop_tm[simp, val_simp]: "val (drop_tm n xs) = drop n xs"
  by (induction n xs rule: drop_tm.induct) (simp_all split: nat.splits)

lemma time_drop_tm: "time (drop_tm n xs) = min n (length xs) + 1"
  by (induction n xs rule: drop_tm.induct) (simp_all split: nat.splits)

lemma time_drop_tm_le: "time (drop_tm n xs) \<le> n + 1"
  by (simp add: time_drop_tm)

subsubsection "@{const append}"

fun append_tm :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"append_tm [] ys =1 return ys"
| "append_tm (x # xs) ys =1 do {
  r \<leftarrow> append_tm xs ys;
  return (x # r)
}"

lemma val_append_tm[simp, val_simp]: "val (append_tm xs ys) = append xs ys"
  by (induction xs ys rule: append_tm.induct) simp_all

lemma time_append_tm[simp]: "time (append_tm xs ys) = length xs + 1"
  by (induction xs ys rule: append_tm.induct) simp_all

subsubsection "@{const fold}"

fun fold_tm where
"fold_tm f [] s =1 return s"
| "fold_tm f (x # xs) s =1 do {
    r \<leftarrow> f x s;
    fold_tm f xs r
  }"

lemma val_fold_tm[simp, val_simp]: "val (fold_tm f xs s) = fold (\<lambda>x y. val (f x y)) xs s"
  by (induction xs s rule: fold_tm.induct; simp)

lemma time_fold_tm_Cons: "time (fold_tm (\<lambda>x y. return (x # y)) xs s) = length xs + 1"
  by (induction xs arbitrary: s; simp)

subsubsection "@{const rev}"

definition rev_tm where "rev_tm xs =1 fold_tm (\<lambda>x y. return (x # y)) xs []"

lemma val_rev_tm[simp, val_simp]: "val (rev_tm xs) = rev xs"
  by (induction xs; simp add: rev_tm_def fold_Cons_rev)

lemma time_rev_tm_le[simp]: "time (rev_tm xs) = length xs + 2"
  unfolding rev_tm_def using time_fold_tm_Cons by auto

subsubsection "@{const replicate}"

fun replicate_tm :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list tm" where
"replicate_tm 0 x =1 return []"
| "replicate_tm (Suc n) x =1 do {
  r \<leftarrow> replicate_tm n x;
  return (x # r)
}"

lemma val_replicate_tm[simp, val_simp]: "val (replicate_tm n x) = replicate n x"
  by (induction n x rule: replicate_tm.induct) simp_all

lemma time_replicate_tm: "time (replicate_tm n x) = n + 1"
  by (induction n x rule: replicate_tm.induct) simp_all

subsubsection "@{const length}"

fun gen_length_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> nat tm" where
"gen_length_tm n [] =1 return n"
| "gen_length_tm n (x # xs) =1 gen_length_tm (Suc n) xs"

lemma val_gen_length_tm[simp, val_simp]: "val (gen_length_tm n xs) = List.gen_length n xs"
  by (induction n xs rule: gen_length_tm.induct) (simp_all add: List.gen_length_def)

lemma time_gen_length_tm[simp]: "time (gen_length_tm n xs) = length xs + 1"
  by (induction n xs rule: gen_length_tm.induct) simp_all

definition length_tm :: "'a list \<Rightarrow> nat tm" where
"length_tm xs = gen_length_tm 0 xs"

lemma val_length_tm[simp, val_simp]: "val (length_tm xs) = length xs"
  by (simp add: length_tm_def length_code)

lemma time_length_tm[simp]: "time (length_tm xs) = length xs + 1"
  by (simp add: length_tm_def)

subsubsection "@{const List.null}"

fun null_tm :: "'a list \<Rightarrow> bool tm" where
"null_tm [] =1 return True"
| "null_tm (x # xs) =1 return False"

lemma val_null_tm[simp, val_simp]: "val (null_tm xs) = List.null xs"
  by (cases xs; simp add: List.null_def)

lemma time_null_tm[simp]: "time (null_tm xs) = 1"
  by (cases xs; simp)

subsubsection "@{const butlast}"

fun butlast_tm :: "'a list \<Rightarrow> 'a list tm" where
"butlast_tm [] =1 return []"
| "butlast_tm (x # xs) =1 do {
    b \<leftarrow> null_tm xs;
    if b then return [] else do {
      r \<leftarrow> butlast_tm xs;
      return (x # r)
    }
  }"

lemma val_butlast_tm[simp, val_simp]: "val (butlast_tm xs) = butlast xs"
  by (induction xs rule: butlast_tm.induct) (simp_all add: List.null_def)

lemma time_butlast_tm: "time (butlast_tm xs) = 2 * (length xs - 1) + 1 + of_bool (length xs \<ge> 1)"
  by (induction xs rule: butlast_tm.induct) (auto simp: List.null_def not_less_eq_eq)

lemma time_butlast_tm_le: "time (butlast_tm xs) \<le> 2 * length xs + 1"
  unfolding time_butlast_tm by (cases xs; simp)

subsubsection "@{const map}"

fun map_tm :: "('a \<Rightarrow> 'b tm) \<Rightarrow> 'a list \<Rightarrow> 'b list tm" where
"map_tm f [] =1 return []"
| "map_tm f (x # xs) =1 do {
    r \<leftarrow> f x;
    rs \<leftarrow> map_tm f xs;
    return (r # rs)
  }"

lemma val_map_tm[simp, val_simp]: "val (map_tm f xs) = map (\<lambda>x. val (f x)) xs"
  by (induction f xs rule: map_tm.induct) simp_all

lemma time_map_tm: "time (map_tm f xs) = (\<Sum>i \<leftarrow> xs. time (f i)) + length xs + 1"
  by (induction f xs rule: map_tm.induct) (simp_all)

lemma time_map_tm_constant:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> time (f i) = c"
  shows "time (map_tm f xs) = (c + 1) * length xs + 1"
proof -
  have "time (map_tm f xs) = (\<Sum>i \<leftarrow> xs. time (f i)) + length xs + 1"
    by (simp add: time_map_tm)
  also have "... = (\<Sum>i \<leftarrow> xs. c) + length xs + 1"
    using assms iffD2[OF map_eq_conv, of xs] by metis
  also have "... = c * length xs + length xs + 1"
    using sum_list_triv[of c xs] by simp
  finally show ?thesis by simp
qed

lemma time_map_tm_bounded:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> time (f i) \<le> c"
  shows "time (map_tm f xs) \<le> (c + 1) * length xs + 1"
proof -
  have "time (map_tm f xs) = (\<Sum>i \<leftarrow> xs. time (f i)) + length xs + 1"
    by (simp add: time_map_tm)
  also have "... \<le> (\<Sum>i \<leftarrow> xs. c) + length xs + 1"
    by (intro add_mono order.refl sum_list_mono assms) argo
  also have "... = c * length xs + length xs + 1"
    using sum_list_triv[of c xs] by simp
  finally show ?thesis by simp
qed

subsubsection "@{const foldl}"

fun foldl_tm :: "('a \<Rightarrow> 'b \<Rightarrow> 'a tm) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a tm"  where
"foldl_tm f a [] =1 return a"
| "foldl_tm f a (x # xs) =1 do {
    r \<leftarrow> f a x;
    foldl_tm f r xs
  }"

lemma val_foldl_tm[simp, val_simp]: "val (foldl_tm f a xs) = foldl (\<lambda>x y. val (f x y)) a xs"
  by (induction f a xs rule: foldl_tm.induct; simp)

subsubsection "@{const concat}"

fun concat_tm where
"concat_tm [] =1 return []"
| "concat_tm (x # xs) =1 do {
    r \<leftarrow> concat_tm xs;
    append_tm x r
  }"

lemma val_concat_tm[simp, val_simp]: "val (concat_tm xs) = concat xs"
  by (induction xs; simp)

lemma time_concat_tm[simp]: "time (concat_tm xs) = 1 + 2 * length xs + length (concat xs)"
  by (induction xs; simp)

subsubsection "@{const nth}"

fun nth_tm where
"nth_tm (x # xs) 0 =1 return x"
| "nth_tm (x # xs) (Suc i) =1 nth_tm xs i"
| "nth_tm [] _ =1 undefined"

lemma val_nth_tm[simp, val_simp]:
  assumes "i < length xs"
  shows "val (nth_tm xs i) = xs ! i"
  using assms
proof (induction i arbitrary: xs)
  case 0
  then show ?case using length_greater_0_conv[of xs] neq_Nil_conv[of xs] by auto
next
  case (Suc i)
  then obtain x xs' where xsr: "xs = x # xs'" by (meson Suc_lessE length_Suc_conv)
  then have "i < length xs'" using Suc.prems by simp
  from Suc.IH[OF this] show ?case unfolding xsr by simp
qed

lemma time_nth_tm[simp]:
  assumes "i < length xs"
  shows "time (nth_tm xs i) = i + 1"
  using assms
proof (induction i arbitrary: xs)
  case 0
  then show ?case using length_greater_0_conv[of xs] neq_Nil_conv[of xs] by auto
next
  case (Suc i)
  then obtain x xs' where xsr: "xs = x # xs'" by (meson Suc_lessE length_Suc_conv)
  then have "i < length xs'" using Suc.prems by simp
  from Suc.IH[OF this] show ?case unfolding xsr by simp
qed

subsubsection "@{const zip}"

fun zip_tm :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list tm" where
"zip_tm xs [] =1 return []"
| "zip_tm [] ys =1 return []"
| "zip_tm (x # xs) (y # ys) =1 do { rs \<leftarrow> zip_tm xs ys; return ((x, y) # rs) }"

lemma val_zip_tm[simp, val_simp]: "val (zip_tm xs ys) = zip xs ys"
  by (induction xs ys rule: zip_tm.induct; simp)

lemma time_zip_tm[simp]: "time (zip_tm xs ys) = min (length xs) (length ys) + 1"
  by (induction xs ys rule: zip_tm.induct; simp)

subsubsection "@{const map2}"

definition map2_tm where
"map2_tm f xs ys =1 do {
  xys \<leftarrow> zip_tm xs ys;
  map_tm (\<lambda>(x,y). f x y) xys
}"

lemma val_map2_tm[simp, val_simp]: "val (map2_tm f xs ys) = map2 (\<lambda>x y. val (f x y)) xs ys"
  unfolding map2_tm_def by (simp split: prod.splits)

lemma time_map2_tm_bounded:
  assumes "length xs = length ys"
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> time (f x y) \<le> c"
  shows "time (map2_tm f xs ys) \<le> (c + 2) * length xs + 3"
proof -
  have "time (map2_tm f xs ys) = length xs + 2 + time (map_tm (\<lambda>(x, y). f x y) (zip xs ys))"
    unfolding map2_tm_def by (simp add: assms)
  also have "... \<le> length xs + 2 + ((c + 1) * length (zip xs ys) + 1)"
    apply (intro add_mono order.refl time_map_tm_bounded)
    using assms by (auto split: prod.splits elim: in_set_zipE)
  also have "... = (c + 2) * length xs + 3"
    using assms by simp
  finally show ?thesis .
qed

subsubsection "@{const upt}"

function upt_tm where
"upt_tm i j =1 do {
  b \<leftarrow> less_nat_tm i j;
  (if b then do {
    rs \<leftarrow> upt_tm (Suc i) j;
    return (i # rs)
  } else return [] )
}"
  by pat_completeness auto
termination by (relation "Wellfounded.measure (\<lambda>(i, j). j - i)") simp_all
declare upt_tm.simps[simp del]

lemma val_upt_tm[simp, val_simp]: "val (upt_tm i j) = [i..<j]"
  apply (induction i j rule: upt_tm.induct)
  subgoal for i j
    by (cases "i < j"; simp add: upt_tm.simps[of i j] upt_conv_Cons)
  done
lemma time_upt_tm_le: "time (upt_tm i j) \<le> (j - i) * (2 * j + 3) + 2 * j + 2"
proof (induction i j rule: upt_tm.induct)
  case (1 i j)
  then show ?case
  proof (cases "i < j")
    case True
    then have "time (upt_tm i j) = (2 * i + 3) + time (upt_tm (Suc i) j)"
      unfolding upt_tm.simps[of i j] tm_time_simps by (simp add: time_less_nat_tm)
    also have "... \<le> (2 * j + 3) + ((j - Suc i) * (2 * j + 3) + 2 * j + 2)"
      apply (intro add_mono mult_le_mono order.refl)
      subgoal using True by simp
      subgoal using 1 True by simp
      done
    also have "... = (j - Suc i + 1) * (2 * j + 3) + 2 * j + 2"
      by simp
    also have "j - Suc i + 1 = (j - i)"
      using True by simp
    finally show ?thesis .
  next
    case False
    then show ?thesis by (simp add: upt_tm.simps[of i j] time_less_nat_tm)
  qed
qed

lemma time_upt_tm_le': "time (upt_tm i j) \<le> 2 * j * j + 5 * j + 2"
  apply (intro order.trans[OF time_upt_tm_le[of i j]])
  apply (estimation estimate: diff_le_self)
  by (simp add: add_mult_distrib2)

subsection "Syntactic sugar"

consts equal_tm :: "'a \<Rightarrow> 'a \<Rightarrow> bool tm"
adhoc_overloading equal_tm equal_nat_tm
adhoc_overloading equal_tm equal_bool_tm

consts plus_tm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a tm"
adhoc_overloading plus_tm plus_nat_tm

consts times_tm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a tm"
adhoc_overloading times_tm times_nat_tm

consts power_tm :: "'a \<Rightarrow> nat \<Rightarrow> 'a tm"
adhoc_overloading power_tm power_nat_tm

consts minus_tm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a tm"
adhoc_overloading minus_tm minus_nat_tm

consts less_tm :: "'a \<Rightarrow> 'a \<Rightarrow> bool tm"
adhoc_overloading less_tm less_nat_tm

consts less_eq_tm :: "'a \<Rightarrow> 'a \<Rightarrow> bool tm"
adhoc_overloading less_eq_tm less_eq_nat_tm

consts divide_tm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a tm"
adhoc_overloading divide_tm divide_nat_tm

consts mod_tm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a tm"
adhoc_overloading mod_tm mod_nat_tm

bundle main_tm_syntax
begin
  notation equal_tm (infixl "=\<^sub>t" 51)
  notation Not_tm ("\<not>\<^sub>t _" [40] 40)
  notation conj_tm (infixr "\<and>\<^sub>t" 35)
  notation disj_tm (infixr "\<or>\<^sub>t" 30)
  notation append_tm (infixr "@\<^sub>t" 65)
  notation plus_tm (infixl "+\<^sub>t" 65)
  notation times_tm (infixl "*\<^sub>t" 70)
  notation power_tm (infixr "^\<^sub>t" 80)
  notation minus_tm (infixl "-\<^sub>t" 65)
  notation less_tm (infix "<\<^sub>t" 50)
  notation less_eq_tm (infix "\<le>\<^sub>t" 50)
  notation mod_tm (infixl "mod\<^sub>t" 70)
  notation divide_tm (infixl "div\<^sub>t" 70)
  notation dvd_tm (infix "dvd\<^sub>t" 50)
end

bundle no_main_tm_syntax
begin
  no_notation equal_tm (infixl "=\<^sub>t" 51)
  no_notation Not_tm ("\<not>\<^sub>t _" [40] 40)
  no_notation conj_tm (infixr "\<and>\<^sub>t" 35)
  no_notation disj_tm (infixr "\<or>\<^sub>t" 30)
  no_notation append_tm (infixr "@\<^sub>t" 65)
  no_notation plus_tm (infixl "+\<^sub>t" 65)
  no_notation times_tm (infixl "*\<^sub>t" 70)
  no_notation power_tm (infixr "^\<^sub>t" 80)
  no_notation minus_tm (infixl "-\<^sub>t" 65)
  no_notation less_tm (infix "<\<^sub>t" 50)
  no_notation less_eq_tm (infix "\<le>\<^sub>t" 50)
  no_notation mod_tm (infixl "mod\<^sub>t" 70)
  no_notation divide_tm (infixl "div\<^sub>t" 70)
  no_notation dvd_tm (infix "dvd\<^sub>t" 50)
end

unbundle main_tm_syntax

end