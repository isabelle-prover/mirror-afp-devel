section Preliminaries

theory Schoenhage_Strassen_Preliminaries
imports
  Main
  "HOL-Library.FuncSet"
  "Karatsuba.Karatsuba_Preliminaries"
  "Karatsuba.Nat_LSBF"
begin

lemma two_pow_pos: "(2 :: nat) ^ x > 0"
  by simp

lemma length_take_cobounded1: "length (take n xs) \<le> n"
  by simp

lemma const_diff_mod_idem:
  assumes "m \<ge> (n :: nat)"
    "f = (\<lambda>i. (m - i) mod n)"
  shows "(\<And>i. i \<in> {0..<n} \<Longrightarrow> f (f i) = i)"
proof -
  fix i
  assume "i \<in> {0..<n}"
  then have "i < n" by simp
  then have "i \<le> m" using \<open>n \<le> m\<close> by simp
  have "n > 0" using \<open>i < n\<close> by simp
  have "int (f (f i)) = int ((m - (m - i) mod n) mod n)"
    using assms by simp
  also have "... = (int m - int (m - i) mod int n) mod int n"
    unfolding zmod_int
    using \<open>n \<le> m\<close> int_ops(6)[of m "(m - i) mod n"] pos_mod_bound[OF \<open>n > 0\<close>]
    by (intro arg_cong2[where f = "(mod)"] refl)
       (metis nat_int_comparison(2) order.asym order.strict_trans1 zmod_int)
  also have "... = int i mod int n"
    using assms(1) \<open>i < n\<close> by (simp add: mod_diff_right_eq)
  also have "... = int i" using \<open>i < n\<close> by simp
  finally show "f (f i) = i" by simp
qed

lemma const_diff_mod_bij: "m \<ge> (n :: nat) \<Longrightarrow> bij_betw (\<lambda>i. (m - i) mod n) {0..<n} {0..<n}"
proof (intro bij_betwI)
  show "(\<lambda>i. (m - i) mod n) \<in> {0..<n} \<rightarrow> {0..<n}" by simp
  show "(\<lambda>i. (m - i) mod n) \<in> {0..<n} \<rightarrow> {0..<n}" by simp
  show "\<And>x. n \<le> m \<Longrightarrow> x \<in> {0..<n} \<Longrightarrow> (m - (m - x) mod n) mod n = x"
    using const_diff_mod_idem[of n] by blast
  show "\<And>x. n \<le> m \<Longrightarrow> x \<in> {0..<n} \<Longrightarrow> (m - (m - x) mod n) mod n = x"
    using const_diff_mod_idem[of n] by blast
qed

lemma const_add_mod_bij: "bij_betw (\<lambda>i. ((m :: nat) + i) mod n) {0..<n} {0..<n}"
proof (intro bij_betwI)
  show "(\<lambda>i. (m + i) mod n) \<in> {0..<n} \<rightarrow> {0..<n}" by simp
  show "(\<lambda>i. (n - (m mod n) + i) mod n) \<in> {0..<n} \<rightarrow> {0..<n}" by simp
  show "\<And>x. x \<in> {0..<n} \<Longrightarrow> (n - m mod n + (m + x) mod n) mod n = x"
  proof -
    fix x
    assume "x \<in> {0..<n}"
    then have "x < n" by simp
    have "int ((n - m mod n + (m + x) mod n) mod n) = (int n - int m mod int n + (int m + int x) mod int n) mod int n"
      using \<open>x < n\<close> zmod_int
      by (metis less_nat_zero_code mod_le_divisor not_gr_zero of_nat_add of_nat_diff)
    also have "... = (int n + (int x) mod int n) mod int n"
      by (metis (no_types, opaque_lifting) add.commute add_diff_eq diff_diff_eq2 diff_self minus_int_code(1) mod_diff_left_eq)
    also have "... = int x" using \<open>x < n\<close> mod_add_self1 by simp
    finally show "(n - m mod n + (m + x) mod n) mod n = x" by linarith
  qed
  show "\<And>y. y \<in> {0..<n} \<Longrightarrow> (m + (n - m mod n + y) mod n) mod n = y"
  proof -
    fix y
    assume "y \<in> {0..<n}"
    then have "y < n" by simp
    then show "(m + (n - m mod n + y) mod n) mod n = y"
      by (metis \<open>\<And>x. x \<in> {0..<n} \<Longrightarrow> (n - m mod n + (m + x) mod n) mod n = x\<close> \<open>y \<in> {0..<n}\<close> add.left_commute mod_add_right_eq)
  qed
qed

lemma mod_diff_add_eq: "(a - b + c) mod (m :: int) = (a mod m - b mod m + c mod m) mod m"
proof -
  have "(a - b + c) mod m = ((a - b) mod m + c mod m) mod m"
    by (intro mod_add_eq[symmetric])
  also have "... = ((a mod m - b mod m) mod m + c mod m) mod m"
    by (simp only: mod_diff_eq)
  also have "... = (a mod m - b mod m + c mod m) mod m"
    by (simp only: mod_add_left_eq)
  finally show "(a - b + c) mod m = (a mod m - b mod m + c mod m) mod m" .
qed

lemma set_map_subseteqI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  assumes "set xs \<subseteq> A"
  shows "set (map f xs) \<subseteq> B"
  using assms by auto

lemma in_set_conv_nth_map2:
  assumes "z \<in> set (map2 f xs ys)"
  shows "\<exists>i. i < min (length xs) (length ys) \<and> z = f (xs ! i) (ys ! i)"
proof -
  from assms obtain i where "i < length (map2 f xs ys)" "z = map2 f xs ys ! i"
    by (metis in_set_conv_nth)
  have "i < min (length xs) (length ys)"
    using \<open>i < length (map2 f xs ys)\<close> by simp
  moreover have "z = f (xs ! i) (ys ! i)"
    using \<open>z = map2 f xs ys ! i\<close> \<open>i < min (length xs) (length ys)\<close> by simp
  ultimately show ?thesis by blast
qed

lemma set_map2:
  assumes "z \<in> set (map2 f xs ys)"
  shows "\<exists>x y. x \<in> set xs \<and> y \<in> set ys \<and> z = f x y"
  using in_set_conv_nth_map2[OF assms] by force

lemma set_map2_subseteqI:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> f x y \<in> C"
  assumes "set xs \<subseteq> A" "set ys \<subseteq> B"
  shows "set (map2 f xs ys) \<subseteq> C"
proof
  fix z
  assume "z \<in> set (map2 f xs ys)"
  then obtain x y where "z = f x y" "x \<in> set xs" "y \<in> set ys"
    using set_map2 by meson
  then show "z \<in> C" using assms by auto
qed

lemma in_set_conv_nth_map3:
  assumes "w \<in> set (map3 f xs ys zs)"
  shows "\<exists>i. i < min (min (length xs) (length ys)) (length zs) \<and> w = f (xs ! i) (ys ! i) (zs ! i)"
proof -
  from assms obtain i where "i < length (map3 f xs ys zs)" "w = map3 f xs ys zs ! i"
    by (metis in_set_conv_nth)
  have "i < min (min (length xs) (length ys)) (length zs)"
    using \<open>i < length (map3 f xs ys zs)\<close>
    unfolding map3_as_map by simp
  moreover have "w = f (xs ! i) (ys ! i) (zs ! i)"
    using \<open>w = map3 f xs ys zs ! i\<close> \<open>i < min (min (length xs) (length ys)) (length zs)\<close>
    unfolding map3_as_map by simp
  ultimately show ?thesis by blast
qed

lemma set_map3:
  assumes "w \<in> set (map3 f xs ys zs)"
  shows "\<exists>x y z. x \<in> set xs \<and> y \<in> set ys \<and> z \<in> set zs \<and> w = f x y z"
  using in_set_conv_nth_map3[OF assms] by force

lemma set_map3_subseteqI:
  assumes "\<And>x y z. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> z \<in> C \<Longrightarrow> f x y z \<in> D"
  assumes "set xs \<subseteq> A" "set ys \<subseteq> B" "set zs \<subseteq> C"
  shows "set (map3 f xs ys zs) \<subseteq> D"
proof
  fix w
  assume "w \<in> set (map3 f xs ys zs)"
  then obtain x y z where "w = f x y z" "x \<in> set xs" "y \<in> set ys" "z \<in> set zs"
    using set_map3 by meson
  then show "w \<in> D" using assms by fastforce
qed

lemma map3_compose3: "map3 (\<lambda>x y z. f x y (g z)) xs ys zs = map3 f xs ys (map g zs)"
  apply (induction zs arbitrary: xs ys)
  subgoal by simp
  subgoal for z zs xs ys by (cases xs; cases ys; simp)
  done

(* faster version of rotate *)
definition rotate_left :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"rotate_left k xs = (let (xs1, xs2) = split_at (k mod length xs) xs in xs2 @ xs1)"

lemma rotate_left_rotate[simp]: "rotate_left k xs = rotate k xs"
  unfolding rotate_left_def by (simp add: rotate_drop_take)

definition rotate_right where
"rotate_right k xs = rotate_left (length xs - (k mod length xs)) xs"

lemma length_rotate_right[simp]: "length (rotate_right k xs) = length xs"
  unfolding rotate_right_def by simp

lemma rotate_right_rotate[simp]: "rotate_right k (rotate k xs) = xs"
proof (cases "xs = []")
  case True
  then show ?thesis unfolding rotate_right_def by simp
next
  case False
  then have "length xs > 0" by simp
  have "rotate_right k (rotate k xs) = rotate (length xs - k mod length xs + k) xs"
    by (simp add: rotate_rotate rotate_right_def)
  also have "... = rotate (length xs + (k - k mod length xs)) xs"
    using mod_le_divisor[of "length xs" k] \<open>length xs > 0\<close> by simp
  also have "... = rotate ((length xs + (k - k mod length xs)) mod length xs) xs"
    using rotate_conv_mod by simp
  also have "... = rotate ((k - k mod length xs) mod length xs) xs"
    by (metis mod_add_self1)
  also have "... = rotate 0 xs"
    by simp
  also have "... = xs" by simp
  finally show ?thesis .
qed
lemma rotate_rotate_right[simp]: "rotate k (rotate_right k xs) = xs"
proof -
  have "rotate k (rotate_right k xs) = rotate (k + (length xs - k mod length xs)) xs"
    by (simp add: rotate_rotate rotate_right_def)
  also have "... = rotate_right k (rotate k xs)"
    by (simp add: rotate_rotate add.commute rotate_right_def)
  finally show ?thesis using rotate_right_rotate by metis
qed

value "rotate 5 [1::nat..<8]"
value "rotate_right 3 [True, False, False]"

lemma rotate_right_append: "rotate_right (length q) (l @ q) = q @ l"
  unfolding rotate_right_def rotate_left_rotate
  using rotate_append[of l q]
  by (metis length_rev rev_append rev_rev_ident rotate_append rotate_rev)

lemma rotate_right_conv_mod: "rotate_right n xs = rotate_right (n mod length xs) xs"
  unfolding rotate_right_def by simp

lemma mod_diff_right_eq_nat:
  assumes "(a::nat) \<ge> b"
  shows "(a - b) mod m = (a - (b mod m)) mod m"
proof -
  have "int ((a - b) mod m) = (int (a - b)) mod int m"
    using zmod_int by presburger
  also have "... = (int a - int b) mod int m"
    using assms by (simp add: of_nat_diff)
  also have "... = (int a - (int b mod int m)) mod int m"
    using mod_diff_right_eq by metis
  also have "... = (int a - int (b mod m)) mod int m"
    using zmod_int by presburger
  also have "... = (int (a - (b mod m))) mod int m"
    by (metis calculation diff_diff_cancel diff_is_0_eq' less_imp_diff_less less_le_not_le mod_less_eq_dividend of_nat_diff verit_comp_simplify1(3) zmod_int)
  also have "... = int ((a - (b mod m)) mod m)"
    using zmod_int by presburger
  finally show ?thesis by simp
qed

lemma "rotate_right k (rotate_right l xs) = rotate_right (k + l) xs"
proof (cases "xs = []")
  case True
  then show ?thesis unfolding rotate_right_def by simp
next
  case False
  then have "rotate_right k (rotate_right l xs) = rotate (length xs - k mod length xs + (length xs - l mod length xs)) xs"
    unfolding rotate_right_def by (simp add: rotate_rotate)
  also have "... = rotate ((length xs + length xs) - (k mod length xs + l mod length xs)) xs"
    using False by simp
  also have "... = rotate (((length xs + length xs) - (k mod length xs + l mod length xs)) mod length xs) xs"
    using rotate_conv_mod by blast
  also have "... = rotate (((length xs + length xs) - (k mod length xs + l mod length xs) mod length xs) mod length xs) xs"
    using mod_diff_right_eq_nat False
    by (metis add_le_mono length_greater_0_conv mod_le_divisor)
  also have "... = rotate (((length xs + length xs) - ((k + l) mod length xs) mod length xs) mod length xs) xs"
    by (simp add: mod_add_eq)
  also have "... = rotate ((length xs + (length xs - ((k + l) mod length xs))) mod length xs) xs"
    using False by simp
  also have "... = rotate ((length xs - ((k + l) mod length xs)) mod length xs) xs"
    by simp
  also have "... = rotate (length xs - ((k + l) mod length xs)) xs"
    using rotate_conv_mod by metis
  also have "... = rotate_right (k + l) xs" unfolding rotate_right_def by simp
  finally show ?thesis .
qed

lemma nth_rotate_right: "n < length xs \<Longrightarrow> m < length xs \<Longrightarrow>  rotate_right m xs ! n = xs ! ((n + length xs - m) mod length xs)"
  by (simp add: nth_rotate add.commute rotate_right_def)

end