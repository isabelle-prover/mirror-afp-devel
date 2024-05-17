subsection "Some Running Time Formalizations"

theory Schoenhage_Strassen_Runtime_Preliminaries
imports
  Main
  "Karatsuba.Time_Monad_Extended"
  "Karatsuba.Main_TM"
  "Karatsuba.Karatsuba_Preliminaries"
  "Karatsuba.Nat_LSBF"
  "Karatsuba.Nat_LSBF_TM"
  "Karatsuba.Estimation_Method"
  "Schoenhage_Strassen_Preliminaries"
  "Akra_Bazzi.Akra_Bazzi"
  "HOL-Library.Landau_Symbols"
begin

fun zip_tm :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list tm" where
"zip_tm xs [] =1 return []"
| "zip_tm [] ys =1 return []"
| "zip_tm (x # xs) (y # ys) =1 do { rs \<leftarrow> zip_tm xs ys; return ((x, y) # rs) }"

lemma val_zip_tm[simp, val_simp]: "val (zip_tm xs ys) = zip xs ys"
  by (induction xs ys rule: zip_tm.induct; simp)

lemma time_zip_tm[simp]: "time (zip_tm xs ys) = min (length xs) (length ys) + 1"
  by (induction xs ys rule: zip_tm.induct; simp)

fun map3_tm :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd tm) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list tm" where
"map3_tm f (x # xs) (y # ys) (z # zs) =1 do {
  r \<leftarrow> f x y z;
  rs \<leftarrow> map3_tm f xs ys zs;
  return (r # rs)
}"
| "map3_tm f _ _ _ =1 return []"

lemma val_map3_tm[simp, val_simp]: "val (map3_tm f xs ys zs) = map3 (\<lambda>x y z. val (f x y z)) xs ys zs"
  by (induction f xs ys zs rule: map3_tm.induct; simp)

lemma time_map3_tm_bounded:
  assumes "\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> time (f x y z) \<le> c"
  shows "time (map3_tm f xs ys zs) \<le> (c + 1) * min (min (length xs) (length ys)) (length zs) + 1"
using assms proof (induction f xs ys zs rule: map3.induct)
  case (1 f x xs y ys z zs)
  then have ih: "time (map3_tm f xs ys zs) \<le> (c + 1) * min (min (length xs) (length ys)) (length zs) + 1"
    by simp
  from "1.prems" have fxyz: "time (f x y z) \<le> c" by simp
  show ?case
    unfolding map3_tm.simps tm_time_simps
    apply (estimation estimate: ih)
    apply (estimation estimate: fxyz)
    by simp
qed simp_all

fun map4_tm :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e tm) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> 'e list tm" where
"map4_tm f (x # xs) (y # ys) (z # zs) (w # ws) =1 do {
  r \<leftarrow> f x y z w;
  rs \<leftarrow> map4_tm f xs ys zs ws;
  return (r # rs)
}"
| "map4_tm f _ _ _ _ =1 return []"

lemma val_map4_tm[simp, val_simp]: "val (map4_tm f xs ys zs ws) = map4 (\<lambda>x y z w. val (f x y z w)) xs ys zs ws"
  by (induction f xs ys zs ws rule: map4_tm.induct; simp)

lemma time_map4_tm_bounded:
  assumes "\<And>x y z w. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> w \<in> set ws \<Longrightarrow> time (f x y z w) \<le> c"
  shows "time (map4_tm f xs ys zs ws) \<le> (c + 1) * min (min (min (length xs) (length ys)) (length zs)) (length ws) + 1"
using assms proof (induction f xs ys zs ws rule: map4.induct)
  case (1 f x xs y ys z zs w ws)
  then have ih: "time (map4_tm f xs ys zs ws) \<le> (c + 1) * min (min (min (length xs) (length ys)) (length zs)) (length ws) + 1"
    by simp
  from "1.prems" have fxyzw: "time (f x y z w) \<le> c" by simp
  show ?case
    unfolding map4_tm.simps tm_time_simps
    apply (estimation estimate: ih)
    apply (estimation estimate: fxyzw)
    by simp
qed simp_all

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

definition rotate_left_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"rotate_left_tm k xs =1 do {
  lenxs \<leftarrow> length_tm xs;
  kmod \<leftarrow> k mod\<^sub>t lenxs;
  (xs1, xs2) \<leftarrow> split_at_tm kmod xs;
  xs2 @\<^sub>t xs1
}"

lemma val_rotate_left_tm[simp, val_simp]: "val (rotate_left_tm k xs) = rotate_left k xs"
  unfolding rotate_left_tm_def rotate_left_def by (simp add: Let_def)

lemma time_rotate_left_tm_le: "time (rotate_left_tm k xs) \<le> 13 + 14 * max k (length xs)"
proof -
  obtain xs1 xs2 where 1: "(xs1, xs2) = split_at (k mod length xs) xs"
    by simp
  then have 2: "length xs2 \<le> length xs" by simp
  have "time (rotate_left_tm k xs) =
    time (length_tm xs) +
    time (k mod\<^sub>t (length xs)) +
    time (split_at_tm (k mod length xs) xs) + time (xs2 @\<^sub>t xs1) + 1"
  unfolding rotate_left_tm_def tm_time_simps val_length_tm val_mod_nat_tm val_split_at_tm
  Product_Type.prod.case 1[symmetric] by simp
  also have "... \<le> (length xs + 1) + (8 * k + 2 * length xs + 7) + (2 * length xs + 3) + (length xs + 1) + 1"
    apply (intro add_mono order.refl)
    subgoal by simp
    subgoal by (estimation estimate: time_mod_nat_tm_le) (rule order.refl)
    subgoal by (simp add: time_split_at_tm)
    subgoal by (simp add: 2)
    done
  also have "... = 13 + 6 * length xs + 8 * k" by simp
  finally show ?thesis by simp
qed

definition rotate_right_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"rotate_right_tm k xs =1 do {
  lenxs \<leftarrow> length_tm xs;
  kmod \<leftarrow> k mod\<^sub>t lenxs;
  rk \<leftarrow> lenxs -\<^sub>t kmod;
  rotate_left_tm rk xs
}"

lemma val_rotate_right_tm[simp, val_simp]: "val (rotate_right_tm k xs) = rotate_right k xs"
  unfolding rotate_right_tm_def rotate_right_def by (simp add: Let_def)

lemma time_rotate_right_tm_le: "time (rotate_right_tm k xs) \<le> 23 + 26 * max k (length xs)"
proof -
  have "time (rotate_right_tm k xs) =
    time (length_tm xs) +
    time (k mod\<^sub>t length xs) +
    time (length xs -\<^sub>t (k mod length xs)) +
    time (rotate_left_tm (length xs - k mod length xs) xs) + 1"
    unfolding rotate_right_tm_def tm_time_simps val_length_tm val_mod_nat_tm val_minus_nat_tm
    by simp
  also have "... \<le> (length xs + 1) +
    (8 * k + 2 * length xs + 7) +
    (length xs + 1) +
    (14 * length xs + 13) + 1"
    apply (intro add_mono order.refl)
    subgoal by simp
    subgoal by (estimation estimate: time_mod_nat_tm_le) (rule order.refl)
    subgoal by simp
    subgoal by (estimation estimate: time_rotate_left_tm_le) simp
    done
  also have "... = 23 + 18 * length xs + 8 * k" by simp
  finally show ?thesis by simp
qed

subsection "Auxiliary Lemmas for Landau Notation"

lemma eventually_early_nat:
  fixes f g :: "nat \<Rightarrow> nat"
  assumes "f \<in> O(g)"
  assumes "\<And>x. x \<ge> n0 \<Longrightarrow> g x > 0"
  shows "\<exists>c. (\<forall>x. x \<ge> n0 \<longrightarrow> f x \<le> c * g x)"
proof -
  from landau_o.bigE[OF \<open>f \<in> O(g)\<close>]
  obtain c_real where "eventually (\<lambda>x. norm (f x) \<le> c_real * norm (g x)) sequentially"
    by auto
  then have "eventually (\<lambda>x. f x \<le> c_real * g x) at_top" by simp
  then obtain n1 where f_le_g_real: "f x \<le> c_real * g x" if "x \<ge> n1" for x
    using eventually_at_top_linorder by meson
  define c where "c = nat (ceiling c_real)"
  then have f_le_g: "f x \<le> c * g x" if "x \<ge> n1" for x
  proof -
    have "real (f x) \<le> c_real * real (g x)" using f_le_g_real[OF that] .
    also have "... \<le> real c * real (g x)" unfolding c_def
      by (simp add: mult_mono real_nat_ceiling_ge)
    also have "... = real (c * g x)" by simp
    finally show ?thesis by linarith
  qed
  consider "n1 \<le> n0" | "n1 > n0" by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      apply (intro exI[of _ c]) using f_le_g by simp
  next
    case 2
    define M where "M = Max (f ` {n0..<n1})"
    define C where "C = (max M 1) * (max c 1)"
    have "f x \<le> C * g x" if "x \<ge> n0" for x
    proof (cases "x < n1")
      case True
      then have "f x \<le> M"
        unfolding M_def using 2
        by (intro Max.coboundedI; simp add: that)
      also have "... \<le> C" unfolding C_def
        using nat_mult_max_right by auto
      also have "... \<le> C * g x"
        using assms(2)[OF that] by simp
      finally show ?thesis .
    next
      case False
      then have "f x \<le> c * g x" using f_le_g by simp
      also have "... \<le> C * g x" unfolding C_def using nat_mult_max_left
        by simp
      finally show ?thesis .
    qed
    then show ?thesis by blast
  qed
qed

lemma eventually_early_real:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "f \<in> O(g)"
  assumes "\<And>x. x \<ge> n0 \<Longrightarrow> f x \<ge> 0 \<and> g x \<ge> 1"
  shows "\<exists>c. (\<forall>x \<ge> n0. f x \<le> c * g x)"
proof -
  from landau_o.bigE[OF \<open>f \<in> O(g)\<close>]
  obtain c where "eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) at_top"
    by auto
  then obtain n1 where f_le_g: "norm (f x) \<le> c * norm (g x)" if "x \<ge> n1" for x
    using eventually_at_top_linorder by meson
  consider "n1 \<le> n0" | "n1 > n0" by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      apply (intro exI[of _ c] allI impI)
      subgoal for x using f_le_g[of x] assms(2)[of x] by simp
      done
  next
    case 2
    define M where "M = Max (f ` {n0..<n1})"
    define C where "C = (max M 1) * (max c 1)"
    then have "C \<ge> 1" using mult_mono[OF max.cobounded2[of 1 M] max.cobounded2[of 1 c]] by argo
    have "C \<ge> c" unfolding C_def using mult_mono[OF max.cobounded2[of 1 M] max.cobounded1[of c 1]]
      by linarith
    have "f x \<le> C * g x" if "x \<ge> n0" for x
    proof (cases "x < n1")
      case True
      then have "f x \<le> M"
        unfolding M_def using 2
        by (intro Max.coboundedI; simp add: that)
      also have "... \<le> C" unfolding C_def
        using mult_mono[OF max.cobounded1[of M 1] max.cobounded2[of 1 c]] by simp
      also have "... \<le> C * g x"
        using assms(2)[OF that] mult_left_mono[of 1 "g x" C] \<open>C \<ge> 1\<close> by argo
      finally show ?thesis .
    next
      case False
      then have "f x \<le> c * g x" using f_le_g[of x] assms(2)[OF that] by simp
      also have "... \<le> C * g x" apply (intro mult_mono[OF \<open>C \<ge> c\<close>])
        subgoal by (rule order.refl)
        subgoal using \<open>C \<ge> 1\<close> by simp
        subgoal using assms(2)[OF that] by simp
        done
      finally show ?thesis .
    qed
    then show ?thesis by blast
  qed
qed

lemma floor_in_nat_iff: "floor x \<in> \<nat> \<longleftrightarrow> x \<ge> 0"
proof
  assume "floor x \<in> \<nat>"
  then obtain n where "floor x = of_nat n" unfolding Nats_def by auto
  then have "floor x \<ge> 0" using of_nat_0_le_iff by simp
  then show "x \<ge> 0" by simp
next
  assume "0 \<le> x"
  then have "floor x \<ge> 0" by simp
  then obtain n where "floor x = of_nat n" using nat_0_le by metis
  then show "floor x \<in> \<nat>" unfolding Nats_def by simp
qed

lemma bigo_floor:
  fixes f :: "nat \<Rightarrow> nat"
  fixes g :: "nat \<Rightarrow> real"
  assumes "(\<lambda>x. real (f x)) \<in> O(g)"
  assumes "eventually (\<lambda>x. g x \<ge> 1) at_top"
  shows "(\<lambda>x. real (f x)) \<in> O(\<lambda>x. real (nat (floor (g x))))"
proof -
  have ineq: "x \<le> 2 * real_of_int (floor x)" if "x \<ge> 1" for x :: real
  proof -
    have "x \<le> real_of_int (floor x) + 1"
      by (rule real_of_int_floor_add_one_ge)
    also have "... \<le> 2 * real_of_int (floor x)"
      using that by simp
    finally show ?thesis .
  qed
  obtain c where "c > 0" and f_le_g: "eventually (\<lambda>x. real (f x) \<le> c * norm (g x)) at_top"
    using landau_o.bigE[OF assms(1)] by auto
  have "eventually (\<lambda>x. g x \<le> 2 * of_int (floor (g x))) at_top"
    using eventually_rev_mp[OF assms(2), of "\<lambda>x. g x \<le> 2 * of_int (floor (g x))"]
    using assms(2) ineq by simp
  then have 1: "eventually (\<lambda>x. c * g x \<le> (2 * c) * of_int (floor (g x))) at_top"
    using eventually_mp[of "\<lambda>x. g x \<le> 2 * of_int (floor (g x))" "\<lambda>x. c * g x \<le> (2 * c) * of_int (floor (g x))"]
    using \<open>c > 0\<close> by simp
  have 2: "eventually (\<lambda>x. c * norm (g x) = c * g x) at_top"
    using eventually_rev_mp[OF assms(2)] by simp
  have 3: "eventually (\<lambda>x. c * norm (g x) \<le> (2 * c) * of_int (floor (g x))) at_top"
    apply (intro eventually_rev_mp[OF eventually_conj[OF 1 2], of "\<lambda>x. c * norm (g x) \<le> (2 * c) * of_int (floor (g x))"])
    apply (intro always_eventually allI impI)
    by argo
  have 4: "eventually (\<lambda>x. real (f x) \<le> (2 * c) * of_int (floor (g x))) at_top"
    apply (intro eventually_rev_mp[OF eventually_conj[OF f_le_g 3], where Q = "\<lambda>x. real (f x) \<le> (2 * c) * of_int (floor (g x))"])
    by simp
  show ?thesis
    apply (intro landau_o.bigI[where c = "2 * c"])
    subgoal using \<open>c > 0\<close> by argo
    subgoal apply (intro eventually_rev_mp[OF eventually_conj[OF 4 assms(2)], where Q = "\<lambda>x. norm (real (f x)) \<le> (2 * c) * norm (real (nat \<lfloor>g x\<rfloor>))"])
      by simp
    done
qed

end