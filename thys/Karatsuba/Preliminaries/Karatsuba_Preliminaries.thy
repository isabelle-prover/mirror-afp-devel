section "Preliminaries"

text "Some general preliminaries."

theory Karatsuba_Preliminaries
  imports Main "Expander_Graphs.Extra_Congruence_Method" "HOL-Number_Theory.Residues"
begin

lemma prop_ifI:
  assumes "Q \<Longrightarrow> P R"
  assumes "\<not> Q \<Longrightarrow> P S"
  shows "P (if Q then R else S)"
  using assms by argo

lemma let_prop_cong:
  assumes "T = T'"
  assumes "P (f T) (f' T')"
  shows "P (let x = T in f x) (let x = T' in f' x)"
  using assms by simp

lemma set_subseteqD:
  assumes "set xs \<subseteq> A"
  shows "\<And>i. i < length xs \<Longrightarrow> xs ! i \<in> A"
  using assms by fastforce

lemma set_subseteqI:
  assumes "\<And>i. i < length xs \<Longrightarrow> xs ! i \<in> A"
  shows "set xs \<subseteq> A"
  using assms
  by (metis in_set_conv_nth subsetI)

lemma Nat_max_le_sum: "max (a :: nat) b \<le> a + b"
  by simp

lemma upt_add_eq_append':
  assumes "a \<le> b" "b \<le> c"
  shows "[a..<c] = [a..<b] @ [b..<c]"
  using assms upt_add_eq_append[of a b "c - b"] by auto

lemma map_add_const_upt: "map (\<lambda>j. j + c) [a..<b] = [a + c..<b + c]"
proof (cases "a < b")
  case True
  then have "map (\<lambda>j. j + c) [a..<b] = map (\<lambda>j. j + c) (map (\<lambda>j. j + a) [0..<b-a])"
    using map_add_upt[of a "b - a"] by simp
  also have "... = map (\<lambda>j. j + (a + c)) [0..<b-a]"
    by simp
  also have "... = [a+c..<b+c]"
    using map_add_upt[of "a + c" "b - a"] True by simp
  finally show ?thesis .
next
  case False
  then show ?thesis by simp
qed

lemma filter_even_upt_even: "filter even [0..<2*n] = map ((*) 2) [0..<n]"
  by (induction n) simp_all
lemma filter_even_upt_odd: "filter even [0..<2*n + 1] = map ((*) 2) [0..<n + 1]"
  by (simp add: filter_even_upt_even)

lemma filter_odd_upt_even: "filter odd [0..<2*n] = map (\<lambda>i. 2*i + 1) [0..<n]"
  by (induction n) simp_all
lemma filter_odd_upt_odd: "filter odd [0..<2*n + 1] = map (\<lambda>i. 2*i + 1) [0..<n]"
  by (simp add: filter_odd_upt_even)

lemma length_filter_even: "length (filter even [0..<n]) = (if even n then n div 2 else n div 2 + 1)"
  by (induction n) simp_all
lemma length_filter_odd: "length (filter odd [0..<n]) = n div 2"
  by (induction n) simp_all

lemma filter_even_nth:
  assumes "i < length (filter even [0..<n])"
  shows "filter even [0..<n] ! i = 2 * i"
proof (cases "even n")
  case True
  then obtain n' where "n = 2 * n'" by blast
  then show ?thesis using filter_even_upt_even[of n'] assms by auto
next
  case False
  then obtain n' where "n = 2 * n' + 1" using oddE by blast
  show ?thesis
    using assms
    apply (simp only: \<open>n = 2 * n' + 1\<close> filter_even_upt_odd length_map nth_map)
    apply (intro arg_cong[where f = "(*) 2"])
    by (metis add_0 diff_zero length_upt nth_upt)
qed

lemma filter_odd_nth:
  assumes "i < length (filter odd [0..<n])"
  shows "filter odd [0..<n] ! i = 2 * i + 1"
proof (cases "even n")
  case True
  then obtain n' where "n = 2 * n'" by blast
  then show ?thesis using filter_odd_upt_even assms by auto
next
  case False
  then obtain n' where "n = 2 * n' + 1" using oddE by blast
  then show ?thesis
    using assms
    by (simp only: filter_odd_upt_odd length_map)
       (simp add: \<open>n = 2 * n' + 1\<close> length_filter_odd)
qed

fun sublist where
"sublist 0 n xs = take n xs"
| "sublist (Suc m) (Suc n) (a # xs) = sublist m n xs"
| "sublist (Suc m) 0 xs = []"
| "sublist (Suc m) (Suc n) [] = []"

lemma length_sublist[simp]: "length (sublist m n xs) = card ({m..<n} \<inter> {0..<length xs})"
  by (induction m n xs rule: sublist.induct) simp_all

lemma length_sublist':
  assumes "m \<le> n"
  assumes "n \<le> length xs"
  shows "length (sublist m n xs) = n - m"
  using assms by simp

lemma nth_sublist:
  assumes "m \<le> n"
  assumes "n \<le> length xs"
  assumes "i < n - m"
  shows "sublist m n xs ! i = xs ! (m + i)"
  using assms
  by (induction m n xs arbitrary: i rule: sublist.induct) simp_all

lemma filter_map_map2:
  assumes "length b = m"
  assumes "length c = m"
  shows "[f (b!i) (c!i). i \<leftarrow> [0..<m]] = map2 f b c"
  using assms by (intro nth_equalityI) simp_all

fun map3 where
"map3 f (x # xs) (y # ys) (z # zs) = f x y z # map3 f xs ys zs"
| "map3 f _ _ _ = []"

lemma map3_as_map: "map3 f xs ys zs = map (\<lambda>((x, y), z). f x y z) (zip (zip xs ys) zs)"
  by (induction f xs ys zs rule: map3.induct; simp)

lemma filter_map_map3:
  assumes "length b = m"
  assumes "length c = m"
  shows "[f (b!i) (c!i) i. i \<leftarrow> [0..<m]] = map3 f b c [0..<m]"
  using assms
  apply (intro nth_equalityI)
  unfolding map3_as_map by simp_all

fun map4 where
"map4 f (x # xs) (y # ys) (z # zs) (w # ws) = f x y z w # map4 f xs ys zs ws"
| "map4 f _ _ _ _ = []"

lemma map4_as_map: "map4 f xs ys zs ws = map (\<lambda>(((x,y),z),w). f x y z w) (zip (zip (zip xs ys) zs) ws)"
  by (induction f xs ys zs ws rule: map4.induct; simp)

lemma nth_map2:
  assumes "i < length xs"
  assumes "i < length ys"
  shows "map2 f xs ys ! i = f (xs ! i) (ys ! i)"
  using assms by simp
lemma nth_map3:
  assumes "i < length xs"
  assumes "i < length ys"
  assumes "i < length zs"
  shows "map3 f xs ys zs ! i = f (xs ! i) (ys ! i) (zs ! i)"
  using assms unfolding map3_as_map by simp
lemma nth_map4:
  assumes "i < length xs"
  assumes "i < length ys"
  assumes "i < length zs"
  assumes "i < length ws"
  shows "map4 f xs ys zs ws ! i = f (xs ! i) (ys ! i) (zs ! i) (ws ! i)"
  using assms unfolding map4_as_map by simp
lemma nth_map4':
  assumes "i < l"
  assumes "length xs = l"
  assumes "length ys = l"
  assumes "length zs = l"
  assumes "length ws = l"
  shows "map4 f xs ys zs ws ! i = f (xs ! i) (ys ! i) (zs ! i) (ws ! i)"
  using assms unfolding map4_as_map by simp

lemma map2_of_map_r: "map2 f xs (map g ys) = map2 (\<lambda>x y. f x (g y)) xs ys"
  by (intro nth_equalityI) simp_all
lemma map2_of_map_l: "map2 f (map g xs) ys = map2 (\<lambda>x y. f (g x) y) xs ys"
  by (intro nth_equalityI) simp_all
lemma map2_of_map2_r: "map2 f xs (map2 g ys zs) = map3 (\<lambda>x y z. f x (g y z)) xs ys zs"
  unfolding map3_as_map by (intro nth_equalityI) simp_all
lemma map_of_map3: "map f (map3 g xs ys zs) = map3 (\<lambda>x y z. f (g x y z)) xs ys zs"
  unfolding map3_as_map by (intro nth_equalityI) simp_all

lemma cyclic_index_lemma:
  fixes n :: nat
  assumes "\<sigma> < n" "\<rho> < n" "i < n"
  shows "(\<sigma> + \<rho>) mod n = i \<longleftrightarrow> \<rho> = (n + i - \<sigma>) mod n"
proof
  assume "(\<sigma> + \<rho>) mod n = i"
  then have "(int \<sigma> + int \<rho>) mod (int n) = int i"
    using zmod_int by fastforce
  also have "... = (int n + int i) mod int n"
    using \<open>i < n\<close> by auto
  finally have "(int \<sigma> + int \<rho> - int \<sigma>) mod (int n) = (int n + int i - int \<sigma>) mod int n"
    using mod_diff_cong by blast
  then have "(int \<rho>) mod (int n) = (int n + int i - int \<sigma>) mod (int n)"
    by simp
  also have "... = (int (n + i - \<sigma>)) mod (int n)"
    using assms by (simp add: int_ops(6))
  finally show "\<rho> = (n + i - \<sigma>) mod n"
    using zmod_int assms by (metis mod_less of_nat_eq_iff)
next
  assume "\<rho> = (n + i - \<sigma>) mod n"
  then have "(\<sigma> + \<rho>) mod n = (\<sigma> + (n + i - \<sigma>)) mod n"
    by presburger
  also have "... = (n + i) mod n"
    using assms by simp
  also have "... = i"
    using assms by simp
  finally show "(\<sigma> + \<rho>) mod n = i" .
qed

lemma (in residues) residues_minus_eq: "x \<ominus>\<^bsub>R\<^esub> y = (x - y) mod m"
proof -
  have "x \<ominus>\<^bsub>R\<^esub> y = x \<oplus>\<^bsub>R\<^esub> (\<ominus>\<^bsub>R\<^esub> y)"
    using a_minus_def by fast
  also have "\<ominus>\<^bsub>R\<^esub> y = (- y) mod m"
    using res_neg_eq[of y] .
  also have "x \<oplus>\<^bsub>R\<^esub> ((-y) mod m) = (x + ((-y) mod m)) mod m"
    by (simp add: R_m_def residue_ring_def)
  also have "... = (x - y) mod m"
    by (simp add: mod_add_right_eq)
  finally show ?thesis .
qed

lemma residue_ring_carrier_eq: "{0..(n::int) - 1} = {0..<n}"
  by auto

context ring
begin

fun nat_embedding :: "nat \<Rightarrow> 'a" where
"nat_embedding 0 = \<zero>"
| "nat_embedding (Suc n) = nat_embedding n \<oplus> \<one>"
fun int_embedding :: "int \<Rightarrow> 'a" where
"int_embedding n = (if n \<ge> 0 then nat_embedding (nat n) else \<ominus> nat_embedding (nat (-n)))"

lemma nat_embedding_closed[simp]: "nat_embedding x \<in> carrier R"
  by (induction x)(simp_all)
lemma int_embedding_closed[simp]: "int_embedding x \<in> carrier R"
  by simp

lemma nat_embedding_a_hom: "nat_embedding (x + y) = nat_embedding x \<oplus> nat_embedding y"
  apply (induction x arbitrary: y)
  using a_comm a_assoc by simp_all
lemma nat_embedding_m_hom: "nat_embedding (x * y) = nat_embedding x \<otimes> nat_embedding y"
  apply (induction x arbitrary: y)
  by (simp_all add: nat_embedding_a_hom l_distr a_comm)
lemma nat_embedding_exp_hom: "nat_embedding (x ^ y) = nat_embedding x [^] y"
  apply (induction y)
  by (simp_all add: nat_embedding_m_hom group_commutes_pow)
lemma int_embedding_neg_hom: "int_embedding (- x) = \<ominus> int_embedding x"
  by simp

end

lemma int_exp_hom: "int x ^ i = int (x ^ i)"
  by simp

end