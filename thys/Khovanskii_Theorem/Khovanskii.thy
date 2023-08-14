section\<open>Khovanskii's Theorem\<close>

text\<open>We formalise the proof of an important theorem in additive combinatorics due to Khovanskii,
attesting that the cardinality of the set of all sums of $n$ many elements of $A$,
where $A$ is a finite subset of an abelian group, is a polynomial in $n$ for all sufficiently large $n$.
We follow a proof due to Nathanson and Ruzsa as presented in the notes
``Introduction to Additive Combinatorics'' by Timothy Gowers for the University of Cambridge.\<close>

theory Khovanskii
  imports
    FiniteProduct
    "Pluennecke_Ruzsa_Inequality.Pluennecke_Ruzsa_Inequality"
    "Bernoulli.Bernoulli"               \<comment> \<open>sums of a fixed power are polynomials\<close>
    "HOL-Analysis.Weierstrass_Theorems" \<comment> \<open>needed for polynomial function\<close>
    "HOL-Library.List_Lenlexorder"      \<comment> \<open>lexicographic ordering for the type @{typ \<open>nat list\<close>}\<close>
begin

(*FIXME: move this, and Transcendental's sum_up_index_split maybe to Set_Interval*)
lemma sum_diff_split:
  fixes f:: "nat \<Rightarrow> 'a::ab_group_add"
  assumes "m \<le> n"
  shows "(\<Sum>i\<le>n - m. f(n - i)) = (\<Sum>i\<le>n. f i) - (\<Sum>i<m. f i)"
proof -
  have inj: "inj_on ((-) n) {m..n}"
    by (auto simp: inj_on_def)
  have "(\<Sum>i\<le>n - m. f(n - i)) = (\<Sum>i\<in>(-) n ` {m..n}. f(n - i))"
  proof (rule sum.cong)
    have "\<And>x. x \<le> n - m \<Longrightarrow> \<exists>k\<ge>m. k \<le> n \<and> x = n - k"
      by (metis assms diff_diff_cancel diff_le_mono2 diff_le_self le_trans)
    then show "{..n - m} = (-) n ` {m..n}"
      by (auto simp: image_iff Bex_def)
  qed auto
  also have "\<dots> = (\<Sum>i=m..n. f i)"
    by (smt (verit) atLeastAtMost_iff diff_diff_cancel sum.reindex_cong [OF inj])
  also have "\<dots> = (\<Sum>i\<le>n. f i) - (\<Sum>i<m. f i)"
    using sum_diff_nat_ivl[of 0 "m" "Suc n" f] assms 
    by (simp only: atLeast0AtMost atLeast0LessThan atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis .
qed

text \<open>The sum of the elements of a list\<close>
abbreviation "\<sigma> \<equiv> sum_list"

text \<open>Related to the nsets of Ramsey.thy, but simpler\<close>
definition finsets :: "['a set, nat] \<Rightarrow> 'a set set"
  where "finsets A n \<equiv> {N. N \<subseteq> A \<and> card N = n}"

lemma card_finsets: "finite N \<Longrightarrow> card (finsets N k) = card N choose k"
  by (simp add: finsets_def n_subsets)

lemma sorted_map_plus_iff [simp]:
  fixes a::"'a::linordered_cancel_ab_semigroup_add"
  shows "sorted (map ((+) a) xs) \<longleftrightarrow> sorted xs"
  by (induction xs) auto

lemma distinct_map_plus_iff [simp]:
  fixes a::"'a::linordered_cancel_ab_semigroup_add"
  shows "distinct (map ((+) a) xs) \<longleftrightarrow> distinct xs"
  by (induction xs) auto

subsection \<open>Arithmetic operations on lists, pointwise on the elements\<close>

text \<open>Weak type class properties.
 Cancellation is difficult to arrange because of complications when lists differ in length.\<close>

instantiation list :: (plus) plus
begin
definition "plus_list \<equiv> map2 (+)"
instance..
end

lemma length_plus_list [simp]:
  fixes xs :: "'a::plus list"
  shows "length (xs+ys) = min (length xs) (length ys)"
  by (simp add: plus_list_def)

lemma plus_Nil [simp]: "[] + xs = []"
  by (simp add: plus_list_def)

lemma plus_Cons: "(y # ys) + (x # xs) = (y+x) # (ys+xs)"
  by (simp add: plus_list_def)

lemma nth_plus_list [simp]:
  fixes xs :: "'a::plus list"
  assumes "i < length xs" "i < length ys"
  shows "(xs+ys)!i = xs!i + ys!i"
  by (simp add: plus_list_def assms)


instantiation list :: (minus) minus
begin
definition "minus_list \<equiv> map2 (-)"
instance..
end

lemma length_minus_list [simp]:
  fixes xs :: "'a::minus list"
  shows "length (xs-ys) = min (length xs) (length ys)"
  by (simp add: minus_list_def)

lemma minus_Nil [simp]: "[] - xs = []"
  by (simp add: minus_list_def)

lemma minus_Cons: "(y # ys) - (x # xs) = (y-x) # (ys-xs)"
  by (simp add: minus_list_def)

lemma nth_minus_list [simp]:
  fixes xs :: "'a::minus list"
  assumes "i < length xs" "i < length ys"
  shows "(xs-ys)!i = xs!i - ys!i"
  by (simp add: minus_list_def assms)

instance list :: (ab_semigroup_add) ab_semigroup_add
proof
  have "map2 (+) (map2 (+) xs ys) zs = map2 (+) xs (map2 (+) ys zs)" for xs ys zs :: "'a list"
  proof (induction xs arbitrary: ys zs)
    case (Cons x xs)
    show ?case
    proof (cases "ys=[] \<or> zs=[]")
      case False
      then obtain y ys' z zs' where "ys = y#ys'" "zs = z # zs'"
        by (meson list.exhaust)
      then show ?thesis
        by (simp add: Cons add.assoc)
    qed auto
  qed auto
  then show "a + b + c = a + (b + c)" for a b c :: "'a list"
    by (auto simp: plus_list_def)
next
  have "map2 (+) xs ys = map2 (+) ys xs" for xs ys :: "'a list"
  proof (induction xs arbitrary: ys)
    case (Cons x xs)
    show ?case
    proof (cases ys)
      case (Cons y ys')
      then show ?thesis
        by (simp add: Cons.IH add.commute)
    qed auto
  qed auto
  then show "a + b = b + a" for a b :: "'a list"
    by (auto simp: plus_list_def)
qed


subsection \<open>The pointwise ordering on two equal-length lists of natural numbers\<close>

text \<open>Gowers uses the usual symbol ($\le$) for his pointwise ordering.
   In our development, $\le$ is the lexicographic ordering and $\unlhd$ is the pointwise ordering.\<close>

definition pointwise_le :: "[nat list, nat list] \<Rightarrow> bool" (infixr "\<unlhd>" 50 )
  where "x \<unlhd> y \<equiv> list_all2 (\<le>) x y"

definition pointwise_less :: "[nat list, nat list] \<Rightarrow> bool" (infixr "\<lhd>" 50 )
  where "x \<lhd> y \<equiv> x \<unlhd> y \<and> x \<noteq> y"

lemma pointwise_le_iff_nth:
  "x \<unlhd> y \<longleftrightarrow> length x = length y \<and> (\<forall>i < length x. x!i \<le> y!i)"
  by (simp add: list_all2_conv_all_nth pointwise_le_def)

lemma pointwise_le_iff:
  "x \<unlhd> y \<longleftrightarrow> length x = length y \<and> (\<forall>(i,j) \<in> set (zip x y). i\<le>j)"
  by (simp add: list_all2_iff pointwise_le_def)

lemma pointwise_append_le_iff [simp]: "u@x \<unlhd> u@y \<longleftrightarrow> x \<unlhd> y"
  by (auto simp: pointwise_le_iff_nth nth_append)

lemma pointwise_le_refl [iff]: "x \<unlhd> x"
  by (simp add: list.rel_refl pointwise_le_def)

lemma pointwise_le_antisym: "\<lbrakk>x \<unlhd> y; y \<unlhd> x\<rbrakk> \<Longrightarrow> x=y"
  by (metis antisym list_all2_antisym pointwise_le_def)

lemma pointwise_le_trans: "\<lbrakk>x \<unlhd> y; y \<unlhd> z\<rbrakk> \<Longrightarrow> x \<unlhd> z"
  by (smt (verit, del_insts) le_trans list_all2_trans pointwise_le_def)

lemma pointwise_le_Nil [simp]: "Nil \<unlhd> x \<longleftrightarrow> x = Nil"
  by (simp add: pointwise_le_def)

lemma pointwise_le_Nil2 [simp]: "x \<unlhd> Nil \<longleftrightarrow> x = Nil"
  by (simp add: pointwise_le_def)

lemma pointwise_le_iff_less_equal: "x \<unlhd> y \<longleftrightarrow> x \<lhd> y \<or> x = y"
  using pointwise_less_def by blast

lemma pointwise_less_iff:
  "x \<lhd> y \<longleftrightarrow> x \<unlhd> y \<and> (\<exists>(i,j) \<in> set (zip x y). i<j)"
  using list_eq_iff_zip_eq pointwise_le_iff pointwise_less_def by fastforce

lemma pointwise_less_iff2: "x \<lhd> y \<longleftrightarrow> x \<unlhd> y \<and> (\<exists>k < length x. x!k <y ! k)"
  unfolding pointwise_less_def pointwise_le_iff_nth
  by (fastforce intro!: nth_equalityI)

lemma pointwise_less_Nil [simp]: "\<not> Nil \<lhd> x"
  by (simp add: pointwise_less_def)

lemma pointwise_less_Nil2 [simp]: "\<not> x \<lhd> Nil"
  by (simp add: pointwise_less_def)

lemma zero_pointwise_le_iff [simp]: "replicate r 0 \<unlhd> x \<longleftrightarrow> length x = r"
  by (auto simp: pointwise_le_iff_nth)

lemma pointwise_le_imp_\<sigma>:
  assumes "xs \<unlhd> ys" shows "\<sigma> xs \<le> \<sigma> ys"
  using assms
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case
    by (simp add: pointwise_le_iff)
next
  case (Cons y ys)
  then obtain x xs' where "x\<le>y" "xs = x#xs'" "xs' \<unlhd> ys"
    by (auto simp: pointwise_le_def list_all2_Cons2)
  then show ?case
    by (simp add: Cons.IH add_le_mono)
qed

lemma sum_list_plus:
  fixes xs :: "'a::comm_monoid_add list"
  assumes "length xs = length ys" shows "\<sigma> (xs + ys) = \<sigma> xs + \<sigma> ys"
  using assms by (simp add: plus_list_def case_prod_unfold sum_list_addf)

lemma sum_list_minus:
  assumes "xs \<unlhd> ys" shows "\<sigma> (ys - xs) = \<sigma> ys - \<sigma> xs"
  using assms
proof (induction ys arbitrary: xs)
  case (Cons y ys)
  then obtain x xs' where "x\<le>y" "xs = x#xs'" "xs' \<unlhd> ys"
    by (auto simp: pointwise_le_def list_all2_Cons2)
  then show ?case
    using pointwise_le_imp_\<sigma> by (auto simp: Cons minus_Cons)
qed (auto simp: in_set_conv_nth)


subsection \<open>Pointwise minimum and maximum of a set of lists\<close>

definition min_pointwise :: "[nat, nat list set] \<Rightarrow> nat list"
  where "min_pointwise \<equiv> \<lambda>r U. map (\<lambda>i. Min ((\<lambda>u. u!i) ` U)) [0..<r]"

lemma min_pointwise_le: "\<lbrakk>u \<in> U; finite U\<rbrakk> \<Longrightarrow> min_pointwise (length u) U \<unlhd> u"
  by (simp add: min_pointwise_def pointwise_le_iff_nth)

lemma min_pointwise_ge_iff:
  assumes "finite U" "U \<noteq> {}" "\<And>u. u \<in> U \<Longrightarrow> length u = r" "length x = r"
  shows "x \<unlhd> min_pointwise r U \<longleftrightarrow> (\<forall>u \<in> U. x \<unlhd> u)"
  by (auto simp: min_pointwise_def pointwise_le_iff_nth assms)

definition max_pointwise :: "[nat, nat list set] \<Rightarrow> nat list"
  where "max_pointwise \<equiv> \<lambda>r U. map (\<lambda>i. Max ((\<lambda>u. u!i) ` U)) [0..<r]"

lemma max_pointwise_ge: "\<lbrakk>u \<in> U; finite U\<rbrakk> \<Longrightarrow> u \<unlhd> max_pointwise (length u) U"
  by (simp add: max_pointwise_def pointwise_le_iff_nth)

lemma max_pointwise_le_iff:
  assumes "finite U" "U \<noteq> {}" "\<And>u. u \<in> U \<Longrightarrow> length u = r" "length x = r"
  shows "max_pointwise r U \<unlhd> x \<longleftrightarrow> (\<forall>u \<in> U. u \<unlhd> x)"
  by (auto simp: max_pointwise_def pointwise_le_iff_nth assms)

lemma max_pointwise_mono:
  assumes "X' \<subseteq> X" "finite X" "X' \<noteq> {}"
  shows  "max_pointwise r X' \<unlhd> max_pointwise r X"
  using assms by (simp add: max_pointwise_def pointwise_le_iff_nth Max_mono image_mono)

lemma pointwise_le_plus: "\<lbrakk>xs \<unlhd> ys; length ys \<le> length zs\<rbrakk> \<Longrightarrow> xs \<unlhd> ys+zs"
proof (induction xs arbitrary: ys zs)
  case (Cons x xs)
  then obtain y ys' z zs' where "ys = y#ys'" "zs = z#zs'"
    unfolding pointwise_le_iff by (metis Suc_le_length_iff le_refl length_Cons)
  with Cons show ?case
    by (auto simp: plus_list_def pointwise_le_def)
qed (simp add: pointwise_le_iff)

lemma pairwise_minus_cancel: "\<lbrakk>z \<unlhd> x;  z \<unlhd> y; x - z = y - z\<rbrakk> \<Longrightarrow> x = y"
  unfolding pointwise_le_iff_nth by (metis eq_diff_iff nth_equalityI nth_minus_list)


subsection \<open>A locale to fix the finite subset @{term "A \<subseteq> G"}\<close>

locale Khovanskii = additive_abelian_group +
  fixes A :: "'a set"
  assumes AsubG: "A \<subseteq> G" and finA: "finite A"

begin

text \<open>finite products of a group element\<close>
definition Gmult :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "Gmult a n \<equiv> (((\<oplus>)a) ^^ n) \<zero>"

lemma Gmult_0 [simp]: "Gmult a 0 = \<zero>"
  by (simp add: Gmult_def)

lemma Gmult_1 [simp]: "a \<in> G \<Longrightarrow> Gmult a (Suc 0) = a"
  by (simp add: Gmult_def)

lemma Gmult_Suc [simp]: "Gmult a (Suc n) = a \<oplus> Gmult a n"
  by (simp add: Gmult_def)

lemma Gmult_in_G [simp,intro]: "a \<in> G \<Longrightarrow> Gmult a n \<in> G"
  by (induction n) auto

lemma Gmult_add_add:
  assumes "a \<in> G"
  shows "Gmult a (m+n) = Gmult a m \<oplus> Gmult a n"
  by (induction m) (use assms local.associative in fastforce)+

lemma Gmult_add_diff:
  assumes "a \<in> G"
  shows "Gmult a (n+k) \<ominus> Gmult a n = Gmult a k"
  by (metis Gmult_add_add Gmult_in_G assms commutative inverse_closed invertible invertible_left_inverse2)

lemma Gmult_diff:
  assumes "a \<in> G" "n\<le>m"
  shows "Gmult a m \<ominus> Gmult a n = Gmult a (m-n)"
  by (metis Gmult_add_diff assms le_add_diff_inverse)


text \<open>Mapping elements of @{term A} to their numeric subscript\<close>
abbreviation "idx \<equiv> to_nat_on A"

text \<open>The elements of @{term A} in order\<close>
definition aA :: "'a list"
  where "aA \<equiv> map (from_nat_into A) [0..<card A]"

definition \<alpha> :: "nat list \<Rightarrow> 'a"
  where "\<alpha> \<equiv> \<lambda>x. fincomp (\<lambda>i. Gmult (aA!i) (x!i)) {..<card A}"

text \<open>The underlying assumption is @{term "length y = length x"}\<close>
definition useless:: "nat list  \<Rightarrow> bool"
  where "useless x \<equiv> \<exists>y < x. \<sigma> y = \<sigma> x \<and> \<alpha> y = \<alpha> x \<and> length y = length x"

abbreviation "useful x \<equiv> \<not> useless x"

lemma alpha_replicate_0 [simp]: "\<alpha> (replicate (card A) 0) = \<zero>"
  by (auto simp: \<alpha>_def intro: fincomp_unit_eqI)

lemma idx_less_cardA:
  assumes "a \<in> A" shows "idx a < card A"
  by (metis assms bij_betw_def finA imageI lessThan_iff to_nat_on_finite)

lemma aA_idx_eq [simp]:
  assumes "a \<in> A" shows "aA ! (idx a) = a"
  by (simp add: aA_def assms countable_finite finA idx_less_cardA)

lemma set_aA: "set aA = A"
  using bij_betw_from_nat_into_finite [OF finA]
  by (simp add: aA_def atLeast0LessThan bij_betw_def)

lemma nth_aA_in_G [simp]: "i < card A \<Longrightarrow> aA!i \<in> G"
  using AsubG aA_def set_aA by auto

lemma alpha_in_G [iff]: "\<alpha> x \<in> G"
  using nth_aA_in_G fincomp_closed by (simp add: \<alpha>_def)

lemma Gmult_in_PiG [simp]: "(\<lambda>i. Gmult (aA!i) (f i)) \<in> {..<card A} \<rightarrow> G"
  by simp

lemma alpha_plus:
  assumes "length x = card A" "length y = card A"
  shows "\<alpha> (x + y) = \<alpha> x \<oplus> \<alpha> y"
proof -
  have "\<alpha> (x + y) = fincomp (\<lambda>i. Gmult (aA!i) (map2 (+) x y!i)) {..<card A}"
    by (simp add: \<alpha>_def plus_list_def)
  also have "\<dots> = fincomp (\<lambda>i. Gmult (aA!i) (x!i + y!i)) {..<card A}"
    by (intro fincomp_cong'; simp add: assms)
  also have "\<dots> = fincomp (\<lambda>i. Gmult (aA!i) (x!i) \<oplus> Gmult (aA!i) (y!i)) {..<card A}"
    by (intro fincomp_cong'; simp add: Gmult_add_add)
  also have "\<dots> = \<alpha> x \<oplus> \<alpha> y"
    by (simp add: \<alpha>_def fincomp_comp)
  finally show ?thesis .
qed

lemma alpha_minus:
  assumes "y \<unlhd> x" "length y = card A"
  shows "\<alpha> (x - y) = \<alpha> x \<ominus> \<alpha> y"
proof -
  have "\<alpha> (x - y) = fincomp (\<lambda>i. Gmult (aA!i) (map2 (-) x y!i)) {..<card A}"
    by (simp add: \<alpha>_def minus_list_def)
  also have "\<dots> = fincomp (\<lambda>i. Gmult (aA!i) (x!i - y!i)) {..<card A}"
    using assms by (intro fincomp_cong') (auto simp: pointwise_le_iff)
  also have "\<dots> = fincomp (\<lambda>i. Gmult (aA!i) (x!i) \<ominus> Gmult (aA!i) (y!i)) {..<card A}"
    using assms
    by (intro fincomp_cong') (simp add: pointwise_le_iff_nth Gmult_diff)+
  also have "\<dots> = \<alpha> x \<ominus> \<alpha> y"
    by (simp add: \<alpha>_def fincomp_comp fincomp_inverse)
  finally show ?thesis .
qed

subsection \<open>Adding one to a list element\<close>

definition list_incr :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where "list_incr i x \<equiv> x[i := Suc (x!i)]"

lemma list_incr_Nil [simp]: "list_incr i [] = []"
  by (simp add: list_incr_def)

lemma list_incr_Cons [simp]: "list_incr (Suc i) (k#ks) = k # list_incr i ks"
  by (simp add: list_incr_def)

lemma sum_list_incr [simp]: "i < length x \<Longrightarrow> \<sigma> (list_incr i x) = Suc (\<sigma> x)"
  by (auto simp: list_incr_def sum_list_update)

lemma length_list_incr [simp]: "length (list_incr i x) = length x"
  by (auto simp: list_incr_def)

lemma nth_le_list_incr: "i < card A \<Longrightarrow> x!i \<le> list_incr (idx a) x!i"
  unfolding list_incr_def
  by (metis Suc_leD linorder_not_less list_update_beyond nth_list_update_eq nth_list_update_neq order_refl)

lemma list_incr_nth_diff: "i < length x \<Longrightarrow> list_incr j x!i - x!i = (if i = j then 1 else 0)"
  by (simp add: list_incr_def)

subsection \<open>The set of all @{term r}-tuples that sum to @{term n}\<close>

definition length_sum_set :: "nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where "length_sum_set r n \<equiv> {x. length x = r \<and> \<sigma> x = n}"

lemma length_sum_set_Nil [simp]: "length_sum_set 0 n = (if n=0 then {[]} else {})"
  by (auto simp: length_sum_set_def)

lemma length_sum_set_Suc [simp]: "k#ks \<in> length_sum_set (Suc r) n \<longleftrightarrow> (\<exists>m. ks \<in> length_sum_set r m \<and> n = m+k)"
  by (auto simp: length_sum_set_def)

lemma length_sum_set_Suc_eqpoll: "length_sum_set (Suc r) n \<approx> Sigma {..n} (\<lambda>i. length_sum_set r (n-i))" (is "?L \<approx> ?R")
  unfolding eqpoll_def
proof
  let ?f = "(\<lambda>l. (hd l, tl l))"
  show "bij_betw ?f ?L ?R"
  proof (intro bij_betw_imageI)
    show "inj_on ?f ?L"
      by (force simp: inj_on_def length_sum_set_def intro: list.expand)
    show "?f ` ?L = ?R"
      by (force simp: length_sum_set_def length_Suc_conv)
  qed
qed

lemma finite_length_sum_set: "finite (length_sum_set r n)"
proof (induction r arbitrary: n)
  case 0
  then show ?case
    by (auto simp: length_sum_set_def)
next
  case (Suc r)
  then show ?case
    using length_sum_set_Suc_eqpoll eqpoll_finite_iff by blast
qed

lemma card_length_sum_set: "card (length_sum_set (Suc r) n) = (\<Sum>i\<le>n. card (length_sum_set r (n-i)))"
proof -
  have "card (length_sum_set (Suc r) n) = card (Sigma {..n} (\<lambda>i. length_sum_set r (n-i)))"
    by (metis eqpoll_finite_iff eqpoll_iff_card finite_length_sum_set length_sum_set_Suc_eqpoll)
  also have "\<dots> = (\<Sum>i\<le>n. card (length_sum_set r (n-i)))"
    by (simp add: finite_length_sum_set)
  finally show ?thesis .
qed

lemma sum_up_index_split':
  assumes "N \<le> n" shows "(\<Sum>i\<le>n. f i) = (\<Sum>i\<le>n-N. f i) + (\<Sum>i=Suc (n-N)..n. f i)"
  by (metis assms diff_add sum_up_index_split)

lemma sum_invert: "N \<le> n \<Longrightarrow> (\<Sum>i = Suc (n - N)..n. f (n - i)) = (\<Sum>j<N. f j)"
proof (induction N)
  case (Suc N)
  then show ?case
    apply (auto simp: Suc_diff_Suc)
    by (metis sum.atLeast_Suc_atMost Suc_leD add.commute diff_diff_cancel diff_le_self)
qed auto

lemma real_polynomial_function_length_sum_set:
  "\<exists>p. real_polynomial_function p \<and> (\<forall>n>0. real (card (length_sum_set r n)) = p (real n))"
proof (induction r)
  case 0
  have "\<forall>n>0. real (card (length_sum_set 0 n)) = 0"
    by auto
  then show ?case
    by blast
next
  case (Suc r)
  then obtain p where poly: "real_polynomial_function p"
    and p: "\<And>n. n>0 \<Longrightarrow> real (card (length_sum_set r n)) = p (real n)"
    by blast
  then obtain a n where p_eq: "p = (\<lambda>x. \<Sum>i\<le>n. a i * x ^ i)"
    using real_polynomial_function_iff_sum by auto
  define q where "q \<equiv> \<lambda>x. \<Sum>j\<le>n. a j * ((bernpoly (Suc j) (1 + x) - bernpoly (Suc j) 0)
                                     / (1 + real j) - 0 ^ j)"
  have rp_q: "real_polynomial_function q"
    by (fastforce simp: bernpoly_def p_eq q_def)
  have q_eq: "(\<Sum>x\<le>k - 1. p (real (k - x))) = q (real k)" if "k>0" for k
    using that
    by (simp add: p_eq q_def sum.swap add.commute sum_of_powers sum_diff_split[where f="\<lambda>i. real i ^ _"]
             flip: sum_distrib_left)
  define p' where "p' \<equiv> \<lambda>x. q x + real (card (length_sum_set r 0))"
  have "real_polynomial_function p'"
    using rp_q by (force simp: p'_def)
  moreover have "(\<Sum>x\<le>n - Suc 0. p (real (n - x))) +
                real (card (length_sum_set r 0)) = p' (real n)" if "n>0" for n
    using that q_eq by (auto simp: p'_def)
  ultimately show ?case
    unfolding card_length_sum_set
    by (force simp: sum_up_index_split' [of 1] p sum_invert)
qed

lemma all_zeroes_replicate: "length_sum_set r 0 = {replicate r 0}"
  by (auto simp: length_sum_set_def replicate_eqI)

lemma length_sum_set_Suc_eq_UN: "length_sum_set r (Suc n) = (\<Union>i<r. list_incr i ` length_sum_set r n)"
proof -
  have "\<exists>i<r. x \<in> list_incr i ` length_sum_set r n"
    if "\<sigma> x = Suc n" and "r = length x" for x
  proof -
    have "x \<noteq> replicate r 0"
      using that by (metis sum_list_replicate Zero_not_Suc mult_zero_right)
    then obtain i where i: "i < r" "x!i \<noteq> 0"
      by (metis \<open>r = length x\<close> in_set_conv_nth replicate_eqI)
    with that have "x[i := x!i - 1] \<in> length_sum_set r n"
      by (simp add: sum_list_update length_sum_set_def)
    with i that show ?thesis
      unfolding list_incr_def by force
  qed
  then show ?thesis
    by (auto simp: length_sum_set_def Bex_def)
qed

lemma alpha_list_incr:
  assumes "a \<in> A" "x \<in> length_sum_set (card A) n"
  shows "\<alpha> (list_incr (idx a) x) = a \<oplus> \<alpha> x"
proof -
  have lenx: "length x = card A"
    using assms length_sum_set_def by blast
  have "\<alpha> (list_incr (idx a) x) \<ominus> \<alpha> x = fincomp (\<lambda>i. Gmult (aA!i) (list_incr (idx a) x!i) \<ominus> Gmult (aA!i) (x!i)) {..<card A}"
    by (simp add: \<alpha>_def fincomp_comp fincomp_inverse)
  also have "\<dots> = fincomp (\<lambda>i. Gmult (aA!i) (list_incr (idx a) x!i - x!i)) {..<card A}"
    by (intro fincomp_cong; simp add: Gmult_diff nth_le_list_incr)
  also have "\<dots> = fincomp (\<lambda>i. if i = idx a then (aA!i) else \<zero>) {..<card A}"
    by (intro fincomp_cong'; simp add: list_incr_nth_diff lenx)
  also have "\<dots> = a"
    using assms by (simp add: fincomp_singleton_swap idx_less_cardA)
  finally have "\<alpha> (list_incr (idx a) x) \<ominus> \<alpha> x = a" .
  then show ?thesis
    by (metis alpha_in_G associative inverse_closed invertible invertible_left_inverse right_unit)
qed

lemma sumset_iterated_enum:
  defines "r \<equiv> card A"
  shows "sumset_iterated A n = \<alpha> ` length_sum_set r n"
proof (induction n)
  case 0
  then show ?case
    by (simp add: all_zeroes_replicate r_def)
next
  case (Suc n)
  have eq: "{..<r} = idx ` A"
    by (metis bij_betw_def finA r_def to_nat_on_finite)
  have "sumset_iterated A (Suc n) = (\<Union>a\<in>A. (\<lambda>i. a \<oplus> \<alpha> i) ` length_sum_set r n)"
    using AsubG by (auto simp: Suc sumset)
  also have "\<dots> = (\<Union>a\<in>A. (\<lambda>i. \<alpha> (list_incr (idx a) i)) ` length_sum_set r n)"
    by (simp add: alpha_list_incr r_def)
  also have "\<dots> = \<alpha> ` length_sum_set r (Suc n)"
    by (simp add: image_UN image_comp length_sum_set_Suc_eq_UN eq)
  finally show ?case .
qed

subsection \<open>Lemma 2.7 in Gowers's notes\<close>

text\<open>The following lemma corresponds to a key fact about the cardinality of the set of all sums of
$n$ many elements of $A$, stated before Gowers's Lemma 2.7.\<close>

lemma card_sumset_iterated_length_sum_set_useful:
  defines "r \<equiv> card A"
  shows "card(sumset_iterated A n) = card (length_sum_set r n \<inter> {x. useful x})"
    (is "card ?L = card ?R")
proof -
  have "\<alpha> x \<in> \<alpha> ` (length_sum_set r n \<inter> {x. useful x})"
    if "x \<in> length_sum_set r n" for x
  proof -
    define y where "y \<equiv> LEAST y. y \<in> length_sum_set r n \<and> \<alpha> y = \<alpha> x"
    have y: "y \<in> length_sum_set (card A) n \<and> \<alpha> y = \<alpha> x"
      by (metis (mono_tags, lifting) LeastI r_def y_def that)
    moreover
    have "useful y"
    proof (clarsimp simp: useless_def)
      show False
        if "\<sigma> z = \<sigma> y" "length z = length y" and "z < y" "\<alpha> z = \<alpha> y" for z
        using that Least_le length_sum_set_def not_less_Least r_def y y_def by fastforce
    qed
    ultimately show ?thesis
      unfolding image_iff length_sum_set_def r_def by (smt (verit) Int_Collect)
  qed
  then have "sumset_iterated A n = \<alpha> ` (length_sum_set r n \<inter> {x. useful x})"
    by (auto simp: sumset_iterated_enum length_sum_set_def r_def)
  moreover have "inj_on \<alpha> (length_sum_set r n \<inter> {x. useful x})"
    apply (simp add: image_iff length_sum_set_def r_def inj_on_def useless_def Ball_def)
    by (metis linorder_less_linear)
  ultimately show ?thesis
    by (simp add: card_image length_sum_set_def)
qed

text\<open>The following lemma corresponds to Lemma 2.7 in Gowers's notes.\<close>

lemma useless_leq_useless:
  defines "r \<equiv> card A"
  assumes "useless x" and "x \<unlhd> y" and "length x = r"
  shows "useless y "
proof -
  have leny: "length y = r"
    using pointwise_le_iff assms by auto
  obtain x' where "x'< x" and \<sigma>x': "\<sigma> x' = \<sigma> x" and \<alpha>x': "\<alpha> x' = \<alpha> x" and lenx': "length x' = length x"
    using assms useless_def by blast
  obtain i where "i < card A" and xi: "x'!i < x!i" and takex': "take i x' = take i x"
    using \<open>x'<x\<close> lenx' assms by (auto simp: list_less_def lenlex_def elim!: lex_take_index)
  define y' where "y' \<equiv> y+x'-x"
  have leny': "length y' = length y"
    using assms lenx' pointwise_le_iff  by (simp add: y'_def)
  have "x!i \<le> y!i"
    using \<open>x \<unlhd> y\<close> \<open>i < card A\<close> assms by (simp add: pointwise_le_iff_nth)
  then have "y'!i < y!i"
    using \<open>i < card A\<close> assms lenx' xi pointwise_le_iff by (simp add: y'_def plus_list_def minus_list_def)
  moreover have "take i y' = take i y"
  proof (intro nth_equalityI)
    show "length (take i y') = length (take i y)"
      by (simp add: leny')
    show "\<And>k. k < length (take i y') \<Longrightarrow> take i y' ! k = take i y!k"
      using takex' by (simp add: y'_def plus_list_def minus_list_def take_map take_zip)
  qed
  ultimately have "y' < y"
    using leny' \<open>i < card A\<close> assms pointwise_le_iff
    by (auto simp: list_less_def lenlex_def lexord_lex lexord_take_index_conv)
  moreover have "\<sigma> y' = \<sigma> y"
    using assms
    by (simp add: \<sigma>x' lenx' leny pointwise_le_plus sum_list_minus sum_list_plus y'_def)
  moreover have "\<alpha> y' = \<alpha> y"
    using assms lenx' \<alpha>x' leny
    by (fastforce simp: y'_def pointwise_le_plus alpha_minus alpha_plus local.associative)
  ultimately show ?thesis
    using leny' useless_def by blast
qed


inductive_set minimal_elements for U
  where "\<lbrakk>x \<in> U; \<And>y. y \<in> U \<Longrightarrow> \<not> y \<lhd> x\<rbrakk> \<Longrightarrow> x \<in> minimal_elements U"


lemma pointwise_less_imp_\<sigma>:
  assumes "xs \<lhd> ys" shows "\<sigma> xs < \<sigma> ys"
proof -
  have eq: "length ys = length xs" and "xs \<unlhd> ys"
    using assms by (auto simp: pointwise_le_iff pointwise_less_iff)
  have "\<forall>k<length xs. xs!k \<le> ys!k"
    using \<open>xs \<unlhd> ys\<close> list_all2_nthD pointwise_le_def by auto
  moreover have "\<exists>k<length xs. xs!k < ys!k"
    using assms pointwise_less_iff2 by force
  ultimately show ?thesis
    by (force simp: eq sum_list_sum_nth intro: sum_strict_mono_ex1)
qed

lemma wf_measure_\<sigma>: "wf (inv_image less_than \<sigma>)"
  by blast

lemma WFP: "wfP (\<lhd>)"
  by (auto simp: wfP_def pointwise_less_imp_\<sigma> intro: wf_subset [OF wf_measure_\<sigma>])

text\<open>The following is a direct corollary of the above lemma, i.e. a corollary of
 Lemma 2.7 in Gowers's notes.\<close>

corollary useless_iff:
  assumes "length x = card A"
  shows "useless x \<longleftrightarrow> (\<exists>x' \<in> minimal_elements (Collect useless). x' \<unlhd> x)"  (is "_=?R")
proof
  assume "useless x"
  obtain z where z: "useless z" "z \<unlhd> x" and zmin: "\<And>y. y \<lhd> z \<Longrightarrow> y \<unlhd> x \<Longrightarrow> useful y"
    using wfE_min [to_pred, where Q = "{z. useless z \<and> z \<unlhd> x}", OF WFP]
    by (metis (no_types, lifting) \<open>useless x\<close> mem_Collect_eq pointwise_le_refl)
  then show ?R
    by (smt (verit) mem_Collect_eq minimal_elements.intros pointwise_le_trans pointwise_less_def)
next
  assume ?R
  with useless_leq_useless minimal_elements.cases show "useless x"
    by (metis assms mem_Collect_eq pointwise_le_iff)
qed

subsection \<open>The set of minimal elements of a set of $r$-tuples is finite\<close>

text\<open>The following general finiteness claim corresponds to Lemma 2.8 in Gowers's notes and is key to
the main proof.\<close>

lemma minimal_elements_set_tuples_finite:
  assumes Ur: "\<And>x. x \<in> U \<Longrightarrow> length x = r"
  shows "finite (minimal_elements U)"
  using assms
proof (induction r arbitrary: U)
  case 0
  then have "U \<subseteq> {[]}"
    by auto
  then show ?case
    by (metis finite.simps minimal_elements.cases finite_subset subset_eq)
next
  case (Suc r)
  show ?case
  proof (cases "U={}")
    case True
    with Suc.IH show ?thesis by blast
  next
    case False
    then obtain u where u: "u \<in> U" and zmin: "\<And>y. y \<lhd> u \<Longrightarrow> y \<notin> U"
      using wfE_min [to_pred, where Q = "U", OF WFP] by blast
    define V where "V = {v \<in> U. \<not> u \<unlhd> v}"
    define VF where "VF \<equiv> \<lambda>i t. {v \<in> V. v!i = t}"
    have [simp]: "length v = Suc r" if "v \<in> VF i t" for v i t
      using that by (simp add: Suc.prems VF_def V_def)
    have *: "\<exists>i\<le>r. v!i < u!i" if "v \<in> V" for v
      using that u Suc.prems
      by (force simp: V_def pointwise_le_iff_nth not_le less_Suc_eq_le)
    with u have "minimal_elements U \<le> insert u (\<Union>i\<le>r. \<Union>t < u!i. minimal_elements (VF i t))"
      by (force simp: VF_def V_def minimal_elements.simps pointwise_less_def)
    moreover
    have "finite (minimal_elements (VF i t))" if "i\<le>r" "t < u!i" for i t
    proof -
      define delete where "delete \<equiv> \<lambda>v::nat list. take i v @ drop (Suc i) v" \<comment> \<open>deletion of @{term i}\<close>
      have len_delete[simp]: "length (delete u) = r" if "u \<in> VF i t" for u
        using Suc.prems VF_def V_def \<open>i \<le> r\<close> delete_def that by auto
      have nth_delete: "delete u!k = (if k<i then u!k else u!Suc k)" if "u \<in> VF i t" "k<r" for u k
        using that by (simp add: delete_def nth_append)
      have delete_le_iff [simp]: "delete u \<unlhd> delete v \<longleftrightarrow> u \<unlhd> v" if "u \<in> VF i t" "v \<in> VF i t" for u v
      proof
        assume "delete u \<unlhd> delete v"
        then have "\<forall>j. (j < i \<longrightarrow> u!j \<le> v!j) \<and> (j < r \<longrightarrow> i \<le> j \<longrightarrow> u!Suc j \<le> v!Suc j)"
          using that \<open>i \<le> r\<close>
          by (force simp: pointwise_le_iff_nth nth_delete split: if_split_asm cong: conj_cong)
        then show "u \<unlhd> v"
          using that \<open>i \<le> r\<close>
          apply (simp add: pointwise_le_iff_nth VF_def)
          by (metis eq_iff le_Suc_eq less_Suc_eq_0_disj linorder_not_less)
      next
        assume "u \<unlhd> v" then show "delete u \<unlhd> delete v"
          using that by (simp add: pointwise_le_iff_nth nth_delete)
      qed
      then have delete_eq_iff: "delete u = delete v \<longleftrightarrow> u = v" if "u \<in> VF i t" "v \<in> VF i t" for u v
        by (metis that pointwise_le_antisym pointwise_le_refl)
      have delete_less_iff: "delete u \<lhd> delete v \<longleftrightarrow> u \<lhd> v" if "u \<in> VF i t" "v \<in> VF i t" for u v
        by (metis delete_le_iff pointwise_le_antisym pointwise_less_def that)
      have "length (delete v) = r" if "v \<in> V" for v
        using id_take_nth_drop Suc.prems V_def \<open>i \<le> r\<close> delete_def that by auto
      then have "finite (minimal_elements (delete ` V))"
        by (metis (mono_tags, lifting) Suc.IH image_iff)
      moreover have "inj_on delete (minimal_elements (VF i t))"
        by (simp add: delete_eq_iff inj_on_def minimal_elements.simps)
      moreover have "delete ` (minimal_elements (VF i t)) \<subseteq> minimal_elements (delete ` (VF i t))"
        by (auto simp: delete_less_iff minimal_elements.simps)
      ultimately show ?thesis
        by (metis (mono_tags, lifting) Suc.IH image_iff inj_on_finite len_delete)
    qed
    ultimately show ?thesis
      by (force elim: finite_subset)
  qed
qed

subsection \<open>Towards Lemma 2.9 in Gowers's notes\<close>

text \<open>Increasing sequences\<close>
fun augmentum :: "nat list \<Rightarrow> nat list"
  where "augmentum [] = []"
  | "augmentum (n#ns) = n # map ((+)n) (augmentum ns)"

definition dementum:: "nat list \<Rightarrow> nat list"
  where "dementum xs \<equiv> xs - (0#xs)"

lemma dementum_Nil [simp]: "dementum [] = []"
  by (simp add: dementum_def)

lemma zero_notin_augmentum [simp]: "0 \<notin> set ns \<Longrightarrow> 0 \<notin> set (augmentum ns)"
  by (induction ns) auto

lemma length_augmentum [simp]:"length (augmentum xs) = length xs"
  by (induction xs) auto

lemma sorted_augmentum [simp]: "0 \<notin> set ns \<Longrightarrow> sorted (augmentum ns)"
  by (induction ns) auto

lemma distinct_augmentum [simp]: "0 \<notin> set ns \<Longrightarrow> distinct (augmentum ns)"
  by (induction ns) (simp_all add: image_iff)

lemma augmentum_subset_sum_list: "set (augmentum ns) \<subseteq> {..\<sigma> ns}"
  by (induction ns) auto

lemma sum_list_augmentum: "\<sigma> ns \<in> set (augmentum ns) \<longleftrightarrow> length ns > 0"
  by (induction ns) auto

lemma length_dementum [simp]: "length (dementum xs) = length xs"
  by (simp add: dementum_def)

lemma sorted_imp_pointwise:
  assumes "sorted (xs@[n])"
  shows "0 # xs \<unlhd> xs @ [n]"
  using assms
  by (simp add: pointwise_le_iff_nth nth_Cons' nth_append sorted_append sorted_wrt_append sorted_wrt_nth_less)

lemma sum_list_dementum:
  assumes "sorted (xs@[n])"
  shows "\<sigma> (dementum (xs@[n])) = n"
proof -
  have "dementum (xs@[n]) = (xs@[n]) - (0 # xs)"
    by (rule nth_equalityI; simp add: nth_append dementum_def nth_Cons')
  then show ?thesis
    by (simp add: sum_list_minus sorted_imp_pointwise assms)
qed

lemma augmentum_cancel: "map ((+)k) (augmentum ns) - (k # map ((+)k) (augmentum ns)) = ns"
proof (induction ns arbitrary: k)
  case Nil
  then show ?case
    by simp
next
  case (Cons n ns)
  have "(+) k \<circ> (+) n = (+) (k+n)" by auto
  then show ?case
    by (simp add: minus_Cons Cons)
qed

lemma dementum_augmentum [simp]:
  assumes "0 \<notin> set ns"
  shows "(dementum \<circ> sorted_list_of_set) ((set \<circ> augmentum) ns) = ns" (is "?L ns = _")
  using assms augmentum_cancel [of 0]
  by (simp add: dementum_def map_idI sorted_list_of_set.idem_if_sorted_distinct)

lemma dementum_nonzero:
  assumes ns: "sorted_wrt (<) ns" and 0: "0 \<notin> set ns"
  shows "0 \<notin> set (dementum ns)"
  unfolding dementum_def minus_list_def
  using sorted_wrt_nth_less [OF ns] 0
  by (auto simp: in_set_conv_nth image_iff set_zip nth_Cons' dest: leD)

lemma nth_augmentum [simp]: "i < length ns \<Longrightarrow> augmentum ns!i = (\<Sum>j\<le>i. ns!j)"
proof (induction ns arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ns)
  show ?case
  proof (cases "i=0")
    case False
    then have "augmentum (a # ns)!i = a + sum ((!) ns) {..i-1}"
      using Cons.IH Cons.prems by auto
    also have "\<dots> = a + (\<Sum>j\<in>{0<..i}. ns!(j-1))"
      using sum.reindex [of Suc "{..i - Suc 0}" "\<lambda>j. ns!(j-1)", symmetric] False
      by (simp add: image_Suc_atMost atLeastSucAtMost_greaterThanAtMost del: sum.cl_ivl_Suc)
    also have "\<dots> = (\<Sum>j = 0..i. if j=0 then a else ns!(j-1))"
      by (simp add: sum.head)
    also have "\<dots> = sum ((!) (a # ns)) {..i}"
      by (simp add: nth_Cons' atMost_atLeast0)
    finally show ?thesis .
  qed auto
qed

lemma augmentum_dementum [simp]:
  assumes "0 \<notin> set ns" "sorted ns"
  shows "augmentum (dementum ns) = ns"
proof (rule nth_equalityI)
  fix i
  assume "i < length (augmentum (dementum ns))"
  then have i: "i < length ns"
    by simp
  show "augmentum (dementum ns)!i = ns!i"
  proof (cases "i=0")
    case True
    then show ?thesis
      using nth_augmentum dementum_def i by auto
  next
    case False
    have ns_le: "\<And>j. \<lbrakk>0 < j; j \<le> i\<rbrakk> \<Longrightarrow> ns ! (j - Suc 0) \<le> ns ! j"
      using \<open>sorted ns\<close> i by (simp add: sorted_iff_nth_mono)
    have "augmentum (dementum ns)!i = (\<Sum>j\<le>i. ns!j - (if j = 0 then 0 else ns!(j-1)))"
      using i by (simp add: dementum_def nth_Cons')
    also have "\<dots> = (\<Sum>j=0..i. if j = 0 then ns!0 else ns!j - ns!(j-1))"
      by (smt (verit, del_insts) diff_zero sum.cong atMost_atLeast0)
    also have "\<dots> = ns!0 + (\<Sum>j\<in>{0<..i}. ns!j - ns!(j-1))"
      by (simp add: sum.head)
    also have "\<dots> = ns!0 + ((\<Sum>j\<in>{0<..i}. ns!j) - (\<Sum>j\<in>{0<..i}. ns!(j-1)))"
      by (auto simp: ns_le intro: sum_subtractf_nat)
    also have "\<dots> = ns!0 + (\<Sum>j\<in>{0<..i}. ns!j) - (\<Sum>j\<in>{0<..i}. ns!(j-1))"
    proof -
      have "(\<Sum>j\<in>{0<..i}. ns ! (j - 1)) \<le> sum ((!) ns) {0<..i}"
        by (metis One_nat_def greaterThanAtMost_iff ns_le sum_mono)
      then show ?thesis by simp
    qed
    also have "\<dots> = ns!0 + (\<Sum>j\<in>{0<..i}. ns!j) - (\<Sum>j\<le>i-Suc 0. ns!j)"
      using sum.reindex [of Suc "{..i - Suc 0}" "\<lambda>j. ns!(j-1)", symmetric] False
      by (simp add: image_Suc_atMost atLeastSucAtMost_greaterThanAtMost)
    also have "\<dots> = (\<Sum>j=0..i. ns!j) - (\<Sum>j\<le>i-Suc 0. ns!j)"
      by (simp add:  sum.head [of 0 i])
    also have "\<dots> = (\<Sum>j=0..i-Suc 0. ns!j) + ns!i - (\<Sum>j\<le>i-Suc 0. ns!j)"
      by (metis False Suc_pred less_Suc0 not_less_eq sum.atLeast0_atMost_Suc)
    also have "\<dots> = ns!i"
      by (simp add: atLeast0AtMost)
    finally show "augmentum (dementum ns)!i = ns!i" .
  qed
qed auto

text\<open>The following lemma corresponds to Lemma 2.9 in Gowers's notes. The proof involves introducing
bijective maps between r-tuples that fulfill certain properties/r-tuples and subsets of naturals,
so as to show the cardinality claim.  \<close>

lemma bound_sum_list_card:
  assumes "r > 0" and n: "n \<ge> \<sigma> x'" and lenx': "length x' = r"
  defines "S \<equiv> {x. x' \<unlhd> x \<and> \<sigma> x = n}"
  shows "card S = (n - \<sigma> x' + r - 1) choose (r-1)"
proof-
  define m where "m \<equiv> n - \<sigma> x'"
  define f where "f \<equiv> \<lambda>x::nat list. x - x'"
  have f: "bij_betw f S (length_sum_set r m)"
  proof (intro bij_betw_imageI)
    show "inj_on f S"
      using pairwise_minus_cancel by (force simp: S_def f_def inj_on_def)
    have "\<And>x. x \<in> S \<Longrightarrow> f x \<in> length_sum_set r m"
      by (simp add: S_def f_def length_sum_set_def lenx' m_def pointwise_le_iff sum_list_minus)
    moreover have "x \<in> f ` S" if "x \<in> length_sum_set r m" for x
    proof
      have x[simp]: "length x = r" "\<sigma> x = m"
        using that by (auto simp: length_sum_set_def)
      have "x = x' + x - x'"
        by (rule nth_equalityI; simp add: lenx')
      then show "x = f (x' + x)"
        unfolding f_def by fastforce
      have "x' \<unlhd> x' + x"
        by (simp add: lenx' pointwise_le_plus)
      moreover have "\<sigma> (x' + x) = n"
        by (simp add: lenx' m_def n sum_list_plus)
      ultimately show "x' + x \<in> S"
        using S_def by blast
    qed
    ultimately show "f ` S = length_sum_set r m" by auto
  qed
  define g where "g \<equiv> \<lambda>x::nat list. map Suc x"
  define g' where "g' \<equiv> \<lambda>x::nat list. x - replicate (length x) 1"
  define T where "T \<equiv> length_sum_set r (m+r) \<inter> lists(-{0})"
  have g: "bij_betw g (length_sum_set r m) T"
  proof (intro bij_betw_imageI)
    show "inj_on g (length_sum_set r m)"
      by (auto simp: g_def inj_on_def)
    have "\<And>x. x \<in> length_sum_set r m \<Longrightarrow> g x \<in> T"
      by (auto simp: g_def length_sum_set_def sum_list_Suc T_def)
    moreover have "x \<in> g ` length_sum_set r m" if "x \<in> T" for x
    proof
      have [simp]: "length x = r"
        using length_sum_set_def that T_def by auto
      have r1_x: "replicate r (Suc 0) \<unlhd> x"
        using that unfolding T_def pointwise_le_iff_nth
        by (simp add: lists_def in_listsp_conv_set Suc_leI)
      show "x = g (g' x)"
        using that by (intro nth_equalityI) (auto simp: g_def g'_def T_def)
      show "g' x \<in> length_sum_set r m"
        using that T_def by (simp add: g'_def r1_x sum_list_minus length_sum_set_def sum_list_replicate)
    qed
    ultimately show "g ` (length_sum_set r m) = T" by auto
  qed
  define U where "U \<equiv> (insert (m+r)) ` finsets {0<..<m+r} (r-1)"
  have h: "bij_betw (set \<circ> augmentum) T U"
  proof (intro bij_betw_imageI)
    show "inj_on ((set \<circ> augmentum)) T"
      unfolding inj_on_def T_def
      by (metis ComplD IntE dementum_augmentum in_listsD insertI1)
    have "(set \<circ> augmentum) t \<in> U" if "t \<in> T" for t
    proof -
      have t: "length t = r" "\<sigma> t = m+r" "0 \<notin> set t"
        using that by (force simp: T_def length_sum_set_def)+
      then have mrt: "m + r \<in> set (augmentum t)"
        by (metis \<open>r>0\<close> sum_list_augmentum)
      then have "set (augmentum t) = insert (m + r) (set (augmentum t) - {m + r})"
        by blast
      moreover have "set (augmentum t) - {m + r} \<in> finsets {0<..<m + r} (r - Suc 0)"
        apply (auto simp: finsets_def mrt distinct_card t)
        by (metis atMost_iff augmentum_subset_sum_list le_eq_less_or_eq subsetD t(2))
      ultimately show ?thesis
        by (metis One_nat_def U_def comp_apply imageI)
    qed
    moreover have "u \<in> (set \<circ> augmentum) ` T" if "u \<in> U" for u
    proof
      from that
      obtain N where u: "u = insert (m + r) N" and Nsub: "N \<subseteq> {0<..<m + r}"
        and [simp]: "card N = r - Suc 0"
        by (auto simp: U_def finsets_def)
      have [simp]: "0 \<notin> N" "m+r \<notin> N" "finite N"
        using finite_subset Nsub by auto
      have [simp]: "card u = r"
        using Nsub \<open>r>0\<close> by (auto simp: u card_insert_if)
      have ssN: "sorted (sorted_list_of_set N @ [m + r])"
        using Nsub by (simp add: less_imp_le_nat sorted_wrt_append subset_eq)
      have so_u_N: "sorted_list_of_set u = insort (m+r) (sorted_list_of_set N)"
        by (simp add: u)
      also have "\<dots> = sorted_list_of_set N @ [m+r]"
        using Nsub by (force intro: sorted_insort_is_snoc)
      finally have so_u: "sorted_list_of_set u = sorted_list_of_set N @ [m+r]" .
      have 0: "0 \<notin> set (sorted_list_of_set u)"
        by (simp add: \<open>r>0\<close> set_insort_key so_u_N)
      show "u = (set \<circ> augmentum) ((dementum \<circ> sorted_list_of_set)u)"
        using 0 so_u ssN u by force
      have sortd_wrt_u: "sorted_wrt (<) (sorted_list_of_set u)"
        by simp
      show "(dementum \<circ> sorted_list_of_set) u \<in> T"
        apply (simp add: T_def length_sum_set_def)
        using sum_list_dementum [OF ssN] sortd_wrt_u 0 by (force simp: so_u dementum_nonzero)+
    qed
    ultimately show "(set \<circ> augmentum) ` T = U" by auto
  qed
  obtain \<phi> where "bij_betw \<phi> S U"
    by (meson bij_betw_trans f g h)
  moreover have "card U = (n - \<sigma> x' + r-1) choose (r-1)"
  proof -
    have "inj_on (insert (m + r)) (finsets {0<..<m + r} (r - Suc 0))"
      by (simp add: inj_on_def finsets_def subset_iff) (meson insert_ident order_less_le)
    then have "card U = card (finsets {0<..<m + r} (r - 1))"
      unfolding U_def by (simp add: card_image)
    also have "\<dots> = (n - \<sigma> x' + r-1) choose (r-1)"
      by (simp add: card_finsets m_def)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (metis bij_betw_same_card)
qed

subsection \<open>Towards the main theorem\<close>

lemma extend_tuple:
  assumes "\<sigma> xs \<le> n" "length xs \<noteq> 0"
  obtains ys where "\<sigma> ys = n" "xs \<unlhd> ys"
proof -
  obtain x xs' where xs: "xs = x#xs'"
    using assms list.exhaust by auto
  define y where "y \<equiv> x + n - \<sigma> xs"
  show thesis
  proof
    show "\<sigma> (y#xs') = n"
      using assms xs y_def by auto
    show "xs \<unlhd> y#xs'"
      using assms y_def pointwise_le_def xs by auto
  qed
qed

lemma extend_preserving:
  assumes "\<sigma> xs \<le> n" "length xs > 1" "i < length xs"
  obtains ys where "\<sigma> ys = n" "xs \<unlhd> ys" "ys!i = xs!i"
proof -
  define j where "j \<equiv> Suc i mod length xs"
  define xs1 where "xs1 = take j xs"
  define xs2 where "xs2 = drop (Suc j) xs"
  define x where "x = xs!j"
  have xs: "xs = xs1 @ [x] @ xs2"
    using assms
    apply (simp add: Cons_nth_drop_Suc assms x_def xs1_def xs2_def j_def)
    by (meson Suc_lessD id_take_nth_drop mod_less_divisor)
  define y where "y \<equiv> x + n - \<sigma> xs"
  define ys where "ys \<equiv> xs1 @ [y] @ xs2"
  have "x \<le> y"
    using assms y_def by linarith
  show thesis
  proof
    show "\<sigma> ys = n"
      using assms(1) xs y_def ys_def by auto
    show "xs \<unlhd> ys"
      using xs ys_def \<open>x \<le> y\<close> pointwise_append_le_iff pointwise_le_def by fastforce
    have "length xs1 \<noteq> i"
      using assms by (simp add: xs1_def j_def min_def mod_Suc)
    then show "ys!i = xs!i"
      by (auto simp: ys_def xs nth_append nth_Cons')
  qed
qed

text\<open>The proof of the main theorem will make use of the inclusion-exclusion formula, in addition to
the previously shown results.\<close>

theorem Khovanskii:
  assumes "card A > 1"
  defines "f \<equiv> \<lambda>n. card(sumset_iterated A n)"
  obtains N p where "real_polynomial_function p" "\<And>n. n \<ge> N \<Longrightarrow> real (f n) = p (real n)"
proof -
  define r where "r \<equiv> card A"
  define C where "C \<equiv> \<lambda>n x'. {x. x' \<unlhd> x \<and> \<sigma> x = n}"
  define X where "X \<equiv> minimal_elements {x. useless x \<and> length x = r}"
  have "r > 1" "r \<noteq> 0"
    using assms r_def by auto
  have Csub: "C n x' \<subseteq> length_sum_set (length x') n" for n x'
    by (auto simp: C_def length_sum_set_def pointwise_le_iff)
  then have finC: "finite (C n x')" for n x'
    by (meson finite_length_sum_set finite_subset)
  have "finite X"
    using "minimal_elements_set_tuples_finite" X_def by force
  then have max_X: "\<And>x'. x' \<in> X \<Longrightarrow>  \<sigma> x' \<le> \<sigma> (max_pointwise r X)"
    using X_def max_pointwise_ge minimal_elements.simps pointwise_le_imp_\<sigma> by force
  let ?z0 = "replicate r 0"
  have Cn0: "C n ?z0 = length_sum_set r n" for n
    by (auto simp: C_def length_sum_set_def)
  then obtain p0 where pf_p0: "real_polynomial_function p0" and p0: "\<And>n. n>0 \<Longrightarrow> p0 (real n) = real (card (C n ?z0))"
    by (metis real_polynomial_function_length_sum_set)
  obtain q where pf_q: "real_polynomial_function q" and q: "\<And>x. q x = x gchoose (r-1)"
    using real_polynomial_function_gchoose by metis
  define p where "p \<equiv> \<lambda>x::real. p0 x - (\<Sum>Y | Y \<subseteq> X \<and> Y \<noteq> {}. (- 1) ^ (card Y + 1) * q((x - real(\<sigma> (max_pointwise r Y)) + real r - 1)))"
  show thesis
  proof
    note pf_q' = real_polynomial_function_compose [OF _ pf_q, unfolded o_def]
    note pf_intros = real_polynomial_function_sum real_polynomial_function_diff real_polynomial_function.intros
    show "real_polynomial_function p"
      unfolding p_def using \<open>finite X\<close> by (intro pf_p0 pf_q' pf_intros | force)+
  next
    fix n
    assume "n \<ge> max 1 (\<sigma> (max_pointwise r X))"
    then have nlarge: "n \<ge> \<sigma> (max_pointwise r X)" and "n > 0"
      by auto
    define U where "U \<equiv> \<lambda>n. length_sum_set r n \<inter> {x. useful x}"
    have 2: "(length_sum_set r n \<inter> {x. useless x}) = (\<Union>x'\<in>X. C n x')"
      unfolding C_def X_def length_sum_set_def r_def
      using useless_leq_useless by (force simp: minimal_elements.simps pointwise_le_iff useless_iff)
    define SUM1 where "SUM1 \<equiv> \<Sum>I | I \<subseteq> C n ` X \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I))"
    define SUM2 where "SUM2 \<equiv> \<Sum>Y | Y \<subseteq> X \<and> Y \<noteq> {}. (- 1) ^ (card Y + 1) * int (card (\<Inter>(C n ` Y)))"
    have SUM1_card: "card(length_sum_set r n \<inter> {x. useless x}) = nat SUM1"
      unfolding SUM1_def using \<open>finite X\<close> by (simp add: finC 2 card_UNION)
    have "SUM1 \<ge> 0"
      unfolding SUM1_def using card_UNION_nonneg finC \<open>finite X\<close> by auto
    have C_empty_iff: "C n x' = {} \<longleftrightarrow> \<sigma> x' > n" if "length x' \<noteq> 0" for x'
      by (simp add: set_eq_iff C_def) (meson extend_tuple linorder_not_le pointwise_le_imp_\<sigma> that)
    have C_eq_1: "C n x' = {[n]}" if "\<sigma> x' \<le> n" "length x' = 1" for x'
      using that by (auto simp: C_def length_Suc_conv pointwise_le_def elim!: list.rel_cases)
    have n_ge_X: "\<sigma> x \<le> n" if "x \<in> X" for x
      by (meson le_trans max_X nlarge that)
    have len_X_r: "x \<in> X \<Longrightarrow> length x = r" for x
      by (auto simp: X_def minimal_elements.simps)

    have "min_pointwise r (C n x') = x'" if "r > 1" "x' \<in> X" for x'
    proof (rule pointwise_le_antisym)
      have [simp]: "length x' = r" "\<sigma> x' \<le> n"
        using X_def minimal_elements.cases that(2) n_ge_X by auto
      have [simp]: "length (min_pointwise r (C n x')) = r"
        by (simp add: min_pointwise_def)
      show "min_pointwise r (C n x') \<unlhd> x'"
      proof (clarsimp simp add: pointwise_le_iff_nth)
        fix i
        assume "i < r"
        then obtain y where "\<sigma> y = n \<and> x' \<unlhd> y \<and> y!i \<le> x'!i"
          by (metis extend_preserving \<open>1 < r\<close> \<open>length x' = r\<close> \<open>x' \<in> X\<close> order.refl n_ge_X)
        then have "\<exists>y\<in>C n x'. y!i \<le> x'!i"
          using C_def by blast
        with \<open>i < r\<close> show "min_pointwise r (C n x')!i \<le> x'!i"
          by (simp add: min_pointwise_def Min_le_iff finC C_empty_iff leD)
      qed
      have "x' \<unlhd> min_pointwise r (C n x')" if "\<sigma> x' \<le> n" "length x' = r" for x'
        by (smt (verit, del_insts) C_def C_empty_iff \<open>r \<noteq> 0\<close> finC leD mem_Collect_eq min_pointwise_ge_iff pointwise_le_iff that)
      then show "x' \<unlhd> min_pointwise r (C n x')"
        using X_def minimal_elements.cases that by force
    qed
    then have inj_C: "inj_on (C n) X"
      by (smt (verit, best) inj_onI mem_Collect_eq \<open>r>1\<close>)
    have inj_on_imageC: "inj_on (image (C n)) (Pow X - {{}})"
      by (simp add: inj_C inj_on_diff inj_on_image_Pow)

    have "Pow (C n ` X) - {{}} \<subseteq> (image (C n)) ` (Pow X - {{}})"
      by (metis Pow_empty image_Pow_surj image_diff_subset image_empty)
    then have "(image (C n)) ` (Pow X - {{}}) = Pow (C n ` X) - {{}}"
      by blast
    then have "SUM1 = sum (\<lambda>I. (- 1) ^ (card I + 1) * int (card (\<Inter>I))) ((image (C n)) ` (Pow X - {{}}))"
      unfolding SUM1_def by (auto intro: sum.cong)
    also have "\<dots> = sum ((\<lambda>I. (- 1) ^ (card I + 1) * int (card (\<Inter> I))) \<circ> (image (C n))) (Pow X - {{}})"
      by (simp add: sum.reindex inj_on_imageC)
    also have "\<dots> = SUM2"
      unfolding SUM2_def using subset_inj_on [OF inj_C] by (force simp: card_image intro: sum.cong)
    finally have "SUM1 = SUM2" .

    have "length_sum_set r n = (length_sum_set r n \<inter> {x. useful x}) \<union> (length_sum_set r n \<inter> {x. useless x})"
      by auto
    then have "card (length_sum_set r n) =
                card (length_sum_set r n \<inter> {x. useful x}) +
                card (length_sum_set r n \<inter> Collect useless)"
      by (simp add: finite_length_sum_set disjnt_iff flip: card_Un_disjnt)
    moreover have "C n ?z0 = length_sum_set r n"
      by (auto simp: C_def length_sum_set_def)
    ultimately have "card (C n ?z0) = card (U n) + nat SUM2"
      by (simp add: U_def flip: \<open>SUM1 = SUM2\<close> SUM1_card)
    then have SUM2_le: "nat SUM2 \<le> card (C n ?z0)"
      by arith
    have \<sigma>_max_pointwise_le: "\<And>Y. \<lbrakk>Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> \<sigma> (max_pointwise r Y) \<le> n"
      by (meson \<open>finite X\<close> le_trans max_pointwise_mono nlarge pointwise_le_imp_\<sigma>)

    have card_C_max: "card (C n (max_pointwise r Y)) =
             (n - \<sigma> (max_pointwise r Y) + r - Suc 0 choose (r - Suc 0))"
      if "Y \<subseteq> X" "Y \<noteq> {}" for Y
    proof -
      have [simp]: "length (max_pointwise r Y) = r"
        by (simp add: max_pointwise_def)
      then show ?thesis
        using \<open>r \<noteq> 0\<close> that C_def by (simp add: bound_sum_list_card [of r] \<sigma>_max_pointwise_le)
    qed

    define SUM3 where "SUM3 \<equiv> (\<Sum>Y | Y \<subseteq> X \<and> Y \<noteq> {}.
         - ((- 1) ^ (card Y) * ((n - \<sigma> (max_pointwise r Y) + r - 1 choose (r - 1)))))"
    have "\<Inter>(C n ` Y) = C n (max_pointwise r Y)" if "Y \<subseteq> X" "Y \<noteq> {}" for Y
    proof
      show "\<Inter> (C n ` Y) \<subseteq> C n (max_pointwise r Y)"
        unfolding C_def
      proof clarsimp
        fix x
        assume "\<forall>y\<in>Y. y \<unlhd> x \<and> \<sigma> x = n"
        moreover have "finite Y"
          using \<open>finite X\<close> infinite_super that by blast
        moreover have "\<And>u. u \<in> Y \<Longrightarrow> length u = r"
          using len_X_r that by blast
        ultimately show "max_pointwise r Y \<unlhd> x \<and> \<sigma> x = n"
          by (smt (verit, del_insts) all_not_in_conv max_pointwise_le_iff pointwise_le_iff_nth that(2))
      qed
    next
      show "C n (max_pointwise r Y) \<subseteq> \<Inter> (C n ` Y)"
        apply (clarsimp simp: C_def)
        by (metis \<open>finite X\<close> finite_subset len_X_r max_pointwise_ge pointwise_le_trans subsetD that(1))
    qed
    then have "SUM2 = SUM3"
      by (simp add: SUM2_def SUM3_def card_C_max)
    have "U n = C n ?z0 - (length_sum_set r n \<inter> {x. useless x})"
      by (auto simp: U_def C_def length_sum_set_def)
    then have "card (U n) = card (C n ?z0) - card(length_sum_set r n \<inter> {x. useless x})"
      using finite_length_sum_set
      by (simp add: C_def Collect_mono_iff inf.coboundedI1 length_sum_set_def flip: card_Diff_subset)
    then have card_U_eq_diff: "card (U n) = card (C n ?z0) - nat SUM1"
      using SUM1_card by presburger
    have "SUM3 \<ge> 0"
      using \<open>0 \<le> SUM1\<close> \<open>SUM1 = SUM2\<close> \<open>SUM2 = SUM3\<close> by blast
    have **: "\<And>Y. \<lbrakk>Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> Suc (\<sigma> (max_pointwise r Y)) \<le> n + r"
      by (metis \<open>1 < r\<close> \<sigma>_max_pointwise_le add.commute add_le_mono less_or_eq_imp_le plus_1_eq_Suc)
    have "real (f n) = card (U n)"
      unfolding f_def r_def U_def length_sum_set_def
      using card_sumset_iterated_length_sum_set_useful length_sum_set_def by presburger
    also have "\<dots> = card (C n ?z0) -  nat SUM3"
      using card_U_eq_diff \<open>SUM1 = SUM2\<close> \<open>SUM2 = SUM3\<close> by presburger
    also have "\<dots> = real (card (C n (replicate r 0))) - real (nat SUM3)"
      using SUM2_le \<open>SUM2 = SUM3\<close> of_nat_diff by blast
    also have "\<dots> = p (real n)"
      using \<open>1 < r\<close> \<open>n>0\<close>
      apply (simp add: p_def p0 q \<open>SUM3 \<ge> 0\<close>)
      apply (simp add: SUM3_def binomial_gbinomial of_nat_diff \<sigma>_max_pointwise_le algebra_simps **)
      done
    finally show "real (f n) = p (real n)" .
  qed
qed

end

end
