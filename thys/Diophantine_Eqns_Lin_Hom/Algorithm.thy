(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Computing Minimal Complete Sets of Solutions\<close>

theory Algorithm
  imports Simple_Algorithm
begin

(*TODO: move*)
lemma all_Suc_le_conv: "(\<forall>i\<le>Suc n. P i) \<longleftrightarrow> P 0 \<and> (\<forall>i\<le>n. P (Suc i))"
  by (metis less_Suc_eq_0_disj nat_less_le order_refl)

(*TODO: move*)
lemma concat_map_filter_filter:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<not> Q x \<Longrightarrow> filter P (f x) = []"
  shows "concat (map (filter P \<circ> f) (filter Q xs)) = concat (map (filter P \<circ> f) xs)"
  using assms by (induct xs) simp_all

(*TODO: move*)
lemma filter_pairs_conj:
  "filter (\<lambda>(x, y). P x y \<and> Q y) xs = filter (\<lambda>(x, y). P x y) (filter (Q \<circ> snd) xs)"
  by (induct xs) auto

(*TODO: move*)
lemma concat_map_filter:
  "concat (map f (filter P xs)) = concat (map (\<lambda>x. if P x then f x else []) xs)"
  by (induct xs) simp_all

fun alls
  where
    "alls B [] = [([], 0)]"
  | "alls B (a # as) = [(x # xs, s + a * x). (xs, s) \<leftarrow> alls B as, x \<leftarrow> [0 ..< B + 1]]"

lemma alls_ne [simp]:
  "alls B as \<noteq> []"
  by (induct as)
    (auto, metis (no_types, lifting) append_is_Nil_conv case_prod_conv list.set_intros(1)
     neq_Nil_conv old.prod.exhaust)

lemma set_alls: "set (alls B a) =
  {(x, s). length x = length a \<and> (\<forall>i<length a. x ! i \<le> B) \<and> s = a \<bullet> x}"
    (is "?L a = ?R a")
proof
  show "?L a \<subseteq> ?R a" by (induct a) (auto simp: nth_Cons split: nat.splits)
next
  show "?R a \<subseteq> ?L a"
  proof (induct a)
    case (Cons a as)
    show ?case
    proof
      fix xs' assume "xs' \<in> ?R (a # as)"
      then obtain x and xs where [simp]: "xs' = (x # xs, (a # as) \<bullet> (x # xs))"
        and "length as = length xs"
        and B: "x \<le> B" "\<forall>i<length as. xs ! i \<le> B"
        by (cases xs', case_tac a) (auto simp: all_Suc_conv)
      then have "(xs, as \<bullet> xs) \<in> ?L as" using Cons by auto
      then show "xs' \<in> ?L (a # as)"
        using B
        apply auto
        apply (rule bexI [of _ "(xs, as \<bullet> xs)"])
         apply auto
        done
    qed
  qed auto
qed

lemma alls_nth0 [simp]: "alls A as ! 0 = (zeroes (length as), 0)"
  by (induct as) (auto simp: nth_append concat_map_nth0)

lemma alls_Cons_tl_conv: "alls A as = (zeroes (length as), 0) # tl (alls A as)"
  by (rule nth_equalityI) (auto simp: nth_Cons nth_tl split: nat.splits)

lemma sorted_wrt_alls:
  "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x) (map fst (alls B xs))"
  by (induct xs) (auto simp: map_concat rlex_Cons sorted_wrt_append
      intro!: sorted_wrt_concat_map sorted_wrt_map_mono [of "(<)"])

definition "alls2 A B a b = [(xs, ys). ys \<leftarrow> alls B b, xs \<leftarrow> alls A a]"

lemma alls2_ne [simp]:
  "alls2 A B a b \<noteq> []"
  by (auto simp: alls2_def) (metis alls_ne list.set_intros(1) neq_Nil_conv surj_pair)

lemma set_alls2:
  "set (alls2 A B a b) = {((x, s), (y, t)). length x = length a \<and> length y = length b \<and>
    (\<forall>i<length a. x ! i \<le> A) \<and> (\<forall>j<length b. y ! j \<le> B) \<and> s = a \<bullet> x \<and> t = b \<bullet> y}"
  by (auto simp: alls2_def set_alls)

lemma alls2_nth0 [simp]: "alls2 A B as bs ! 0 = ((zeroes (length as), 0), (zeroes (length bs), 0))"
  by (auto simp: alls2_def concat_map_nth0)

lemma alls2_Cons_tl_conv: "alls2 A B as bs =
  ((zeroes (length as), 0), (zeroes (length bs), 0)) # tl (alls2 A B as bs)"
  apply (rule nth_equalityI)
   apply (auto simp: alls2_def nth_Cons nth_tl length_concat concat_map_nth0 split: nat.splits)
  apply (cases "alls B bs"; simp)
  done

abbreviation gen2
  where
    "gen2 A B a b \<equiv> map (\<lambda>(x, y). (fst x, fst y)) (alls2 A B a b)"

lemma sorted_wrt_gen2:
  "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) (gen2 A B a b)"
  apply (rule sorted_wrt_map_mono [of "\<lambda>(x, y) (u, v). (fst x, fst y) <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 (fst u, fst v)"])
   apply (auto simp: alls2_def map_concat)
  apply (fold rlex2.simps)
  apply (rule sorted_wrt_concat_map_map)
     apply (rule sorted_wrt_map_distr, rule sorted_wrt_alls)
    apply (rule sorted_wrt_map_distr, rule sorted_wrt_alls)
   apply (auto simp: rlex_def set_alls intro: lex_append_left lex_append_right)
  done

definition generate
  where
    "generate A B a b = tl (map (\<lambda>(x, y). (fst x, fst y)) (alls2 A B a b))"

lemma sorted_wrt_generate:
  "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) (generate A B a b)"
  by (auto simp: generate_def sorted_wrt_gen2 sorted_wrt_tl)

lemma gen2_nth0 [simp]:
  "gen2 A B a b ! 0 = (zeroes (length a), zeroes (length b))"
  by (auto simp: generate_def)

lemma gen2_ne [simp, intro]: "gen2 m n b c \<noteq> []"
  by (auto simp: generate_def)

lemma in_generate: "x \<in> set (generate m n c b) \<Longrightarrow> x \<in> set (gen2 m n c b)"
  unfolding generate_def by (rule list.set_sel) simp

definition "cond_cons P = (\<lambda>(ys, s). case ys of [] \<Rightarrow> True | ys \<Rightarrow> P ys s)"

lemma cond_cons_simp [simp]:
  "cond_cons P ([], s) = True"
  "cond_cons P (x # xs, s) = P (x # xs) s"
  by (auto simp: cond_cons_def)

fun suffs
  where
    "suffs P as (xs, s) \<longleftrightarrow>
      length xs = length as \<and>
      s = as \<bullet> xs \<and>
      (\<forall>i\<le>length xs. cond_cons P (drop i xs, drop i as \<bullet> drop i xs))"
declare suffs.simps [simp del]

lemma suffs_Nil [simp]: "suffs P [] ([], s) \<longleftrightarrow> s = 0"
  by (auto simp: suffs.simps)

lemma suffs_Cons:
  "suffs P (a # as) (x # xs, s) \<longleftrightarrow>
    s = a * x + as \<bullet> xs \<and> cond_cons P (x # xs, s) \<and> suffs P as (xs, as \<bullet> xs)"
  apply (auto simp: suffs.simps cond_cons_def split: list.splits)
    apply force
   apply (metis Suc_le_mono drop_Suc_Cons)
  by (metis One_nat_def Suc_le_mono Suc_pred dotprod_Cons drop_Cons' le_0_eq not_le_imp_less)


subsection \<open>The Algorithm\<close>

fun maxne0_impl
  where
    "maxne0_impl [] a = 0"
  | "maxne0_impl x [] = 0"
  | "maxne0_impl (x#xs) (a#as) = (if x > 0 then max a (maxne0_impl xs as) else maxne0_impl xs as)"

lemma maxne0_impl:
  assumes "length x = length a"
  shows "maxne0_impl x a = maxne0 x a"
  using assms by (induct x a rule: list_induct2) (auto)

lemma maxne0_impl_le:
  "maxne0_impl x a \<le> Max (set (a::nat list))"
  apply (induct x a rule: maxne0_impl.induct)
  apply (auto simp add: max.coboundedI2)
  by (metis List.finite_set Max_insert Nat.le0 le_max_iff_disj maxne0_impl.elims maxne0_impl.simps(2) set_empty)

context
  fixes a b :: "nat list"
begin

definition special_solutions :: "(nat list \<times> nat list) list"
  where
    "special_solutions = map (\<lambda>(i, j). sij a b i j) (List.product [0 ..< length a] [0 ..< length b])"

definition big_e :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "big_e x j = map (\<lambda>i. eij a b i j - 1) (filter (\<lambda>i. x ! i \<ge> dij a b i j) [0 ..< length x])"

definition big_d :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "big_d y i = map (\<lambda>j. dij a b i j - 1) (filter (\<lambda>j. y ! j \<ge> eij a b i j) [0 ..< length y])"

definition big_d' :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "big_d' y i =
      (let l = length y; n = length b in
      if l > n then [] else
      (let k = n - l in
      map (\<lambda>j. dij a b i (j + k) - 1) (filter (\<lambda>j. y ! j \<ge> eij a b i (j + k)) [0 ..< length y])))"

definition maxy_impl :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "maxy_impl x j =
      (if j < length b \<and> big_e x j \<noteq> [] then Min (set (big_e x j))
      else Max (set a))"

definition maxx_impl :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "maxx_impl y i =
      (if i < length a \<and> big_d y i \<noteq> [] then Min (set (big_d y i))
      else Max (set b))"

definition maxx_impl' :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "maxx_impl' y i =
      (if i < length a \<and> big_d' y i \<noteq> [] then Min (set (big_d' y i))
      else Max (set b))"

definition cond_a :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "cond_a xs ys \<longleftrightarrow> (\<forall>x\<in>set xs. x \<le> maxne0 ys b)"

definition cond_b :: "nat list \<Rightarrow> bool"
  where
    "cond_b xs \<longleftrightarrow> (\<forall>k\<le>length a.
      take k a \<bullet> take k xs \<le> b \<bullet> (map (maxy_impl (take k xs)) [0 ..< length b]))"

definition boundr_impl :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "boundr_impl x y \<longleftrightarrow> (\<forall>j<length b. y ! j \<le> maxy_impl x j)"

definition cond_d :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "cond_d xs ys \<longleftrightarrow> (\<forall>l\<le>length b. take l b \<bullet> take l ys \<le> a \<bullet> xs)"

definition pdprodr_impl :: "nat list \<Rightarrow> bool"
  where
    "pdprodr_impl ys \<longleftrightarrow> (\<forall>l\<le>length b.
      take l b \<bullet> take l ys \<le> a \<bullet> map (maxx_impl (take l ys)) [0 ..< length a])"

definition pdprodl_impl :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "pdprodl_impl x y \<longleftrightarrow> (\<forall>k\<le>length a. take k a \<bullet> take k x \<le> b \<bullet> y)"

definition "boundl_impl x y \<longleftrightarrow> (\<forall>i<length a. x ! i \<le> maxx_impl y i)"

definition static_bounds
  where
    "static_bounds x y \<longleftrightarrow>
      (let mx = maxne0_impl y b; my = maxne0_impl x a in
      (\<forall>x\<in>set x. x \<le> mx) \<and> (\<forall>y\<in>set y. y \<le> my))"

definition "check_cond =
  (\<lambda>(x, y). static_bounds x y \<and> a \<bullet> x = b \<bullet> y \<and> boundr_impl x y \<and> pdprodl_impl x y \<and> pdprodr_impl y)"

definition "check' = filter check_cond"

definition "non_special_solutions =
  (let A = Max (set b); B = Max (set a)
  in minimize (check' (generate A B a b)))"

definition "solve = special_solutions @ non_special_solutions"

end

lemma sorted_wrt_check_generate:
  "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) (check' a b (generate A B a b))"
  by (auto simp: check'_def intro!: sorted_wrt_filter sorted_wrt_generate sorted_wrt_tl)

lemma big_e:
  "set (big_e a b xs j) = hlde_ops.Ej a b j xs"
  by (auto simp: hlde_ops.Ej_def big_e_def)

lemma big_d:
  "set (big_d a b ys i) = hlde_ops.Di a b i ys"
  by (auto simp: hlde_ops.Di_def big_d_def)

lemma big_d':
  "length ys \<le> length b \<Longrightarrow> set (big_d' a b ys i) = hlde_ops.Di' a b i ys"
  by (auto simp: hlde_ops.Di'_def big_d'_def Let_def)

lemma maxy_impl:
  "maxy_impl a b x j = hlde_ops.maxy a b x j"
  by (simp add: maxy_impl_def big_e hlde_ops.maxy_def set_empty [symmetric])

lemma maxx_impl:
  "maxx_impl a b y i = hlde_ops.maxx a b y i"
  by (simp add: maxx_impl_def big_d hlde_ops.maxx_def set_empty [symmetric])

lemma maxx_impl':
  assumes "length y \<le> length b"
  shows "maxx_impl' a b y i = hlde_ops.maxx' a b y i"
  by (simp add: maxx_impl'_def big_d' [OF assms] hlde_ops.maxx'_def set_empty [symmetric])

lemma (in hlde) cond_a [simp]: "cond_a b x y = cond_A x y"
  by (simp add: cond_a_def cond_A_def)

lemma (in hlde) cond_b [simp]: "cond_b a b x = cond_B x"
  using maxy_impl by (auto simp: cond_b_def cond_B_def) presburger+

lemma (in hlde) boundr_impl [simp]: "boundr_impl a b x y = boundr x y"
  by (simp add: boundr_impl_def boundr_def maxy_impl)

lemma (in hlde) cond_d [simp]: "cond_d a b x y = cond_D x y"
  by (simp add: cond_d_def cond_D_def)

lemma (in hlde) pdprodr_impl [simp]: "pdprodr_impl a b y = subprodr y"
  using maxx_impl by (auto simp: pdprodr_impl_def subprodr_def) presburger+

lemma (in hlde) pdprodl_impl [simp]: "pdprodl_impl a b x y = subprodl x y"
  by (simp add: pdprodl_impl_def subprodl_def)

lemma (in hlde) cond_bound_impl [simp]: "boundl_impl a b x y = boundl x y"
  by (simp add: boundl_impl_def boundl_def maxx_impl)

lemma (in hlde) check [simp]:
  "check' a b =
    filter (\<lambda>(x, y). static_bounds a b x y \<and> a \<bullet> x = b \<bullet> y \<and> boundr x y \<and>
    subprodl x y \<and>
    subprodr y)"
  by (simp add: check'_def check_cond_def)

text \<open>
  conditions B, C, and D from Huet as well as "subprodr" and "subprodl" are
  preserved by smaller solutions
\<close>
lemma (in hlde) le_imp_conds:
  assumes le: "u \<le>\<^sub>v x" "v \<le>\<^sub>v y"
    and len: "length x = m" "length y = n"
  shows "cond_B x \<Longrightarrow> cond_B u"
    and "boundr x y \<Longrightarrow> boundr u v"
    and "a \<bullet> u = b \<bullet> v \<Longrightarrow> cond_D x y \<Longrightarrow> cond_D u v"
    and "a \<bullet> u = b \<bullet> v \<Longrightarrow> subprodl x y \<Longrightarrow> subprodl u v"
    and "subprodr y \<Longrightarrow> subprodr v"
proof -
  assume B: "cond_B x"
  have "length u = m" using len and le by (auto)
  show "cond_B u"
  proof (unfold cond_B_def, intro allI impI)
    fix k
    assume k: "k \<le> m"
    moreover have *: "take k u \<le>\<^sub>v take k x" if "k \<le> m" for k
      using le and that by (intro le_take) (auto simp: len)
    ultimately have "take k a \<bullet> take k u \<le> take k a \<bullet> take k x"
      by (intro dotprod_le_right) (auto simp: len)
    also have "\<dots> \<le> b \<bullet> map (maxy (take k x)) [0..<n]"
      using k and B by (auto simp: cond_B_def)
    also have "\<dots> \<le> b \<bullet> map (maxy (take k u)) [0..<n]"
      using le_imp_maxy_ge [OF * [OF k]]
      using k by (auto simp: len intro!: dotprod_le_right less_eqI)
    finally show "take k a \<bullet> take k u \<le> b \<bullet> map (maxy (take k u)) [0..<n]" .
  qed
next
  assume subprodr: "subprodr y"
  have "length v = n" using len and le by (auto)
  show "subprodr v"
  proof (unfold subprodr_def, intro allI impI)
    fix l
    assume l: "l \<le> n"
    moreover have *: "take l v \<le>\<^sub>v take l y" if "l \<le> n" for l
      using le and that by (intro le_take) (auto simp: len)
    ultimately have "take l b \<bullet> take l v \<le> take l b \<bullet> take l y"
      by (intro dotprod_le_right) (auto simp: len)
    also have "\<dots> \<le> a \<bullet> map (maxx (take l y)) [0..<m]"
      using l and subprodr by (auto simp: subprodr_def)
    also have "\<dots> \<le> a \<bullet> map (maxx (take l v)) [0..<m]"
      using le_imp_maxx_ge [OF * [OF l]]
      using l by (auto simp: len intro!: dotprod_le_right less_eqI)
    finally show "take l b \<bullet> take l v \<le> a \<bullet> map (maxx (take l v)) [0..<m]" .
  qed
next
  assume C: "boundr x y"
  show "boundr u v"
    using le_imp_maxy_ge [OF \<open>u \<le>\<^sub>v x\<close>] and C and le
    by (auto simp: boundr_def len less_eq_def) (meson order_trans)
next
  assume "a \<bullet> u = b \<bullet> v" and "cond_D x y"
  then show "cond_D u v"
    using le by (auto simp: cond_D_def len le_length intro: dotprod_le_take)
next
  assume "a \<bullet> u = b \<bullet> v" and "subprodl x y"
  then show "subprodl u v"
    using le by (metis subprodl_def dotprod_le_take le_length len(1))
qed

lemma (in hlde) special_solutions [simp]:
  shows "set (special_solutions a b) = Special_Solutions"
proof -
  have "set (special_solutions a b) \<subseteq> Special_Solutions"
    by (auto simp: Special_Solutions_def special_solutions_def) (blast)
  moreover have "Special_Solutions \<subseteq> set (special_solutions a b)"
    by (auto simp: Special_Solutions_def special_solutions_def)
      (metis SigmaI atLeast0LessThan lessThan_iff pair_imageI)
  ultimately show ?thesis ..
qed

lemma set_gen2:
  "set (gen2 A B a b) = {(x, y). x \<le>\<^sub>v replicate (length a) A \<and> y \<le>\<^sub>v replicate (length b) B}"
  (is "?L = ?R")
proof (intro equalityI subrelI)
  fix xs ys assume "(xs, ys) \<in> ?R"
  then have "\<forall>x\<in>set xs. x \<le> A" and "\<forall>y\<in>set ys. y \<le> B"
    and "length xs = length a" and "length ys = length b"
    by (auto simp: less_eq_def in_set_conv_nth)
  then have "((xs, a \<bullet> xs), (ys, b \<bullet> ys)) \<in> set (alls2 A B a b)" by (auto simp: set_alls2)
  then have "(\<lambda>(x, y). (fst x, fst y)) ((xs, a \<bullet> xs), (ys, b \<bullet> ys)) \<in> (\<lambda>(x, y). (fst x, fst y)) ` set (alls2 A B a b)"
    by (intro imageI)
  then show "(xs, ys) \<in> ?L" by simp
qed (auto simp: less_eq_def set_alls2)

lemma set_gen2':
  "(\<lambda>(x, y). (fst x, fst y)) ` set (alls2 A B a b) =
    {(x, y). x \<le>\<^sub>v replicate (length a) A \<and> y \<le>\<^sub>v replicate (length b) B}"
  using set_gen2 by simp

lemma (in hlde) in_non_special_solutions:
  assumes "(x, y) \<in> set (non_special_solutions a b)"
  shows "(x, y) \<in> Solutions"
  using assms
  by (auto dest!: minimize_wrtD in_generate
    simp: non_special_solutions_def Solutions_def minimize_def set_alls2)

lemma generate_unique:
  assumes "i < length (generate A B a b)"
    and "j < length (generate A B a b)"
    and "i < j"
  shows "generate A B a b ! i \<noteq> generate A B a b ! j"
  using sorted_wrt_nth_less [OF sorted_wrt_generate assms]
  by (auto simp: rlex2_irrefl)

lemma gen2_unique:
  assumes "i < length (gen2 A B a b)"
    and "j < length (gen2 A B a b)"
    and "i < j"
  shows "gen2 A B a b ! i \<noteq> gen2 A B a b ! j"
  using sorted_wrt_nth_less [OF sorted_wrt_gen2 assms]
  by (auto simp: rlex2_irrefl)

lemma zeroes_ni_generate:
  "(zeroes (length a), zeroes (length b)) \<notin> set (generate A B a b)"
proof -
  have "gen2 A B a b ! 0 = (zeroes (length a), zeroes (length b))" by (auto)
  with gen2_unique [of 0 A B a b] show ?thesis
    by (auto simp: in_set_conv_nth nth_tl generate_def)
      (metis One_nat_def Suc_eq_plus1 less_diff_conv zero_less_Suc)
qed

lemma set_generate':
  "set (generate A B a b) =
    {(x, y). (x, y) \<noteq> (zeroes (length a), zeroes (length b)) \<and> (x, y) \<in> set (gen2 A B a b)}"
proof
  show "set (generate A B a b)
        \<subseteq> {(x, y).(x, y) \<noteq> (zeroes (length a), zeroes (length b)) \<and> (x, y) \<in> set (gen2 A B a b)}"
    using in_generate and mem_Collect_eq and zeroes_ni_generate by (auto)
next
  have "(zeroes (length a), zeroes (length b)) = hd (gen2 A B a b)"
    by (simp add: hd_conv_nth)
  moreover have "set (gen2 A B a b) = set (tl (gen2 A B a b)) \<union> {(zeroes (length a), zeroes (length b))}"
    by (metis Un_empty_right Un_insert_right gen2_ne calculation list.exhaust_sel list.simps(15))
  ultimately show " {(x, y). (x, y) \<noteq> (zeroes (length a), zeroes (length b)) \<and> (x, y) \<in> set (gen2 A B a b)}
        \<subseteq> set (generate A B a b)"
    unfolding generate_def by blast
qed

lemma set_generate:
  "set (generate A B a b) =
  {(x, y). (x, y) \<noteq> (zeroes (length a), zeroes (length b)) \<and> x \<le>\<^sub>v replicate (length a) A \<and> y \<le>\<^sub>v replicate (length b) B}"
  by (simp add: set_generate' set_gen2')

lemma (in hlde) zeroes_ni_non_special_solutions:
  shows "(zeroes m, zeroes n) \<notin> set (non_special_solutions a b)"
proof -
  define All_lex where
    All_lex: "All_lex = gen2 (Max (set b)) (Max (set a)) a b"
  define z where z: "z = (zeroes m, zeroes n)"
  have "set (non_special_solutions a b) \<subseteq> set (tl (All_lex))"
    by (auto simp: All_lex generate_def non_special_solutions_def minimize_def dest: subsetD [OF minimize_wrt_subset])
  moreover have "z \<notin> set (tl (All_lex))"
    using zeroes_ni_generate All_lex z by (auto simp: generate_def)
  ultimately show ?thesis
    using z by blast
qed

lemma (in hlde) in_solve_in_solutions:
  assumes "(x, y) \<in> set (solve a b)"
  shows "(x, y) \<in> set (solutions a b)"
proof -
  consider "(x, y) \<in> set (special_solutions a b)"
    | (nonspecial) "(x, y) \<in> set (non_special_solutions a b)"
    using assms by (auto simp: solve_def)
  then show ?thesis
  proof (cases)
    case nonspecial
    then have "(x, y) \<in> Solutions" by (fact in_non_special_solutions)
    then have [simp]: "length x = m" "length y = n" by (auto simp: Solutions_def)
    have "(x, y) \<in> Minimal_Solutions"
    proof (intro Minimal_SolutionsI')
      show "(x, y) \<in> Solutions" by fact
      then show "nonzero x"
        using zeroes_ni_non_special_solutions and nonspecial
        by (auto dest: nonzero_Solutions_iff simp: not_nonzero_iff)
      show "\<not> (\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y)"
      proof
        assume "\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y"
        then obtain u and v where "(u, v) \<in> Minimal_Solutions"
          and less: "u @ v <\<^sub>v x @ y" by blast
        then consider "(u, v) \<in> Special_Solutions" | "(u, v) \<in> Minimal_Solutions - Special_Solutions" by blast
        then show False
        proof (cases)
          case 1
          then obtain i and j where ij: "i < m" "j < n"
            and [simp]: "u = (zeroes m)[i := dij i j]" "v = (zeroes n)[j := eij i j]"
            by (auto simp: Special_Solutions_def sij_def)
          moreover have "dij i j \<le> x ! i" and "eij i j \<le> y ! j"
            using less and ij
             apply auto
             apply (metis \<open>length x = m\<close> le_append length_list_update length_replicate less_eq_def nth_list_update_eq order_vec.dual_order.strict_iff_order)
            apply (metis \<open>length x = m\<close> le_append length_list_update length_replicate less_eq_def nth_list_update_eq order_vec.dual_order.strict_iff_order)
            done
          moreover then have "eij i j - 1 \<in> Ej j x" using ij by (auto simp: Ej_def)
          moreover then have ne: "Ej j x \<noteq> {}" and "Min (Ej j x) \<le> eij i j - 1" by (auto simp: finite_Ej)
          moreover have "boundr_impl a b x y"
            using nonspecial
            by (auto simp: non_special_solutions_def minimize_def dest!: minimize_wrtD)
          ultimately show False
            using less
            apply (auto simp: boundr_def sij_def Special_Solutions_def maxy_def)
            apply (drule_tac x = j in spec) apply (auto simp: if_P [OF ne])
            using eij_neq_0 by fastforce
        next
          case 2
          let ?P = "\<lambda>(x, y) (u, v). \<not> x @ y <\<^sub>v u @ v"
          let ?A = "Max (set b)" and ?B = "Max (set a)"
          let ?xs = "check' a b (generate ?A ?B a b)"
          have xy: "(x, y) \<in> set (minimize ?xs)" using nonspecial by (auto simp: non_special_solutions_def)
          have sorted: "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) ?xs" by (intro sorted_wrt_check_generate)
          have rlex2: "(u, v) <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 (x, y)" by (intro less_imp_rlex2) (auto simp: less)
          note minimize_False = in_minimize_wrt_False [OF rlex2_not_sym sorted _ _ rlex2, of ?P, folded minimize_def]
          show False using less
          proof (intro minimize_False [OF _ xy])
            show "(u, v) \<in> set ?xs"
              using 2 and max_coeff_bound_right
              apply (auto dest: conds simp: set_gen2' set_generate Minimal_Solutions_length max_coeff_bound static_bounds_def maxne0_impl)
              using Minimal_Solutions_gt0 apply fastforce
              apply (metis Minimal_Solutions_length hlde.max_coeff_bound_right hlde_axioms le_not_less_replicate le_trans maxne0_le_Max order_vec.dual_order.strict_implies_order order_vec.eq_iff)
              apply (metis Minimal_Solutions_length hlde.max_coeff_bound hlde_axioms le_replicateI le_trans maxne0_le_Max)
              using Minimal_Solutions_imp_Solutions Solutions_def apply blast
              done
          qed auto
        qed
      qed
    qed
    then show ?thesis by simp
  qed (simp add: Special_Solutions_in_Minimal_Solutions)
qed

lemma (in hlde) in_solutions_in_solve:
  assumes "(x, y) \<in> set (solutions a b)"
  shows "(x, y) \<in> set (solve a b)"
proof -
  have "(x, y) \<in> Minimal_Solutions" using assms by simp
  then show ?thesis
    apply (auto simp: solve_def non_special_solutions_def minimize_def conds static_bounds_def set_gen2' set_generate intro!: in_minimize_wrtI)
    using Minimal_Solutions_gt0 apply fastforce
          apply (metis Minimal_Solutions_length le_replicateI le_trans max_coeff_bound_right maxne0_le_Max)
         apply (metis Minimal_Solutions_length le_replicateI le_trans max_coeff_bound maxne0_le_Max)
        apply (auto simp add: Minimal_Solutions_length max_coeff_bound maxne0_impl)
    using Minimal_Solutions_imp_Solutions Solutions_def apply blast
     apply (metis (no_types, hide_lams) Minimal_Solutions_min eq_0_iff length_replicate less_eq_def nonzero_append nonzero_iff)
    by (metis (no_types, hide_lams) Minimal_Solutions_min eq_0_iff length_replicate less_eq_def nonzero_append nonzero_iff)
qed

lemma (in hlde) solutions_solve_conv:
  "set (solutions a b) = set (solve a b)"
  by (auto simp only: in_solutions_in_solve in_solve_in_solutions)


subsubsection \<open>Correctness: \<open>solve\<close> generates only minimal solutions.\<close>

lemma (in hlde) solve_subset_Minimal_Solutions:
  shows "set (solve a b) \<subseteq> Minimal_Solutions"
proof (rule subrelI)
  let ?a = "Max (set a)" and ?b = "Max (set b)"
  fix x y
  assume ass: "(x, y) \<in> set (solve a b)"
  then consider "(x, y) \<in> set (special_solutions a b)" | "(x, y) \<in> set (non_special_solutions a b)"
    unfolding solve_def and set_append by blast
  then show "(x, y) \<in> Minimal_Solutions"
  proof (cases)
    case 1
    then have "(x, y) \<in> Special_Solutions"
      unfolding special_solutions .
    then show ?thesis
      by (simp add: Special_Solutions_in_Minimal_Solutions)
  next
    let ?xs = "[(x, y) \<leftarrow> generate ?b ?a a b.
      static_bounds a b x y \<and> a \<bullet> x = b \<bullet> y \<and> boundr x y (*\<and> cond_B x \<and> cond_D x y*) \<and>
      subprodl x y \<and>
      subprodr y]"
    case 2
    then have conds: "\<forall>e\<in>set x. e \<le> Max (set b)" "boundr x y" (*"cond_B x" "cond_D x y"*)
      "subprodl x y" "subprodr y"
      and xs: "(x, y) \<in> set (minimize ?xs)"
      by (auto simp: non_special_solutions_def minimize_def set_alls2
        dest!: minimize_wrtD in_generate)
        (metis in_set_conv_nth)
    have sol: "(x, y) \<in> Solutions"
      using ass by (auto simp: solve_def Special_Solutions_in_Solutions in_non_special_solutions)
    then have len: "length x = m" "length y = n" by (auto simp: Solutions_def)
    have "nonzero x"
      using sol Solutions_snd_not_0 [of y x]
      by (metis "2" eq_0_iff len nonzero_Solutions_iff nonzero_iff zeroes_ni_non_special_solutions)
    moreover have "\<not> (\<exists>(u, v) \<in> Minimal_Solutions. u @ v <\<^sub>v x @ y)"
    proof
      let ?P = "\<lambda>(x, y) (u, v). \<not> x @ y <\<^sub>v u @ v"
      let ?Q = "(\<lambda>(x, y). static_bounds a b x y \<and> a \<bullet> x = b \<bullet> y \<and> boundr x y (*\<and> cond_B x \<and> cond_D x y*) \<and>
        subprodl x y \<and>
        subprodr y)"
      note sorted = sorted_wrt_generate [THEN sorted_wrt_filter, of ?Q ?b ?a a b]
      note * = in_minimize_wrt_False [OF _ sorted, of "(x, y)" ?P, OF _ xs [unfolded minimize_def]]

      assume "\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y"
      then obtain u and v where
        uv: "(u, v) \<in> Minimal_Solutions" and less: "u @ v <\<^sub>v x @ y" by blast
      from uv and less have le: "u \<le>\<^sub>v x" "v \<le>\<^sub>v y" and sol': "a \<bullet> u = b \<bullet> v"
        and nonzero: "nonzero u"
        using sol by (auto simp: Minimal_Solutions_def Solutions_def elim!: less_append_cases)
      (*with le_imp_conds [OF le conds(2-)]*)
      with le_imp_conds(2,4,5) [OF le] and conds(2-)
      have conds': "\<forall>e\<in>set u. e \<le> Max (set b)" "boundr u v" (*"cond_B u" "cond_D u v"*)
        "subprodl u v" "subprodr v"
        using conds(1,3,4) by (auto simp: len less_eq_def) (metis in_set_conv_nth le_trans len(1))
      moreover have "static_bounds a b u v"
        using max_coeff_bound [OF uv] and Minimal_Solutions_length [OF uv]
        by (auto simp: static_bounds_def maxne0_impl)
      moreover have "x \<le>\<^sub>v replicate m ?b"
        using xs set_generate [of "Max (set b)" "Max (set a)" a b]
          cond_A_def conds(1) le_replicateI len by metis
      moreover have "y \<le>\<^sub>v replicate n ?a"
        using xs by (auto simp: less_eqI minimize_def set_generate set_alls2 dest!: minimize_wrtD)
      ultimately have "(u, v) \<in> set ?xs"
        using sol' set_generate [of ?b ?a a b] uv [THEN Minimal_Solutions_imp_Solutions] and nonzero
        unfolding set_generate and set_gen2
        apply (simp add:)
        unfolding set_generate set_gen2
        apply (simp)
        by (metis in_set_replicate le order_vec.dual_order.trans nonzero_iff)
      from * [OF _ _ _ this] and less show False
        using less_imp_rlex and rlex_not_sym by force
    qed
    ultimately show ?thesis by (simp add: Minimal_SolutionsI' sol)
  qed
qed


subsubsection \<open>Completeness: every minimal solution is generated by \<open>solve\<close>\<close>

lemma (in hlde) Minimal_Solutions_subset_solve:
  shows "Minimal_Solutions \<subseteq> set (solve a b)"
proof (rule subrelI)
  fix x y
  assume min: "(x, y) \<in> Minimal_Solutions"
  then have sol: "a \<bullet> x = b \<bullet> y" "length x = m" "length y = n"
    and [dest]: "x = zeroes m \<Longrightarrow> y = zeroes n \<Longrightarrow> False"
    by (auto simp: Minimal_Solutions_def Solutions_def nonzero_iff)
  consider (special) "(x, y) \<in> Special_Solutions"
    | (not_special) "(x, y) \<notin> Special_Solutions" by blast
  then show "(x, y) \<in> set (solve a b)"
  proof (cases)
    case special
    then show ?thesis
      by (simp add: no0 solve_def)
  next
    define all where "all = generate (Max (set b)) (Max (set a)) a b"
    have *: "\<forall>(u, v) \<in> set (check' a b all). \<not> u @ v <\<^sub>v x @ y"
      using min and no0
      by (auto simp: all_def set_generate neq_0_iff' nonzero_iff dest!: Minimal_Solutions_min)

    case not_special
    from conds [OF min] and not_special
    have "(x, y) \<in> set (check' a b all)"
      using max_coeff_bound [OF min] and maxne0_le_Max
        and Minimal_Solutions_length [OF min]
      apply (auto simp: sol all_def set_generate cond_A_def less_eq_def static_bounds_def maxne0_impl)
       apply (metis le_trans nth_mem sol(2))
       by (metis le_trans nth_mem sol(3))
    from in_minimize_wrtI [OF this, of "\<lambda>(x, y) (u, v). \<not> x @ y <\<^sub>v u @ v"] *
    have "(x, y) \<in> set (non_special_solutions a b)"
      by (auto simp: non_special_solutions_def minimize_def all_def)
    then show ?thesis
      by (simp add: solve_def)
  qed
qed


text \<open>the main correctness and completeness result of our algorithm\<close>
lemma (in hlde) solve [simp]:
  shows "set (solve a b) = Minimal_Solutions"
  unfolding set_solutions [symmetric]
  using in_solve_in_solutions and in_solutions_in_solve by auto


section \<open>Making the Algorithm More Efficient\<close>

locale bounded_gen_check =
  fixes C :: "nat list \<Rightarrow> nat \<Rightarrow> bool"
    and B :: nat
  assumes bound: "\<And>x xs s. x > B \<Longrightarrow> C (x # xs) s = False"
    and cond_antimono: "\<And>x x' xs s s'. C (x # xs) s \<Longrightarrow> x' \<le> x \<Longrightarrow> s' \<le> s \<Longrightarrow> C (x' # xs) s'"
begin

function incs :: "nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat) \<Rightarrow> (nat list \<times> nat) list"
  where
    "incs a x (xs, s) =
      (let t = s + a * x in
      if C (x # xs) t then (x # xs, t) # incs a (Suc x) (xs, s) else [])"
  by (auto)
termination
  by (relation "measure (\<lambda>(a, x, xs, s). B + 1 - x)", rule wf_measure, case_tac "x > B")
    (use bound in auto)
declare incs.simps [simp del]

lemma in_incs:
  assumes "(ys, t) \<in> set (incs a x (xs, s))"
  shows "length ys = length xs + 1 \<and> t = s + hd ys * a \<and> tl ys = xs \<and> C ys t"
  using assms
  by (induct a x "(xs, s)" arbitrary: ys t rule: incs.induct)
    (subst (asm) (2) incs.simps, auto simp: Let_def)

lemma incs_Nil [simp]: "x > B \<Longrightarrow> incs a x (xs, s) = []"
  apply (induct a x "(xs, s)" rule: incs.induct)
  apply (subst incs.simps)
  apply (insert bound, auto simp: Let_def)
  done

lemma incs_filter:
  assumes "x \<le> B"
  shows "incs a x = (\<lambda>(xs, s). filter (cond_cons C) (map (\<lambda>x. (x # xs, s + a * x)) [x ..< B + 1]))"
proof
  fix xss
  show "incs a x xss = (\<lambda>(xs, s). filter (cond_cons C) (map (\<lambda>x. (x # xs, s + a * x)) [x ..< B + 1])) xss"
    using assms
  proof (induct a x xss rule: incs.induct)
    case (1 a x xs s)
    then show ?case
      apply (subst incs.simps)
      apply (cases "x = B")
       apply (auto simp: filter_empty_conv Let_def cond_cons_def upt_conv_Cons intro: cond_antimono)
      done
  qed
qed

fun gen_check :: "nat list \<Rightarrow> (nat list \<times> nat) list"
  where
    "gen_check [] = [([], 0)]"
  | "gen_check (a # as) = concat (map (incs a 0) (gen_check as))"

lemma gen_check_len:
  assumes "(ys, s) \<in> set (gen_check as)"
  shows "length ys = length as"
  using assms
proof (induct as arbitrary: ys s)
  case (Cons a as)
  have "\<exists>(la,t) \<in> set (gen_check as). (ys, s) \<in> set (incs a 0 (la,t))"
    using Cons.prems(1) by auto
  moreover obtain  la t where "(la,t) \<in> set (gen_check as)"
    using calculation by auto
  moreover have "length ys = length la + 1"
    using calculation
    by (metis (no_types, lifting) Cons.hyps case_prodE in_incs)
  moreover have "length la = length as"
    using calculation
    using Cons.hyps Cons.prems by fastforce
  ultimately show ?case by simp
qed (auto)

lemma in_gen_check:
  assumes "(xs, s) \<in> set (gen_check as)"
  shows "length xs = length as \<and> s = as \<bullet> xs"
  using assms
  apply (induct as arbitrary: xs s)
   apply (auto simp: in_incs)
  apply (case_tac xs)
   apply (auto dest: in_incs)
  done

lemma gen_check_filter:
  "gen_check as = filter (suffs C as) (alls B as)"
proof (induct as)
next
  case (Cons a as)
  have "filter (suffs C (a # as)) (alls B (a # as)) =
    filter (\<lambda>(xs, s). cond_cons C (xs, s) \<and> suffs C as (tl xs, as \<bullet> tl xs)) (alls B (a # as))"
    by (intro filter_cong [OF refl])
      (auto simp: set_alls suffs.simps all_Suc_le_conv ac_simps split: list.splits)
  also have "\<dots> =
    concat (map (\<lambda>(xs, s). filter (cond_cons C) (map (\<lambda>x. (x # xs, s + a * x)) [0..<B + 1]))
      (filter (suffs C as) (alls B as)))"
    unfolding alls.simps
    unfolding filter_concat
    unfolding map_map
    by (subst concat_map_filter_filter [symmetric, where Q = "suffs C as"])
      (auto simp: set_alls intro!: arg_cong [of _ _ concat] filter_cong)
  finally have *: "filter (suffs C (a # as)) (alls B (a # as)) =
    concat (map (\<lambda>(xs, s).
      filter (cond_cons C) (map (\<lambda>x. (x # xs, s + a * x)) [0..<B + 1])) (filter (suffs C as) (alls B as)))" .
  have "gen_check (a # as) = filter (suffs C (a # as)) (alls B (a # as))"
    unfolding *
    by (simp add: incs_filter [OF zero_le] Cons)
  then show ?case by simp
qed simp

lemma in_gen_check_cond:
  assumes "(xs, s) \<in> set (gen_check as)"
  shows "\<forall>j\<le>length xs. drop j xs \<noteq> [] \<longrightarrow> C (drop j xs) (s - take j as \<bullet> take j xs)"
  using assms
  apply (induct as arbitrary: xs s)
   apply auto
  apply (case_tac xs)
   apply auto
  apply (case_tac j)
   apply (auto dest: in_incs)
  done

lemma sorted_gen_check:
  "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x) (map fst (gen_check xs))"
proof -
  have sort_map: "sorted_wrt (\<lambda>x y. x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x y) (map fst (alls B xs))"
    using sorted_wrt_alls by auto
  then have "sorted_wrt (\<lambda>x y. fst x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x fst y) (alls B xs)"
    using sorted_wrt_map_distr [of "(<\<^sub>r\<^sub>l\<^sub>e\<^sub>x)" fst "alls B xs"]
    by (auto)
  then have "sorted_wrt (\<lambda>x y. fst x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x fst y) (filter (suffs C xs) (alls B xs))"
    using sorted_wrt_alls sorted_wrt_filter sorted_wrt_map
    by blast
  then show ?thesis
    using gen_check_filter
    by (simp add: case_prod_unfold sorted_wrt_map_mono)
qed

end

locale bounded_generate_check =
  c2: bounded_gen_check C\<^sub>2 B\<^sub>2 for C\<^sub>2 B\<^sub>2 +
  fixes C\<^sub>1 and B\<^sub>1
  assumes cond1: "\<And>b ys. ys \<in> fst ` set (c2.gen_check b) \<Longrightarrow> bounded_gen_check (C\<^sub>1 b ys) (B\<^sub>1 b)"
begin

definition "generate_check a b =
  [(xs, ys). ys \<leftarrow> c2.gen_check b, xs \<leftarrow> bounded_gen_check.gen_check (C\<^sub>1 b (fst ys)) a]"

lemma generate_check_filter_conv:
  "generate_check a b = [(xs, ys).
    ys \<leftarrow> filter (suffs C\<^sub>2 b) (alls B\<^sub>2 b),
    xs \<leftarrow> filter (suffs (C\<^sub>1 b (fst ys)) a) (alls (B\<^sub>1 b) a)]"
  using bounded_gen_check.gen_check_filter [OF cond1]
  by (force simp: generate_check_def c2.gen_check_filter intro!: arg_cong [of _ _ concat] map_cong)

lemma generate_check_filter:
  "generate_check a b = [(xs, ys) \<leftarrow> alls2 (B\<^sub>1 b) B\<^sub>2 a b. suffs (C\<^sub>1 b (fst ys)) a xs \<and> suffs C\<^sub>2 b ys]"
  by (auto intro: arg_cong [of _ _ concat]
    simp: generate_check_filter_conv alls2_def filter_concat concat_map_filter filter_map o_def)

lemma tl_generate_check_filter:
  assumes "suffs (C\<^sub>1 b (zeroes (length b))) a (zeroes (length a), 0)"
    and "suffs C\<^sub>2 b (zeroes (length b), 0)"
  shows "tl (generate_check a b) = [(xs, ys) \<leftarrow> tl (alls2 (B\<^sub>1 b) B\<^sub>2 a b). suffs (C\<^sub>1 b (fst ys)) a xs \<and> suffs C\<^sub>2 b ys]"
  using assms
  apply (auto simp: generate_check_filter)
  apply (subst (1 2) alls2_Cons_tl_conv)
  apply auto
  done

end

context
  fixes a b :: "nat list"
begin

fun cond1
  where
    "cond1 ys [] s \<longleftrightarrow> True"
  | "cond1 ys (x # xs) s \<longleftrightarrow> s \<le> b \<bullet> ys \<and> x \<le> maxne0_impl ys b"

lemma maxx_impl'_conv:
  "i < length a \<Longrightarrow> length y = length b \<Longrightarrow> maxx_impl' a b y i = maxx_impl a b y i"
  by (auto simp: maxx_impl'_def maxx_impl_def Let_def big_d'_def big_d_def)

fun cond2
  where
    "cond2 [] s \<longleftrightarrow> True"
  | "cond2 (y # ys) s \<longleftrightarrow> y \<le> Max (set a) \<and> s \<le> a \<bullet> map (maxx_impl' a b (y # ys)) [0 ..< length a]"

lemma le_imp_big_d'_subset:
  assumes "v \<le>\<^sub>v y"
  shows "set (big_d' a b v i) \<subseteq> set (big_d' a b y i)"
  using assms and le_trans
  by (auto simp: Let_def big_d'_def less_eq_def hlde_ops.dij_def hlde_ops.eij_def)

lemma finite_big_d':
  "finite (set (big_d' a b y i))"
  by (rule finite_subset [of _ "(\<lambda>j. dij a b i (j + length b - length y) - 1) ` {0 ..< length y}"])
    (auto simp: Let_def big_d'_def)

lemma Min_big_d'_le:
  assumes "i < length a"
    and "big_d' a b y i \<noteq> []"
    and "length y \<le> length b"
  shows "Min (set (big_d' a b y i)) \<le> Max (set b)" (is "?m \<le> _")
proof -
  have "?m \<in> set (big_d' a b y i)"
    using assms and finite_big_d' and Min_in by auto
  then obtain j where
    j: "?m = dij a b i (j + length b - length y) - 1" "j < length y" "y ! j \<ge> eij a b i (j + length b - length y)"
    by (auto simp: big_d'_def Let_def split: if_splits)
  then have "j + length b - length y < length b"
    using assms by auto
  moreover
  have "lcm (a ! i) (b ! (j + length b - length y)) div a ! i \<le> b ! (j + length b - length y)" by (rule lcm_div_le')
  ultimately show ?thesis
    using j and assms
    by (auto simp: hlde_ops.dij_def)
      (meson List.finite_set Max_ge diff_le_self le_trans less_le_trans nth_mem)
qed

lemma le_imp_maxx_impl'_ge:
  assumes "v \<le>\<^sub>v y"
    and "i < length a"
  shows "maxx_impl' a b v i \<ge> maxx_impl' a b y i"
  using assms and le_imp_big_d'_subset [OF assms(1), of i]
    and Min_in [OF finite_big_d', of y i]
    and finite_big_d' and Min_le
  by (auto simp: maxx_impl'_def Let_def intro!: Min_big_d'_le [of i y])
    (fastforce simp: big_d'_def intro: leI)

end

global_interpretation c12: bounded_generate_check "(cond2 a b)" "Max (set a)" "cond1" "\<lambda>b. Max (set b)"
  defines c2_gen_check = c12.c2.gen_check and c2_incs = c12.c2.incs
    and c12_generate_check = c12.generate_check
proof -
  { fix x xs s assume "Max (set a) < x"
    then have "cond2 a b (x # xs) s = False" by (auto) }
  note 1 = this

  { fix x x' xs s s' assume "cond2 a b (x # xs) s" and "x' \<le> x" and "s' \<le> s"
    moreover have "map (maxx_impl' a b (x # xs)) [0..<length a] \<le>\<^sub>v map (maxx_impl' a b (x' # xs)) [0..<length a]"
      using le_imp_maxx_impl'_ge [of "x' # xs" "x # xs"] and \<open>x' \<le> x\<close>
      by (auto simp: le_Cons less_eq_def all_Suc_conv)
    ultimately have "cond2 a b (x' # xs) s'"
      by (auto simp: le_Cons) (metis dotprod_le_right le_trans length_map map_nth) }
  note 2 = this

  interpret c2: bounded_gen_check "cond2 a b" "Max (set a)" by (standard) fact+

  { fix b ys x xs s assume "ys \<in> fst ` set (c2.gen_check b)" and "Max (set b) < x"
  then have "cond1 b ys (x # xs) s = False"
    by (auto dest!: c2.in_gen_check) (metis leD less_le_trans maxne0_impl maxne0_le_Max) }
  note 3 = this

  { fix b ys x x' xs s s' assume "ys \<in> fst ` set (c2.gen_check b)" and "cond1 b ys (x # xs) s"
      and "x' \<le> x" and "s' \<le> s"
    then have "cond1 b ys (x' # xs) s'" by auto }
  note 4 = this

  show "bounded_generate_check (cond2 a b) (Max (set a)) cond1 (\<lambda>b. Max (set b))"
    using 1 and 2 and 3 and 4 by (unfold_locales) metis+
qed

definition "post_cond a b = (\<lambda>(x, y). static_bounds a b x y \<and> a \<bullet> x = b \<bullet> y \<and> boundr_impl a b x y)"

definition "fast_filter a b =
  filter (post_cond a b) (map (\<lambda>(x, y). (fst x, fst y)) (tl (c12_generate_check a b a b)))"

lemma cond1_cond2_zeroes:
  shows "suffs (cond1 b (zeroes (length b))) a (zeroes (length a), 0)"
    and "suffs (cond2 a b) b (zeroes (length b), 0)"
   apply (auto simp: suffs.simps cond_cons_def split: list.splits)
     apply (metis dotprod_0_right length_drop)
    apply (metis Cons_replicate_eq Nat.le0)
   apply (metis Cons_replicate_eq Nat.le0)
  by (metis Nat.le0 dotprod_0_right length_drop)

lemma suffs_cond1I:
  assumes "\<forall>y\<in>set aa. y \<le> maxne0_impl aaa b"
    and "length aa = length a"
    and "a \<bullet> aa = b \<bullet> aaa"
  shows "suffs (cond1 b aaa) a (aa, b \<bullet> aaa)"
  using assms
  apply (auto simp: suffs.simps cond_cons_def split: list.splits)
   apply (metis dotprod_le_drop)
  by (metis in_set_dropD list.set_intros(1))

lemma suffs_cond2_conv:
  assumes "length ys = length b"
  shows "suffs (cond2 a b) b (ys, b \<bullet> ys) \<longleftrightarrow>
    (\<forall>y\<in>set ys. y \<le> Max (set a)) \<and> pdprodr_impl a b ys"
    (is "?L \<longleftrightarrow> ?R")
proof
  assume *: ?L
  then have "\<forall>y\<in>set ys. y \<le> Max (set a)"
    apply (auto simp: suffs.simps cond_cons_def in_set_conv_nth split: list.splits)
    apply (auto simp: hd_drop_conv_nth [symmetric])
    apply (case_tac "drop i ys")
      apply simp_all
    using less_or_eq_imp_le by blast
  moreover
  { fix l assume l: "l \<le> length b"
    have "take l b \<bullet> take l ys \<le> b \<bullet> ys"
      using l and assms by (simp add: dotprod_le_take)
    also have "\<dots> \<le> a \<bullet> map (maxx_impl' a b ys) [0 ..< length a]"
      using * apply (auto simp: suffs.simps cond_cons_def split: list.splits)
      apply (drule_tac x = "0" in spec)
        apply (cases ys)
       apply auto
      done
    also have "\<dots> = a \<bullet> map (maxx_impl a b ys) [0 ..< length a]"
      using maxx_impl'_conv [OF _ assms, of _ a]
      by (metis (mono_tags, lifting) atLeastLessThan_iff map_eq_conv set_upt)
    also have "\<dots> \<le> a \<bullet> map (maxx_impl a b (take l ys)) [0 ..< length a]"
      unfolding maxx_impl using hlde_ops.maxx_le_take [OF eq_imp_le, OF assms, of a]
      by (intro dotprod_le_right) (auto simp: less_eq_def)
    finally have "take l b \<bullet> take l ys \<le> a \<bullet> map (maxx_impl a b (take l ys)) [0 ..< length a]" .
  }
  ultimately show "?R" by (auto simp: pdprodr_impl_def)
next
  assume *: ?R
  then have "\<forall>y\<in>set ys. y \<le> Max (set a)" and "pdprodr_impl a b ys" by auto
  moreover
  { fix i assume i: "i \<le> length b"
    have "drop i b \<bullet> drop i ys \<le> b \<bullet> ys"
      using i and assms by (simp add: dotprod_le_drop)
    also have "\<dots> \<le> a \<bullet> map (maxx_impl a b ys) [0 ..< length a]"
      using * and assms by (auto simp: pdprodr_impl_def)
    also have "\<dots> = a \<bullet> map (maxx_impl' a b ys) [0 ..< length a]"
      using maxx_impl'_conv [OF _ assms, of _ a]
      by (metis (mono_tags, lifting) atLeastLessThan_iff map_eq_conv set_upt)
    also have "\<dots> \<le> a \<bullet> map (maxx_impl' a b (drop i ys)) [0 ..< length a]"
      using hlde_ops.maxx'_le_drop [OF eq_imp_le, OF assms, of a]
      by (intro dotprod_le_right) (auto simp: less_eq_def maxx_impl' i assms)
    finally have "drop i b \<bullet> drop i ys \<le> a \<bullet> map (maxx_impl' a b (drop i ys)) [0 ..< length a]" .
  }
  ultimately show "?L"
    using assms
    apply (auto simp: suffs.simps cond_cons_def split: list.splits)
     apply (metis in_set_dropD list.set_intros(1))
    apply force
    done
qed

lemma suffs_cond2I:
  assumes "\<forall>y\<in>set aaa. y \<le> Max (set a)"
    and "length aaa = length b"
    and "pdprodr_impl a b aaa"
  shows "suffs (cond2 a b) b (aaa, b \<bullet> aaa)"
  using assms by (subst suffs_cond2_conv) simp_all

lemma check_cond_conv:
  assumes "(x, y) \<in> set (alls2 (Max (set b)) (Max (set a)) a b)"
  shows "check_cond a b (fst x, fst y) \<longleftrightarrow>
    static_bounds a b (fst x) (fst y) \<and> a \<bullet> fst x = b \<bullet> fst y \<and> boundr_impl a b (fst x) (fst y) \<and>
    suffs (cond1 b (fst y)) a x \<and>
    suffs (cond2 a b) b y"
  using assms
  apply (cases x; cases y; auto simp: static_bounds_def check_cond_def set_alls2 split: list.splits)
     apply (auto intro: suffs_cond1I suffs_cond2I simp: pdprodl_impl_def suffs_cond2_conv)
  apply (metis in_set_conv_nth)
  by (metis dotprod_le_take)

lemma tune:
  "check' a b (generate (Max (set b)) (Max (set a)) a b) = fast_filter a b"
  using cond1_cond2_zeroes
  unfolding fast_filter_def
  apply (subst c12.tl_generate_check_filter)
    apply (auto simp: check'_def generate_def map_tl [symmetric] filter_map post_cond_def intro!: map_cong)
  apply (auto simp: o_def)
  apply (rule filter_cong)
   apply (auto dest!: list.set_sel(2) [THEN check_cond_conv, OF alls2_ne])
  done

locale bounded_incs =
  fixes cond :: "nat list \<Rightarrow> nat \<Rightarrow> bool"
    and B :: nat
  assumes bound: "\<And>x xs s. x > B \<Longrightarrow> cond (x # xs) s = False"
begin

function incs :: "nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat) \<Rightarrow> (nat list \<times> nat) list"
  where
    "incs a x (xs, s) =
      (let t = s + a * x in
      if cond (x # xs) t then (x # xs, t) # incs a (Suc x) (xs, s) else [])"
  by (auto)
termination
  by (relation "measure (\<lambda>(a, x, xs, s). B + 1 - x)", rule wf_measure, case_tac "x > B")
    (use bound in auto)
declare incs.simps [simp del]

lemma in_incs:
  assumes "(ys, t) \<in> set (incs a x (xs, s))"
  shows "length ys = length xs + 1 \<and> t = s + hd ys * a \<and> tl ys = xs \<and> cond ys t"
  using assms
  by (induct a x "(xs, s)" arbitrary: ys t rule: incs.induct)
    (subst (asm) (2) incs.simps, auto simp: Let_def)

lemma incs_Nil [simp]: "x > B \<Longrightarrow> incs a x (xs, s) = []"
  apply (induct a x "(xs, s)" rule: incs.induct)
  apply (subst incs.simps)
  apply (insert bound, auto simp: Let_def)
  done

end

global_interpretation incs1:
  bounded_incs "(cond1 b ys)" "(Max (set b))"
  for b ys :: "nat list"
  defines c1_incs = incs1.incs
proof
  fix x xs s
  assume "Max (set b) < x"
  then show "cond1 b ys (x # xs) s = False"
    using maxne0_impl_le [of ys b] by auto
qed

fun c1_gen_check
  where
    "c1_gen_check b ys [] = [([], 0)]"
  | "c1_gen_check b ys (a # as) = concat (map (c1_incs b ys a 0) (c1_gen_check b ys as))"

definition "generate_check a b = [(xs, ys). ys \<leftarrow> c2_gen_check a b b, xs \<leftarrow> c1_gen_check b (fst ys) a]"

lemma c1_gen_check_conv:
  assumes "(ys, s) \<in> set (c2_gen_check a b b)"
  shows "c1_gen_check b ys a = bounded_gen_check.gen_check (cond1 b ys) a"
proof -
  interpret c1: bounded_gen_check "(cond1 b ys)" "Max (set b)"
    by (unfold_locales) (auto, meson leD less_le_trans maxne0_impl_le)
  have eq: "c1_incs b ys a1 0 (a, ba) = c1.incs a1 0 (a, ba)" if "(a, ba) \<in> set (c1.gen_check a2)"
    for a a1 a2 ba
    using that
    apply (induct rule: c1.incs.induct)
    apply (auto dest!: c1.in_gen_check)
    apply (subst incs1.incs.simps)
    apply (subst c1.incs.simps)
    by (auto simp: Let_def)
  show ?thesis
    by (induct a) (auto intro!: arg_cong [of _ _ concat] dest: eq)
qed


subsection \<open>Code Generation\<close>

lemma solve_efficient [code]:
  "solve a b = special_solutions a b @ minimize (fast_filter a b)"
  by (auto simp: solve_def non_special_solutions_def tune)

lemma c12_generate_check_code [code_unfold]:
  "c12_generate_check a b a b = generate_check a b"
  by (auto simp: generate_check_def c12.generate_check_def c1_gen_check_conv intro!: arg_cong [of _ _ concat])

end
