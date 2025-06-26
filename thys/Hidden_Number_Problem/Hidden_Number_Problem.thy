theory Hidden_Number_Problem
  imports
    "HOL-Number_Theory.Number_Theory"
    "Babai_Correctness_Updated"
    "Misc_PMF"

begin

hide_fact Finite_Cartesian_Product.mat_def
hide_const Finite_Cartesian_Product.mat
hide_const Finite_Cartesian_Product.row
hide_fact Finite_Cartesian_Product.row_def
hide_const Determinants.det
hide_fact Determinants.det_def
hide_type Finite_Cartesian_Product.vec
hide_const Finite_Cartesian_Product.vec
hide_fact Finite_Cartesian_Product.vec_def
hide_const (open) Finite_Cartesian_Product.transpose
hide_fact (open) Finite_Cartesian_Product.transpose_def
unbundle no inner_syntax
unbundle no vec_syntax
hide_const (open) Missing_List.span
hide_const (open)
  dependent
  independent
  real_vector.representation
  real_vector.subspace
  span
  real_vector.extend_basis
  real_vector.dim
hide_const (open) orthogonal
no_notation fps_nth (infixl "$" 75)

section "General helper lemmas"

(* Note that the dimension assumption is important here *)
lemma uminus_sq_norm:
  fixes u v :: "rat vec"
  assumes "dim_vec u = dim_vec v"
  shows "sq_norm (u - v) = sq_norm (v - u)"
  using assms
proof-
  have "u-v = (-1) \<cdot>\<^sub>v (v - u)" using assms by auto
  then show ?thesis
    using sq_norm_smult_vec[of "-1" "v-u"] by auto
qed

(* modified from smult_add_distrib_vec in the libraries *)
lemma smult_sub_distrib_vec:
  assumes "v \<in> carrier_vec q" "w \<in> carrier_vec q"
  shows "(a::'a::ring) \<cdot>\<^sub>v (v - w) = a \<cdot>\<^sub>v v - a \<cdot>\<^sub>v w"
  apply (rule eq_vecI)
  unfolding smult_vec_def plus_vec_def
  using assms right_diff_distrib 
  apply force
  by auto

lemma set_list_subset:
  fixes l :: "'a list"
  fixes S :: "'a set"
  assumes "\<forall>i \<in> {0..<length l}. l ! i \<in> S"
  shows "set l \<subseteq> S"
  by (metis assms atLeastLessThan_iff in_set_conv_nth le0 subset_code(1))

lemma nat_subset_inf:
  fixes A :: "int set"
  assumes "A \<subseteq> \<nat>"
  assumes "A \<noteq> {}"
  shows "Inf A \<in> A"
proof-
  let ?A' = "nat`A"
  have "?A' \<noteq> {}" using assms(2) by blast
  hence "Inf ?A' \<in> ?A'" using Inf_nat_def1 by presburger
  then obtain z where z: "z \<in> A \<and> nat z = Inf ?A'" by fastforce
  moreover have "Inf A = z"
  proof-
    have *: "z \<ge> 0" using z assms(1) Nats_altdef2 by blast
    have "\<forall>z' \<in> A. z \<le> z'"
    proof
      fix z' assume **: "z' \<in> A"
      hence "nat z' \<in> ?A'" by blast
      hence "nat z \<le> nat z'" using z wellorder_Inf_le1[of "nat z'" ?A'] by argo
      moreover have "z' \<ge> 0" using ** assms(1) Nats_altdef2 by fastforce
      ultimately show "z \<le> z'" using * by linarith
    qed
    thus ?thesis using z by (meson cInf_eq_minimum)
  qed
  ultimately show ?thesis by argo
qed

lemma cong_set_subseteq:
  fixes a b m :: "'a :: {unique_euclidean_ring,abs}"
  defines "S \<equiv> {\<bar>a + z * m\<bar> | z. True}"
  defines "S' \<equiv> {\<bar>b + z * m\<bar> | z. True}"
  assumes "[a = b] (mod m)"
  shows "S \<subseteq> S'"
proof
  fix x assume "x \<in> S"
  then obtain z where z: "x = \<bar>a + z * m\<bar>" unfolding S_def by blast
  moreover obtain k where k: "a = b + k * m"
    by (metis assms(3) cong_iff_lin cong_sym mult_commute_abs)
  ultimately have "x = \<bar>b + k * m + z * m\<bar>"
    by presburger
  also have "\<dots> = \<bar>b + (k + z) * m\<bar>"
    by (metis Groups.group_cancel.add1 distrib_right)
  also have "\<dots> \<in> S'" unfolding S'_def by blast
  finally show "x \<in> S'" .
qed

lemma cong_set_eq:
  fixes a b m :: "'a :: {unique_euclidean_ring,abs}"
  defines "S \<equiv> {\<bar>a + z * m\<bar> | z. True}"
  defines "S' \<equiv> {\<bar>b + z * m\<bar> | z. True}"
  assumes "[a = b] (mod m)"
  shows "S = S'"
  apply auto[1]
   using cong_set_subseteq[of a b m] assms apply blast
  using cong_set_subseteq[of b a m] assms cong_sym by blast


context vec_module
begin

(* This may be somewhere in the libraries *)
lemma sumlist_distrib:
  fixes ys :: "('a::comm_ring_1) vec list"
  assumes "\<And>w. List.member ys w \<Longrightarrow> dim_vec w = n"
  shows "k \<cdot>\<^sub>v sumlist ys = sumlist (map (\<lambda>i. k \<cdot>\<^sub>v i) ys)"
  using assms
proof (induct ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  have sumlist_is: "sumlist (a # ys) = a + sumlist ys"
    by simp
  have dim_a: "a \<in> carrier_vec n"
    using Cons(2) 
    by (metis carrier_vecI member_rec(1))
  have dim_sumlist: "sumlist ys \<in> carrier_vec n"
    using Cons(2)
    by (metis List.member_def carrier_vec_dim_vec dim_sumlist member_rec(1)) 
  have distrib: "k \<cdot>\<^sub>v (a + sumlist ys) = k \<cdot>\<^sub>v a +  k \<cdot>\<^sub>v sumlist ys"
    using smult_add_distrib_vec[OF dim_a dim_sumlist]
    by auto
  have ih: "(\<And>w. List.member ys w \<Longrightarrow> dim_vec w = n)"
    using Cons(2)
    by (meson member_rec(1)) 
  show ?case unfolding sumlist_is distrib 
    using Cons.hyps[OF ih]
    by auto
qed

(* This may be somewhere in the libraries *)
lemma smult_in_lattice_of:
  fixes lattice_basis :: "('a::comm_ring_1) vec list"
  assumes "\<And>w. List.member lattice_basis w \<Longrightarrow> dim_vec w = n"
  fixes init_vec :: "('a::comm_ring_1) vec"
  fixes k :: "'a::comm_ring_1"
  assumes "init_vec \<in> lattice_of lattice_basis"
  shows "k \<cdot>\<^sub>v init_vec \<in> lattice_of ((map ((\<cdot>\<^sub>v) k) lattice_basis))"
proof -
  have dims: "\<And>w. List.member (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v lattice_basis ! i)
       [0..<length lattice_basis]) w \<Longrightarrow> dim_vec w = n" for c
    using assms(1)
    by (smt (verit) List.member_def in_set_conv_nth index_smult_vec(2) length_map map_nth map_nth_eq_conv) 
  obtain c where "init_vec = sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v lattice_basis ! i)
           [0..<length lattice_basis])"
    using vec_module.in_latticeE[OF assms(2)]  by blast
  then have "k \<cdot>\<^sub>v init_vec = k \<cdot>\<^sub>v sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v lattice_basis ! i)
           [0..<length lattice_basis])"
    by blast
  moreover have "\<dots> =   sumlist (map (\<lambda>i. k \<cdot>\<^sub>v i) ((map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v lattice_basis ! i)
           [0..<length lattice_basis])))"
    using sumlist_distrib dims
    by blast
  moreover have "\<dots> =  sumlist (map (\<lambda>i. k \<cdot>\<^sub>v (of_int (c i) \<cdot>\<^sub>v lattice_basis ! i))
           [0..<length lattice_basis])"
    by (smt (verit, best) in_set_conv_nth length_map length_upt map_eq_conv map_upt_len_conv nth_map)
  moreover have k_is: "\<dots> = sumlist (map (\<lambda>i. k \<cdot>\<^sub>v (of_int (c i) \<cdot>\<^sub>v lattice_basis ! i))
           [0..<length lattice_basis])"
    by argo
  ultimately have k_is: "k \<cdot>\<^sub>v init_vec = sumlist (map (\<lambda>i. (of_int (c i) \<cdot>\<^sub>v (k \<cdot>\<^sub>v lattice_basis ! i)))
           [0..<length lattice_basis])"
    by (simp add: mult_ac(2) smult_smult_assoc)
  then have "k \<cdot>\<^sub>v init_vec =
    sumlist
     (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v
               map ((\<cdot>\<^sub>v) k) lattice_basis ! i)
       [0..<length lattice_basis])"
    by (smt (verit, del_insts) length_map map_nth map_nth_eq_conv)
  then have mult_vec_is: "k \<cdot>\<^sub>v init_vec =
    sumlist
     (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v
               map ((\<cdot>\<^sub>v) k) lattice_basis ! i)
       [0..<length (map ((\<cdot>\<^sub>v) k) lattice_basis)])"
    by auto
  then show ?thesis
    using assms in_latticeI[OF mult_vec_is]
    by blast
  qed

end

lemma filter_distinct_sorted:
  fixes l :: "('a::linorder) list"
  fixes A :: "'a set"
  defines "P \<equiv> (\<lambda>x. x \<in> A)"
  defines "n \<equiv> length l"
  assumes "sorted l"
  assumes "distinct l"
  assumes "A \<subseteq> set l"
  shows "filter P l = sorted_list_of_set A"
  using assms
proof(induct l arbitrary: n A P)
  case Nil
  thus ?case by force
next
  case (Cons a l')
  define A' where "A' \<equiv> A - {a}"
  define n' where "n' \<equiv> length l'"
  define P' where "P' \<equiv> (\<lambda>x. x \<in> A')"
  define l where "l \<equiv> Cons a l'"
  define P where "P \<equiv> (\<lambda>x. x \<in> A)"
  have 1: "sorted l'" using Cons(2) by simp
  have 2: "distinct l'" using Cons(3) by simp
  have 3: "A' \<subseteq> set l'" using A'_def Cons(4) by auto
  have ih: "filter P' l' = sorted_list_of_set A'" using Cons.hyps(1)[OF 1 2 3] unfolding P'_def .

  have ?case if "a \<notin> A"
  proof-
    have "filter P l = filter P' l'"
      unfolding l_def filter.simps(2) P_def P'_def A'_def using that by auto
    moreover have "A' = A" using that unfolding A'_def by blast
    ultimately show ?thesis unfolding l_def P_def using ih by argo
  qed
  moreover have ?case if "a \<in> A"
  proof-
    have "\<forall>x \<in> set l'. P x = P' x" using Cons(3) unfolding P_def P'_def A'_def by fastforce
    hence *: "filter P l = a # (filter P' l')"
      using that filter_cong[of l' l' P P']
      unfolding l_def filter.simps(2) P_def P'_def A'_def
      by presburger
    have 1: "finite A" using Cons(4) finite_subset by blast
    have 2: "A \<noteq> {}" using that by blast
    hence a: "a = Min A"
      using sorted_Cons_Min[OF Cons.prems(1)]
      by (metis 1 Cons(4) Lattices_Big.linorder_class.Min.boundedE List.list.simps(15) Min_antimono Min_eqI finite_set that)
    show ?thesis
      using sorted_list_of_set_nonempty[OF 1 2] ih * unfolding a A'_def P_def P'_def l_def by argo
  qed
  ultimately show ?case by blast
qed


lemma filter_or:
  fixes n a b
  fixes l :: "nat list"
  defines "l \<equiv> [0..<n]"
  defines "P \<equiv> (\<lambda>x. x = a \<or> x = b)"
  assumes "a < b"
  assumes "b < length l"
  shows "filter P l = [a, b]"
proof-
  have 1: "sorted l" using l_def sorted_upt by blast
  have 2: "distinct l" using distinct_upt l_def by blast
  have 3: "{a, b} \<subseteq> set l" using assms(3,4) l_def length_upt by auto
  have P: "P = (\<lambda>x. x \<in> {a, b})" unfolding P_def by simp
  have *: "sorted_list_of_set {a, b} = [a, b]"
    using sorted_list_of_set.idem_if_sorted_distinct[of "[a,b]"] assms(3) by force
  show ?thesis using filter_distinct_sorted[OF 1 2 3] unfolding P * .
qed

subsection "Casting lemmas"

lemma int_rat_real_casting_helper:
  assumes "a = rat_of_int b"
  shows "real_of_rat a = real_of_int b"
  using assms by simp

(* NOTE: This is not true if just one of w1 and w2 is an integer *)
lemma casting_expansion_aux:
  shows "int_of_rat (rat_of_int w1 + rat_of_int w2) = w1 + w2"
proof - 
  have "rat_of_int w1 + rat_of_int w2 = rat_of_int (w1+w2)"
    by auto
  then show ?thesis
    using int_of_rat by algebra
qed

(* NOTE: The strong assumptions are necessary *)
lemma casting_expansion:
  assumes "dim_vec w1 = dim_vec w2"
  assumes "\<exists>w2_vec. w2 = map_vec rat_of_int w2_vec"
  shows "map_vec int_of_rat ((map_vec rat_of_int w1) + w2) = 
    map_vec int_of_rat (map_vec rat_of_int w1) + (map_vec int_of_rat w2)"
proof -
  have "vec (dim_vec w1)
     (\<lambda>i. int_of_rat
           ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ i)) $ idx =
    (vec (dim_vec w1)
     (\<lambda>i. int_of_rat (vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) $ i)) +
    vec (dim_vec w2) (\<lambda>i. int_of_rat (w2 $ i))) $ idx" if idx_lt: "idx < dim_vec w1" for idx
  proof - 
    have "vec (dim_vec w1)
     (\<lambda>i. int_of_rat
           ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ i)) $ idx =
     int_of_rat ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ idx)"
      using idx_lt by simp
    have "vec (dim_vec w1)
     (\<lambda>i. int_of_rat
           ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ i)) $
    idx = int_of_rat ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ idx)"
      using idx_lt by simp
    then have  "vec (dim_vec w1)
     (\<lambda>i. int_of_rat
           ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ i)) $
    idx = int_of_rat (rat_of_int (w1 $ idx) + w2$idx)"
      using assms idx_lt by auto
    then have "vec (dim_vec w1)
     (\<lambda>i. int_of_rat ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ i)) $ idx 
     = int_of_rat (rat_of_int (w1 $ idx)) + int_of_rat (w2$idx)"
      using assms(1) assms(2) casting_expansion_aux idx_lt by force
    then show ?thesis using assms 
      using idx_lt by fastforce
  qed
  then have "vec (dim_vec w1)
     (\<lambda>i. int_of_rat
           ((vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) + w2) $ i)) =
    vec (dim_vec w1)
     (\<lambda>i. int_of_rat (vec (dim_vec w1) (\<lambda>i. rat_of_int (w1 $ i)) $ i)) +
    vec (dim_vec w2) (\<lambda>i. int_of_rat (w2 $ i))"
    using assms by auto
  then show ?thesis using assms
    unfolding map_vec_def 
    by auto
qed

lemma casting_sum_aux:
  assumes "dim_vec k1 = dim_vec k2"
  shows "(map_vec rat_of_int k1) + (map_vec rat_of_int k2) = 
    map_vec rat_of_int (k1 + k2)"
  using assms
proof (induct k1 arbitrary: k2)
  case vNil
  then show ?case by auto
next
  case (vCons h1 T1)
  then obtain h2 T2 where k2_is: "k2 = vCons h2 T2"
    by (metis Nat.nat.simps(3) dim_vec dim_vec_vCons vec_cases)
  then have "map_vec rat_of_int T1 + map_vec rat_of_int T2 = map_vec rat_of_int (T1 + T2)"
    using vCons
    by auto
  then show ?case
    unfolding k2_is using vCons(2) k2_is by auto
qed

lemma casting_sum_lemma:
  assumes "\<And>mem. List.member w mem \<Longrightarrow> dim_vec mem = n"
  assumes "\<And>mem. List.member w mem \<Longrightarrow> 
      (\<exists>k::int vec. map_vec rat_of_int k = mem)"
  shows "(\<exists>k::int vec. (abelian_monoid.sumlist (module_vec TYPE(rat) n) w) = map_vec rat_of_int k)"
  using assms
proof (induct w)
  interpret vec_space "TYPE(rat)" n .
  case Nil
  then show ?case by (metis Matrix.of_int_hom.vec_hom_zero sumlist_Nil) 
next
  interpret vec_space "TYPE(rat)" n .
  case (Cons a w)
  then obtain k1 where k1_prop: "a = map_vec rat_of_int k1"
    by (metis member_rec(1))
  then obtain k2 where "sumlist w = map_vec rat_of_int k2"
    using Cons 
    by (meson member_rec(1))
  then have sumlist_is: "sumlist (a # w) = (map_vec rat_of_int k1) + (map_vec rat_of_int k2)"
    using k1_prop sumlist_Cons by presburger
  then have "sumlist (a # w) = (map_vec rat_of_int (k1 + k2))"
    using Cons(2) using casting_sum_aux
    by (metis List.member_def dim_sumlist index_add_vec(2) index_map_vec(2) k1_prop member_rec(1))
  then show ?case
    by blast
qed

(* The strong assumptions are needed here *)
lemma casting_lattice_aux:
  assumes "\<exists>k::int vec. map_vec rat_of_int k = v"
  assumes "map_vec int_of_rat v =
    map_vec int_of_rat (abelian_monoid.sumlist (module_vec TYPE(rat) n) w)"
  assumes "\<And>mem. List.member w mem \<Longrightarrow> 
      (\<exists>k::int vec. map_vec rat_of_int k = mem)"
  assumes "\<And>mem. List.member w mem \<Longrightarrow> dim_vec mem = n"
  shows "map_vec int_of_rat v =
    abelian_monoid.sumlist (module_vec TYPE(int) n)
     (map (map_vec int_of_rat) w)"
proof -
  interpret vec_space "TYPE(rat)" n .
  interpret vec_int: vec_module "TYPE(int)" n .
  obtain k :: "int vec" where k_prop: "v = map_vec rat_of_int k"
    using assms by auto
  then have map_k: "map_vec int_of_rat (map_vec rat_of_int k) =
    map_vec int_of_rat (sumlist w)"
    using assms(2) 
    by auto

  have "map_vec int_of_rat (sumlist w) = vec_int.M.sumlist (map (map_vec int_of_rat) w)"
    using assms(3) assms(4)
  proof (induct w)
    case Nil
    then show ?case
      unfolding sumlist_def local.vec_int.M.sumlist_def
      by auto
  next
    case (Cons a w)
    have " foldr (+) (map (map_vec int_of_rat) (a # w)) (0\<^sub>v n) = 
      (map_vec int_of_rat a) + (foldr (+) (map (map_vec int_of_rat) w) (0\<^sub>v n))"
      by simp
    then have h1: "foldr (+) (map (map_vec int_of_rat) (a # w)) (0\<^sub>v n) = 
      (map_vec int_of_rat a) + map_vec int_of_rat (sumlist w)"
      using Cons unfolding sumlist_def vec_int.M.sumlist_def
      by (simp add: member_rec(1))

    obtain k :: "int vec" where k_prop: "map_vec rat_of_int k = a"
      using Cons(2) 
      by (meson member_rec(1))

    then have dim_vec_k: "dim_vec k = dim_vec a"
      by auto
    then have "dim_vec k = n"
      by (simp add: Cons(3) member_rec(1))

    have "\<exists>w2_vec. foldr (+) w (0\<^sub>v n) = map_vec rat_of_int w2_vec"
      using Cons(2) casting_sum_lemma 
      by (metis Cons(3) member_rec(1) sumlist_def)

    then have expand: "map_vec int_of_rat ((map_vec rat_of_int k) + foldr (+) w (0\<^sub>v n)) = 
    map_vec int_of_rat (map_vec rat_of_int k) + map_vec int_of_rat (foldr (+) w (0\<^sub>v n))"
      using casting_expansion[of k "foldr (+) w (0\<^sub>v n)"]  dim_vec_k
      by (metis List.member_def \<open>dim_vec k = n\<close> dim_sumlist index_add_vec(2) local.Cons.prems(2) sumlist_Cons sumlist_def)

    have "map_vec int_of_rat (foldr (+) (a # w) (0\<^sub>v n)) = 
       map_vec int_of_rat (a + foldr (+) w (0\<^sub>v n))"
      by simp
    then have "map_vec int_of_rat (foldr (+) (a # w) (0\<^sub>v n)) =  map_vec int_of_rat ((map_vec rat_of_int k) + foldr (+) w (0\<^sub>v n))"
      using k_prop by auto

    then have "map_vec int_of_rat (foldr (+) (a # w) (0\<^sub>v n)) = 
      map_vec int_of_rat (map_vec rat_of_int k) + map_vec int_of_rat (sumlist w)"
      using Cons(2) k_prop expand 
      using sumlist_def by presburger
    then show ?case 
      using h1 k_prop
      unfolding sumlist_def vec_int.M.sumlist_def
      by argo
  qed

  then have "map_vec int_of_rat (map_vec rat_of_int k) =
    vec_int.M.sumlist
     (map (map_vec int_of_rat) w)"
    using map_k by argo
  then show ?thesis unfolding k_prop by blast
qed

lemma in_lattice_casting:
  assumes "\<And>mem. List.member qs mem \<Longrightarrow> (\<exists>k::int vec. map_vec rat_of_int k = mem)"
  assumes "(\<And>mem. List.member qs mem \<Longrightarrow> dim_vec mem = n)"
  assumes "v \<in> vec_module.lattice_of n qs"
  shows "\<exists>k. map_vec rat_of_int k = v"
proof - 
  let ?sumlist = "abelian_monoid.sumlist (module_vec TYPE(rat) n)"
  obtain c where v_is: "v = ?sumlist (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length qs])"
    using assms(3) unfolding vec_module.lattice_of_def by blast
  let ?w = "map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length qs]"
  have dims: "(\<And>mem. List.member ?w mem \<Longrightarrow> dim_vec mem = n)"
    using assms(2) 
    by (smt (verit, del_insts) List.member_def in_set_conv_nth index_smult_vec(2) length_map map_nth map_nth_eq_conv)
  have mem_w: "\<exists>k. map_vec rat_of_int k = mem"
    if mem_is: "List.member (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length qs]) mem" for mem
  proof - 
    obtain i where "i < length qs" "mem = rat_of_int (c i) \<cdot>\<^sub>v qs ! i"
      using mem_is 
      by (smt (verit) List.member_def add_0 in_set_conv_nth length_map map_nth map_nth_eq_conv nth_upt)
    then show ?thesis using assms(1) mem_is 
      by (metis Matrix.of_int_hom.vec_hom_smult in_set_conv_nth in_set_member)
  qed
  then obtain k where "v = map_vec rat_of_int k"
    unfolding v_is
    using casting_sum_lemma[of ?w, OF dims _ ]
    by blast
  then show ?thesis
    by auto
qed

lemma casting_lattice_lemma_aux2: 
  assumes "\<And>mem. List.member qs mem \<Longrightarrow> 
      (\<exists>k::int vec. map_vec rat_of_int k = mem)"
  shows  "(map (map_vec int_of_rat) (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i)
         [0..<length qs])) =
     (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v map (map_vec int_of_rat) qs ! i) [0..<length qs])"
proof - 
  have "((map_vec int_of_rat) (rat_of_int (c i) \<cdot>\<^sub>v qs ! i))  = 
    of_int (c i) \<cdot>\<^sub>v (map_vec int_of_rat) (qs ! i)" if i_lt: "i < length qs" for i
  proof - 
    obtain k :: "int vec" where qs_i_is: "qs ! i = map_vec rat_of_int k"
      using assms i_lt 
      by (metis List.member_def in_set_conv_nth)
    have "map_vec rat_of_int ((c i) \<cdot>\<^sub>v k) = (rat_of_int (c i) \<cdot>\<^sub>v qs ! i)"
      using qs_i_is by force
    then have lhs_is: "(map_vec int_of_rat (rat_of_int (c i) \<cdot>\<^sub>v qs ! i)) = 
      (c i) \<cdot>\<^sub>v k"
      using qs_i_is 
      by (metis eq_vecI index_map_vec(1) index_map_vec(2) int_of_rat(1))
    have "map_vec int_of_rat (map_vec rat_of_int k) = k"
      by force
    then have rhs_is: "of_int (c i) \<cdot>\<^sub>v map_vec int_of_rat (qs ! i) = (c i) \<cdot>\<^sub>v k"
      unfolding qs_i_is by simp
    then show ?thesis using lhs_is rhs_is by argo
  qed
  then show ?thesis by auto
qed

(* This holds, but note that the assumptions are strong.  *)
lemma casting_lattice_lemma:
  fixes v :: "rat vec"
  fixes qs :: "rat vec list"
  assumes "\<exists>k::int vec. map_vec rat_of_int k =  v"
  assumes "\<And>mem. List.member qs mem \<Longrightarrow> 
      (\<exists>k::int vec. map_vec rat_of_int k = mem)"
  assumes dim_vecs: "\<And>mem. List.member qs mem \<Longrightarrow> dim_vec mem = n"
  assumes "v \<in> vec_module.lattice_of n qs"
  shows "map_vec int_of_rat v
    \<in> vec_module.lattice_of n (map (map_vec int_of_rat) qs)"
proof - 
  let ?sumlist = "abelian_monoid.sumlist (module_vec TYPE(rat) n)"
  let ?int_sumlist = "abelian_monoid.sumlist (module_vec TYPE(int) n)"
  obtain c :: "nat \<Rightarrow> int" where "v = ?sumlist (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length qs])"
    using assms unfolding vec_module.lattice_of_def by blast
  then have map_is: "map_vec int_of_rat v
      = map_vec int_of_rat (?sumlist (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length qs]))"
    by blast
  have length_qs: "length qs = length (map (map_vec int_of_rat) qs)"
    by simp
  then have map_vec_v: "map_vec int_of_rat v
      = map_vec int_of_rat
        (?sumlist (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length (map (map_vec int_of_rat) qs)]))"
    using map_is by argo

  let ?w = "(?sumlist (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length (map (map_vec int_of_rat) qs)]))"

  have dim_vecs: "(\<And>mem. List.member
             (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i)
               [0..<length (map (map_vec int_of_rat) qs)])
             mem \<Longrightarrow>
            dim_vec mem = n)"
    using dim_vecs 
    by (smt (verit, ccfv_threshold) List.member_def in_set_conv_nth index_smult_vec(2) length_map map_nth map_nth_eq_conv)

  have casting_mem: "\<exists>k. map_vec rat_of_int k = mem" if mem_assm: "List.member
             (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i)
               [0..<length (map (map_vec int_of_rat) qs)]) mem" for mem
  proof - 
    obtain i where i_prop: "mem = rat_of_int (c i) \<cdot>\<^sub>v qs ! i" 
                   "i < length (map (map_vec int_of_rat) qs)"
      using mem_assm 
      by (smt (verit, ccfv_SIG) List.member_def arith_simps(49) in_set_conv_nth length_map map_nth map_nth_eq_conv nth_upt)
    obtain k1 where "map_vec rat_of_int k1 = qs ! i"
      using i_prop(2) assms(2) 
      by (metis List.member_def \<open>length qs = length (map (map_vec int_of_rat) qs)\<close> in_set_conv_nth)
    then show ?thesis using i_prop(1) 
      by (metis Matrix.of_int_hom.vec_hom_smult)
  qed
  have map_vec_v: "map_vec int_of_rat v =
   (?int_sumlist
     (map (map_vec int_of_rat) (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v qs ! i) [0..<length (map (map_vec int_of_rat) qs)])))"
    using casting_lattice_aux[OF assms(1) map_vec_v casting_mem dim_vecs]
    by blast
  have "map_vec int_of_rat v = ?int_sumlist
              (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v map (map_vec int_of_rat) qs ! i)
                [0..<length (map (map_vec int_of_rat) qs)])"
    unfolding map_vec_v using casting_lattice_lemma_aux2 length_qs
    by (metis (no_types, lifting) assms(2))
  then show ?thesis unfolding vec_module.lattice_of_def by blast
qed 

section "HNP adversary locale"

locale hnp_adversary =
  fixes d p :: nat
begin

type_synonym adversary = "(nat \<times> nat) list \<Rightarrow> nat"

definition int_gen_basis :: "nat list \<Rightarrow> int vec list" where
  "int_gen_basis ts = map (\<lambda>i.  (p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d]  
                  @ [vec_of_list ((map (\<lambda>x. (of_nat p) * x) ts) @ [1])]" 

fun int_to_nat_residue :: "int \<Rightarrow> nat \<Rightarrow> nat"
  where "int_to_nat_residue I modulus = nat (I mod modulus)"

definition ts_from_pairs :: "(nat \<times> nat) list \<Rightarrow> nat list" where
  "ts_from_pairs pairs = map fst pairs"

definition scaled_uvec_from_pairs :: "(nat \<times> nat) list \<Rightarrow> int vec" where
  "scaled_uvec_from_pairs pairs = vec_of_list ((map (\<lambda>(a,b). p*b) pairs) @ [0])"

fun \<A>_vec :: "(nat \<times> nat) list \<Rightarrow> int vec" where
  "\<A>_vec pairs = (full_babai 
                    (int_gen_basis (ts_from_pairs pairs)) 
                    (map_vec rat_of_int (scaled_uvec_from_pairs pairs)) 
                    (4/3))"

fun \<A> :: adversary where 
  "\<A> pairs =  int_to_nat_residue ((\<A>_vec pairs)$d) p"

end

section "HNP locales"

subsubsection "Arithmetic locale"

locale hnp_arith = 
  fixes n \<alpha> d p k :: nat
  assumes p: "prime p"
  assumes \<alpha>: "\<alpha> \<in> {1..<p}"
  assumes d: "d =  2 * ceiling (sqrt n)"
  assumes n: "n = ceiling (log 2 p)"
  assumes k: "k = ceiling (sqrt n) + ceiling (log 2 n)"
  assumes n_big: "961 < n"
begin

definition \<mu> :: nat where
  "\<mu> \<equiv> nat (ceiling (1/2 * (sqrt n)) + 3)"

lemma \<mu>: "\<mu> = (ceiling (1/2 * (sqrt n)) + 3)"
proof-
  have "ceiling (1/2 * (sqrt n)) + 3 \<ge> 0"
  proof-
    have "sqrt n \<ge> 0" by auto
    thus ?thesis by linarith
  qed
  thus ?thesis unfolding \<mu>_def by presburger
qed

lemma int_p_prime: "prime (int p)" by (simp add: p)

lemma p_geq_2: "p \<ge> 2" using p prime_ge_2_nat by blast

lemma n_geq_1: "n \<ge> 1"
proof-
  have "log 2 p > 0"
    by (smt (verit) p less_imp_of_nat_less of_nat_1 prime_gt_1_nat zero_less_log_cancel_iff)
  thus ?thesis using n by linarith
qed

lemma \<mu>_le_k:
  shows "\<mu> + 1 \<le> k"
proof-
  have "144 \<le> n" using n_big by simp
  then have "sqrt(144) \<le> sqrt n" using numeral_le_real_of_nat_iff real_sqrt_le_iff by blast 
  then have "4 + sqrt (n) / 2 \<le> (sqrt n) - 2" by auto
  then have "ceiling(sqrt (n) / 2) + 3 \<le> ceiling (sqrt n) - 1" by linarith
  moreover have "0 \<le> log 2 (n)" using n_big by auto
  ultimately show ?thesis using \<mu> k by linarith
qed

lemma k_plus_1_lt:
  shows "k + 1 < log 2 p"
proof - 
  obtain r::real where r_eq: "r = log 2 (real p)" "r \<le> n" "r > n-1"
    by (smt (verit, best) n Multiseries_Expansion.intyness_simps(1) add_diff_inverse_nat linorder_not_less n_geq_1 nat_ceiling_le_eq nat_int of_nat_less_iff of_nat_simps(2))

  then have p_eq: "p = 2 powr r"
    using n log_powr_cancel[of 2 r]
    by (simp add: p prime_gt_0_nat) 

  then have p_gt: "p > n"
    using n n_big
    by (smt (verit, del_insts) One_nat_def Suc_pred r_eq(1,3) le_neq_implies_less le_simps(3) less_exp log2_of_power_le nat_le_real_less p prime_gt_0_nat)
    
  have "real n = \<lceil>log 2 (real p)\<rceil>"
    using n by linarith
  then have "int k = \<lceil>sqrt \<lceil>log 2 (real p)\<rceil>\<rceil> + \<lceil>log 2 \<lceil>log 2 (real p)\<rceil>\<rceil>"
    using k by auto
  then have k_plus_1_eq: "k + 1 = \<lceil>sqrt \<lceil>log 2 (real p)\<rceil>\<rceil> + \<lceil>log 2 \<lceil>log 2 (real p)\<rceil>\<rceil> + 1"
    by linarith
  let ?logp = "\<lceil>log 2 (real p)\<rceil>"
  have log_p_bound: "?logp > 100"
    using p_gt n_big p_eq r_eq
    by linarith

  have geq: "(log 2 (real p)) / 2 > (\<lceil>log 2 (real p)\<rceil> - 1) / 2"
    using log_p_bound 
    by (smt (verit) divide_strict_right_mono less_ceiling_iff)
  have arb: "real_of_int \<lceil>sqrt (real_of_int a)\<rceil>
    < real_of_int (a - 1) / 2" if a_gt: "a > 100"
    for a::int
    using a_gt 
  proof - 
    have eq: "(a - 3) / 2 = (a - 1) / 2 - 1"
      using a_gt by auto
    have "10*a < a*a"
      using a_gt by simp
    then have "10*a < a^2"
      by (simp add: power2_eq_square)
    then have "10*a < a^2 + 9"
      by auto
    then have "4*a < a^2 - 6*a + 9"
      by simp
    then have "4*a < (a - 3)^2"
      using a_gt power2_sum[of a "-3"] by simp
    then have "sqrt (4*a) < sqrt ((a - 3)^2)"
      using real_sqrt_less_iff by presburger
    then have "sqrt (4*a) < a - 3"
      using a_gt by simp
    then have "2*(sqrt a) < a - 3"
      by (simp add: real_sqrt_mult)
    then have "sqrt a < (a - 3) / 2"
      by simp
    then have "sqrt a < (a - 1) / 2 - 1"
      using eq
      by algebra
    then have "sqrt (real_of_int a) + 1
    < real_of_int (a - 1) / 2"
      using a_gt by argo
    then show ?thesis
      by linarith
  qed
  then have "real_of_int \<lceil>sqrt (real_of_int \<lceil>log 2 (real p)\<rceil>)\<rceil>
    < (\<lceil>log 2 (real p)\<rceil> - 1) / 2"
    using arb[OF log_p_bound]
    by blast
  then have ineq1: "\<lceil>sqrt (real_of_int ?logp)\<rceil> < (log 2 (real p))/2"
    using geq by linarith

  have ineq2: "\<lceil>log 2 (real_of_int ?logp)\<rceil> + 1 \<le> (log 2 (real p))/2"
  proof - 
    have " 99 < log 2 (real p)"
      using log_p_bound by simp
    then have p_gt: "2^99 < p"
      by (metis Nat.bot_nat_0.extremum le_trans linorder_not_le log2_of_power_le of_nat_numeral p_gt)
    obtain q::nat where q_prop: "2^q \<le> p \<and> 2^(q+1) > p"
      using ex_power_ivl1 le_refl p prime_ge_1_nat by presburger
    then have q_geq: "q \<ge> 99" using p_gt 
      by (smt (verit) less_log2_of_power log2_of_power_less nat_le_real_less numeral_plus_one of_nat_add of_nat_numeral p prime_gt_0_nat)
    have leq_q: "\<lceil>log 2 (real p)\<rceil> \<le> q+1"
      using q_prop 
      by (metis ceiling_mono ceiling_of_nat less_le log2_of_power_le p prime_gt_0_nat)

    have arith_help: "98 < q \<Longrightarrow> 32 * q + 48 < 2 ^ q" for q
    proof (induct q)
      case 0
      then show ?case by auto
    next
      case (Suc q)
      {assume *:  "99 = Suc q"
        then have ?case
          by simp
      } moreover {assume *:  "99 < Suc q"
        then have "32 * q + 48 < 2 ^ q"
          using Suc by linarith
        then have ?case
          using Suc by auto
      }
      ultimately show ?case
        using Suc by linarith
    qed
    have "(q+1)^2*16 < 2^q"
      using q_geq
    proof (induct q)
      case 0
      then show ?case by auto
    next
      case (Suc q)
      { assume *: "99 = Suc q"
        then have ?case
          by simp
      }
      moreover {
        assume *: "99 < Suc q"
        then have q_plus: "(q + 1)\<^sup>2 * 16 < 2 ^ q"
          using Suc by auto
        have "(Suc q + 1)\<^sup>2 = q^2 + 4*q + 4"
          by (smt (verit) Groups.ab_semigroup_add_class.add.commute Groups.semigroup_add_class.add.assoc nat_1_add_1 numeral_Bit0_eq_double plus_1_eq_Suc power2_eq_square power2_sum)
        then have "(Suc q + 1)\<^sup>2 = (q+1)^2 + 2*q + 3"
          by (metis (no_types, lifting) add_2_eq_Suc' add_Suc_right more_arith_simps(6) mult_2 numeral_Bit1 numeral_One one_power2 plus_1_eq_Suc power2_sum semiring_norm(163))
        then have suc_q: "(Suc q + 1)\<^sup>2 * 16  = 16*(q+1)^2 + 32*q + 3*16"
          by simp
         have "32*q + 48 < 2^q"
           using * arith_help by auto
        then have "16*(q+1)^2 + 32*q + 3*16 < 2 * 2^q"
          using q_plus by linarith
        then have "(Suc q + 1)\<^sup>2 * 16 < 2 * 2^q"
          using suc_q by argo
        then have ?case
          by auto
      }
      ultimately show ?case 
        using Suc by linarith
    qed
    then have "(real_of_int (q+1)) powr 2*16 \<le> 2^q"
    proof -
      have "0 < q + 1"
        by simp
      then have "real_of_int (int (q + 1)) powr real_of_int (int 2) * real_of_int (int 16) \<le> real_of_int (int 2) ^ q"
        by (metis (no_types) Power.semiring_1_class.of_nat_power \<open>(q + 1)\<^sup>2 * 16 < 2 ^ q\<close> less_le of_int_of_nat_eq of_nat_0_less_iff of_nat_less_numeral_power_cancel_iff of_nat_numeral of_nat_simps(5) powr_realpow)
      then show ?thesis
        by simp
    qed
    then have "(real_of_int (q+1)) powr 2*16 \<le> (real p)"
      using q_prop 
      using numeral_power_le_of_nat_cancel_iff order_trans_rules(23) by blast
    then have "(real_of_int ?logp) powr 2*16 \<le> (real p)"
      using leq_q 
      by (smt (verit) ceiling_le_iff p powr_less_mono2 prime_ge_1_nat real_of_nat_ge_one_iff zero_le_log_cancel_iff)
    then have "(2 powr (log 2 (real_of_int ?logp))) powr 2*16 \<le> (real p)"
      using log_p_bound by fastforce
    then have "2 powr (log 2 (real_of_int ?logp)*2)*16 \<le> (real p)"
      using powr_powr[of 2] by auto
    then have "2 powr (2*log 2 (real_of_int ?logp))*16 \<le> (real p)"
      by argo
    then have "2 powr (2*log 2 (real_of_int ?logp) + 4) \<le> (real p)"
      by (simp add: powr_add)
    then have "2*log 2 (real_of_int ?logp) + 4 \<le> (log 2 (real p))"
      using le_log_iff p_gt by auto
    then show ?thesis using log_p_bound
      by (smt (verit, ccfv_threshold) ceiling_add_one field_sum_of_halves of_int_ceiling_le_add_one)
  qed

  have "\<lceil>sqrt (real_of_int \<lceil>log 2 (real p)\<rceil>)\<rceil> + \<lceil>log 2 (real_of_int \<lceil>log 2 (real p)\<rceil>)\<rceil> + 1
      < log 2 (real p)"
    using ineq1 ineq2 by linarith
  then show ?thesis using k_plus_1_eq by linarith
qed

lemma p_k_le_p_mu:
  shows "p/(2^k)\<le>p/(2^(\<mu> + 1))"
proof-
  have "real(2) ^ (\<mu> + 1) \<le> 2^k" using \<mu>_le_k power_increasing[of "\<mu> + 1" k "real 2"] by force
  then show ?thesis using divide_left_mono[of "real(2) ^ (\<mu> + 1)" "2^k" p] by simp
qed

lemma k_geq_1: "k \<ge> 1" using n_geq_1 k \<mu>_le_k by linarith

lemma final_ineq:
   "(((4::real)/3) powr ((d + 1)/2) * (11/10) * (d + 1) * (p / (2 powr (real k - 1)))
    < p / (2 powr \<mu>))"
proof-
  let ?crn = "ceiling (sqrt n)"
  let ?chrn = "ceiling (1/2 * sqrt n)"
  have "31^2 < n" using n_big
    by simp
  then have sn: "31 < sqrt n" using real_less_rsqrt by auto
  have pos1: "0 \<le> (2 * 3 / 4 * 2 powr (- 1 / 2)) powr real_of_int \<lceil>sqrt (real n)\<rceil>" by auto
  have pos2: "0 < 2 powr ?crn" using sn by simp
  have pos3: "0 < (3/4) powr ?crn " by simp
  have "(2::real) powr (- 1 / 2) = 1/(2 powr (1/2))"
    using powr_minus[of "2::real" "1/2"]
    by (simp add: powr_minus_divide)
  then have powr_2_is: "2 powr (- 1 / 2) = 1 / (sqrt 2)"
    by (metis powr_half_sqrt rel_simps(27))
  have "(2* sqrt 2)^2 < 3^2"
    by simp
  then have "2* sqrt 2 < 3"
    using real_less_rsqrt by fastforce
  then have gt_1: "3/2 * 1 / (sqrt 2) > 1"
    by simp
  have one_half: "(1/sqrt 2) powr 2 = 1/2"
    by (smt (verit, best) eq_divide_eq powr_2_is powr_half_sqrt_powr powr_powr real_sqrt_divide real_sqrt_eq_iff real_sqrt_one)
  have three_halves: "((3::real)/2) ^ 2 = (9/4::real)"
    using power_divide[of "3::real" 2 2] by simp
  have "((3::real)/2 * 1 / (sqrt 2)) powr 2 = (3/2) ^ 2 * ((1/sqrt 2) powr 2)"
    using powr_mult[of "3/2" "1 / (sqrt 2)"]
    by auto
  then have mult: "((3::real)/2 * 1 / (sqrt 2)) powr 2 = 9/8"
    by (simp add: one_half three_halves) 
  have "(5::real) < (9^15/8^15)"
    by auto
  then have "(5::real) < (9/8) ^ 15"
    by (metis power_divide)
  then have "(5::real) < (9/8) powr 15"
    by simp
  then have "(5::real) < ((3/2 * 1 / (sqrt 2)) powr 2) powr 15"
    using mult by presburger
  then have "(5::real) < (3/2 * 1 / (sqrt 2)) powr 30"
    by auto
  then have "(5::real) < (3/2 * 1 / (sqrt 2)) powr 31"
    using gt_1 
    by (smt (verit) powr_less_cancel_iff)
  then have "(5::real) < (2 * 3/4 * 2 powr (- 1/2) ) powr 31"  (*Pure number calculation*)
    using powr_2_is by auto
  moreover have "(31::real) < ?crn" using sn by simp
  moreover have "1 < ((2::real) * 3/4 * 2 powr (- 1/2) )" 
    using gt_1 powr_2_is by linarith (*Pure number calculation*)
  ultimately have 1: "(5::real) < (2 * 3/4 * 2 powr (- 1/2) ) powr ?crn" 
    using powr_less_mono[of 31 ?crn "((2::real) * 3/4 * 2 powr (- 1/2) )"] by linarith
  have mult_eq: "(32::real) * (11/10) * 3 / 5 = 1056/50"
    by simp
  have "((4::real)/3) * 1056^2 < 1550^2"
    by auto
  then have "((4::real)/3) powr (1/2) * 1056 < 1550"
    by (metis divide_nonneg_nonneg powr_half_sqrt real_sqrt_less_mono real_sqrt_mult real_sqrt_pow2 real_sqrt_power zero_le_numeral)
  then have "((4::real)/3) powr (1/2) * (32::real) * (11/10) * 3 / 5 < 31"
    using mult_eq by linarith (*Pure number calculation*)
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * 3 / 5 < sqrt n"
    using sn by simp
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * 3 < sqrt n * 5" by linarith
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * 3 < sqrt n * (2 * 3/4 * 2 powr (- 1/2) ) powr ?crn" 
    using 1 mult_strict_left_mono[of 5 "(2 * 3 / 4 * 2 powr (- 1 / 2)) powr real_of_int \<lceil>sqrt (real n)\<rceil>" "sqrt n"] by fastforce
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * 3 / sqrt n < (2 * 3/4 * 2 powr (- 1/2) ) powr ?crn"
    using sn divide_less_eq[of "(4 / 3) powr (1 / 2) * 32 * (11 / 10) * 3" "sqrt n" "(2 * 3 / 4 * 2 powr (- 1 / 2)) powr real_of_int \<lceil>sqrt (real n)\<rceil>"] by argo
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 / sqrt n) < (2 * 3/4 * 2 powr (- 1/2) ) powr ?crn" by auto
  moreover have "3 / sqrt n = 3 * sqrt n / n"
  proof-
    have "3 / sqrt n = 3 / (sqrt n) * (sqrt n / sqrt n)" using sn by force
    also have "\<dots> = 3 * sqrt n / (sqrt n * sqrt n)" using sn by argo
    finally show ?thesis by auto
  qed
  ultimately have "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n) < (2 * 3/4 * 2 powr (- 1/2) ) powr ?crn" by simp
  moreover have "(2 * 3/4 * 2 powr (- 1/2)) powr ?crn = (2 powr ?crn) * ((3/4) powr ?crn) * ((2 powr (- 1/2)) powr ?crn)"
    by (metis times_divide_eq_right powr_mult) (* Distribute power over product *)
  ultimately have "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n) < (2 powr ?crn) * ((3/4) powr ?crn) * ((2 powr (- 1/2)) powr ?crn)" by linarith
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n) < ((2 powr (- 1/2)) powr ?crn) * ( (3 /4 ) powr ?crn) * (2 powr ?crn)" by argo
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n) / (2 powr ?crn) < ((2 powr (- 1/2)) powr ?crn) * ( (3/4) powr ?crn)" 
    using pos2 pos_divide_less_eq[of "2 powr real_of_int \<lceil>sqrt (real n)\<rceil>" "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n)" "((2 powr (- 1/2)) powr ?crn) * ( (3 /4 ) powr ?crn)"] by linarith
  then have "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n) / (2 powr ?crn) / ( (3/4) powr ?crn) <  ((2 powr (- 1/2)) powr ?crn)"
    using pos3 pos_divide_less_eq[of "((3/4) powr ?crn)" "((4::real)/3) powr (1/2) * 32 * (11/10) * (3 * sqrt n / n) / (2 powr ?crn)" "((2 powr (- 1/2)) powr ?crn)"] by linarith
  then have main: "( ((4::real)/3) powr (1/2) / ( (3 /4 ) powr ?crn) ) * 
              (16 * 11/10) * 
              ( (2 * 3 * sqrt n / n) / (2 powr ?crn) )
            < ((2 powr (- 1/2)) powr ?crn)" by argo

  have k_ineq: "(d + 1) / (2 powr ( real k - 1 )) \<le> ( (2 * 3 * sqrt n / n) / (2 powr ?crn) )"
  proof-
    have "d \<le> 3 * sqrt n" using sn d by linarith
    have "n = 2 powr log 2 n"
      using n_geq_1 by auto
    moreover have "2 powr log 2 n \<le> 2 powr (ceiling (log 2 n))" by fastforce
    ultimately have "2 / (2 powr (ceiling (log 2 n) ) ) \<le> 2 / n"
      by (metis frac_le ge_refl powr_nonneg_iff verit_comp_simplify(7) verit_comp_simplify1(3) verit_eq_simplify(5))
    moreover have "( (2 * 3 * sqrt n / n) / (2 powr ?crn) ) =   3 * sqrt n * (2 / n / 2 powr ?crn)" by argo
    moreover have "0 \<le> 3 * sqrt n" using sn by linarith
    ultimately have *: " 3 * sqrt n * (2 / (2 powr (ceiling (log 2 n))) / 2 powr ?crn) \<le> (2 * 3 * sqrt n / n) / (2 powr ?crn)"
      using mult_left_mono[of "2 / (2 powr (ceiling (log 2 n) ) )" "2 / n" "3 * sqrt (real n)"] 
            divide_right_mono[of "3 * sqrt n * (2 / (2 powr (ceiling (log 2 n))))" "(2 * 3 * sqrt n / n)" "2 powr ?crn"]
            pos2 by simp
    have "2 / (2 powr (ceiling (log 2 n) ) ) = 2 powr ( 1 - ceiling (log 2 n))" using powr_diff[of 2 1 "ceiling (log 2 n)"] by fastforce
    then have "(2 / (2 powr (ceiling (log 2 n))) / 2 powr ?crn) = 2 powr (1 - ceiling (log 2 n) - ?crn)" 
      using powr_diff[of 2 "1 - ceiling (log 2 n)" "?crn"] by fastforce
    moreover have " - (1 - ceiling (log 2 n) - ?crn) = ?crn + ceiling (log 2 n) - 1" by fastforce
    ultimately have "(2 / (2 powr (ceiling (log 2 n))) / 2 powr ?crn) = 1 / (2 powr (?crn + ceiling (log 2 n) - 1))"
      by (smt (verit) of_int_minus powr_minus_divide)
    moreover have "real_of_int (?crn + ceiling (log 2 n) - 1) = real_of_int (?crn + ceiling (log 2 n)) - 1" by linarith
    ultimately have "(2 / (2 powr (ceiling (log 2 n))) / 2 powr ?crn) = 1 / (2 powr (real_of_int (int k) - 1))" 
      using k by presburger
    then have " 3 * sqrt n / (2 powr (real k - 1)) \<le> (2 * 3 * sqrt n / n) / (2 powr ?crn)" using * by force
    moreover have "(d + 1) \<le> 3 * sqrt n"
      using d sn by linarith
    moreover have "0 < 2 powr (k - 1)" by force
    ultimately show ?thesis
      using divide_right_mono[of "d + 1" "3 * sqrt n" "2 powr (real k - 1)"]
      by auto
  qed

  have "( ((4::real)/3) powr (1/2) / ( (3 /4 ) powr ?crn) ) = (4/3) powr ((d + 1) / 2)"
  proof-
    have inv: "1/((4::real)/3) = (3::real) / 4"
      by force
    have "(4 / 3) powr real_of_int (- \<lceil>sqrt (real n)\<rceil>) =  1 / (4 / 3) powr real_of_int \<lceil>sqrt (real n)\<rceil>"
      using powr_minus_divide[of "4/3" "?crn"] 
      by simp
    then have "(4 / 3) powr real_of_int (- \<lceil>sqrt (real n)\<rceil>) =  1 powr real_of_int \<lceil>sqrt (real n)\<rceil> / (4 / 3) powr real_of_int \<lceil>sqrt (real n)\<rceil>"
      by simp
    then have powr_minus_div: "(4 / 3) powr real_of_int (- \<lceil>sqrt (real n)\<rceil>) =  (1 / (4 / 3)) powr real_of_int \<lceil>sqrt (real n)\<rceil>"
      by (simp add: powr_divide)
    have "(3 /4) powr ?crn = (4/3) powr (- ?crn)" 
      unfolding powr_minus_div inv
      by auto (* Division negates exponent *)
    then have "((4::real)/3) powr (1/2) / ( (3 /4 ) powr ?crn) = ((4::real) / 3) powr (1/2 - (- ?crn))"
      using powr_diff[of "4/3" "1/2" "-?crn"] by algebra
    moreover have "1/2 - (- ?crn) = (d + 1)/2" using d by force
    ultimately show ?thesis by presburger
  qed
  then have " (4/3) powr ((d + 1) / 2) * 
              (16 * 11/10) * 
              ( (2 * 3 * sqrt n / n) / (2 powr ?crn) )
            < ((2 powr (- 1/2)) powr ?crn)" using main
    by presburger
  moreover have "0<(4/3) powr ((d + 1) / 2) * 
              (16 * 11/10)" by fastforce
  ultimately have "(4/3) powr ((d + 1) / 2) * (16 * 11/10) * (d + 1) / (2 powr ( real k - 1 )) < (2 powr (- 1/2)) powr ?crn"
    using mult_left_mono[of "real (d + 1) / 2 powr (real k - 1)" "2 * 3 * sqrt (real n) / real n / 2 powr real_of_int \<lceil>sqrt (real n)\<rceil>" "(4 / 3) powr (real (d + 1) / 2) * (16 * 11 / 10)"]
          k_ineq by argo
  then have "(4/3) powr ((d + 1) / 2)  * (11/10) * (d + 1) / (2 powr ( real k - 1 )) < (2 powr (- 1/2)) powr ?crn / 16" by linarith
  also have "\<dots> = 2 powr (- 1/2 * ?crn) / 16"
    by (simp add: powr_powr)
  also have "\<dots> = 2 powr (- 1/2 * ?crn - 4)"
    using powr_diff[of 2 "-1/2*?crn" "4"] by force
  also have "\<dots> \<le> 2 powr (-\<mu>)" using powr_mono[of  "- 1/2 * ?crn - 4" "-\<mu>" "2::real"] \<mu> by linarith
  also have "\<dots> = 1 / 2 powr (\<mu>)"
    by (simp add: powr_minus_divide)
  finally have "(4/3) powr ((d + 1) / 2)  * (11/10) * (d + 1) / (2 powr ( real k - 1 )) < 1 / 2 powr (\<mu>)"
    by meson
  then have "(4/3) powr ((d + 1) / 2)  * (11/10) * (d + 1) / (2 powr ( real k - 1 )) * p <  1 / 2 powr (\<mu>) * p"
    using p mult_strict_right_mono[of "(4/3) powr ((d + 1) / 2)  * (11/10) * (d + 1) / (2 powr ( real k - 1 ))" "1 / 2 powr (\<mu>)" p]
    by fastforce
  then show ?thesis
    by force
qed

end

subsection "Main HNP locale"

locale hnp = hnp_arith n \<alpha> d p k + hnp_adversary d p for n \<alpha> d p k + 
  fixes msb_p :: "nat \<Rightarrow> nat"
  assumes msb_p_dist: "\<And>x. \<bar>int x - int (msb_p x)\<bar> < p / (2^k)"
begin

subsection "Uniqueness lemma"

sublocale vec_space "TYPE(rat)" "d + 1" .

lemma sumlist_index_commute:
  fixes Lst :: "rat vec list"
  fixes i :: nat
  assumes "set Lst \<subseteq> carrier_vec (d + 1)"
  assumes "i < (d + 1)"
  shows "(sumlist Lst)$i = sum_list (map (\<lambda>j. (Lst!j)$i) [0..<(length Lst)])"
  using assms vec_module.sumlist_vec_index
  by (smt (verit, ccfv_SIG) map_eq_conv map_upt_len_conv subset_code(1))

definition ts_pmf where "ts_pmf = replicate_pmf d (pmf_of_set {1..<p})"

lemma set_pmf_ts: "set_pmf ts_pmf = {l. length l = d \<and> (\<forall>i < d. l!i \<in> {1..<p})}"
proof-
  have "set_pmf ts_pmf = {xs \<in> lists (set_pmf (pmf_of_set {1..<p})). length xs = d}"
    unfolding ts_pmf_def using set_replicate_pmf[of d "pmf_of_set {1..<p}"] .
  also have "\<dots> = {l. length l = d \<and> (\<forall>i < d. l!i \<in> {1..<p})}"
    apply safe
     apply(metis One_nat_def \<alpha> empty_iff finite_atLeastLessThan nth_mem set_pmf_of_set)
    by (metis empty_iff finite_atLeastLessThan in_set_conv_nth set_pmf_of_set)
  finally show ?thesis .
qed

definition ts_to_as :: "nat list \<Rightarrow> nat list" where
  "ts_to_as ts = (map (msb_p \<circ> (\<lambda>t. (\<alpha>*t) mod p)) ts)"

definition ts_to_u :: "nat list \<Rightarrow> rat vec" where 
  "ts_to_u ts = vec_of_list (map of_nat (ts_to_as ts) @ [0])"

lemma ts_to_u_alt:
  "ts_to_u ts = vec_of_list ((map (of_nat \<circ> msb_p \<circ> (\<lambda>t. (\<alpha>*t) mod p)) ts) @ [0])"
  unfolding ts_to_u_def ts_to_as_def by (metis map_map)

lemma u_carrier: "length ts = d \<Longrightarrow> ts_to_u ts \<in> carrier_vec (d + 1)"
  by (simp add: carrier_dim_vec ts_to_as_def ts_to_u_def)

lemma ts_to_u_carrier:
  fixes ts :: "nat list"
  shows "(ts_to_u ts) \<in> carrier_vec ((length ts) + 1)"
proof - 
  have "dim_vec (vec_of_list (map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts @ [0])) 
    = (length ts + 1)"
    by simp
  then show ?thesis
    unfolding ts_to_u_def ts_to_as_def carrier_vec_def by fastforce
qed

subsubsection "Lattice construction and lemmas"

definition p_vecs :: "rat vec list" where
  "p_vecs = map (\<lambda>i. of_int_hom.vec_hom ((of_nat p) \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d]"

lemma length_p_vecs: "length p_vecs = d" unfolding p_vecs_def by auto

lemma p_vecs_carrier: "\<forall>v \<in> set p_vecs. dim_vec v = d + 1" unfolding p_vecs_def by force

lemma lincomb_of_p_vecs_last: "(lincomb_list (of_int \<circ> cs) p_vecs)$d = 0" (is "?lhs = 0")
proof-
  let ?xs = "(map (\<lambda>i. (rat_of_int \<circ> cs) i \<cdot>\<^sub>v p_vecs ! i) [0..<length p_vecs])"
  have dim: "\<forall>v \<in> set ?xs. dim_vec v = d + 1" using p_vecs_carrier by simp
  have *: "\<forall>v \<in> set ?xs. v$d = 0" unfolding p_vecs_def by fastforce
  have "?lhs = sumlist (map (\<lambda>i. (rat_of_int \<circ> cs) i \<cdot>\<^sub>v p_vecs ! i) [0..<length p_vecs])$d"
    unfolding lincomb_list_def by blast
  also have "\<dots> = (\<Sum>j = 0..<length ?xs. ?xs ! j $ d)"
    using sumlist_nth[OF dim, of d] by linarith
  finally show ?thesis using * by force
qed

definition gen_basis :: "nat list \<Rightarrow> rat vec list" where
  "gen_basis ts = p_vecs @ [vec_of_list ((map of_nat ts) @ [1 / (of_nat p)])]"

lemma gen_basis_length: "length (gen_basis ts) = d + 1" unfolding gen_basis_def p_vecs_def by force

lemma gen_basis_units:
  assumes "i < d"
  assumes "j < d + 1"
  shows "((gen_basis ts)!i)$j = of_nat (if i = j then p else 0)" (is "(?x)$j = _")
proof-
  have "?x = of_int_hom.vec_hom ((of_nat p) \<cdot>\<^sub>v (unit_vec (d+1) i))"
  proof-
    have "?x = (map (\<lambda>i. of_int_hom.vec_hom ((of_nat p) \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d])!i"
      unfolding gen_basis_def p_vecs_def using assms(1) by (simp add: nth_append)
    also have "\<dots> = of_int_hom.vec_hom ((of_nat p) \<cdot>\<^sub>v (unit_vec (d+1) i))" by (simp add: assms(1))
    finally show ?thesis .
  qed
  thus ?thesis using assms by auto
qed

definition int_gen_lattice :: "nat list \<Rightarrow> int vec set" where
  "int_gen_lattice ts = vec_module.lattice_of (d + 1) (int_gen_basis ts)"

definition gen_lattice :: "nat list \<Rightarrow> rat vec set" where
  "gen_lattice ts = vec_module.lattice_of (d + 1) (gen_basis ts)"

definition close_vec :: "nat list \<Rightarrow> rat vec \<Rightarrow> bool" where
  "close_vec ts v \<longleftrightarrow> (sq_norm ((ts_to_u ts) - v) < ((of_nat p) / 2^\<mu>)^2)"

definition good_vec :: "rat vec \<Rightarrow> bool" where
  "good_vec v \<longleftrightarrow> dim_vec v = d + 1 \<and> (\<exists>\<beta>::int. [\<alpha> = \<beta>] (mod p) \<and> of_rat (v$d) = \<beta>/p)"

definition good_lattice :: "nat list \<Rightarrow> bool" where
  "good_lattice ts \<longleftrightarrow> (\<forall>v \<in> gen_lattice ts. close_vec ts v \<longrightarrow> good_vec v)"

definition bad_lattice :: "nat list \<Rightarrow> bool" where
  "bad_lattice ts \<longleftrightarrow> \<not> good_lattice ts"

definition sampled_lattice_good :: "bool pmf" where
  "sampled_lattice_good = do {
    ts \<leftarrow> ts_pmf;
    return_pmf (good_lattice ts)
  }"

interpretation vec_int: vec_module "TYPE(int)" "d + 1" .

lemma int_gen_basis_carrier:
  fixes ts :: "nat list"
  assumes "length ts = d"
  shows "set (int_gen_basis ts) \<subseteq> carrier_vec (d + 1)"
proof - 
  have first_part: "\<And>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i \<in> carrier_vec (d + 1)"
    unfolding unit_vec_def by simp
  have second_part: "(vec_of_list (map ((*) (int p)) (map int ts) @ [1])) \<in> carrier_vec (d+1)"
    by (simp add: assms carrier_dim_vec)
  show ?thesis
    unfolding int_gen_basis_def using first_part second_part
    by auto
qed

lemma int_gen_lattice_carrier:
  fixes ts :: "nat list"
  assumes "length ts = d"
  shows "int_gen_lattice ts \<subseteq> carrier_vec (d + 1)"
proof -
  have "set (int_gen_basis ts) \<subseteq> carrier_vec (d + 1)"
    using int_gen_basis_carrier[OF assms(1)] unfolding int_gen_basis_def
    by blast
  then show ?thesis
    unfolding int_gen_lattice_def
    using lattice_of_as_mat_mult by blast
qed

lemma gen_basis_vecs_carrier:
  fixes ts :: "nat list"
  fixes i :: nat
  assumes "length ts = d"
  assumes "i \<in> {0..< d + 1}"
  shows "(gen_basis ts) ! i \<in> carrier_vec (d + 1)"
proof (cases "i=d")
  case t:True
  have "length (gen_basis ts) = d + 1" unfolding gen_basis_def p_vecs_def by auto
  then have 1: "(gen_basis ts) ! i = vec_of_list ((map of_nat ts) @ [1 / (of_nat p)])"
    unfolding gen_basis_def using t by (simp add: append_Cons_nth_middle)
  have "length ((map of_nat ts) @ [1 / (of_nat p)]) = d + 1" using assms by fastforce
  then have "vec_of_list ((map of_nat ts) @ [1 / (of_nat p)]) \<in> carrier_vec (d + 1)"
    by (metis vec_of_list_carrier)
  then show ?thesis using 1 by algebra
next
  case False
  then have less: "i<d" using assms by simp
  have "length (gen_basis ts) = d + 1" unfolding gen_basis_def p_vecs_def by auto
  then have "(gen_basis ts) ! i = of_int_hom.vec_hom ((of_nat p) \<cdot>\<^sub>v (unit_vec (d+1) i))"
    using less by (simp add: gen_basis_def nth_append p_vecs_def)
  then show ?thesis by fastforce
qed

lemma gen_basis_carrier:
  fixes ts :: "nat list"
  assumes "length ts = d"
  shows "set (gen_basis ts) \<subseteq> carrier_vec (d + 1)"
proof-
  have "length (gen_basis ts) = d + 1" unfolding gen_basis_def p_vecs_def by auto
  then have "(gen_basis ts) ! i \<in> carrier_vec (d + 1)" if in_range: "i \<in> {0..<(length (gen_basis ts))}" for i
    using gen_basis_vecs_carrier[of ts i] in_range assms by argo
  then show ?thesis using set_list_subset[of "gen_basis ts" "carrier_vec (d + 1)"] by presburger
qed


lemma gen_lattice_carrier:
  fixes ts :: "nat list"
  assumes "length ts = d"
  shows "gen_lattice ts \<subseteq> carrier_vec (d + 1)" 
  proof - 
    have set_basis: "set (gen_basis ts) \<subseteq> carrier_vec (d + 1)"
      using gen_basis_carrier[of ts] assms unfolding gen_lattice_def
      by auto
    then have "dim_vec v = d+1" if v_in: "v \<in> lattice_of (gen_basis ts)" for v
      proof - 
        obtain c where v_is: "v = sumlist (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v gen_basis ts ! i) [0..<length (gen_basis ts)])"
          using v_in unfolding lattice_of_def by blast
        have all_x: "\<forall>x\<in>set (map (\<lambda>i. rat_of_int (c i) \<cdot>\<^sub>v gen_basis ts ! i) [0..<length (gen_basis ts)]).
           dim_vec x = d + 1"
          using set_basis unfolding carrier_vec_def 
          using assms gen_basis_length gen_basis_vecs_carrier by auto
        then show ?thesis
          using v_is carrier_dim_vec dim_sumlist[OF all_x]
          by argo
    qed
  then show ?thesis unfolding gen_lattice_def using carrier_dim_vec by blast
qed

lemma sampled_lattice_good_map_pmf: "sampled_lattice_good = map_pmf good_lattice ts_pmf"
  by (simp add: sampled_lattice_good_def map_pmf_def)

lemma coordinates_of_gen_lattice:
  fixes ts :: "nat list"
  fixes c :: "nat \<Rightarrow> int"
  fixes i :: nat
  assumes "i \<le> length ts"
  assumes "length ts = d"
  shows "(sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i)) [0 ..< length (gen_basis ts)]))$i 
          = (if (i = d) then (rat_of_int (c d) / rat_of_nat p) else rat_of_int ((c d) * ts!i + (c i)*p))"
proof(cases "i=d")
  case t:True
  define Lst where "Lst = (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i)) [0 ..< length (gen_basis ts)])"
  have "\<And>x. x \<in> set Lst \<Longrightarrow> x \<in> carrier_vec (d + 1)"
  proof-
    fix x assume "x \<in> set Lst"
    then obtain y where y: "Lst!y = x \<and> y\<in>{0..<length(Lst)}"
      by (meson atLeastLessThan_iff find_first_le nth_find_first zero_le)
    then have "x = of_int (c y) \<cdot>\<^sub>v ((gen_basis ts) ! y)" unfolding Lst_def by auto
    moreover have "length(Lst) = d + 1" unfolding Lst_def using gen_basis_length[of ts] by force
    ultimately show "x \<in> carrier_vec (d + 1)" using gen_basis_vecs_carrier[of ts] assms y by auto
  qed
  then have "(sumlist Lst)$i = sum_list (map (\<lambda>l. l$i) Lst)" 
    using sumlist_vec_index[of Lst i] gen_basis_carrier[of ts] assms by force
  moreover have "sum_list (map (\<lambda>l. l$i) Lst) 
               = sum_list (map (
                            (\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))
                               )
                              [0 ..< length (gen_basis ts)])" 
    unfolding Lst_def by auto
  moreover have "\<And>j. j \<in> (set [0 ..< length (gen_basis ts)])
                  \<Longrightarrow> \<not> (j = i \<or> j = d) 
                  \<Longrightarrow>  ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) j = 0"
  proof-
    fix j assume j1: "j \<in> (set [0 ..< length (gen_basis ts)])" and j2: "\<not> (j = i \<or> j = d)"
    have j3: "j < d \<and> j \<noteq> i" using j2 j1 gen_basis_length[of ts] by force
    have "((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) j = 
          (of_int (c j) \<cdot>\<^sub>v ((gen_basis ts) ! j))$i" by simp
    also have "(of_int (c j) \<cdot>\<^sub>v ((gen_basis ts) ! j))$i = (of_int (c j) * ((gen_basis ts) ! j)$i)"
      using gen_basis_vecs_carrier[of ts j] j1 assms gen_basis_length[of ts] by fastforce
    also have "((gen_basis ts) ! j)$i = 0"
      using gen_basis_units[of j i ts] j3 assms by fastforce
    finally show "((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) j = 0" by fastforce
  qed
  ultimately have "(sumlist Lst)$i
                 = sum_list (map 
                            ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i)))
                            (filter (\<lambda>j. j=i \<or> j = d)
                                 [0 ..< length (gen_basis ts)]))"
    using sum_list_map_filter[of "[0..<length (gen_basis ts)]" "(\<lambda>j. j=i \<or> j = d)" 
                                 "(\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))"] by argo
  moreover have "(filter (\<lambda>j. j=i \<or> j = d) [0 ..< length (gen_basis ts)]) = [d]"
    using t gen_basis_length[of ts] by fastforce
  ultimately have "(sumlist Lst)$i = (of_int (c d) \<cdot>\<^sub>v ((gen_basis ts) ! d))$d" using t by force
  also have "(of_int (c d) \<cdot>\<^sub>v ((gen_basis ts) ! d))$d = (of_int (c d)) * (gen_basis ts)!d$d"
    using gen_basis_vecs_carrier[of ts d] assms by simp
  also have "(gen_basis ts)!d$d = 1 / (rat_of_nat p)"
  proof-
    have "(gen_basis ts)!d = vec_of_list ((map of_nat ts) @ [1 / (of_nat p)])"
      using gen_basis_length[of ts] unfolding gen_basis_def
      by (simp add: append_Cons_nth_middle)
    also have "(vec_of_list ((map of_nat ts) @ [1 / (of_nat p)]))$d = ((map of_nat ts) @ [1 / (of_nat p)])!d"
      by auto
    also have "((map of_nat ts) @ [1 / (of_nat p)])!d = 1 / (of_nat p)"
      using assms append_Cons_nth_middle[of d "(map of_nat ts)" "1 / (of_nat p)" "[]"]
      by force
    finally show ?thesis by fastforce
  qed
  finally show ?thesis using t unfolding Lst_def by simp
next 
  case f:False
  define Lst where "Lst = (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i)) [0 ..< length (gen_basis ts)])"
  have "\<And>x. x \<in> set Lst \<Longrightarrow> x \<in> carrier_vec (d + 1)"
  proof-
    fix x assume "x \<in> set Lst"
    then obtain "y" where y_def: "x = Lst!y \<and> y\<in>{0..<length(Lst)}"
      by (metis atLeastLessThan_iff in_set_conv_nth zero_le)
    then have "x = of_int (c y) \<cdot>\<^sub>v ((gen_basis ts) ! y)"
      using Lst_def by force
    moreover have "y\<in>{0..<d+1}" 
      using y_def gen_basis_length[of ts] unfolding Lst_def by simp 
    ultimately show "x \<in> carrier_vec (d + 1)"
      using gen_basis_vecs_carrier[of ts y] assms by fastforce
  qed
  then have "(sumlist Lst)$i = sum_list (map (\<lambda>l. l$i) Lst)" 
    using sumlist_vec_index[of Lst i] gen_basis_carrier[of ts] assms by force
  moreover have "sum_list (map (\<lambda>l. l$i) Lst) 
               = sum_list (map (
                            (\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))
                               )
                              [0 ..< length (gen_basis ts)])" 
    unfolding Lst_def by auto
  moreover have "\<And>j. j \<in> (set [0 ..< length (gen_basis ts)])
                  \<Longrightarrow> \<not> (j = i \<or> j = d) 
                  \<Longrightarrow>  ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) j = 0"
  proof-
    fix j assume j1: "j \<in> (set [0 ..< length (gen_basis ts)])" and j2: "\<not> (j = i \<or> j = d)"
    have j3: "j < d \<and> j \<noteq> i" using j2 j1 gen_basis_length[of ts] by force
    have "((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) j = 
          (of_int (c j) \<cdot>\<^sub>v ((gen_basis ts) ! j))$i" by simp
    also have "(of_int (c j) \<cdot>\<^sub>v ((gen_basis ts) ! j))$i = (of_int (c j) * ((gen_basis ts) ! j)$i)"
      using gen_basis_vecs_carrier[of ts j] j1 assms gen_basis_length[of ts] by fastforce
    also have "((gen_basis ts) ! j)$i = 0"
      using gen_basis_units[of j i ts] j3 assms by fastforce
    finally show "((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) j = 0" by fastforce
  qed
  ultimately have "(sumlist Lst)$i
                 = sum_list (map 
                            ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i)))
                            (filter (\<lambda>j. j=i \<or> j = d)
                                 [0 ..< length (gen_basis ts)]))"
    using sum_list_map_filter[of "[0..<length (gen_basis ts)]" "(\<lambda>j. j=i \<or> j = d)" 
                                 "(\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))"] by argo
  moreover have "(filter (\<lambda>j. j = i \<or> j = d) [0 ..< length (gen_basis ts)]) = [i, d]"
    using filter_or[of i d "length (gen_basis ts)"] assms gen_basis_length[of ts] f
    by fastforce
  ultimately have "(sumlist Lst)$i = 
                   ( ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) i) +
                   ( ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) d)" by fastforce
  also have "( ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) i) = (of_int (c i) * ((gen_basis ts) ! i)$i)"
    using gen_basis_vecs_carrier[of ts i] assms gen_basis_length[of ts] by force
  also have "((gen_basis ts) ! i)$i = rat_of_nat p"
    using gen_basis_units[of i i ts] assms f by force
  also have "( ((\<lambda>l. l$i) \<circ> (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ts) ! i))) d) = (of_int (c d) * ((gen_basis ts) ! d)$i)"
    using gen_basis_vecs_carrier[of ts d] assms gen_basis_length[of ts] by force
  also have "((gen_basis ts) ! d)$i = rat_of_nat (ts!i)"
  proof-
    have "(gen_basis ts)!d = vec_of_list ((map of_nat ts) @ [1 / (of_nat p)])"
      using gen_basis_length[of ts] unfolding gen_basis_def
      by (simp add: append_Cons_nth_middle)
    also have "(vec_of_list ((map of_nat ts) @ [1 / (of_nat p)]))$i = ((map of_nat ts) @ [1 / (of_nat p)])!i"
      by auto
    also have "((map of_nat ts) @ [1 / (of_nat p)])!i = rat_of_nat (ts!i)"
      using assms f append_Cons_nth_left[of i "(map of_nat ts)" "1 / (of_nat p)" "[]"]
      by force
    finally show ?thesis by fastforce
  qed
  finally have "(sumlist Lst)$i = (of_int (c i)) * (rat_of_nat p) + (rat_of_int (c d)) * (rat_of_nat (ts!i))"
    by blast
  then show ?thesis using f unfolding Lst_def by force
qed

lemma gen_lattice_int_gen_lattice_vec:
  fixes scaled_v :: "int vec"
  fixes ts :: "nat list"
  assumes "length ts = d"
  assumes "(scaled_v \<in> int_gen_lattice ts)"
  shows "((1/(of_nat p)) \<cdot>\<^sub>v (map_vec rat_of_int scaled_v) \<in> (gen_lattice ts))"
proof-
  let ?iL = "int_gen_lattice ts"
  let ?ib = "int_gen_basis ts"
  let ?L = "gen_lattice ts"
  let ?b = "gen_basis ts"
  have il: "length ?ib = d + 1"
    unfolding int_gen_basis_def by fastforce
  obtain c where c: "scaled_v = vec_int.lincomb_list (of_int \<circ> c) ?ib"
    using int_gen_basis_carrier[of ts] assms unfolding int_gen_lattice_def vec_int.lincomb_list_def vec_int.lattice_of_def by auto
  let ?v = "lincomb_list (of_int \<circ> c) ?b"
  have carr_v: "?v \<in> carrier_vec (d + 1)"
    using lincomb_list_carrier gen_basis_carrier assms by blast
  have carr_sv: "(1/(of_nat p)) \<cdot>\<^sub>v (map_vec rat_of_int scaled_v) \<in> carrier_vec (d + 1)"
    using assms int_gen_lattice_carrier[of ts] by auto
  have carr_iv: "scaled_v \<in> carrier_vec (d + 1)"
    using int_gen_lattice_carrier[of ts] assms by fast
  have "?v \<in> ?L"
    unfolding lincomb_list_def gen_lattice_def lattice_of_def by simp 
  moreover have "?v = (1/(of_nat p)) \<cdot>\<^sub>v (map_vec rat_of_int scaled_v)"
  proof-
    have "?v$i = ((1/(of_nat p)) \<cdot>\<^sub>v (map_vec rat_of_int scaled_v))$i" if in_range: "i\<in>{0..<(d + 1)}" for i
    proof-
      let ?Lst = "(map (\<lambda>i. (of_int \<circ> c) i \<cdot>\<^sub>v int_gen_basis ts ! i) [0..<length (int_gen_basis ts)])"
      have "length (int_gen_basis ts) = d + 1" unfolding int_gen_basis_def by force
      then have "set ?Lst \<subseteq> carrier_vec (d + 1)"
        using int_gen_basis_carrier[of ts] assms(1) gen_basis_vecs_carrier length_map map_eq_conv map_nth set_list_subset smult_closed
        by fastforce
      then have "scaled_v $ i = sum_list (map (\<lambda>l. l$i) ?Lst)"
        using vec_int.sumlist_vec_index[of ?Lst i] in_range c
        unfolding vec_int.lincomb_list_def by auto
      then have *: "scaled_v $ i = sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<(d + 1)])"
        using il by simp
      show ?thesis (*Lots of repeated logic here, could probably use a clean-up*)
      proof(cases "i = d")
        case t:True
        have "[0..<(d  + 1)] = [0..<d] @ [d]" by simp
        then have sv: "scaled_v $ i = sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<(d)]) + ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) d"
          using * by fastforce
        have "x = 0" if x: "x \<in> set ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<(d)])" for x
        proof-
          obtain "l" where l: "x = ((of_int \<circ> c) l \<cdot>\<^sub>v (?ib ! l))$i \<and> l\<in>{0..<d}" using x by fastforce
          then have "(?ib ! l) \<in> carrier_vec (d + 1)" using int_gen_basis_carrier[of ts] assms il by auto
          then have "((of_int \<circ> c) l \<cdot>\<^sub>v (?ib ! l))$i = (of_int \<circ> c) l * (?ib !l)$i" using t by auto
          moreover have "(?ib !l)$i = (int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) l)$i"
            unfolding int_gen_basis_def using append_Cons_nth_left[of l "map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d]" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])" "[]"] l
            by force
          moreover have "(int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) l)$i = 0"
            using t in_range l by fastforce
          ultimately show "x = 0" using l by simp
        qed
        then have "sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<(d)]) = 0"
          using sum_list_neutral by blast
        moreover have "((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) d = c d"
        proof-
          have c: "(?ib ! d) \<in> carrier_vec (d + 1)"
            using int_gen_basis_carrier[of ts] assms il by force
          have "((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) d = (((of_int \<circ> c) d) \<cdot>\<^sub>v (?ib ! d))$i" by simp
          moreover have "\<dots> = ((of_int \<circ> c) d) * (?ib ! d)$i" using c t by simp
          moreover have "((?ib ! d))$i = 1"
            unfolding int_gen_basis_def 
            using append_Cons_nth_middle[of d "map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d]" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])" "[]"]
                  t append_Cons_nth_middle[of i "map ((*) (int p)) (map int ts)" 1 "[]"] assms(1) by force
          ultimately show ?thesis by force
        qed
        ultimately have "scaled_v $ i = c d" using sv by presburger
        then have "((1/(of_nat p)) \<cdot>\<^sub>v (map_vec rat_of_int scaled_v))$i = rat_of_int (c d) / rat_of_nat p"
          using carr_iv t by simp
        then show ?thesis using coordinates_of_gen_lattice[of d ts c] 
          unfolding lincomb_list_def using assms t by force
      next
        case f:False
        then have "[0..<(d  + 1)] = [0..<i]@[i]@[(i + 1)..<d]@[d]"
          using in_range upt_append by fastforce
        then have 0: "scaled_v $ i =  sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<i]) +
                                    ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) i +
                                   sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [(i + 1)..<(d)]) +
                                    ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) d"
          using * by force
        have 3: "x = 0" if x: "x \<in> set ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [(i+1)..<d])" for x (*third component*)
        proof-
          obtain l where l: "x = ((of_int \<circ> c) l \<cdot>\<^sub>v (?ib!l) )$i \<and> l\<in>{(i+1)..<d}" using x by auto
          then have "?ib!l \<in> carrier_vec (d + 1)"
            using int_gen_basis_carrier[of ts] assms(1) il by fastforce
          then have "((of_int \<circ> c) l \<cdot>\<^sub>v (?ib!l) )$i = (of_int \<circ> c) l * (?ib!l)$i"
            using f in_range by fastforce
          moreover have "?ib!l$i = (int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) l)$i"
            unfolding int_gen_basis_def using append_Cons_nth_left[of l "map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d]" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])"]
            using l by simp
          moreover have "(int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) l)$i = 0" using l by fastforce
          ultimately show ?thesis using x l by presburger
        qed
        have "x = 0" if x: "x \<in> set ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<i])" for x (*first component*)
        proof-
         obtain l where l: "x = ((of_int \<circ> c) l \<cdot>\<^sub>v (?ib!l) )$i \<and> l\<in>{0..<i}" using x by auto
         then have "?ib!l \<in> carrier_vec (d + 1)"
            using int_gen_basis_carrier[of ts] assms(1) il in_range by fastforce
          then have "((of_int \<circ> c) l \<cdot>\<^sub>v (?ib!l) )$i = (of_int \<circ> c) l * (?ib!l)$i"
            using f in_range by fastforce
          moreover have "?ib!l$i = (int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) l)$i"
            unfolding int_gen_basis_def using append_Cons_nth_left[of l "map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d]" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])"]
            using l in_range by simp
          moreover have "(int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) l)$i = 0" using l in_range by fastforce
          ultimately show ?thesis using x l by presburger
        qed
        then have "sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [0..<i]) = 0"
          using sum_list_neutral by blast
        moreover have "sum_list ((map ((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) )) [(i+1)..<d]) = 0"
          using sum_list_neutral 3 by blast
        moreover have "((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) i = c i * p^2"
        proof-
          have "?ib!i \<in> carrier_vec (d + 1)"
            using int_gen_basis_carrier[of ts] assms(1) il in_range by force
          then have "((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) i = ((of_int \<circ> c) i) * (?ib!i$i)"
            using in_range by force
          moreover have "?ib!i = (int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i)"
            unfolding int_gen_basis_def using append_Cons_nth_left[of i "map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d]" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])"]
            in_range f by fastforce
          moreover have "(int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i)$i = p^2" using in_range by force
          ultimately show ?thesis by simp
        qed
        moreover have "((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) d = c d * p * (ts!i)"
        proof-
          have "?ib!d \<in> carrier_vec (d + 1)"
            using int_gen_basis_carrier[of ts] assms(1) il by fastforce
          then have "((\<lambda>l. l$i) \<circ> (\<lambda>j. (of_int \<circ> c) j \<cdot>\<^sub>v (?ib ! j) ) ) d = ((of_int \<circ> c) d) * (?ib!d$i)"
            using in_range by simp
          moreover have "(?ib!d) = vec_of_list (map ((*) (int p)) (map int ts) @ [1])" 
            unfolding int_gen_basis_def
            using append_Cons_nth_middle[of d "map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d]" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])"]
            by simp
          moreover have "vec_of_list (map ((*) (int p)) (map int ts) @ [1]) $ i = map ((*) (int p)) (map int ts) ! i"
            using append_Cons_nth_left[of i "map ((*) (int p)) (map int ts)" 1 "[]"] in_range f 
                  vec_index_vec_of_list[of "(map ((*) (int p)) (map int ts) @ [1])" i] assms by force
          moreover have " map ((*) (int p)) (map int ts) ! i = (int p) * ts!i" using in_range f assms by auto
          ultimately show ?thesis by auto
        qed
        ultimately have scv: "scaled_v $ i = (c i) * p^2 + c d * p*(ts!i)" using 0 by linarith
        have foil: "rat_of_int (c i * int (p\<^sup>2) + c d * int p * int (ts ! i)) = 
          rat_of_nat p * rat_of_int (c i * int p + c d * int (ts ! i))"
          by (smt (verit, del_insts) Power.semiring_1_class.of_nat_power Ring_Hom.of_int_hom.hom_mult int_distrib(1) more_arith_simps(11) mult_ac(2) of_int_of_nat_eq power2_eq_square)
        have "((1/(of_nat p))\<cdot>\<^sub>v(map_vec rat_of_int scaled_v))$i = rat_of_int ((c i) * p^2 + c d * p*(ts!i)) / (rat_of_nat p)"
          using scv carr_iv f in_range by force
        moreover have "\<dots> = rat_of_int ((c i) * p + (c d) * (ts!i))"
          using foil p by auto
        ultimately show ?thesis
          using coordinates_of_gen_lattice[of i ts c] assms f in_range
          unfolding lincomb_list_def
          by simp
      qed
    qed
    then show ?thesis using carr_v carr_sv by auto
  qed
  ultimately show "(1/(of_nat p)) \<cdot>\<^sub>v (map_vec rat_of_int scaled_v) \<in> ?L" by argo
qed

definition t_vec :: "nat list \<Rightarrow> rat vec" where
  "t_vec ts = vec_of_list ((map of_nat ts) @ [1 / (of_nat p)])"

lemma t_vec_dim: "dim_vec (t_vec ts) = length ts + 1"
  unfolding t_vec_def by simp

lemma t_vec_last: "length ts = d \<Longrightarrow> (t_vec ts)$d = 1 / (of_nat p)"
  unfolding t_vec_def
  by (simp add: append_Cons_nth(1)) 

definition z_vecs :: "int vec set" where
  "z_vecs = {v. dim_vec v = d + 1 \<and> v$d = 0}"

definition vec_class :: "nat list \<Rightarrow> int \<Rightarrow> rat vec set" where
  "vec_class ts \<beta> = {(of_int \<beta>) \<cdot>\<^sub>v (t_vec ts) + lincomb_list (of_int \<circ> cs) p_vecs | cs :: nat \<Rightarrow> int. True}"

definition vec_class_mod_p :: "nat list \<Rightarrow> int \<Rightarrow> rat vec set" where
  "vec_class_mod_p ts \<beta> = \<Union>{vec_class ts \<beta>' | \<beta>'. [\<beta> = \<beta>'] (mod p)}"

lemma vec_class_carrier:
  assumes "length ts = d"
  shows "vec_class ts \<beta> \<subseteq> carrier_vec (d + 1)"
proof
  fix x assume "x \<in> vec_class ts \<beta>"
  then obtain cs where "x = (of_int \<beta>) \<cdot>\<^sub>v (t_vec ts) + lincomb_list (of_int \<circ> cs) p_vecs"
    unfolding vec_class_def by blast
  moreover have "t_vec ts \<in> carrier_vec (d + 1)"
    using t_vec_dim[of ts] unfolding assms(1) carrier_vec_def by blast
  moreover have "lincomb_list (of_int \<circ> cs) p_vecs \<in> carrier_vec (d + 1)"
    by (metis p_vecs_carrier carrier_vec_dim_vec lincomb_list_carrier subsetI)
  ultimately show "x \<in> carrier_vec (d + 1)" by blast
qed

lemma vec_class_mod_p_carrier:
  assumes "length ts = d"
  shows "vec_class_mod_p ts \<beta> \<subseteq> carrier_vec (d + 1)"
  unfolding vec_class_mod_p_def using assms vec_class_carrier by blast

lemma vec_class_last:
  assumes "length ts = d"
  assumes "v \<in> vec_class ts \<beta>"
  shows "v$d = rat_of_int \<beta> / rat_of_int p"
  using assms(2) unfolding vec_class_def
proof-
  obtain cs where cs: "v = rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts + lincomb_list (rat_of_int \<circ> cs) p_vecs"
    using assms(2) unfolding vec_class_def by blast
  let ?a = "rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts"
  let ?b = "lincomb_list (rat_of_int \<circ> cs) p_vecs"
  have "?a$d = rat_of_int \<beta> / rat_of_int p"
    using t_vec_last[OF assms(1)] by (simp add: assms(1) t_vec_dim)
  moreover have "?b$d = 0" using lincomb_of_p_vecs_last by blast
  ultimately show ?thesis using cs vec_class_carrier[OF assms(1), of \<beta>]
    by (smt (z3) One_nat_def add_Suc_right assms(1,2) carrier_vec_dim_vec index_add_vec(1) index_add_vec(2) lessI r_zero semiring_norm(51) subsetD t_vec_dim)
qed

(* NOTE: This depends very closely on the structure of ts.
  Generally was somewhat challenging to prove with all of the casting. *)
lemma gen_lattice_int_gen_lattice_vec':
  fixes v :: "rat vec"
  fixes ts :: "nat list"
  assumes "length ts = d"
  assumes "v \<in> gen_lattice ts"
  shows "map_vec int_of_rat ((of_nat p) \<cdot>\<^sub>v v) \<in> int_gen_lattice ts"
        "map_vec rat_of_int (map_vec int_of_rat ((of_nat p) \<cdot>\<^sub>v v)) = (rat_of_nat p) \<cdot>\<^sub>v v"
proof - 
  have dims: "(\<And>w. List.member (gen_basis ts) w \<Longrightarrow> dim_vec w = d + 1)"
    by (meson List.member_def assms(1) carrier_dim_vec gen_basis_carrier subsetD)
  have pv_in: "(rat_of_nat p \<cdot>\<^sub>v v) \<in> lattice_of (map (\<lambda>x. rat_of_nat p \<cdot>\<^sub>v x) (gen_basis ts))"
    using assms(2)
    unfolding gen_lattice_def
    using smult_in_lattice_of[OF dims, of "(gen_basis ts)" v "rat_of_nat p"]
    by blast
 then have lattice_of_map: "rat_of_nat p \<cdot>\<^sub>v v
  \<in> lattice_of
      (map ((\<cdot>\<^sub>v) (rat_of_nat p))
        (p_vecs @
         [vec_of_list
           (map rat_of_nat ts @ [1 / rat_of_nat p])]))"
   unfolding gen_basis_def by blast
  then have eq1: "rat_of_nat p \<cdot>\<^sub>v v
    \<in> lattice_of
      ((map ((\<cdot>\<^sub>v) (rat_of_nat p))
        (p_vecs)) @
        [((\<cdot>\<^sub>v) (rat_of_nat p) (vec_of_list
           (map rat_of_nat ts @ [1 / rat_of_nat p])))])"
    by simp
  have generic_aux: "\<And>p::rat. [(\<cdot>\<^sub>v) p (vec_of_list ell)] = [vec_of_list (map (\<lambda>x. p*x) ell)]"
    for ell :: "rat list"
    by auto
  have generic: "\<And>p elt::rat. [(\<cdot>\<^sub>v) p (vec_of_list (ell @ [elt]))] = 
      [ (vec_of_list ((map (\<lambda>x. p*x) ell) @ [p* elt]))]"
    for ell :: "rat list" 
  proof -
    fix p elt :: "rat"
    have "[(\<cdot>\<^sub>v) p (vec_of_list (ell @ [elt]))] = [vec_of_list (map (\<lambda>x. p*x) (ell @ [elt]))]"
      using generic_aux by blast
    then show "[(\<cdot>\<^sub>v) p (vec_of_list (ell @ [elt]))] = 
      [ (vec_of_list ((map (\<lambda>x. p*x) ell) @ [p* elt]))]"
      by simp
  qed
  have h1: "(map ((*) (rat_of_nat p)) (map rat_of_nat ts)) = map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts"
    by simp
  have h2: "rat_of_nat p * (1 / rat_of_nat p) = 1"
    by (simp add: p prime_gt_0_nat)
  then have eq1: "[((\<cdot>\<^sub>v) (rat_of_nat p) (vec_of_list
           (map rat_of_nat ts @ [1 / rat_of_nat p])))] = 
      [vec_of_list
           (map (\<lambda>x. (rat_of_nat p) * rat_of_nat x) ts @ [1])]"
    unfolding generic[of "(rat_of_nat p)" "map rat_of_nat ts" "1 / rat_of_nat p"]
    using h1 h2 by argo

  let ?qs = "p_vecs @ [vec_of_list (map rat_of_nat ts @ [1 / rat_of_nat p])]"
  let ?qs2 = "(map ((\<cdot>\<^sub>v) (rat_of_nat p))
        (p_vecs)) @
         [vec_of_list
           (map (\<lambda>x. (rat_of_nat p) * rat_of_nat x) ts @ [1])]"

  have rat_of_nat_qs2: "rat_of_nat p \<cdot>\<^sub>v v \<in> lattice_of ?qs2"
    using eq1 gen_basis_def pv_in by force


  have mem1: "\<exists>k. map_vec rat_of_int k = mem" if 
      is_mem: "List.member (map ((\<cdot>\<^sub>v) (rat_of_nat p)) p_vecs) mem"
    for mem
  proof - 
    obtain i where i_prop: "mem = ((\<cdot>\<^sub>v) (rat_of_nat p))
     (map_vec rat_of_int (int p \<cdot>\<^sub>v unit_vec (d + 1) i))"
      "i < d"
      using is_mem unfolding p_vecs_def 
      by (smt (verit, ccfv_SIG) Groups.monoid_add_class.add.left_neutral List.List.list.set_map List.member_def diff_zero imageE in_set_conv_nth length_map length_upt nth_map_upt)
    show ?thesis
      unfolding i_prop(1)
      by (metis Matrix.of_int_hom.vec_hom_smult of_int_of_nat_eq) 
  qed
  have mem2: "\<exists>k. map_vec rat_of_int k = mem" if mem_ts: "mem = vec_of_list (map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts @ [1])" for mem
  proof - 
    let ?k = "vec_of_list (map (\<lambda>x. (int p) * x) ts @ [1])"
    have "map rat_of_int (map (\<lambda>x. (int p) * x) ts @ [1]) = 
      map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts @ [1]"
      by auto
    then have "map_vec rat_of_int ?k =
        vec_of_list (map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts @ [1])"
      by (metis vec_of_list_map)
    then show ?thesis unfolding mem_ts
      by blast
  qed

  have mem_int: "(\<And>mem. List.member ?qs2 mem \<Longrightarrow> \<exists>k. map_vec rat_of_int k = mem)"
    using mem1 mem2 
    by (metis append_insert in_set_member insert_iff)
  have mem_dims: "(\<And>mem. List.member ?qs2 mem \<Longrightarrow> dim_vec mem = d + 1)"
    using dims gen_basis_def
    by (smt (verit, ccfv_threshold) List.List.list.set_map List.member_def append_insert eq1 imageE index_smult_vec(2) insert_iff)
  then have casting_hyp: "\<exists>k::int vec. map_vec rat_of_int k = rat_of_nat p \<cdot>\<^sub>v v"
    using assms(2) unfolding gen_lattice_def gen_basis_def 
    using in_lattice_casting[OF mem_int mem_dims rat_of_nat_qs2]
    by blast

  have rat_of_nat_is: "rat_of_nat p \<cdot>\<^sub>v v
    \<in> lattice_of
      ((map ((\<cdot>\<^sub>v) (rat_of_nat p))
        (p_vecs)) @
         [vec_of_list
           (map (\<lambda>x. (rat_of_nat p) * rat_of_nat x) ts @ [1])])"
    using eq1 lattice_of_map by simp
  have vec_is_in_lattice: "(map_vec int_of_rat (rat_of_nat p \<cdot>\<^sub>v v))
    \<in> local.vec_int.lattice_of 
        (map (map_vec int_of_rat) (map ((\<cdot>\<^sub>v) (rat_of_nat p)) p_vecs @
         [vec_of_list (map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts @ [1])]))"
    using casting_lattice_lemma[OF casting_hyp mem_int mem_dims rat_of_nat_is]
    by blast

  have big_map_is: "(map (map_vec int_of_rat)
     (map ((\<cdot>\<^sub>v) (rat_of_nat p))
       (map (\<lambda>i. map_vec rat_of_int
                  (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)))
         [0..<d]))) ! i = 
   map_vec int_of_rat ((\<cdot>\<^sub>v) (rat_of_nat p) (map_vec rat_of_int
                  (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0))))" if i_lt: "i < d" for i
    using i_lt by auto
  have "(\<cdot>\<^sub>v) (rat_of_nat p) (map_vec rat_of_int
                  (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0))) = 
    map_vec rat_of_int ((\<cdot>\<^sub>v) p (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)))" if i_lt: "i < d" for i
    by (simp add: Matrix.of_int_hom.vec_hom_smult)
  then have "map_vec int_of_rat ((\<cdot>\<^sub>v) (rat_of_nat p) (map_vec rat_of_int
                  (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)))) =  
  map_vec int_of_rat (map_vec rat_of_int ((\<cdot>\<^sub>v) p (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0))))" if i_lt: "i < d" for i
    by auto
  then have "map_vec int_of_rat ((\<cdot>\<^sub>v) (rat_of_nat p) (map_vec rat_of_int
                  (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)))) =  
     ((\<cdot>\<^sub>v) p (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)))" if i_lt: "i < d" for i
    by (metis (no_types, lifting) Matrix.of_int_hom.vec_hom_smult eq_vecI index_map_vec(1) index_map_vec(2) int_of_rat(1) of_int_of_nat_eq)
  then have lhs_is: "(map (map_vec int_of_rat)
     (map ((\<cdot>\<^sub>v) (rat_of_nat p))
       (map (\<lambda>i. map_vec rat_of_int
                  (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)))
         [0..<d]))) ! i = 
   (\<cdot>\<^sub>v) p (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0))" if i_lt: "i < d" for i
    using i_lt by simp
  
  have rhs_is: "(map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)) [0..<d]) ! i = 
    int (p\<^sup>2) \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)" if i_lt: "i < d" for i
    using i_lt by simp

  have lhs_eq_rhs: "(\<cdot>\<^sub>v) p (int p \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)) = int (p\<^sup>2) \<cdot>\<^sub>v vec (d + 1) (\<lambda>j. if j = i then 1 else 0)" if i_lt: "i < d" for i
    by (simp add: local.vec_int.smult_assoc_simp power2_eq_square)

  have first_part_eq: "map (map_vec int_of_rat) (map ((\<cdot>\<^sub>v) (rat_of_nat p)) p_vecs) = 
    (map (\<lambda>i. int (p\<^sup>2) \<cdot>\<^sub>v unit_vec (d + 1) i) [0..<d])"
    unfolding p_vecs_def unit_vec_def 
    using lhs_is rhs_is lhs_eq_rhs by simp
  have map_vec_is: "map int_of_rat (map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts @ [1])
    = (map ((*) (int p)) (map int ts) @ [1])"
    apply (induct ts) 
    subgoal by simp (metis int_of_rat(1) of_int_1)
    subgoal by simp (metis int_of_rat(1) of_int_of_nat_eq of_nat_simps(5))
    done
  then have last_elem_eq: "map (map_vec int_of_rat) [vec_of_list
         (map (\<lambda>x. rat_of_nat p * rat_of_nat x) ts @ [1])] = 
  [vec_of_list (map ((*) (int p)) (map int ts) @ [1])]"
    by (smt (verit) List.list.simps(8) List.list.simps(9) vec_of_list_map)
  show int_gen_lattice: "map_vec int_of_rat ((of_nat p) \<cdot>\<^sub>v v) \<in> int_gen_lattice ts"
    unfolding int_gen_lattice_def int_gen_basis_def gen_basis_def p_vecs_def
    using vec_is_in_lattice last_elem_eq first_part_eq
    by auto
  have LHS_simp: "(rat_of_int
           (vec (dim_vec v)
             (\<lambda>i. int_of_rat
                   (vec (dim_vec v)
                     (\<lambda>i. rat_of_nat p * v $ i) $
                    i)) $
            i)) = 
    rat_of_int
           (int_of_rat
                   (rat_of_nat p * v $ i))" if i_lt: "i < dim_vec v" for i
    using i_lt by simp
  have same_dims: "dim_vec
                 (vec (dim_vec
                 (vec (dim_vec v)
                   (\<lambda>i. rat_of_nat p * v $ i)))
            (\<lambda>i. int_of_rat
                  (vec (dim_vec v)
                    (\<lambda>i. rat_of_nat p * v $ i) $
                   i))) = dim_vec v"
    by simp
 have "rat_of_int
           (vec (dim_vec v)
             (\<lambda>i. int_of_rat
                   (vec (dim_vec v)
                     (\<lambda>i. rat_of_nat p * v $ i) $
                    i)) $
            i) = rat_of_nat p * v $ i" if i_lt: "i < dim_vec v"
   for i
 proof - 
    show ?thesis 
      using i_lt unfolding LHS_simp[OF i_lt] 
      by (metis casting_hyp index_map_vec(1) index_map_vec(2) index_smult_vec(1) index_smult_vec(2) int_of_rat(1))
  qed
  then have same_vec: "vec (dim_vec v) (\<lambda>i. rat_of_int
           (vec (dim_vec
                  (vec (dim_vec v)
                    (\<lambda>i. rat_of_nat p * v $ i)))
             (\<lambda>i. int_of_rat
                   (vec (dim_vec v)
                     (\<lambda>i. rat_of_nat p * v $ i) $
                    i)) $
            i)) = vec (dim_vec v) (\<lambda>i. rat_of_nat p * v $ i)" using same_dims
    by (simp add: Matrix.vec_eq_iff)
  show "map_vec rat_of_int (map_vec int_of_rat ((of_nat p) \<cdot>\<^sub>v v)) = (of_nat p)\<cdot>\<^sub>v v"
    unfolding map_vec_def smult_vec_def 
    using same_dims same_vec by argo
qed

lemma gen_lattice_int_gen_lattice_closest:
  fixes scaled_v :: "int vec"
  fixes u :: "rat vec"
  fixes ts :: "nat list"
  assumes "length ts = d"
  assumes "dim_vec u = d + 1"
  shows "real(p^2) * Inf{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}
    = babai.closest_distance_sq (int_gen_basis ts) ((rat_of_nat p) \<cdot>\<^sub>v u)"
proof-
  let ?iL = "int_gen_lattice ts"
  let ?ib = "int_gen_basis ts"
  let ?L = "gen_lattice ts"
  let ?b = "gen_basis ts"
  have il: "length ?ib = d + 1"
    unfolding int_gen_basis_def by fastforce
  have su: "dim_vec ((rat_of_nat p)\<cdot>\<^sub>v u) = d + 1" 
    using assms(2) by force 
  let ?lhs = "real(p^2) * Inf{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}"
  let ?rhs = "babai.closest_distance_sq (int_gen_basis ts) ((rat_of_nat p)\<cdot>\<^sub>vu)"
  let ?coset = "{(map_vec rat_of_int x) - ((rat_of_nat p)\<cdot>\<^sub>vu)| x. x \<in> int_gen_lattice ts}"
  have bab: "babai ?ib ((rat_of_nat p)\<cdot>\<^sub>vu)"
    using il su unfolding babai_def by argo
  have "?coset \<noteq> {}" unfolding int_gen_lattice_def vec_int.lattice_of_def by blast
  then have *: "{(real_of_rat (sq_norm (x)))| x. x\<in> ?coset} \<noteq> {}" by simp
  have "?L \<noteq> {}" unfolding gen_lattice_def lattice_of_def by blast
  then have **: "{(real_of_rat (sq_norm (x - u)))| x. x \<in> ?L} \<noteq> {}" by blast
  have rhs: "?rhs = Inf {(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}"
    using babai.closest_distance_sq_def[of ?ib "rat_of_nat p \<cdot>\<^sub>v u"] bab su il LLL.LLL.L_def[of "d + 1" ?ib] unfolding int_gen_lattice_def by presburger
  have "\<forall>x\<in>{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}. 0 \<le> x"
    using sq_norm_vec_ge_0 by fastforce
  then have bdd: "bdd_below {real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}" by fast
  have "\<forall>x\<in>{(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}. 0 \<le> x"
    using sq_norm_vec_ge_0 by fastforce
  then have bdd2: "bdd_below {(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}" by fast
  have "?lhs \<le> ?rhs"
  proof(rule ccontr)
    assume "\<not>(?lhs \<le> ?rhs)"
    then have "?lhs > ?rhs" by linarith
    then obtain D where D: "D < ?lhs \<and> D \<in> {(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}" 
      using rhs cInf_lessD[of "{(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}" ?lhs] * by auto
    then obtain iv where iv: "real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) ) = D \<and> iv \<in> ?iL" by blast
    then have iv_carr: "iv \<in> carrier_vec (d + 1)"
      using int_gen_lattice_carrier assms by fast
    let ?v = "(1/(of_nat p))\<cdot>\<^sub>v (map_vec rat_of_int iv)"
    have "?v \<in> ?L" using iv gen_lattice_int_gen_lattice_vec assms by presburger
    then have "real_of_rat (sq_norm (?v - u)) \<in> {real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}" by fast
    moreover have "real_of_rat (sq_norm (?v - u)) < Inf{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}"
    proof-
      have h: "0<real(p^2)" using p by simp
      have "real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) ) < ?lhs"
        using D iv by fast
      then have "real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) ) < Inf{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts} * real(p^2)" by argo
      then have "real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) ) / (of_nat p^2) < Inf{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}"
        using h divide_less_eq[of "real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) )" "real (p^2)" "Inf{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}"]
        by simp
      moreover have "real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) ) / (of_nat p^2) = real_of_rat (sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u))  / (of_nat p^2))"
        by (simp add: Ring_Hom.of_rat_hom.hom_div Ring_Hom.of_rat_hom.hom_power)
      moreover have "\<dots> = real_of_rat ( sq_norm_conjugate (1 / (of_nat p)) * sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) )" 
        using conjugatable_ring_1_abs_real_line_class.sq_norm_as_sq_abs[of "1 / (of_nat p)"]
        by (simp add: power2_eq_square)
      moreover have "sq_norm_conjugate (1 / (of_nat p)) * sq_norm ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) 
                    = sq_norm ( (1 / (of_nat p)) \<cdot>\<^sub>v ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) )"
        using sq_norm_smult_vec by metis
      moreover have "(1 / (of_nat p)) \<cdot>\<^sub>v ((map_vec rat_of_int iv) - (rat_of_nat p \<cdot>\<^sub>v u)) = 1 / (of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int iv) - (1 / (of_nat p)) \<cdot>\<^sub>v(rat_of_nat p \<cdot>\<^sub>v u)"
        using su iv_carr carrier_vecI[OF su] 
        using p smult_sub_distrib_vec[of _ "d+1" "rat_of_nat p \<cdot>\<^sub>v u" "1 / rat_of_nat p"]
        by auto
      moreover have " (1 / (of_nat p)) \<cdot>\<^sub>v(rat_of_nat p \<cdot>\<^sub>v u) = u" 
        using smult_smult_assoc[of "(1 / (of_nat p))" "rat_of_nat p"] p by auto
      ultimately show ?thesis by algebra
    qed
    ultimately show False
      using cInf_lower[of "real_of_rat (sq_norm (?v - u))" "{real_of_rat (sq_norm (x - u))| x. x\<in> gen_lattice ts}"] bdd by linarith
  qed
  moreover have "?rhs \<le> ?lhs"
  proof(rule ccontr)
    assume "\<not>(?rhs \<le> ?lhs)"
    then have "?rhs > ?lhs" by linarith
    then have "?rhs / p^2 > Inf {(real_of_rat (sq_norm (x - u)))| x. x \<in> ?L}"
      using p
      by (metis (no_types, lifting) less_divide_eq mult_of_nat_commute of_nat_0_less_iff power_pos prime_gt_0_nat)
    then obtain D where D: "D < (?rhs / p^2) \<and> D \<in> {(real_of_rat (sq_norm (x - u)))| x. x \<in> ?L}"
      using cInf_lessD[of "{(real_of_rat (sq_norm (x - u)))| x. x \<in> ?L}" "?rhs / p^2"] ** by meson
    then obtain v where v: "(real_of_rat (sq_norm (v - u))) = D \<and> v \<in> ?L"
      by blast
    let ?iv = "map_vec int_of_rat ((rat_of_nat p) \<cdot>\<^sub>v v)"
    have "?iv \<in> ?iL" using gen_lattice_int_gen_lattice_vec' assms(1) v by blast
    then have "real_of_rat (sq_norm ((map_vec rat_of_int ?iv) - ((rat_of_nat p)\<cdot>\<^sub>vu))) \<in> {(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}" by fast
    moreover have "real_of_rat (sq_norm ((map_vec rat_of_int ?iv) - ((rat_of_nat p)\<cdot>\<^sub>vu))) < ?rhs"
    proof-
      have dim_v: "v \<in> carrier_vec (d + 1)"
        using v assms(1) gen_lattice_carrier by blast
      have "0<real(p^2)" using p by simp
      then have "(real_of_rat (sq_norm (v - u))) * p^2 < ?rhs"
        using less_divide_eq[of "real_of_rat (sq_norm (v - u))" ?rhs "real(p^2)"] using D v by algebra
      moreover have "(real_of_rat (sq_norm (v - u))) * p^2  = real_of_rat ( rat_of_nat p^2 * sq_norm (v - u))"
        by (metis Power.semiring_1_class.of_nat_power Ring_Hom.of_rat_hom.hom_mult cross3_simps(11) of_rat_of_nat_eq)
      moreover have "real_of_rat ( rat_of_nat p^2 * sq_norm (v - u)) = real_of_rat ((sq_norm_conjugate (rat_of_nat p)) * sq_norm (v - u))"
        using conjugatable_ring_1_abs_real_line_class.sq_norm_as_sq_abs[of "rat_of_nat p"] power2_eq_square[of "rat_of_nat p"] by simp
      moreover have "(sq_norm_conjugate (rat_of_nat p)) * sq_norm (v - u) = sq_norm ((rat_of_nat p) \<cdot>\<^sub>v (v-u) )"
        using sq_norm_smult_vec by metis
      moreover have "(rat_of_nat p) \<cdot>\<^sub>v (v-u) = (rat_of_nat p) \<cdot>\<^sub>v v- (rat_of_nat p) \<cdot>\<^sub>v u"
        using smult_sub_distrib_vec[OF dim_v, of u "(rat_of_nat p)"]
        using assms(2)
        using carrier_vecI by blast
      moreover have "(rat_of_nat p) \<cdot>\<^sub>v v = (map_vec rat_of_int ?iv)"
        using gen_lattice_int_gen_lattice_vec' assms v by simp
      ultimately show ?thesis by algebra
    qed
    ultimately show False
      using rhs bdd2 cInf_lower[of "real_of_rat (sq_norm ((map_vec rat_of_int ?iv) - ((rat_of_nat p)\<cdot>\<^sub>vu)))" "{(real_of_rat (sq_norm (x)))| x. x\<in> ?coset}"] by linarith
  qed
  ultimately show "?lhs = ?rhs" by simp
qed

lemma close_vector_exists:
  fixes ts :: "nat list"
  assumes "length ts = d"
  shows "\<exists>w\<in>(gen_lattice ts). sq_norm ((ts_to_u ts) - w) \<le> (of_nat ((d+1) * p^2))/2^(2*k)"
proof-
  let ?u = "(ts_to_u ts)"
  let ?basis = "gen_basis ts"
  let ?L = "gen_lattice ts"

  (*coefficients of linear combination*)
  let ?c = "\<lambda>i. (if i = d  then int_of_nat \<alpha> else (- int_of_nat (\<alpha> * ts ! i div p)))"

  let ?Lst = "(map (\<lambda>i. of_int (?c i) \<cdot>\<^sub>v (?basis ! i)) [0 ..< length ?basis])"
  let ?w = "sumlist ?Lst" (*vector close to u*)
  have l: "length ?basis = d + 1" unfolding gen_basis_def p_vecs_def by simp
  then have l2: "length ?Lst = d + 1" by auto
  have in_lattice: "?w \<in> ?L" unfolding gen_lattice_def lattice_of_def by fast
  have dim_u: "?u \<in> carrier_vec (d + 1)" using ts_to_u_carrier[of ts] assms by blast
  have dim_w: "?w \<in> carrier_vec (d + 1)" 
    using in_lattice gen_lattice_carrier[of ts] assms by blast
 
  have k_small: "k + 1 < log 2 p" using k_plus_1_lt by linarith

  have lst_i: "?Lst ! i = rat_of_int (?c i) \<cdot>\<^sub>v ?basis ! i"
    if in_range: "i\<in>{0..<d+1}" for i using in_range 
    by (smt (verit, ccfv_threshold) in_set_conv_nth l length_map map_nth nth_map set_upt)
  then have "?Lst ! i \<in> carrier_vec (d + 1)" if in_range: "i\<in>{0..<d+1}" for i
      using gen_basis_vecs_carrier[of ts i] assms in_range l by simp
  then have carr: "set ?Lst \<subseteq> carrier_vec (d + 1)" 
    using set_list_subset[of ?Lst "carrier_vec (d + 1)"] l2 by presburger
  have w_coord: "(?w $ i = rat_of_int (\<alpha> * (ts ! i) mod p))" if in_range: "i \<in> {0..<d}" for i
  proof-
    have "?w $ i = sum_list (map (\<lambda>j. (?Lst!j)$i) [0..<(length ?Lst)])" 
      using sumlist_index_commute[of ?Lst i] in_range carr by fastforce
    moreover have "\<And>j. j\<in>{0..<d+1} \<Longrightarrow> \<not> (j=i \<or> j = d) \<Longrightarrow> ?Lst!j$i = 0"
    proof-
      fix j
      assume j_in_range: "j\<in>{0..<d+1}"
      assume "\<not> (j=i \<or> j = d)"
      then have "j \<noteq> i \<and> j \<noteq> d" using j_in_range by argo
      then have off_diag: "j \<noteq> i \<and> j \<in> {0..<d}" using j_in_range by fastforce
      have dim_basis: "dim_vec (?basis ! j) = (d + 1)" 
        using gen_basis_vecs_carrier[of ts j] off_diag assms by simp
      have "?Lst!j$i = (rat_of_int (?c j) \<cdot>\<^sub>v ?basis ! j)$i"
        using lst_i[of j] off_diag by simp
      also have "(rat_of_int (?c j) \<cdot>\<^sub>v ?basis ! j)$i 
                = rat_of_int (?c j) * (?basis ! j)$i"
        using dim_basis in_range by force
      also have "(?basis ! j)$i = 0" using gen_basis_units[of j i ts] off_diag in_range by simp
      finally show "?Lst!j$i = 0" by linarith
    qed
    moreover have "set [0..<(length ?Lst)] = {0..<d+1}" using l2 by auto
    ultimately have "?w $ i = sum_list (map (\<lambda>j. (?Lst!j)$i) (filter (\<lambda>j. j=i \<or> j = d) [0..<(length ?Lst)]))"
      using sum_list_map_filter[of "[0..<(length ?Lst)]" "(\<lambda>j. j=i \<or> j = d)" "(\<lambda>j. (?Lst!j)$i)"] l2 by algebra
    also have "(filter (\<lambda>j. j=i \<or> j = d) [0..<(length ?Lst)]) = [i, d]"
      using filter_or[of i d]
      by (smt (verit) atLeastLessThan_iff diff_zero filter_or in_range l2 length_upt less_add_one)
    finally have "?w $ i = sum_list (map (\<lambda>j. (?Lst!j)$i) [i, d])" by force
    then have "?w $ i = ?Lst!i$i + ?Lst!d$i" by simp
    then have "?w $ i = 
                        (rat_of_int (?c i) \<cdot>\<^sub>v ?basis ! i)$i +
                        (rat_of_int (?c d) \<cdot>\<^sub>v ?basis ! d)$i"
      using lst_i[of i] lst_i[of d] in_range by force
    also have "(rat_of_int (?c i) \<cdot>\<^sub>v ?basis ! i)$i = rat_of_int (- int_of_nat (\<alpha> * ts ! i div p)) * rat_of_nat p"
      using in_range gen_basis_vecs_carrier[of ts i] assms gen_basis_units[of i i] by force
    also have "(rat_of_int (?c d) \<cdot>\<^sub>v ?basis ! d)$i = rat_of_int (int_of_nat \<alpha>) * ?basis!d$i"
      using in_range gen_basis_vecs_carrier[of ts d] assms by simp
    also have "?basis!d$i = vec_of_list ((map of_nat ts) @ [1 / (of_nat p)]) $ i" 
      unfolding gen_basis_def p_vecs_def using gen_basis_length[of ts] by (simp add: append_Cons_nth_middle)
    also have "vec_of_list ((map of_nat ts) @ [1 / (of_nat p)]) $ i = ((map of_nat ts) @ [1 / (of_nat p)])!i" 
      by simp
    also have "((map of_nat ts) @ [1 / (of_nat p)])!i = (map of_nat ts)!i"
      using in_range assms append_Cons_nth_left[of i "(map of_nat ts)" "1 / (of_nat p)" "[]"] by auto
    also have "(map of_nat ts)!i = of_nat (ts!i)" using in_range assms by auto
    finally have "?w $ i =  rat_of_int (- int_of_nat (\<alpha> * ts ! i div p)) * rat_of_nat p
                            + rat_of_int (int_of_nat \<alpha>) * (of_nat (ts!i))" by blast
    also have "rat_of_int (- int_of_nat (\<alpha> * ts ! i div p)) * rat_of_nat p
                            + rat_of_int (int_of_nat \<alpha>) * (of_nat (ts!i))
              = rat_of_int (int_of_nat (\<alpha> * (ts!i)) - int_of_nat ((\<alpha> * ts ! i div p) *  p))"
      using int_of_nat_def by auto
    also have "rat_of_int (int_of_nat (\<alpha> * (ts!i)) - int_of_nat ((\<alpha> * ts ! i div p) *  p)) = 
              rat_of_int (\<alpha> * (ts!i) mod p)"
      by (simp add: int_of_nat_def int_ops(9) minus_div_mult_eq_mod of_nat_div)
    finally show "(?w $ i = rat_of_int (\<alpha> * (ts ! i) mod p))" by linarith
  qed
  then have coords_close: "abs((?u-?w)$i)\<le>rat_of_nat p/ rat_of_nat 2^k" if in_range: "i\<in>{0..<d+1}" for i
  proof(cases "i = d")
    case f:False
    have i_upper: "i\<in>{0..<d}" using f in_range by auto
    then have ree: "i<length(ts @ [0])" using assms by fastforce
    moreover have "?u \<in> carrier_vec (d + 1)" using ts_to_u_carrier[of ts] assms by blast
    moreover have "?w \<in> carrier_vec (d + 1)" 
      using in_lattice gen_lattice_carrier[of ts] assms by blast
    ultimately have "(?u - ?w)$i = ?u$i - ?w$i" using in_range by fastforce
    moreover have "?u$i = (map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts @ [0]) !i"
      unfolding ts_to_u_alt by fastforce
    moreover have "(map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts @ [0]) !i 
             = (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) (ts!i)" 
      using List.nth_map[of i "(ts @ [0])" "(rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p))"]
            i_upper append_Cons_nth_left[of i "map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts" 0 "[]"]
            assms ree 
      by simp
    moreover have "(rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) (ts!i) = rat_of_nat (msb_p (\<alpha> * ts!i mod p))"
      by force
    ultimately have "(?u - ?w)$i = rat_of_nat (msb_p (\<alpha> * ts!i mod p)) - rat_of_nat (\<alpha> * ts!i mod p)"
      using w_coord[of i] ree i_upper by linarith
    then have rat_of_int: "(?u - ?w)$i = rat_of_int ((int (msb_p (\<alpha> * ts!i mod p)) - int(\<alpha> * ts!i mod p)))"
      by linarith
    have "real_of_rat ((?u - ?w)$i) = real_of_int ((int (msb_p (\<alpha> * ts!i mod p)) - int(\<alpha> * ts!i mod p)))"
      using int_rat_real_casting_helper[OF rat_of_int]
      by blast
    then have "abs(real_of_rat ((?u - ?w)$i)) = \<bar>real_of_int (int (msb_p (\<alpha> * ts!i mod p)) - int (\<alpha> * ts!i mod p))\<bar>"
      by presburger
    also have "\<dots> = real_of_int \<bar>(int (msb_p (\<alpha> * ts!i mod p)) - (\<alpha> * ts!i mod p))\<bar>"
      by linarith
    finally have "abs(real_of_rat ((?u - ?w)$i)) \<le> real(p)/2^(k)"
      using msb_p_dist[of "(\<alpha> * ts!i mod p)"] by linarith
    moreover have "real(p)/2^(k) = real_of_rat((rat_of_nat p) / 2^k)"
      by (simp add: of_rat_divide of_rat_power)
    moreover have "abs(real_of_rat ((?u - ?w)$i)) = real_of_rat (abs ((?u - ?w)$i))" by simp
    ultimately have "real_of_rat (abs ((?u - ?w)$i))\<le>real_of_rat((rat_of_nat p) / 2^k)" by algebra
    then have "(abs ((?u - ?w)$i))\<le>(rat_of_nat p) / 2^k"
      using of_rat_less_eq by blast
    then show ?thesis by auto
  next
    case t:True
    have "?u \<in> carrier_vec (d + 1)" using ts_to_u_carrier[of ts] assms by blast
    moreover have "?w \<in> carrier_vec (d + 1)" 
      using in_lattice gen_lattice_carrier[of ts] assms by blast
    ultimately have "(?u - ?w)$i = ?u$i - ?w$i" using in_range by fastforce
    also have "?u$i = (map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts @ [0])!i" 
      unfolding ts_to_u_alt using t assms by auto
    also have "(map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts @ [0])!i = 0" 
      unfolding ts_to_u_def 
      using append_Cons_nth_middle[of i "(map (rat_of_nat \<circ> msb_p \<circ> (\<lambda>t. \<alpha> * t mod p)) ts)" 0 "[]"]
            t assms 
      by fastforce
    also have "?w$i = (rat_of_int (int_of_nat \<alpha>))/(rat_of_nat p)" 
      using coordinates_of_gen_lattice[of i ts "\<lambda>i. (if i = d then int_of_nat \<alpha> else - int_of_nat (\<alpha> * ts ! i div p))"]
            t assms by auto 
    finally have "(?u-?w)$i = -(rat_of_int (int_of_nat \<alpha>))/(rat_of_nat p)" by linarith
    moreover have "rat_of_int (int_of_nat \<alpha>) = rat_of_nat \<alpha>"
      using int_of_nat_def by fastforce
    moreover have "\<alpha> < p" using \<alpha> by auto
    ultimately have "abs((?u-?w)$i) \<le> 1" by force
    moreover have "1 \<le> rat_of_nat p / rat_of_nat 2^k"
    proof-
      have "k < log 2 p" using k_small by linarith
      then have "2 powr k < 2 powr (log 2 p)" by force
      then have "2^k < p" using powr_realpow[of 2 k] p prime_gt_0_nat[of p] by force
      then show "1 \<le> rat_of_nat p / rat_of_nat 2^k" by force
    qed
    ultimately show ?thesis by order
  qed
  define Lst where "Lst = (list_of_vec (?u - ?w))"
  have "Lst!i = (?u - ?w)$i" if "i\<in>{0..<d+1}" for i
    using dim_u dim_w l list_of_vec_index unfolding Lst_def by blast
  then have abs_small: "abs(Lst!i) \<le> rat_of_nat p / rat_of_nat 2^k" if in_range: "i\<in>{0..<d+1}" for i
    using in_range coords_close by presburger
  then have small_coord: "sq_norm (Lst!i) \<le> (rat_of_nat p / rat_of_nat 2^k)^2" if in_range: "i\<in>{0..<d+1}" for i
  proof-
    have "sq_norm (Lst!i) = (Lst!i) ^2"
      by (simp add: power2_eq_square)
    moreover have "(Lst!i)^2 = abs(Lst!i)^2" by auto
    moreover have "0\<le>abs(Lst!i)" by simp
    ultimately show ?thesis using abs_small[of i] in_range
      by (metis Power.linordered_semidom_class.power_mono)
  qed
  moreover have length: "length Lst = d + 1" unfolding Lst_def using dim_u dim_w by auto
  ultimately have "\<And>x. x \<in> set Lst \<Longrightarrow> sq_norm x \<le> (rat_of_nat p / rat_of_nat 2^k)^2"
  proof-
    fix x assume "x \<in> set Lst"
    then obtain "y" where x_def: "x = Lst ! y \<and> y\<in> {0..<length Lst}"
      by (metis atLeastLessThan_iff in_set_conv_nth le0)
    then have "sq_norm (Lst ! y) \<le> (rat_of_nat p / rat_of_nat 2^k)^2"
      using length small_coord[of y] by argo
    then show "sq_norm x \<le> (rat_of_nat p / rat_of_nat 2^k)^2" using x_def by blast 
  qed
  moreover have "sq_norm (?u - ?w) = sum_list (map sq_norm (list_of_vec (?u - ?w)))" 
    using sq_norm_vec_def[of "?u - ?w"] by fast
  ultimately have "sq_norm (?u - ?w) \<le> sum_list (map (\<lambda>x. (rat_of_nat p / rat_of_nat 2^k)^2) (list_of_vec (?u - ?w)))"
    unfolding Lst_def using sum_list_mono[of "(list_of_vec (?u - ?w))" "sq_norm" "(\<lambda>x. (rat_of_nat p / rat_of_nat 2^k)^2)"]
    by argo
  also have "sum_list (map (\<lambda>x. (rat_of_nat p / rat_of_nat 2^k)^2) (list_of_vec (?u - ?w))) 
              = rat_of_nat (d + 1) * (rat_of_nat p / rat_of_nat 2^k)^2"
    using length sum_list_triv[of "(rat_of_nat p / rat_of_nat 2^k)^2" "(list_of_vec (?u - ?w))"]
    unfolding Lst_def
    by argo
  finally have "sq_norm (?u - ?w) \<le> rat_of_nat (d + 1) * (rat_of_nat p / rat_of_nat 2^k)^2"
    by blast
  also have "rat_of_nat (d + 1) * (rat_of_nat p / rat_of_nat 2^k)^2 
      = rat_of_nat (d + 1) * ((rat_of_nat p)^2 / (rat_of_nat 2^k)^2 )"
    by (simp add: power_divide)
  also have "rat_of_nat (d + 1) * ((rat_of_nat p)^2 / (rat_of_nat 2^k)^2 ) 
      = (rat_of_nat (d + 1) * ((rat_of_nat p)^2)) / (rat_of_nat 2^k)^2"
    by simp
  also have "(rat_of_nat (d + 1) * ((rat_of_nat p)^2)) / (rat_of_nat 2^k)^2 
      = rat_of_nat ((d + 1) * p^2) / ((2^k)^2)"
    by (metis Power.semiring_1_class.of_nat_power of_nat_numeral of_nat_simps(5))
  also have "rat_of_nat ((d + 1) * p^2) / ((2^k)^2) = rat_of_nat ((d + 1) * p^2) / ((2^(2*k)))"
    by (simp add: power_even_eq)
  finally show ?thesis using in_lattice by force
qed

lemma gen_lattice_dim:
  assumes "ts \<in> set_pmf ts_pmf"
  assumes "v \<in> gen_lattice ts"
  shows "dim_vec v = d + 1"
  using assms set_pmf_ts carrier_dim_vec gen_lattice_carrier gen_basis_carrier
  unfolding gen_lattice_def lattice_of_def
  by fast

lemma vec_class_union:
  fixes ts :: "nat list"
  assumes "ts \<in> set_pmf ts_pmf"
  defines "L \<equiv> gen_lattice ts"
  shows "L = \<Union>{vec_class ts \<beta> | \<beta>. True}"
proof safe
  let ?\<B> = "gen_basis ts"
  have length_\<B>: "length ?\<B> = d + 1" using gen_basis_length .
  have length_ts: "length ts = d" using assms(1) set_pmf_ts by blast
  fix x assume *: "x \<in> L"
  then obtain cs where cs: "x = sumlist (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i) [0..<length ?\<B>])"
    unfolding L_def gen_lattice_def using in_latticeE by blast
  define xs where "xs \<equiv> (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i) [0..<length ?\<B>])"
  have x: "x = sumlist xs" unfolding xs_def cs by blast

  define \<beta> where "\<beta> \<equiv> cs d"
  have "x \<in> vec_class ts \<beta>"
  proof-
    let ?I = "[0..<length ?\<B> - 1]"
    define as where "as \<equiv> (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i) [0..<length ?\<B> - 1])"
    define bs where "bs \<equiv> (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i) [length ?\<B> - 1])"
    define a where "a \<equiv> sumlist as"
    define b where "b \<equiv> sumlist bs"
    have "\<forall>i < length ?\<B>. ?\<B>!i \<in> carrier_vec (d + 1)"
      using gen_basis_carrier length_ts nth_mem by blast
    hence c_\<B>_dims: "\<forall>i < length ?\<B>. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i \<in> carrier_vec (d + 1)" by blast
    hence as_dims: "set as \<subseteq> carrier_vec (d + 1)" unfolding as_def by auto
    have bs_dims: "set bs \<subseteq> carrier_vec (d + 1)"
      apply (simp add: bs_def)
      using c_\<B>_dims by (simp add: length_\<B>)

    have a_carr: "a \<in> carrier_vec (d + 1)" using a_def as_dims sumlist_carrier by presburger
    moreover have b_carr: "b \<in> carrier_vec (d + 1)" using b_def bs_dims sumlist_carrier by blast
    ultimately have ab_comm: "a + b = b + a" using a_ac(2) a_carr b_carr by presburger

    have "b = sumlist [(of_int (cs (length ?\<B> - 1)) \<cdot>\<^sub>v ?\<B>!(length ?\<B> - 1))]"
      unfolding b_def bs_def by force
    hence b: "b = (of_int (cs (length ?\<B> - 1)) \<cdot>\<^sub>v ?\<B>!(length ?\<B> - 1))"
      by (metis cV diff_add_inverse2 gen_basis_carrier length_\<B> length_ts less_add_one local.M.add.l_cancel_one local.M.add.one_closed nth_mem smult_closed sum_simp sumlist_Cons sumlist_Nil)

    have "x = a + b"
    proof-
      have "xs = as @ bs" by (simp add: length_\<B> xs_def as_def bs_def)
      thus ?thesis using sumlist_append[OF as_dims bs_dims] unfolding x a_def b_def by blast
    qed
    hence 1: "x = b + a" using ab_comm by blast
    have 2: "a = lincomb_list (rat_of_int \<circ> cs) p_vecs" (is "a = ?rhs")
    proof-
      have "\<forall>i < length p_vecs. p_vecs!i = ?\<B>!i"
        unfolding gen_basis_def using length_p_vecs by (simp add: append_Cons_nth_left)
      hence "\<forall>i < length p_vecs. of_int (cs i) \<cdot>\<^sub>v p_vecs ! i = of_int (cs i) \<cdot>\<^sub>v ?\<B>!i"
        by presburger
      hence "(map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v p_vecs ! i) [0..<length p_vecs])
          = (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i) [0..<length p_vecs])"
        by simp
      moreover have "?rhs = sumlist (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v p_vecs ! i) [0..<length p_vecs])"
        using lincomb_list_def[of "rat_of_int \<circ> cs" p_vecs] by simp
      ultimately have "?rhs = sumlist (map (\<lambda>i. of_int (cs i) \<cdot>\<^sub>v ?\<B>!i) [0..<length p_vecs])"
        by argo
      thus ?thesis unfolding a_def as_def length_\<B> length_p_vecs by force
    qed
    have 3: "b = rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts"
    proof
      show dims: "dim_vec b = dim_vec (rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts)"
        using b_carr length_ts t_vec_dim by auto
      show "\<And>i. i < dim_vec (rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts) \<Longrightarrow> b $ i = (rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts) $ i"
      proof-
        fix i assume *: "i < dim_vec (rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts)"
        show "b $ i = (rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts) $ i"
        proof(cases "i = d")
          case True
          hence "b$i = (of_int (cs (length ?\<B> - 1)) \<cdot>\<^sub>v ?\<B>!(length ?\<B> - 1))$i" unfolding b by blast
          also have "\<dots> = (of_int (cs (length ?\<B> - 1)) * (?\<B>!(length ?\<B> - 1))$i)"
            using dims * b by auto
          also have "\<dots> = (of_int (cs (length ?\<B> - 1)) * (last ?\<B>)$i)"
            by (metis length_\<B> True last_conv_nth length_0_conv less_add_one not_less0)
          also have "\<dots> = (of_int (cs (length ?\<B> - 1)) * (1 / of_nat p))"
            using length_ts by (simp add: gen_basis_def True append_Cons_nth_middle)
          also have "\<dots> = of_int \<beta> / of_nat p" by (simp add: \<beta>_def length_\<B>)
          finally show ?thesis
            by (metis t_vec_def List.list.discI List.list.size(4) One_nat_def \<beta>_def b diff_add_inverse2 gen_basis_def last_conv_nth last_snoc length_0_conv length_\<B> length_ts)
        next
          case False
          hence "i < d"
            by (metis "*" Suc_eq_plus1 b_carr carrier_vecD dims less_Suc_eq)
          hence "(?\<B>!d)$i = of_nat (ts!i)"
            by (simp add: gen_basis_def append_Cons_nth_left append_Cons_nth_middle length_p_vecs length_ts)
          thus ?thesis
            apply (simp add: b length_\<B> t_vec_def \<beta>_def)
            by (metis gen_basis_def length_p_vecs nth_append_length)
        qed
      qed
    qed
    have "x = (rat_of_int \<beta> \<cdot>\<^sub>v t_vec ts) + (lincomb_list (rat_of_int \<circ> cs) p_vecs)"
      unfolding 1 2 3 by blast
    thus ?thesis unfolding vec_class_def by blast
  qed
  thus "x \<in> \<Union>{vec_class ts \<beta> | \<beta>. True}" by blast
next
  fix x \<beta>
  assume "x \<in> vec_class ts \<beta>"
  then obtain cs where cs: "x = of_int \<beta> \<cdot>\<^sub>v t_vec ts + lincomb_list (of_int \<circ> cs) p_vecs"
    unfolding vec_class_def by blast
  define cs' where "cs' = (\<lambda>x. if x < d then cs x else \<beta>)"

  have "x = sumlist (map (\<lambda>i. rat_of_int (cs' i) \<cdot>\<^sub>v gen_basis ts ! i) [0..<length (gen_basis ts)])"
    (is "x = ?sum")
  proof-
    let ?f' = "\<lambda>i. rat_of_int (cs' i) \<cdot>\<^sub>v gen_basis ts ! i"
    let ?f = "\<lambda>i. rat_of_int (cs i) \<cdot>\<^sub>v p_vecs ! i"
    let ?I = "[0..<length (gen_basis ts)]"
    let ?I1 = "[0..<length (gen_basis ts) - 1]"
    let ?I2 = "[length (gen_basis ts) - 1]"

    have length_ts: "length ts = d" using assms(1) set_pmf_ts by blast
    have I: "?I = ?I1 @ ?I2" using gen_basis_length by auto
    have I_dims: "set (map ?f' ?I) \<subseteq> carrier_vec (d + 1)"
      using gen_basis_carrier[OF length_ts] gen_basis_length[of ts] by fastforce
    have I1_dims: "set (map ?f' ?I1) \<subseteq> carrier_vec (d + 1)" using I I_dims by simp
    have I2_dims: "set (map ?f' ?I2) \<subseteq> carrier_vec (d + 1)" using I I_dims by simp

    have sum1_dim: "sumlist (map ?f' ?I1) \<in> carrier_vec (d + 1)"
      using I1_dims sumlist_carrier by blast
    have sum2_dim: "sumlist (map ?f' ?I2) \<in> carrier_vec (d + 1)"
      using I2_dims sumlist_carrier by blast

    from I have "map ?f' ?I = (map ?f' ?I1) @ (map ?f' ?I2)" by auto
    hence "sumlist (map ?f' ?I) = sumlist (map ?f' ?I1) + sumlist (map ?f' ?I2)"
      using sumlist_append[of "map ?f' ?I1" "map ?f' ?I2"] I1_dims I2_dims by argo
    hence "sumlist (map ?f' ?I) = sumlist (map ?f' ?I2) + sumlist (map ?f' ?I1)"
      using sum1_dim sum2_dim a_ac(2) by presburger
    moreover have "sumlist (map ?f' ?I1) = lincomb_list (of_int \<circ> cs) p_vecs"
    proof-
      have "\<forall>i < d. gen_basis ts ! i = p_vecs ! i"
        by (simp add: nth_append length_p_vecs gen_basis_def)
      moreover have "\<forall>i < d. cs i = cs' i" using cs'_def by presburger
      ultimately have "\<forall>i < d. ?f' i = ?f i" by presburger
      hence "map ?f' [0..<d] = map ?f [0..<d]" by fastforce
      hence "sumlist (map ?f' [0..<d]) = sumlist (map ?f [0..<d])" by argo
      thus ?thesis unfolding lincomb_list_def length_p_vecs gen_basis_length by auto
    qed
    moreover have "sumlist (map ?f' ?I2) = of_int \<beta> \<cdot>\<^sub>v t_vec ts"
    proof-
      have "sumlist (map ?f' ?I2) = ?f' (length (gen_basis ts) - 1)"
        unfolding sumlist_def
        using Suc_eq_plus1 I assms(1) diff_add_inverse2 diff_diff_left diff_zero gen_basis_length gen_basis_vecs_carrier length_upt lessI mem_Collect_eq nth_append_length nth_mem right_zero_vec set_pmf_ts set_upt
        by auto
      also have "\<dots> = of_int (cs' d) \<cdot>\<^sub>v gen_basis ts ! d" by (simp add: gen_basis_length)
      also have "\<dots> = of_int \<beta> \<cdot>\<^sub>v gen_basis ts ! d" unfolding cs'_def by auto
      also have "\<dots> = of_int \<beta> \<cdot>\<^sub>v t_vec ts"
        by (simp add: append_Cons_nth_middle length_p_vecs t_vec_def gen_basis_def)
      finally show ?thesis .
    qed
    ultimately show ?thesis using cs by argo
  qed
  thus "x \<in> L" unfolding L_def vec_class_def gen_lattice_def lattice_of_def by blast
qed

lemma vec_class_mod_p_union:
  fixes ts :: "nat list"
  assumes "ts \<in> set_pmf ts_pmf"
  defines "L \<equiv> gen_lattice ts"
  shows "L = \<Union>{vec_class_mod_p ts \<beta> | \<beta>. \<beta> \<in> {0..<p::int}}" (is "_ = ?rhs")
proof
  show "L \<subseteq> ?rhs"
  proof
    fix x assume "x \<in> L"
    then obtain \<beta> where \<beta>: "x \<in> vec_class ts \<beta>"
      using vec_class_union[OF assms(1)] unfolding L_def by blast
    define \<beta>\<^sub>p where "\<beta>\<^sub>p \<equiv> \<beta> mod p"
    hence "\<beta>\<^sub>p \<in> {0..<p::int}"
      by (metis Nat.bot_nat_0.not_eq_extremum mod_ident_iff mod_mod_trivial not_prime_0 of_nat_0_less_iff p)
    moreover have "x \<in> vec_class_mod_p ts \<beta>\<^sub>p"
      unfolding vec_class_mod_p_def \<beta>\<^sub>p_def
      by (smt (verit, best) UnionI \<beta> cong_mod_right cong_refl mem_Collect_eq)
    ultimately show "x \<in> ?rhs" by blast
  qed
  show "?rhs \<subseteq> L" using vec_class_union[OF assms(1)] unfolding L_def vec_class_mod_p_def by blast
qed

subsubsection "dist-p definition and lemmas"

definition dist_p :: "int \<Rightarrow> int \<Rightarrow> int" where 
  "dist_p i j = Inf {abs (i - j + z * (of_nat p)) | z. True}" 

lemma dist_p_well_defined:
  fixes i :: int
  fixes j :: int
  shows "dist_p i j \<in> {abs (i - j + z * (of_nat p)) | z. True}" (is "_ \<in> ?S")
proof-
  have "?S \<subseteq> \<nat>" by (smt (verit, del_insts) mem_Collect_eq range_abs_Nats range_eqI subsetI)
  moreover have "?S \<noteq> {}" by blast
  ultimately show ?thesis using nat_subset_inf unfolding dist_p_def by algebra
qed

lemma dist_p_set_bdd_below:
  fixes i j :: int
  shows "\<forall>x \<in> {abs (i - j + z * (of_nat p)) | z. True}. 0 \<le> x" 
  by force

lemma dist_p_le:
  fixes i j :: int
  shows "\<forall>x \<in> {abs (i - j + z * (of_nat p)) | z. True}. dist_p i j \<le> x" (is "\<forall>x \<in> ?S. _")
proof
  fix x assume *: "x \<in> ?S"
  have "bdd_below ?S" using dist_p_set_bdd_below by fast
  thus "dist_p i j \<le> x"
    unfolding dist_p_def using dist_p_well_defined[of i j] cInf_lower[of x ?S] * by fast
qed

lemma dist_p_equiv:
  fixes i :: int
  fixes j :: int
  shows "[dist_p i j = i - j] (mod p) \<or> [dist_p i j = j - i] (mod p)"
proof-
  let ?S = "{abs (i - j + z * (of_nat p)) | z. True}"
  have "[x = i - j] (mod p) \<or> [x = j - i] (mod p)" if x_in: "x \<in> ?S" for x
  proof-
    obtain "z" where "x = abs (i - j + z * (of_nat p))" using x_in by blast
    then have "x = i - j + z * (of_nat p) \<or> x = - (i - j + z * (of_nat p))" by linarith
    then show ?thesis
    proof(rule disjE)
      assume left: "x = i - j + z * (of_nat p)"
      then have "x - (i - j) = z * (of_nat p)" by force
      also have "[z * (of_nat p) = 0] (mod p)" using cong_mult_self_right[of z "of_nat p"] by blast
      finally have "[x - (i - j) = 0] (mod p)" by blast
      then have "[x = i - j] (mod p)" using cong_diff_iff_cong_0[of x "i - j" "int p"] by presburger
      then show ?thesis by blast
    next
      assume right: "x = - (i - j + z * (of_nat p))"
      then have "x = j - i - z * (of_nat p)" by linarith
      then have "x - (j - i) = - z * (of_nat p)" by force
      also have "[- z * (of_nat p) = 0] (mod p)" using cong_mult_self_right[of "-z" "of_nat p"] by blast
      finally have "[x - (j - i) = 0] (mod p)" by blast
      then have "[x = j - i] (mod p)" using cong_diff_iff_cong_0[of x "j - i" "int p"] by presburger
      then show ?thesis by blast
    qed
  qed
  then show ?thesis using dist_p_well_defined[of i j] by presburger
qed

lemma dist_p_equiv':
  fixes i :: int
  fixes j :: int
  shows "dist_p i j = min ((i - j) mod p) ((j - i) mod p)"
proof-
  let ?S = "{abs (i - j + z * (of_nat p)) | z. True}"
  have "[dist_p i j = i - j] (mod p) \<or> [dist_p i j = j - i] (mod p)" using dist_p_equiv .
  moreover have "0 \<le> dist_p i j" using dist_p_well_defined[of i j] by force
  moreover have "dist_p i j < p"
  proof(rule ccontr)
    obtain k where k: "dist_p i j = \<bar>i - j + k * int p\<bar>"
      using dist_p_well_defined[of i j] by blast
    hence k_min: "(\<forall>k'. dist_p i j \<le> \<bar>i - j + k' * int p\<bar>)"
      using dist_p_well_defined[of i j] by (metis (mono_tags, lifting) dist_p_le mem_Collect_eq)

    assume "\<not> dist_p i j < int p"
    hence *: "dist_p i j \<ge> p" by linarith
    show False
    proof(cases "i - j + k * int p \<ge> 0")
      case True
      hence "dist_p i j = i - j + k * p" using k by fastforce
      moreover then have "0 \<le> i - j + k * p - p" using * by simp
      moreover then have "\<dots> = \<bar>i - j + (k - 1) * p\<bar>" by (simp add: left_diff_distrib')
      moreover have "p > 0" using p prime_gt_0_nat by blast
      ultimately have "dist_p i j > \<bar>i - j + (k - 1) * p\<bar>" by fastforce
      moreover have "dist_p i j \<le> \<bar>i - j + (k - 1) * p\<bar>" using k_min by blast
      ultimately show False by fastforce
    next
      case False
      hence "dist_p i j = - i + j - k * p" using k by linarith
      moreover then have "0 \<le> - i + j - k * p - p" using * by simp
      moreover then have "\<dots> = \<bar>i - j + (k + 1) * p\<bar>"
        by (smt (verit, ccfv_SIG) left_diff_distrib' mult_cancel_right2)
      moreover have "p > 0" using p prime_gt_0_nat by blast
      ultimately have "dist_p i j > \<bar>i - j + (k + 1) * p\<bar>" by fastforce
      moreover have "dist_p i j \<le> \<bar>i - j + (k + 1) * p\<bar>" using k_min by blast
      ultimately show False by fastforce
    qed
  qed
  ultimately have *: "dist_p i j = (i - j) mod p \<or> dist_p i j = (j - i) mod p"
    by (simp add: Cong.unique_euclidean_semiring_class.cong_def)

  have "(i - j) mod p \<in> ?S"
  proof-
    obtain k :: int where "(i - j) mod p = (i - j) + k * p"
      by (metis mod_eqE mod_mod_trivial mult_of_nat_commute)
    moreover have "(i - j) mod p \<ge> 0" using prime_gt_1_nat[OF p] by simp
    ultimately have "(i - j) mod p = \<bar>i - j + k * p\<bar>" by force
    thus ?thesis by auto
  qed
  moreover have "(j - i) mod p \<in> ?S"
  proof-
    obtain k :: int where "(j - i) mod p = (j - i) + k * p"
      by (metis mod_eqE mod_mod_trivial mult_of_nat_commute)
    hence "(j - i) mod p = - ((i - j) - k * p)" by simp
    moreover have "(j - i) mod p \<ge> 0" using prime_gt_1_nat[OF p] by simp
    ultimately have "(j - i) mod p = \<bar>i - j - k * p\<bar>" by force
    then obtain k' :: int where "(j - i) mod p = \<bar>(i - j) + k' * p\<bar>" using that[of "- k"] by force
    thus ?thesis by blast
  qed
  ultimately have "dist_p i j \<le> (i - j) mod p \<and> dist_p i j \<le> (j - i) mod p"
    by (metis dist_p_le)
  thus ?thesis using * by linarith
qed

lemma dist_p_equiv'':
  fixes i :: int
  fixes j :: int
  shows "dist_p i j = ((i - j) mod p) \<or> dist_p i j = ((j - i) mod p)"
  using dist_p_equiv'[of i j] by linarith

lemma dist_p_instances_help:
  fixes i :: int
  fixes j :: int
  fixes dist :: int
  assumes "coprime (i - j) p"
  shows "card {t \<in> {1..<p}. (dist_p (t*i) (t*j)) = dist} \<le> 2"
proof-
  obtain ij_inv where ij_inv: "[(i-j)*ij_inv = 1] (mod p)" 
    using assms(1) cong_solve_coprime_int[of "(i - j)" p] by auto
  have "coprime (j - i) p"
    by (meson assms(1) coprimeE coprimeI dvd_diff_commute)
  then obtain ji_inv where ji_inv: "[(j - i)*ji_inv = 1] (mod p)" 
    using cong_solve_coprime_int[of "(j - i)" p] by auto
  have disj: "[t = dist*ij_inv] (mod p) \<or> [t = dist*ji_inv] (mod p)"
      if dist_eq: "(dist_p (t*i) (t*j)) = dist"
      for t::int
  proof-
    have "[dist = (t*i - t*j) ] (mod p) \<or> [dist = t*j - t*i] (mod p)"
      using dist_p_equiv[of "t*i" "t*j"] dist_eq by simp
    then show ?thesis 
    proof(rule disjE)
      assume left: "[dist = (t*i - t*j) ] (mod p)"
      have "t * (i - j) = t * i - t * j"
        using int_distrib(4) by auto
      then have "[t * (i - j) = t * i - t * j] (mod p)" by simp
      then have "[dist = t * (i - j)] (mod p)" 
        using cong_trans[of "t * (i - j)" "t * i - t * j" p dist] left cong_sym
        by blast
      then have "[dist * ij_inv = t * (i - j) * ij_inv] (mod p)"
        using cong_mult[of dist "t * (i - j)" p ij_inv] by force
      moreover have "[t * (i - j) * ij_inv = t * ((i - j) * ij_inv)] (mod p)"
        by (simp add: more_arith_simps(11))
      moreover have "[t * ((i - j) * ij_inv) = t] (mod p)" 
        using ij_inv cong_mult[of "t" t p "(i - j) * ij_inv" 1] by auto
      ultimately show ?thesis using cong_trans cong_sym by meson
    next
      assume right: "[dist = t*j - t*i] (mod p)"
      have "t * (j - i) = t * j - t * i"
        using int_distrib(4) by auto
      then have "[t * (j - i) = t * j - t * i] (mod p)" by simp
      then have "[dist = t * (j - i)] (mod p)" 
        using cong_trans[of "t * (j - i)" "t * j - t * i" p dist] right cong_sym
        by blast
      then have "[dist * ji_inv = t * (j - i) * ji_inv] (mod p)"
        using cong_mult[of dist "t * (j - i)" p ji_inv] by force
      moreover have "[t * (j - i) * ji_inv = t * ((j - i) * ji_inv)] (mod p)"
        by (simp add: more_arith_simps(11))
      moreover have "[t * ((j - i) * ji_inv) = t] (mod p)" 
        using ji_inv cong_mult[of "t" t p "(j - i) * ji_inv" 1] by auto
      ultimately show ?thesis using cong_trans cong_sym by meson
    qed
  qed 
  define S1 where "S1 = ({t \<in> {1..<p}. (dist_p (t*i) (t*j)) = dist} \<inter> {t\<in> {1..<p}. [t = dist*ij_inv] (mod p)})"
  define S2 where "S2 = ({t \<in> {1..<p}. (dist_p (t*i) (t*j)) = dist} \<inter> {t\<in> {1..<p}. \<not> ([t = dist*ij_inv] (mod p))})"
  have "{t \<in> {1..<p}. (dist_p (t*i) (t*j)) = dist} = S1 \<union> S2"
    unfolding S1_def S2_def by blast
  moreover have card1: "card(S1) \<le> 1"
  proof(rule ccontr)
    assume "\<not> card S1 \<le> 1"
    hence *: "card S1 \<ge> 2" by simp
    obtain t1 t2 where ts: "t1 \<noteq> t2 \<and> t1 \<in> S1 \<and> t2 \<in> S1"
    proof-
      obtain t1 S1' where t1: "t1 \<in> S1 \<and> S1' = S1 - {t1}" using * by fastforce
      hence "card S1' \<ge> 1" using * by fastforce
      then obtain t2 where "t2 \<in> S1'" by fastforce
      hence "t1 \<noteq> t2 \<and> t1 \<in> S1 \<and> t2 \<in> S1" using t1 by blast
      thus ?thesis using that by blast
    qed
    have 1: "[t1 = dist*ij_inv] (mod p)" using ts unfolding S1_def by simp
    have 2: "[t2 = dist*ij_inv] (mod p)" using ts unfolding S1_def by simp
    have "t1<p" using ts unfolding S1_def by simp
    moreover have "0\<le>t1" using ts unfolding S1_def by simp
    moreover have "t2<p" using ts unfolding S1_def by simp
    moreover have "0\<le>t2" using ts unfolding S1_def by simp
    moreover have "[int t1 = int t2] (mod p)" 
      using 1 2 cong_sym[of t2 "dist*ij_inv"  p] cong_trans[of t1 "dist*ij_inv" p t2] 
      by blast
    ultimately have "int t1 = int t2" 
      using cong_less_imp_eq_int[of "int t1" p "int t2"] by auto
    then have "t1 = t2" by simp
    then show False using ts by auto
  qed
  moreover have "card(S2) \<le> 1"
  proof(rule ccontr)
    assume "\<not> card S2 \<le> 1"
    hence *: "card S2 \<ge> 2" by simp
    obtain t1 t2 where ts: "t1 \<noteq> t2 \<and> t1 \<in> S2 \<and> t2 \<in> S2"
    proof-
      obtain t1 S2' where t1: "t1 \<in> S2 \<and> S2' = S2 - {t1}" using * by fastforce
      hence "card S2' \<ge> 1" using * by fastforce
      then obtain t2 where "t2 \<in> S2'" by fastforce
      hence "t1 \<noteq> t2 \<and> t1 \<in> S2 \<and> t2 \<in> S2" using t1 by blast
      thus ?thesis using that by blast
    qed
    have "\<not>[t1 = dist*ij_inv] (mod p)" using ts unfolding S2_def by simp
    then have 1: "[t1 = dist*ji_inv] (mod p)" using disj ts unfolding S2_def by blast
    have "\<not>[t2 = dist*ij_inv] (mod p)" using ts unfolding S2_def by simp
    then have 2: "[t2 = dist*ji_inv] (mod p)" using disj ts unfolding S2_def by blast
    have "t1<p" using ts unfolding S2_def by simp
    moreover have "0\<le>t1" using ts unfolding S2_def by simp
    moreover have "t2<p" using ts unfolding S2_def by simp
    moreover have "0\<le>t2" using ts unfolding S2_def by simp
    moreover have "[int t1 = int t2] (mod p)" 
      using 1 2 cong_sym[of t2 "dist*ji_inv"  p] cong_trans[of t1 "dist*ji_inv" p t2] 
      by blast
    ultimately have "int t1 = int t2" 
      using cong_less_imp_eq_int[of "int t1" p "int t2"] by auto
    then have "t1 = t2" by simp
    then show False using ts by auto
  qed
  ultimately show ?thesis using card_Un_le[of S1 S2] by simp
qed

lemma dist_p_nat:
  fixes i :: int
  fixes j :: int
  shows "dist_p i j \<in> \<nat>"
proof-
  let ?S = "{abs (i - j + z * (of_nat p)) | z. True}"
  have "?S \<subseteq> \<nat>" by (smt (verit, del_insts) mem_Collect_eq range_abs_Nats range_eqI subsetI)
  then show ?thesis using dist_p_well_defined[of i j] by blast
qed

lemma dist_p_nat':
  shows "nat (dist_p i j) = dist_p i j"
  by (metis dist_p_nat[of i j] Nats_induct int_eq_iff)

lemma dist_p_instances:
  fixes i :: int
  fixes j :: int
  fixes bound :: rat
  assumes "i \<noteq> j"
  assumes "coprime (i - j) p"
  assumes "0 < bound"
  shows "rat_of_nat (card {t \<in> {1..<p}. rat_of_int (dist_p (t*i) (t*j)) \<le> bound}) \<le> 2*bound"
proof-
  let ?f = "\<lambda>t. (dist_p (t*i) (t*j))"
  define S where  "S = {t \<in> {1..<p}. rat_of_int (?f t) \<le> bound}"
  have "S = {t \<in> {1..<p}. rat_of_int (?f t) \<le> bound \<and> (?f t) \<in> \<nat>} 
          \<union> {t \<in> {1..<p}. rat_of_int (?f t) \<le> bound \<and> (?f t) \<notin> \<nat>}"
    unfolding S_def by fastforce
  moreover have "{t \<in> {1..<p}. rat_of_int (?f t) \<le> bound \<and> (?f t) \<notin> \<nat>} = {}"
    using dist_p_nat by force
  ultimately have "S = {t \<in> {1..<p}. rat_of_int (?f t) \<le> bound \<and> (?f t) \<in> \<nat>}" 
    by fast
  moreover have "(rat_of_int (?f t) \<le> bound \<and> (?f t) \<in> \<nat>)
      \<longleftrightarrow> ((?f t) \<in> {1..<floor(bound)+1})" (is "?P = ?Q") if "t \<in> {1..<p}" for t
  proof
    assume *: ?P
    hence "?f t < (floor bound) + 1" by linarith
    moreover have "1 \<le> ?f t"
    proof-
      have "\<forall>x \<in> {abs ((t*i) - (t*j) + z * (of_nat p)) | z. True}. 1 \<le> x"
      proof
        fix x assume "x \<in> {abs ((t*i) - (t*j) + z * (of_nat p)) | z. True}"
        then obtain z where z: "x = abs ((t*i) - (t*j) + z * (of_nat p))" by blast
        moreover have "t \<noteq> 0" using that by force
        ultimately have x: "x = abs(t * (i - j) + z * p)" using int_distrib(4) by presburger
        have "x \<noteq> 0"
        proof-
          have "coprime t p"
            unfolding coprime_def'
          proof clarify
            fix r assume *: "r dvd t" "r dvd p"
            have "is_unit r \<or> r = p"
              by (metis *(2) One_nat_def dvd_1_iff_1 p prime_nat_iff)
            moreover have "r \<noteq> p" using *(1) that by auto
            ultimately show "is_unit r" by blast
          qed
          moreover have "coprime (i - j) p" using assms(2) .
          ultimately have "coprime (t * (i - j)) p" using p by auto
          hence "\<not> (p dvd (t * (i - j)))"
            by (metis coprime_def' One_nat_def Suc_0_not_prime_nat abs_of_nat dvd_refl int_ops(2) nat_int p zdvd1_eq)
          hence "t * (i - j) \<noteq> - z * p" by fastforce
          hence "t * (i - j) + z * p \<noteq> 0" by fastforce
          thus ?thesis unfolding x by simp
        qed
        moreover have "x \<ge> 0" using z by force
        ultimately show "1 \<le> x" by linarith
      qed
      thus ?thesis using dist_p_well_defined[of "t*i" "t*j"] unfolding dist_p_def by blast
    qed
    ultimately show ?Q by force
  next
    assume ?Q
    thus ?P by (simp add: dist_p_nat le_floor_iff)
  qed
  ultimately have "S = {t \<in> {1..<p}. ((?f t) \<in> {1..<floor(bound)+1})}" by blast
  moreover have "{1..<floor(bound)+1} = \<Union>{{i}| i. i\<in>{1..<floor(bound)+1}}" by blast
  ultimately have "S = \<Union>{{t \<in> {1..<p}. (?f t) \<in> {dist}} |dist. dist\<in>{1..<floor(bound)+1}}"
    by blast
  then have "card S \<le> sum card {{t \<in> {1..<p}. (?f t) \<in> {dist}} |dist. dist\<in>{1..<floor(bound)+1}}"
    using card_Union_le_sum_card[of "{{t \<in> {1..<p}. (?f t) \<in> {dist}} |dist. dist\<in>{1..<floor(bound)+1}}"] 
    by blast
  moreover have "card s \<le> 2" if s_def: "s \<in> {{t \<in> {1..<p}. (?f t) \<in> {dist}} |dist. dist\<in>{1..<floor(bound)+1}}" for s
  proof-
    obtain "dist" where "s = {t \<in> {1..<p}. (?f t) \<in> {dist}}"
      using s_def by blast
    then show ?thesis using dist_p_instances_help[of i j dist] assms(2) by auto
  qed                               
  ultimately have "card S \<le> sum (\<lambda>s. 2) {{t \<in> {1..<p}. (?f t) \<in> {dist}} | dist. dist \<in> {1..<floor(bound)+1}}"
    using sum_mono[of "{{t \<in> {1..<p}. (?f t) \<in> {dist}} |dist. dist\<in>{1..<floor(bound)+1}}" "card" "(\<lambda>s. 2)"]
    by force
  moreover have "sum (\<lambda>s. 2) {{t \<in> {1..<p}. (?f t) \<in> {dist}} | dist. dist \<in> {1..<floor(bound)+1}} 
          = 2 * card{{t \<in> {1..<p}. (?f t) \<in> {dist}} | dist. dist \<in> {1..<floor(bound)+1}}" by force
  moreover have "card{{t \<in> {1..<p}. (?f t) \<in> {dist}} | dist. dist \<in> {1..<floor(bound)+1}} \<le> card{1..<floor(bound)+1}"
  proof-
    have "finite{1..<floor(bound)+1}" by blast
    moreover have "(\<lambda>dist. {t \<in> {1..<p}. (?f t) \<in> {dist}}) ` {1..<floor(bound)+1} 
            = {{t \<in> {1..<p}. (?f t) \<in> {dist}} | dist. dist \<in> {1..<floor(bound)+1}}"
      by blast
    ultimately show ?thesis 
      using card_image_le[of "{1..<floor(bound)+1}" "\<lambda>dist. {t \<in> {1..<p}. (?f t) \<in> {dist}}"] 
      by algebra
  qed
  moreover have "rat_of_nat (card{1..<floor(bound)+1}) \<le> bound"
    using assms(3) by force
  ultimately show ?thesis
    using S_def mult_2 of_nat_simps(4) by auto
qed

lemma dist_p_smallest:
  fixes \<beta> ts i
  assumes "ts \<in> set_pmf ts_pmf"
  assumes "v \<in> vec_class_mod_p ts \<beta>"
  assumes "i < d"
  defines "u \<equiv> ts_to_u ts"
  shows "(of_int (dist_p (int (ts ! i) * \<beta>) (int (ts_to_as ts ! i))))\<^sup>2 \<le> ((u - v)$i)\<^sup>2"
    (is "(of_int ?d)\<^sup>2 \<le> _")
proof-
  have len_ts: "length ts = d" using assms(1) by (simp add: set_pmf_ts)
  have v_carrier: "v \<in> carrier_vec (d + 1)" using assms(2) len_ts vec_class_mod_p_carrier by blast
  have u_carrier: "u \<in> carrier_vec (d + 1)" using len_ts u_carrier u_def by blast
  obtain \<beta>' where \<beta>': "v \<in> vec_class ts \<beta>'" "[\<beta> = \<beta>'] (mod p)"
    using assms(2) unfolding vec_class_mod_p_def by blast
  let ?a = "int (ts ! i) * \<beta>"
  let ?a' = "int (ts ! i) * \<beta>'"
  let ?b = "int (ts_to_as ts ! i)"
  let ?S = "{abs (?a - ?b + z * (of_nat p)) | z. True}"
  let ?S' = "{abs (?a' - ?b + z * (of_nat p)) | z. True}"
  obtain cs where cs: "v = sumlist (map (\<lambda>i. rat_of_int (cs i) \<cdot>\<^sub>v gen_basis ts ! i) [0..<length (gen_basis ts)])"
  proof-
    have "v \<in> gen_lattice ts"
      by (smt (verit, ccfv_SIG) vec_class_mod_p_union assms(1,2) mem_Collect_eq mem_simps(9) vec_class_mod_p_def vec_class_union)
    thus ?thesis unfolding gen_lattice_def lattice_of_def using that by fast
  qed
  obtain z :: int where z: "\<bar>(u - v)$i\<bar> = of_int \<bar>?a' - ?b + z * p\<bar>"
  proof-
    have "v$i = of_int (cs d * int (ts ! i) + cs i * int p)"
      using coordinates_of_gen_lattice[of i ts cs] assms(3) len_ts unfolding cs by auto
    moreover have "u$i = of_int ?b"
      using len_ts assms(3) by (simp add: append_Cons_nth_left ts_to_as_def u_def ts_to_u_def)
    ultimately have "(u - v)$i = of_int (?b - cs d * int (ts ! i) - cs i * int p)"
      using v_carrier u_carrier assms(3) by simp
    moreover have "cs d = \<beta>'"
    proof-
      have "v$d = rat_of_int (cs d) / rat_of_nat p"
        using coordinates_of_gen_lattice[of d ts cs] len_ts unfolding cs by fastforce
      hence "rat_of_int (cs d) = v$d * (rat_of_nat p)" using p by simp
      moreover have "(v$d) = rat_of_int \<beta>' / rat_of_nat p"
        using vec_class_last[OF len_ts \<beta>'(1)] by simp
      ultimately show ?thesis using p by fastforce
    qed
    ultimately have "(u - v)$i = of_int (?b - \<beta>' * int (ts ! i) - cs i * int p)" by blast
    hence "-(u - v)$i = of_int (\<beta>' * int (ts ! i) - ?b + cs i * int p)" by auto
    moreover have "\<bar>-(u - v)$i\<bar> = \<bar>(u - v)$i\<bar>" by fastforce
    ultimately have "\<bar>(u - v)$i\<bar> = \<bar>of_int (\<beta>' * int (ts ! i) - ?b + cs i * int p)\<bar>" by presburger
    moreover have "\<bar>rat_of_int (\<beta>' * int (ts ! i) - int (ts_to_as ts ! i) + cs i * int p)\<bar>
        = rat_of_int \<bar>\<beta>' * int (ts ! i) - int (ts_to_as ts ! i) + cs i * int p\<bar>"
      by linarith
    moreover have "\<beta>' * int (ts ! i) = int (ts ! i) * \<beta>'" by simp
    ultimately show ?thesis using that[of "cs i"] by argo
  qed
  let ?c = "\<bar>?a' - ?b + z * p\<bar>"
  have "?c \<in> ?S'" by blast
  moreover have "?d = Inf ?S" by (rule dist_p_def)
  moreover have "?S = ?S'"
  proof-
    have a_a': "[?a - ?b = ?a' - ?b] (mod int p)"
      using \<beta>'(2) cong_scalar_left cong_diff cong_refl by blast
    show ?thesis using cong_set_eq[OF a_a'] .
  qed
  ultimately have "?d \<le> ?c" using dist_p_le by blast
  hence "?d\<^sup>2 \<le> ?c\<^sup>2"
    by (meson dist_p_set_bdd_below dist_p_well_defined Power.linordered_semidom_class.power_mono)
  moreover have "\<bar>(u - v)$i\<bar>\<^sup>2 = ((u - v)$i)\<^sup>2" by auto
  ultimately show ?thesis
    by (metis (mono_tags, lifting) of_int_le_of_int_power_cancel_iff of_int_power z)
qed

lemma dist_p_diff_helper:
  fixes a b b'
  assumes "b \<ge> b'"
  shows "\<bar>dist_p a b - dist_p a b'\<bar> \<le> b - b'"
proof-
  let ?d = "dist_p a b"
  let ?d' = "dist_p a b'"
  obtain k where d: "?d = \<bar>a - b + k * int p\<bar>" using dist_p_well_defined[of a b] by blast
  obtain k' where d': "?d' = \<bar>a - b' + k' * int p\<bar>" using dist_p_well_defined[of a b'] by blast
  show ?thesis
  proof(cases "?d' \<le> ?d")
    case True
    have "\<forall>z :: int. 0 \<le> \<bar>a - b + z * (of_nat p)\<bar>" by fastforce
    hence "bdd_below {\<bar>a - b + z * (of_nat p)\<bar> | z. True}" by fast
    hence "?d \<le> \<bar>a - b + k' * int p\<bar>" 
      unfolding dist_p_def
      using cInf_lower[of "\<bar>a - b + k' * int p\<bar>" "{\<bar>a - b + z * (of_nat p)\<bar> | z. True}"]
      by blast
    also have "\<dots> = \<bar>a - b' + b' - b + k' * int p\<bar>" by auto
    also have "\<dots> \<le> ?d' + \<bar>b' - b\<bar>" using d' by auto
    finally show ?thesis using True assms by simp
  next
    case False (*This case is symmetric; could possibly combine the two using triangle inequality*)
    have "\<forall>z :: int. 0 \<le> \<bar>a - b' + z * (of_nat p)\<bar>" by fastforce
    hence "bdd_below {\<bar>a - b' + z * (of_nat p)\<bar> | z. True}" by fast
    hence "?d' \<le> \<bar>a - b' + k * int p\<bar>"
      unfolding dist_p_def
      using cInf_lower[of "\<bar>a - b' + k * int p\<bar>" "{\<bar>a - b' + z * (of_nat p)\<bar> | z. True}"]
      by fast
    also have "\<dots> = \<bar>a - b + b - b' + k * int p\<bar>" by auto
    also have "\<dots> \<le> ?d + \<bar>b - b'\<bar>" using d by simp
    finally show ?thesis using False assms by simp
  qed
qed

lemma dist_p_diff:
  fixes a b b'
  shows "\<bar>dist_p a b - dist_p a b'\<bar> \<le> \<bar>b - b'\<bar>"
  apply(cases "b \<ge> b'")
   using dist_p_diff_helper[of b' b a] apply linarith
  using dist_p_diff_helper[of b b' a] by linarith

subsubsection "Uniquness lemma argument"

definition good_beta where
  "good_beta ts \<beta> \<longleftrightarrow> (\<forall>v \<in> vec_class_mod_p ts \<beta>. close_vec ts v \<longrightarrow> good_vec v)"

definition bad_beta where
  "bad_beta ts \<beta> \<longleftrightarrow> \<not> good_beta ts \<beta>"

definition some_bad_beta where
  "some_bad_beta ts \<longleftrightarrow> (\<exists>\<beta> \<in> {0..<p::int}. bad_beta ts \<beta>)"

definition bad_beta_union where
  "bad_beta_union = (\<Union>\<beta> \<in> {0..<p::int}. {ts. bad_beta ts \<beta>})"

lemma reduction_1:
  assumes "ts \<in> set_pmf ts_pmf"
  assumes "\<not> good_lattice ts"
  shows "some_bad_beta ts"
  using assms vec_class_mod_p_union set_pmf_ts
  unfolding some_bad_beta_def bad_beta_def good_beta_def good_lattice_def
  by blast

lemma reduction_1_pmf:
  "pmf sampled_lattice_good False \<le> pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (some_bad_beta ts))) True"
proof-
  have "pmf sampled_lattice_good False = pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (\<not> good_lattice ts))) True"
    unfolding sampled_lattice_good_def pmf_true_false by presburger
  also have "\<dots> \<le> pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (some_bad_beta ts))) True"
    using reduction_1 pmf_subset[of ts_pmf "\<lambda>ts. \<not> good_lattice ts" "\<lambda>ts. some_bad_beta ts"]
    by blast
  finally show ?thesis .
qed

lemma reduction_2: "{ts. some_bad_beta ts} \<subseteq> bad_beta_union"
  unfolding some_bad_beta_def bad_beta_union_def by blast

lemma reduction_2_pmf:
  "pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> {ts. some_bad_beta ts}))) True
    \<le> pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> bad_beta_union))) True"
  using reduction_2
  using pmf_subset[of ts_pmf "\<lambda>ts. ts \<in> {ts. some_bad_beta ts}" "\<lambda>ts. ts \<in> bad_beta_union"]
  by blast

lemma bad_beta_union_bound:
  "pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> bad_beta_union))) True
    \<le> (\<Sum>\<beta> \<in> {0..<p::int}. pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> {ts. bad_beta ts \<beta>}))) True)"
  (is "?lhs \<le> ?rhs")
proof-
  let ?I = "{0..<p::int}"
  let ?B = "\<lambda>\<beta>. {ts. bad_beta ts \<beta>}"
  let ?M = "ts_pmf"
  have "bad_beta_union = (\<Union>\<beta> \<in> ?I. ?B \<beta>)"
    unfolding bad_beta_union_def by blast
  hence *: "?lhs = measure ts_pmf (\<Union>\<beta> \<in> ?I. ?B \<beta>)" using pmf_in_set by metis

  have 1: "finite ?I" by auto
  have 2: "?B ` ?I \<subseteq> sets ?M" using sets_measure_pmf by blast
  have "?lhs \<le> (\<Sum>i\<in>?I. measure ?M (?B i))"
    unfolding * using measure_pmf.finite_measure_subadditive_finite[OF 1 2] .
  also have "\<dots> = ?rhs"
  proof-
    have "\<And>\<beta>. measure ?M (?B \<beta>)
        = pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> {ts. bad_beta ts \<beta>}))) True"
      by (smt (verit, ccfv_SIG) bind_pmf_cong measure_pmf_single mem_Collect_eq pmf_in_set)
    thus ?thesis by presburger
  qed
  finally show ?thesis .
qed

lemma fixed_beta_close_vec_dist_p:
  fixes \<beta> ts
  assumes "ts \<in> set_pmf ts_pmf"
  assumes "v \<in> vec_class_mod_p ts \<beta>"
  assumes "close_vec ts v"
  defines "u \<equiv> ts_to_u ts"
  shows "\<forall>i < d. real_of_int (dist_p (int (ts ! i) * \<beta>) (int (ts_to_as ts ! i))) < real p / 2 ^ \<mu>"
proof clarify
  fix i assume *: "i < d"
  have "(of_int (dist_p ((ts ! i) * \<beta>) ((ts_to_as ts ! i))))\<^sup>2 \<le> ((u - v)$i)\<^sup>2"
    using dist_p_smallest[OF assms(1,2) *] unfolding u_def .
  moreover have "of_rat \<dots> < (p / 2 ^ \<mu>)\<^sup>2"
  proof-
    have "u - v \<in> carrier_vec (d + 1)"
    proof-
      have "u \<in> carrier_vec (d + 1)"
        unfolding u_def using u_carrier assms(1) set_pmf_ts vec_class_mod_p_carrier by blast
      moreover have "v \<in> carrier_vec (d + 1)"
        using assms(1,2) set_pmf_ts vec_class_mod_p_carrier by fastforce
      ultimately show ?thesis by auto
    qed
    hence "((ts_to_u ts - v) $ i)\<^sup>2 < (rat_of_nat p / 2 ^ \<mu>)\<^sup>2"
      using assms(3) vec_le_sq_norm[of "u - v" "d + 1" i] *
      unfolding close_vec_def u_def sq_norm_vec_def
      by fastforce
    thus ?thesis
      unfolding u_def
      by (metis (mono_tags, opaque_lifting) Ring_Hom.of_rat_hom.hom_div of_nat_numeral of_rat_less of_rat_of_nat_eq of_rat_power)
  qed
  ultimately show "(of_int (dist_p ((ts ! i) * \<beta>) ((ts_to_as ts ! i)))) < p / 2 ^ \<mu>"
    by (smt (verit, ccfv_SIG) Power.linordered_semidom_class.power_mono divide_nonneg_nonneg of_nat_0_le_iff of_rat_less_eq of_rat_of_int_eq of_rat_power zero_less_power)
qed

lemma fixed_beta_bad_prob_arith_helper:
  defines "T_lwr_bnd \<equiv> (rat_of_nat (p - 1) - 2 * (2 * (rat_of_nat p))/(2^\<mu>))"
  shows "1 - 5/(2^\<mu>) \<le> real_of_rat T_lwr_bnd / (p - 1)"
proof-
  have "5 \<le> p"
  proof-
    have "2 powr (log 2 p) = p" by (simp add: p prime_gt_0_nat)
    moreover have "n - 1 \<le> log 2 p" using n n_big by linarith
    ultimately have "2^(n - 1) \<le> p" by (meson log2_of_power_less not_le p prime_gt_0_nat)
    moreover have "32 = (2::nat)^5" by simp
    moreover have "\<dots> \<le> 2^(n - 1)"
    proof-
      have "5 \<le> n - 1" using n_big by auto
      thus ?thesis by (meson pow_mono_exp rel_simps(25))
    qed
    ultimately show ?thesis by linarith
  qed
  hence "4*p \<le> 5*(p - 1)" by fastforce
  hence "(4 * p) / (p - 1) \<le> 5"
    by (metis (mono_tags, opaque_lifting) Multiseries_Expansion.intyness_simps(6) divide_le_eq not_le of_nat_0_le_iff of_nat_le_iff of_nat_simps(5))
  hence "((4 * p) / (p - 1)) * (1 / 2^\<mu>) \<le> 5 / (2^\<mu>)" using divide_right_mono by fastforce
  hence "(4 * p) / ((p - 1) * 2^\<mu>) \<le> 5 / (2^\<mu>)" by auto
  hence "1 - 5 / (2^\<mu>) \<le> 1 - (4 * p) / ((p - 1) * 2^\<mu>)" by argo
  also have "\<dots> = ((p - 1) * (1 / (p - 1))) - ((4 * p) / (2^\<mu>)) * (1 / (p - 1))"
    using \<open>5 \<le> p\<close> by auto
  also have "\<dots> = ((p - 1) - ((4 * p) / (2^\<mu>))) / (p - 1)" by argo
  also have "\<dots> = real_of_rat T_lwr_bnd / (p - 1)"
    by (simp add: T_lwr_bnd_def Ring_Hom.of_rat_hom.hom_div Ring_Hom.of_rat_hom.hom_mult Ring_Hom.of_rat_hom.hom_power of_rat_diff)
  finally show ?thesis .
qed

lemma dist_p_helper:
  fixes ts i
  assumes ts: "ts \<in> set_pmf ts_pmf"
  assumes i: "i < d"
  assumes dist: "dist_p (int (ts!i) * \<beta>) ((ts_to_as ts)!i) < p/(2^\<mu>)"
  shows "dist_p ((ts!i) * \<beta>) ((ts!i) * \<alpha>) \<le> (2*p)/(2^\<mu>)"
proof-
  let ?x = "\<alpha> * (ts ! i) mod p"
  let ?a\<^sub>i = "msb_p ?x"
  let ?ts\<^sub>i_\<beta> = "(ts ! i) * \<beta>"
  let ?ts\<^sub>i_\<alpha> = "(ts ! i) * \<alpha>"
  have "ts_to_as ts ! i = ?a\<^sub>i" unfolding ts_to_as_def using i ts set_pmf_ts by force
  hence *: "dist_p ?ts\<^sub>i_\<beta> ?a\<^sub>i < real p / 2 ^ \<mu>" using ts i dist by metis

  have 1: "1 < p" using p prime_gt_1_nat by blast
  have 2: "real (k + 1) < log 2 (real p)" using k_plus_1_lt by blast
  have "\<bar>int ?x - ?a\<^sub>i\<bar> \<le> real p / 2 ^ k" using msb_p_dist[of ?x] by argo
  also have "\<dots> \<le> real p / 2 ^ \<mu>"
  proof-
    have "(2::real) ^ k \<ge> 2 ^ \<mu>" using \<mu>_le_k by auto
    thus ?thesis
      by (metis frac_le less_eq_real_def of_nat_0_le_iff zero_less_numeral zero_less_power)
  qed
  finally have "\<bar>int ?x - ?a\<^sub>i\<bar> \<le> real p / 2 ^ \<mu>" .

  hence "dist_p ?ts\<^sub>i_\<beta> ?x - dist_p ?ts\<^sub>i_\<beta> (int (msb_p ?x)) \<le> real p / 2 ^ \<mu>"
    using dist_p_diff[of ?ts\<^sub>i_\<beta> ?x ?a\<^sub>i] by linarith
  hence "dist_p ?ts\<^sub>i_\<beta> ?x \<le> real p / 2 ^ \<mu> + dist_p ?ts\<^sub>i_\<beta> ?a\<^sub>i" by linarith
  also have "\<dots> \<le> real p / 2 ^ \<mu> + real p / 2 ^ \<mu>" using * by argo
  also have "\<dots> = real (2 * p) / 2 ^ \<mu>" by simp
  finally have "dist_p ?ts\<^sub>i_\<beta> ?x \<le> real (2 * p) / 2 ^ \<mu>" .
  moreover have "dist_p ?ts\<^sub>i_\<beta> (ts ! i * \<alpha>) \<le> dist_p ?ts\<^sub>i_\<beta> ?x" (is "?lhs \<le> ?rhs")
  proof- (* this is an equality but we only need \<le> *)
    let ?a = ?ts\<^sub>i_\<beta>
    let ?b = "ts ! i * \<alpha>"
    let ?b' = ?x
    let ?S = "{\<bar>?a - ?b + z * int p\<bar> | z. True}"
    have "?rhs \<in> ?S"
    proof-
      obtain k where k: "?rhs = \<bar>?a - ?b' + k * int p\<bar>" using dist_p_well_defined[of ?a ?b'] by fast
      have "[?b = ?b'] (mod int p)"
        by (simp add: Groups.ab_semigroup_mult_class.mult.commute of_nat_mod)
      then obtain k' where "?b' = ?b + k' * int p" by (metis cong_iff_lin cross3_simps(11))
      hence "?rhs = \<bar>?a - (?b + k' * int p) + k * int p\<bar>" using k by presburger
      also have "\<dots> = \<bar>?a - ?b - k' * int p + k * int p\<bar>" by linarith
      also have "\<dots> = \<bar>?a - ?b + (- k' + k) * int p\<bar>"
        by (smt (verit, ccfv_SIG) Rings.ring_class.ring_distribs(2))
      also have "\<dots> \<in> ?S" by blast
      finally show ?thesis .
    qed
    thus ?thesis unfolding dist_p_def using dist_p_le dist_p_def by auto
  qed
  ultimately show "real_of_int (dist_p (map int ts ! i * \<beta>) (int (ts ! i * \<alpha>))) \<le> real (2 * p) / 2 ^ \<mu>"
    using i ts set_pmf_ts by fastforce
qed

lemma prob_A_helper:
  fixes \<beta> :: int
  defines [simp]: "t_pmf \<equiv> pmf_of_set {1..<p}"
  defines [simp]: "A_cond \<equiv> \<lambda>t. (2*p)/(2^\<mu>) < dist_p (\<beta> * t) (\<alpha> * t)"
  defines [simp]: "A_pmf \<equiv> t_pmf \<bind> (\<lambda>t. return_pmf (A_cond t))"
  defines [simp]: "A \<equiv> pmf A_pmf True"
  assumes \<beta>: "\<beta> \<in> {0..<p::int}"
  assumes False: "\<not> (\<beta> = \<alpha> mod p)"
  shows "(1 - A) \<le> (5 / (2^\<mu>))"
proof-
  let ?S = "{1..<p}"
  let ?T = "{x \<in> ?S. A_cond x}"
  let ?T_lwr_bnd = "(rat_of_nat (p - 1) - 2 * (2 * (rat_of_nat p))/(2^\<mu>))"
  have card_S: "card ?S = p - 1" by simp
  have fin_S: "finite ?S" and S_nempty: "?S \<noteq> {}" using p_geq_2 by simp_all
  have "A = card ?T / card ?S"
    using pmf_of_finite_set_event[OF S_nempty fin_S, of A_cond] by simp
  moreover have "real_of_rat ?T_lwr_bnd \<le> real_of_nat (card ?T)"
  proof-
    let ?bound = "(2 * (rat_of_nat p))/(2^\<mu>)"
    let ?good = "\<lambda>t. rat_of_int (dist_p (t * \<beta>) (t * int \<alpha>)) \<le> ?bound"
    let ?bad = "\<lambda>t. \<not> ?good t"
    let ?good_ts = "{t \<in> ?S. ?good t}"
    let ?bad_ts = "{t \<in> ?S. ?bad t}"
    have good_bad_card: "card ?bad_ts = card ?S - card ?good_ts"
    proof-
      have "?S = ?good_ts \<union> ?bad_ts" by fastforce
      moreover have "?good_ts \<inter> ?bad_ts = {}" by blast
      ultimately have "card ?good_ts + card ?bad_ts = card ?S"
        by (smt (verit, ccfv_threshold) card_Un_disjoint fin_S finite_Un)
      thus ?thesis by linarith
    qed

    have 1: "\<beta> \<noteq> int \<alpha>" using False \<beta> by force
    have 2: "coprime (\<beta> - \<alpha>) p"
    proof-
      have 1: "\<not> p dvd (\<beta> - \<alpha>)"
        by (metis assms(5,6) int_ops(9) int_p_prime mod_eq_dvd_iff mod_ident_iff prime_gt_0_int)
      show ?thesis using prime_imp_power_coprime[OF int_p_prime 1, of 1] by simp
    qed
    have 3: "0 < 2 * rat_of_nat p / 2 ^ \<mu>" using p by (simp add: prime_gt_0_nat)
    have "rat_of_nat (card ?good_ts) \<le> 2 * ?bound"
      by (rule dist_p_instances[OF 1 2 3])
    hence "rat_of_nat (p - 1) - 2 * ?bound \<le> rat_of_nat ((p - 1) - card ?good_ts)" by linarith
    also have "\<dots> = rat_of_nat (card ?bad_ts)" using good_bad_card card_S by fastforce
    also have "\<dots> \<le> rat_of_nat (card ?T)"
    proof-
      have "?bad_ts \<subseteq> ?T"
      proof
        fix t assume "t \<in> ?bad_ts"
        hence *: "t \<in> ?S \<and> ?bad t" by blast
        hence "2 * rat_of_nat p / 2^\<mu> < rat_of_int (dist_p (int t * \<beta>) (int t * int \<alpha>))" by linarith
        hence "A_cond t"
        proof(subst A_cond_def)
          assume *: "2 * rat_of_nat p / 2 ^ \<mu> < rat_of_int (dist_p (int t * \<beta>) (int t * int \<alpha>))"
          hence "real_of_rat (2 * rat_of_nat p / 2 ^ \<mu>) < real_of_rat (rat_of_int (dist_p (int t * \<beta>) (int t * int \<alpha>)))"
            using of_rat_less by blast
          moreover have "real_of_rat (2 * rat_of_nat p / 2 ^ \<mu>) = real (2 * p) / 2 ^ \<mu>"
            by (metis (no_types, opaque_lifting) Ring_Hom.of_rat_hom.hom_div Ring_Hom.of_rat_hom.hom_power of_nat_numeral of_nat_simps(5)
                of_rat_of_nat_eq)
          moreover have "real_of_rat (rat_of_int (dist_p (int t * \<beta>) (int t * int \<alpha>)))
            = real_of_int (dist_p (\<beta> * int t) (int (\<alpha> * t)))"
            by (simp add: mult_ac(2))
          ultimately show "real (2 * p) / 2 ^ \<mu> < real_of_int (dist_p (\<beta> * int t) (int (\<alpha> * t)))"
            by algebra
        qed
        thus "t \<in> ?T" unfolding A_cond_def using * by blast
      qed
      moreover have "finite ?T" by simp
      ultimately show ?thesis by (meson card_mono of_nat_mono)
    qed
    finally show ?thesis
      by (metis (lifting) of_rat_less_eq of_rat_of_nat_eq times_divide_eq_right)
  qed
  ultimately have "real_of_rat ?T_lwr_bnd / (card ?S) \<le> A" using divide_right_mono by blast
  moreover have "card ?S = p - 1" by fastforce
  ultimately have "real_of_rat ?T_lwr_bnd / (p - 1) \<le> A" by simp
  moreover have "1 - 5 / (2^\<mu>) \<le> real_of_rat ?T_lwr_bnd / (p - 1)"
    by (rule fixed_beta_bad_prob_arith_helper)
  ultimately show ?thesis by argo
qed

lemma prob_A_helper':
  fixes \<beta> :: int
  defines [simp]: "t_pmf \<equiv> pmf_of_set {1..<p}"
  defines [simp]: "A_cond \<equiv> \<lambda>t. (2*p)/(2^\<mu>) < dist_p (\<beta> * t) (\<alpha> * t)"
  defines [simp]: "A_pmf \<equiv> t_pmf \<bind> (\<lambda>t. return_pmf (A_cond t))"
  defines [simp]: "A \<equiv> pmf A_pmf True"
  assumes \<beta>: "\<beta> \<in> {0..<p::int}"
  assumes False: "\<not> (\<beta> = \<alpha> mod p)"
  shows "(1 - A)^d \<le> (5 / (2^\<mu>))^d"
  using prob_A_helper[OF \<beta> False] apply simp
  by (meson Power.linordered_semidom_class.power_mono diff_ge_0_iff_ge pmf_le_1)

lemma fixed_beta_bad_prob:
  fixes \<beta>
  assumes "\<beta> \<in> {0..<p::int}"
  defines "M \<equiv> ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> {ts. bad_beta ts \<beta>}))"
  shows "\<beta> = \<alpha> mod p \<Longrightarrow> pmf M True = 0" 
        "\<not> (\<beta> = \<alpha> mod p) \<Longrightarrow> pmf M True \<le> (5/(2^\<mu>))^d"
proof-
  assume True: "\<beta> = \<alpha> mod p"
  have "\<forall>ts \<in> set_pmf ts_pmf. \<not> bad_beta ts \<beta>"
  proof
    fix ts assume ts: "ts \<in> set_pmf ts_pmf"
    hence length_ts: "length ts = d" by (simp add: set_pmf_ts)

    show "\<not> bad_beta ts \<beta>"
      unfolding bad_beta_def good_beta_def
    proof clarify
      fix v assume v: "v \<in> vec_class_mod_p ts \<beta>" "close_vec ts v"
      hence dim_v: "dim_vec v = d + 1" using vec_class_mod_p_carrier[OF length_ts, of \<beta>] by auto
      have "(\<exists>\<beta>::int. [\<alpha> = \<beta>] (mod p) \<and> real_of_rat (v $ d) = \<beta> / p)" 
      proof-
        from v(1) obtain \<beta> where \<beta>: "[\<alpha> = \<beta>] (mod int p) \<and> v \<in> vec_class ts \<beta>"
          unfolding vec_class_mod_p_def using True
          by (smt (verit, ccfv_threshold) UnionE mem_Collect_eq mod_mod_trivial of_nat_mod
              unique_euclidean_semiring_class.cong_def)
        then obtain cs where cs: "v = (of_int \<beta>) \<cdot>\<^sub>v (t_vec ts) + lincomb_list (of_int \<circ> cs) p_vecs"
          unfolding vec_class_def by blast
        hence "v $ d = ((of_int \<beta>) \<cdot>\<^sub>v (t_vec ts))$d + (lincomb_list (of_int \<circ> cs) p_vecs)$d"
            (is "_ = ?a + ?b")
          using dim_v by simp
        hence "real_of_rat (v$d) = real_of_rat ?a + real_of_rat ?b" by (simp add: of_rat_add)
        moreover have "real_of_rat ?a = \<beta> / p"
        proof-
          have "(t_vec ts)$d = 1 / (rat_of_nat p)"
            unfolding t_vec_def using length_ts t_vec_def t_vec_last by presburger
          hence "real_of_rat ((t_vec ts)$d) = 1 / p" by (simp add: of_rat_divide)
          moreover have "?a = (of_int \<beta>) * ((t_vec ts)$d)"
            using length_ts t_vec_dim by auto
          ultimately show ?thesis by (simp add: of_rat_mult)
        qed
        moreover have "real_of_rat ?b = 0" using lincomb_of_p_vecs_last[of cs] by blast
        ultimately have "[\<alpha> = \<beta>] (mod p) \<and> real_of_rat (v $ d) = \<beta> / p" using \<beta> by linarith
        thus ?thesis by blast
      qed
      moreover have "dim_vec v = d + 1"
        using vec_class_mod_p_carrier[OF length_ts, of \<beta>] v by force
      ultimately show "good_vec v" unfolding good_vec_def by blast
    qed
  qed
  thus "pmf M True = 0"
    apply (simp add: M_def pmf_def)
    by (smt (verit, ccfv_SIG) Probability_Mass_Function.set_pmf.rep_eq bind_eq_return_pmf bind_return_pmf mem_Collect_eq return_pmf_inj)
next
  assume False: "\<not> (\<beta> = \<alpha> mod p)"
  let ?a = "\<lambda>ts i. (ts_to_as ts)!i"
  let ?u = "\<lambda>ts. ts_to_u ts"
  let ?E1 = "\<lambda>ts. \<forall>i < d. dist_p (int (ts!i) * \<beta>) (?a ts i) < p/(2^\<mu>)"
  let ?E2 = "\<lambda>ts. \<forall>i < d. dist_p ((ts!i) * \<beta>) ((ts!i) * \<alpha>) \<le> (2*p)/(2^\<mu>)"
  let ?E1_pmf = "ts_pmf \<bind> (\<lambda>ts. return_pmf (?E1 ts))"
  let ?E2_pmf = "ts_pmf \<bind> (\<lambda>ts. return_pmf (?E2 ts))"
  let ?t_pmf = "pmf_of_set {1..<p}"
  let ?A_cond = "\<lambda>t. (2*p)/(2^\<mu>) < dist_p (\<beta> * t) (\<alpha> * t)"
  let ?A_pmf = "?t_pmf \<bind> (\<lambda>t. return_pmf (?A_cond t))"
  let ?A = "pmf ?A_pmf True"
  
  (* bad_beta means that we have a close vector whose associated beta is not congruent to alpha
    mod p *)
  have "\<forall>ts \<in> set_pmf ts_pmf. bad_beta ts \<beta> \<longrightarrow> ?E1 ts"
    using fixed_beta_close_vec_dist_p unfolding bad_beta_def good_beta_def by blast
  (* Since beta is not congruent to alpha, that means that every close vector
    in the vec_class_mod_p is bad; i.e., we're splitting the lattice into
    portions and focusing on one particular portion and all of the close
    vectors in that portion are bad *)
  moreover have "\<forall>ts \<in> set_pmf ts_pmf. ?E1 ts \<longrightarrow> ?E2 ts" using dist_p_helper by blast
  ultimately have "\<forall>ts \<in> set_pmf ts_pmf. ts \<in> {ts. bad_beta ts \<beta>} \<longrightarrow> ?E2 ts" by blast
  hence "pmf M True \<le> pmf (?E2_pmf) True"
    unfolding M_def using pmf_subset[of ts_pmf "\<lambda>ts. ts \<in> {ts. bad_beta ts \<beta>}" ?E2] by blast
  also have "\<dots> \<le> (1 - ?A)^d"
  proof-
    let ?E = "\<lambda>x. dist_p (int x * \<beta>) (int x * \<alpha>) \<le> (2*p)/(2^\<mu>)"
    have *: "pmf (pmf_of_set {1..<p} \<bind> (\<lambda>x. return_pmf (?E x))) True \<le> (1 - ?A)"
    proof-
      let ?A'_pmf = "?t_pmf \<bind> (\<lambda>t. return_pmf (\<not> ?A_cond t))"
      let ?p = "pmf_of_set {1..<p} \<bind> (\<lambda>x. return_pmf (?E x))"
      have 1: "\<forall>x \<in> set_pmf ?t_pmf. ?E x \<longrightarrow> \<not> ?A_cond x" by (simp add: mult_ac(2))
      have "pmf ?p True \<le> pmf ?A'_pmf True" using pmf_subset[OF 1] by blast
      also have "\<dots> = pmf ?A_pmf False" using pmf_true_false[of ?t_pmf] by presburger
      also have "\<dots> = 1 - (pmf ?A_pmf True)" using pmf_True_conv_False by auto
      finally show ?thesis
        by (smt (verit, del_insts) \<alpha> empty_iff finite_atLeastLessThan pmf_of_set_def)
    qed
    show ?thesis
      using replicate_pmf_same_event_leq[OF *, of d, folded ts_pmf_def]
      by (smt (verit, best) bind_pmf_cong mem_Collect_eq nth_map of_nat_simps(5) set_pmf_ts)
  qed
  also have "\<dots> \<le> (5 / (2^\<mu>))^d" by (rule prob_A_helper'[OF assms(1) False])
  finally show "pmf M True \<le> (5/(2^\<mu>))^d" .
qed

lemma bad_beta_union_bound_pmf:
  "pmf (ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> bad_beta_union))) True \<le> (p - 1) * (5/(2^\<mu>))^d"
proof-
  let ?b = "(5/(2^\<mu>))^d"
  let ?M' = "\<lambda>\<beta>. ts_pmf \<bind> (\<lambda>ts. return_pmf (ts \<in> {ts. bad_beta ts \<beta>}))"
  have "(\<Sum>\<beta> \<in> {0..<p::int}. pmf (?M' \<beta>) True) \<le> (p - 1) * ?b"
  proof-
    let ?x = "\<lambda>\<beta>. pmf (?M' \<beta>) True"
    let ?A = "{0..<p::int}"
    have "\<alpha> \<in> ?A" using \<alpha> by force
    hence "(\<Sum>\<beta> \<in> ?A. ?x \<beta>) = (\<Sum>\<beta> \<in> ?A - {\<alpha>}. ?x \<beta>) + ?x \<alpha>"
      using sum.remove[of ?A \<alpha> ?x] by fastforce
    also have "\<dots> \<le> (\<Sum>\<beta> \<in> ?A - {\<alpha>}. ?b) + ?x \<alpha>"
    proof-
      have "\<And>\<beta>. \<beta> \<in> ?A - {\<alpha>} \<Longrightarrow> ?x \<beta> \<ge> 0" by auto
      moreover have "\<And>\<beta>. \<beta> \<in> ?A - {\<alpha>} \<Longrightarrow> ?x \<beta> \<le> ?b" using fixed_beta_bad_prob(2)
        by (metis DiffE \<open>int \<alpha> \<in> {0..<int p}\<close> atLeastLessThan_iff insertI1 linorder_not_le nat_mod_eq' of_nat_le_iff)
      ultimately have "(\<Sum>\<beta> \<in> ?A - {\<alpha>}. ?x \<beta>) \<le> (\<Sum>\<beta> \<in> ?A - {\<alpha>}. ?b)" by (meson sum_mono)
      thus ?thesis by argo
    qed
    also have "\<dots> = (p - 1) * ?b" using fixed_beta_bad_prob(1)[of \<alpha>] \<alpha> by simp
    finally show ?thesis .
  qed
  thus ?thesis using bad_beta_union_bound by linarith
qed

lemma sampled_lattice_unlikely_bad:
  shows "pmf sampled_lattice_good False \<le> (p - 1) * ((5/(2^\<mu>))^d)"
  using reduction_1_pmf reduction_2_pmf bad_beta_union_bound_pmf by force

subsubsection "Main uniqueness lemma statement"

lemma sampled_lattice_likely_good: "pmf sampled_lattice_good True \<ge> 1/2"
proof-
  have "(p - 1) * ((5/(2^\<mu>))^d) \<le> 1/2" 
  proof-
    have *: "(5/(2^\<mu>))^d \<le> ((2 powr (2.5 * (of_nat d)) / (2^(\<mu>*d)))::real)"
    proof-
      have "(5::real)^d \<le> ((2::real) powr 2.5)^d"
      proof-
        have "(2::real) powr 2 = 4" by fastforce
        moreover have "(2::real) powr 0.5 \<ge> 1.25"
        proof-
          have "(1.25::real) * 1.25 = 1.5625" by fastforce
          moreover have "(1.25::real) * 1.25 = 1.25 powr 2" by (simp add: power2_eq_square)
          ultimately have "(1.25::real) powr 2 \<le> 2" by simp
          hence "(1.25::real) powr 2 \<le> (sqrt 2) powr 2" by fastforce
          moreover have "sqrt 2 = (2::real) powr 0.5" using powr_half_sqrt by simp
          ultimately show ?thesis by fastforce
        qed
        moreover have "(2::real) powr 2.5 = (2 powr 2) * (2 powr 0.5)"
        proof-
          have "(2::real) powr 2.5 = (2::real) powr (2 + 0.5)" by fastforce
          thus ?thesis by (metis powr_add)
        qed
        ultimately have "(5::real) \<le> 2 powr 2.5" by auto
        thus ?thesis by (simp add: nonneg_power_le)
      qed
      also have "\<dots> = (2::real) powr (2.5 * d)"
        by (simp add: Groups.ab_semigroup_mult_class.mult.commute powr_power)
      finally have "(5::real)^d \<le> (2::real) powr (2.5 * d)" .
      hence "(5^d/2^(\<mu>*d)) \<le> ((2::real) powr (2.5 * d)) / 2^(\<mu>*d)" by (simp add: divide_right_mono)
      moreover have "((5::real)/(2^\<mu>))^d = (5^d/2^(\<mu>*d))" by (simp add: power_divide power_mult)
      ultimately show ?thesis by presburger
    qed

    have "\<mu> * d \<ge> n + 6 * ceiling (sqrt n)"
    proof-
      have "\<mu> * d = 6 * ceiling (sqrt n) + (\<lceil>1 / 2 * sqrt (real n)\<rceil> * 2 * \<lceil>sqrt (real n)\<rceil>)"
        by (simp add: \<mu> d Ring_Hom.mult_hom.hom_add mult_ac(2))
      moreover have "\<lceil>1 / 2 * sqrt (real n)\<rceil> * 2 * \<lceil>sqrt (real n)\<rceil> \<ge> 1 / 2 * sqrt (real n) * 2 * sqrt (real n)"
      proof-
        have "\<lceil>1 / 2 * sqrt (real n)\<rceil> \<ge> 1 / 2 * sqrt (real n)" by linarith
        moreover have "\<lceil>sqrt (real n)\<rceil> \<ge> sqrt (real n)" by linarith
        ultimately show ?thesis
          by (smt (verit, best) Ring_Hom.mult_hom.hom_add divide_nonneg_nonneg mult_2_right mult_mono of_int_add of_int_mult of_nat_0_le_iff powr_ge_zero powr_half_sqrt)
      qed
      moreover have "1 / 2 * sqrt (real n) * 2 * sqrt (real n) = n" by simp
      ultimately show ?thesis by linarith
    qed
    hence "2 powr (\<mu>*d) \<ge> 2 powr (n + 6 * ceiling (sqrt n))"
      by (smt (verit) of_int_le_iff of_int_of_nat_eq powr_mono)
    hence "2 powr (2.5*d) / (2 powr (\<mu>*d)) \<le> 2 powr (2.5*d) / ((2::real) powr (n + 6 * ceiling (sqrt n)))"
      by (metis frac_le less_eq_real_def powr_ge_zero powr_gt_zero)
    moreover have "2 powr (2.5*d) \<le> 2 powr (5 * ceiling (sqrt n))"
      using d by fastforce
    ultimately have "2 powr (2.5*d) / (2 powr (\<mu>*d))
        \<le> (2 powr (5 * ceiling (sqrt n))) / ((2::real) powr (n + 6 * ceiling (sqrt n)))"
      by (smt (verit, ccfv_SIG) frac_le powr_gt_zero)
    also have "\<dots> = ((2::real) powr (5 * ceiling (sqrt n))) / ((2 powr n) * (2 powr (6 * ceiling (sqrt n))))"
      using powr_add by auto
    also have "\<dots> \<le> (1 / ((2::real) powr n)) * (2 powr (5 * ceiling (sqrt n))) / ((2 powr (6 * ceiling (sqrt n))))"
      by argo
    also have "\<dots> = (1 / ((2::real) powr n)) * (2 powr (5 * ceiling (sqrt n))) / ((2 powr (ceiling (sqrt n))) * (2 powr (5 * ceiling (sqrt n))))"
      by (smt (verit) of_int_add powr_add)
    also have "\<dots> = (1 / ((2::real) powr n)) * (1 / (2 powr (ceiling (sqrt n))))"
      by auto
    finally have **: "2 powr (2.5*d) / (2 powr (\<mu>*d)) \<le> (1 / (2 powr n)) * (1 / (2 powr (ceiling (sqrt n))))"
      (is "?A \<le> _") .
    moreover have "((2::real) powr n) * \<dots> = (1 / (2 powr (ceiling (sqrt n))))" by fastforce
    ultimately have "((2::real) powr n) * ?A \<le> (1 / (2 powr (ceiling (sqrt n))))"
      by (metis mult_left_mono powr_ge_zero)
    moreover have "(p - 1) * ?A \<le> ((2::real) powr n) * ?A"
    proof-
      have "p - 1 \<le> ((2::real) powr n)"
      proof-
        have "p - 1 \<le> p" by simp
        also have "\<dots> = 2 powr (log 2 p)" by (simp add: p prime_gt_0_nat)
        also have "\<dots> \<le> (2::real) powr n"
          by (smt (verit, ccfv_SIG) n le_diff_iff le_diff_iff' le_numeral_extra(4) n_geq_1 nat_ceiling_le_eq nat_int powr_le_cancel_iff)
        finally show ?thesis by blast
      qed
      thus ?thesis by (meson divide_nonneg_nonneg less_eq_real_def mult_mono powr_ge_zero)
    qed
    ultimately have "(p - 1) * ?A \<le> (1 / (2 powr (ceiling (sqrt n))))" by linarith
    moreover have "(5/(2^\<mu>))^d \<le> ?A" by (smt (verit, best) * powr_realpow)
    moreover have "(1 / (2 powr (ceiling (sqrt n)))) \<le> 1/2"
    proof-
      have "sqrt n \<ge> 1" using n_geq_1 by simp
      hence "ceiling (sqrt n) \<ge> 1" by fastforce
      hence "2 powr (ceiling (sqrt n)) \<ge> 2"
        by (metis of_int_1_le_iff powr_mono powr_one rel_simps(25) rel_simps(27))
      thus ?thesis by force
    qed
    ultimately show ?thesis by (smt (verit, best) mult_left_mono of_nat_0_le_iff)
  qed
  hence "1 - (p - 1) * ((5/(2^\<mu>))^d) \<ge> 1/2" by simp
  moreover have "pmf sampled_lattice_good True = 1 - pmf sampled_lattice_good False"
    using pmf_True_conv_False by blast
  ultimately show ?thesis using sampled_lattice_unlikely_bad by linarith
qed

subsection "Main theorem"

subsubsection "Oracle definition"

definition "\<O>" :: "nat \<Rightarrow> nat" where
  "\<O> t = msb_p ((\<alpha> * t) mod p)"

subsubsection "Apply Babai lemmas to adversary"
text "We use Babai lemmas to show that the adversary wins when the \<open>ts\<close> generate a good lattice."

lemma gen_basis_assms:
  fixes ts :: "nat list"
  assumes "length ts = d"
  shows "LLL.LLL_with_assms (d+1) (d+1) (int_gen_basis ts) (4/3)"
proof-
  have l: "length (int_gen_basis ts) = d + 1" unfolding int_gen_basis_def by force
  moreover have "LLL.lin_indep (d + 1) (int_gen_basis ts)"
  proof-
    let ?b = "int_gen_basis ts"
    let ?M = "(mat_of_rows (d + 1) (LLL.RAT ?b))"
    let ?Mt = "transpose_mat ?M"
    have carrier_M: "?M \<in> carrier_mat (d + 1) (d + 1)" using l by force
    have diag: "?Mt$$(i,i) \<noteq> 0" if i: "i\<in>{0..<dim_row ?Mt}" for i 
    proof(cases "i=d")
      case t:True
      have carrier_vec: "(LLL.RAT ?b)!i \<in> carrier_vec (d + 1)" 
        using int_gen_basis_carrier[of ts] assms l i by fastforce
      have "?Mt$$(i,i) = ?M$$(i,i)" 
        using index_transpose_mat carrier_M i by auto
      also have "?M$$(i,i) = row ?M i $i" using carrier_M i by auto
      also have "row ?M i $i = (LLL.RAT ?b)!i$i" 
        using mat_of_rows_row l i carrier_M carrier_vec by auto
      finally have 1: "?Mt$$(i,i) = (LLL.RAT ?b)!d$d" using t by simp
      moreover have "(LLL.RAT ?b)!d$d = (of_int_hom.vec_hom (?b!d))$d" using nth_map l by auto
      moreover have "(of_int_hom.vec_hom (?b!d))$d = of_int_hom.vec_hom(vec_of_list (map ((*) (int p)) (map int ts) @ [1]))$d"
        using append_Cons_nth_middle[of d "(map (\<lambda>i.  (p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d])" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])" "[]"]
        unfolding int_gen_basis_def by auto
      moreover have "of_int_hom.vec_hom (vec_of_list (map ((*) (int p)) (map int ts) @ [1]))$d = 1"
        using append_Cons_nth_middle[of d "map ((*) (int p)) (map int ts)" 1 "[]"] assms by fastforce
      ultimately have "?Mt$$(i,i) = 1"
        by metis
      then show ?thesis
        by simp
    next
      case f:False
      have carrier_vec: "(LLL.RAT ?b)!i \<in> carrier_vec (d + 1)" 
        using int_gen_basis_carrier[of ts] assms l i by fastforce
      have "?Mt$$(i,i) = ?M$$(i,i)" 
        using index_transpose_mat carrier_M i by auto
      also have "?M$$(i,i) = row ?M i $i" using carrier_M i by auto
      also have "row ?M i $i = (LLL.RAT ?b)!i$i" 
        using mat_of_rows_row l i carrier_M carrier_vec by auto
      finally have 1: "?Mt$$(i,i) = (LLL.RAT ?b)!i$i" by simp
      moreover have "(LLL.RAT ?b)!i$i = (of_int_hom.vec_hom (?b!i))$i" using nth_map l i by auto
      moreover have "(of_int_hom.vec_hom (?b!i))$i = of_int_hom.vec_hom(p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))$i"
        using append_Cons_nth_left[of i "(map (\<lambda>i.  (p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d])" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])" "[]"]
              i f l
        unfolding int_gen_basis_def by auto
      moreover have "of_int_hom.vec_hom(p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))$i = rat_of_nat (p^2 * (unit_vec (d+1) i)$i)" using i
        by simp
      moreover have "(unit_vec (d+1) i)$i = 1" using i by simp
      ultimately have "?Mt$$(i,i) = rat_of_nat (p^2 * 1)" by metis
      then show ?thesis using p
        by auto
    qed
    have "?Mt$$(i,j) = 0" if ij: "i\<in>{0..<dim_row ?Mt} \<and> j\<in>{0..<i}" for i j
    proof-
      have carrier_vec: "(LLL.RAT ?b)!j \<in> carrier_vec (d + 1)" 
        using int_gen_basis_carrier[of ts] assms l ij by fastforce
      have "?Mt$$(i,j) = ?M$$(j,i)" 
        using index_transpose_mat carrier_M ij by auto
      also have "?M$$(j,i) = row ?M j $i" using carrier_M ij by auto
      also have "row ?M j $i = (LLL.RAT ?b)!j$i" 
        using mat_of_rows_row l ij carrier_M carrier_vec by auto
      finally have 1: "?Mt$$(i,j) = (LLL.RAT ?b)!j$i" by simp
      have jd: "j<d" using ij carrier_M by simp
      then have "?b!j =  (map (\<lambda>i.  (p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d])!j"
        using append_Cons_nth_left[of j "(map (\<lambda>i.  (p^2 \<cdot>\<^sub>v (unit_vec (d+1) i))) [0..<d])" "vec_of_list (map ((*) (int p)) (map int ts) @ [1])" "[]"]
        unfolding int_gen_basis_def
        by fastforce
      then have "?b!j = p^2 \<cdot>\<^sub>v (unit_vec (d+1) j)" using jd by force
      then have "(LLL.RAT ?b)!j = of_int_hom.vec_hom (p^2 \<cdot>\<^sub>v (unit_vec (d+1) j))" 
        using nth_map[of j ?b of_int_hom.vec_hom] jd l
        by auto
      then have "(LLL.RAT ?b)!j$i = rat_of_nat ((p^2 \<cdot>\<^sub>v (unit_vec (d+1) j))$i)" 
        using  ij by force
      also have "rat_of_nat ((p^2 \<cdot>\<^sub>v (unit_vec (d+1) j))$i) = rat_of_nat (p^2 * (unit_vec (d+1) j)$i)"
        using ij by auto
      also have "(unit_vec (d+1) j)$i = 0" unfolding unit_vec_def using ij
        by simp
      finally have "(LLL.RAT ?b)!j$i = 0" by linarith
      then show ?thesis using 1
        by presburger
    qed
    then have "upper_triangular ?Mt"
      by auto
    moreover have carrier_Mt: "?Mt \<in> carrier_mat (d + 1) (d + 1)" using carrier_M by simp
    moreover have "0 \<notin> set (diag_mat ?Mt)" using diag unfolding diag_mat_def
      by fastforce
    ultimately have "det ?Mt \<noteq> 0" using upper_triangular_imp_det_eq_0_iff[of ?Mt] by blast
    then have det_M: "det ?M \<noteq> 0"
      by (metis Determinant.det_transpose Matrix.transpose_transpose carrier_Mt)
    then have "lin_indpt (set (Matrix.rows ?M))" using det_not_0_imp_lin_indpt_rows[of ?M] carrier_M
      by fast
    then have LI: "lin_indpt (set (LLL.RAT ?b))" 
      using rows_mat_of_rows[of "LLL.RAT ?b" "d + 1"] int_gen_basis_carrier[of ts] assms by fastforce
    have "(LLL.RAT (int_gen_basis ts))!i \<noteq> (LLL.RAT (int_gen_basis ts))!j" if ij: "i\<noteq>j \<and> i<(d + 1) \<and> j < (d + 1)" for i j
    proof-
      have "(LLL.RAT (int_gen_basis ts))!j \<in> carrier_vec (d + 1)" 
        using int_gen_basis_carrier[of ts] assms l ij by fastforce
      moreover have "(LLL.RAT (int_gen_basis ts))!i \<in> carrier_vec (d + 1)" 
        using int_gen_basis_carrier[of ts] assms l ij by fastforce
      moreover have "row ?M i \<noteq> row ?M j"
        using Determinant.det_identical_rows[of ?M "d + 1" i j] carrier_M using ij det_M by fast
      ultimately show "(LLL.RAT (int_gen_basis ts))!i \<noteq> (LLL.RAT (int_gen_basis ts))!j"
        using mat_of_rows_row[of i "(LLL.RAT (int_gen_basis ts))" "d + 1"]
              mat_of_rows_row[of j "(LLL.RAT (int_gen_basis ts))" "d + 1"]
              ij l
        by force
    qed
    then have "distinct (LLL.RAT (int_gen_basis ts))" 
      using distinct_conv_nth[of "LLL.RAT (int_gen_basis ts)"] l by simp
    moreover have set_in: "set (LLL.RAT (int_gen_basis ts)) \<subseteq> carrier_vec (d + 1)" 
      using int_gen_basis_carrier[of ts] assms by auto
    ultimately show ?thesis unfolding Gram_Schmidt_2.cof_vec_space.lin_indpt_list_def using LI
      by blast
  qed
  ultimately show ?thesis unfolding LLL_with_assms_def by simp
qed

definition u_vec_is_msbs :: "(nat\<times>nat) list \<Rightarrow> bool" where
  "u_vec_is_msbs pairs = ((of_nat p) \<cdot>\<^sub>v ts_to_u (ts_from_pairs pairs) = of_int_hom.vec_hom (scaled_uvec_from_pairs pairs))"

lemma updated_full_Babai_correct_int_target:
  assumes "full_babai_with_assms (map_vec rat_of_int target) (d + 1) fs_init (4/3)"
  shows "real_of_int (sq_norm ( (full_babai fs_init (map_vec rat_of_int target) (4/3)) - target)) 
      \<le> ((4/3)^(d + 1) * (d + 1)) * 11/10 * babai.closest_distance_sq fs_init (map_vec rat_of_int target) \<and> 
        (full_babai fs_init (map_vec rat_of_int target) (4/3)) \<in> vec_module.lattice_of (d + 1) fs_init" 
proof-
  have 1: "0\<le>real_of_int (sq_norm ( (full_babai fs_init (map_vec rat_of_int target) (4/3)) - target))" by auto
  have "real_of_int (sq_norm ( (full_babai fs_init (map_vec rat_of_int target) (4/3)) - target)) 
      \<le> (real_of_rat (4/3)^(d + 1) * (d + 1)) * babai.closest_distance_sq fs_init (map_vec rat_of_int target) \<and> 
        (full_babai fs_init (map_vec rat_of_int target) (4/3)) \<in> vec_module.lattice_of (d + 1) fs_init"
    using full_babai_correct_int_target[of target "d + 1" fs_init "4/3"] assms by blast
  moreover then have 2: "0 \<le> (real_of_rat (4/3)^(d + 1) * (d + 1)) * babai.closest_distance_sq fs_init (map_vec rat_of_int target)"
    using 1 by linarith
  moreover have "(real_of_rat (4/3)^(d + 1) * (d + 1)) * babai.closest_distance_sq fs_init (map_vec rat_of_int target) = 
                 ((4/3)^(d + 1) * (d + 1)) * babai.closest_distance_sq fs_init (map_vec rat_of_int target)"
    by (simp add: Ring_Hom.of_rat_hom.hom_div)
  moreover then have "((4/3)^(d + 1) * (d + 1)) * babai.closest_distance_sq fs_init (map_vec rat_of_int target) \<le>
                ((4/3)^(d + 1) * (d + 1)) * 11/10 * babai.closest_distance_sq fs_init (map_vec rat_of_int target)"
    using mult_right_mono[of 1 "11/10" "((4/3)^(d + 1) * (d + 1)) * babai.closest_distance_sq fs_init (map_vec rat_of_int target)"] 2 by argo
  ultimately show ?thesis by argo
qed

lemma ad_output_vec_close:
  fixes pairs :: "(nat\<times>nat) list"
  assumes "length pairs = d"
  assumes "u_vec_is_msbs pairs"
  shows "real_of_int(sq_norm 
            ((\<A>_vec pairs)
          - (scaled_uvec_from_pairs pairs))) \<le> 
    (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k) 
    \<and> (\<A>_vec pairs)  \<in> int_gen_lattice (ts_from_pairs pairs)"
proof-
  define ts where "ts = ts_from_pairs pairs"
  define u_vec where "u_vec = scaled_uvec_from_pairs pairs"
  define rat_u_vec where "rat_u_vec = map_vec rat_of_int u_vec"
  define basis where "basis = int_gen_basis ts"
  have t_length: "length ts = d" unfolding ts_def ts_from_pairs_def using assms by fastforce
  have basis_length: "length basis = d + 1" unfolding basis_def int_gen_basis_def by auto
  have p_le: "0\<le>real(p^2)" by blast
  have u_dim: "dim_vec u_vec = d + 1" unfolding scaled_uvec_from_pairs_def u_vec_def using assms by force
  then have rat_u_dim: "dim_vec rat_u_vec = d + 1" unfolding rat_u_vec_def by fastforce
  have "length ts = d" unfolding ts_from_pairs_def ts_def using assms by fastforce
  then have LLL_assms: "LLL.LLL_with_assms (d+1) (d+1) basis (4/3)" 
    using gen_basis_assms[of ts] unfolding basis_def by argo
  then have f: "full_babai_with_assms rat_u_vec (d + 1) basis (4/3)"
    using u_dim unfolding rat_u_vec_def full_babai_with_assms_def by force
  then have 1: "real_of_int (sq_norm ((full_babai basis rat_u_vec (4/3)) - u_vec))
             \<le>  ((4::real)/3)^(d+1) * (d + 1) * 11/10 * babai.closest_distance_sq basis rat_u_vec \<and>
              (full_babai basis rat_u_vec (4/3)) \<in> vec_module.lattice_of (d + 1) basis"
    using updated_full_Babai_correct_int_target[of u_vec basis] u_dim
    unfolding rat_u_vec_def by blast
  have "babai.closest_distance_sq basis rat_u_vec 
    = Inf {real_of_rat (sq_norm x )| x. x \<in> {of_int_hom.vec_hom x - rat_u_vec| x. x\<in>LLL.LLL.L (d + 1) basis}}"
    using babai.closest_distance_sq_def[of basis rat_u_vec] babai_def[of basis rat_u_vec]
          basis_length rat_u_dim by presburger
  moreover have "0\<le>(real(4)/3)^(d+1) * (d + 1) * 11/10" by force
  moreover have "0\<le>babai.closest_distance_sq basis rat_u_vec"
  proof-
    have b: "babai_with_assms (LLL_Impl.reduce_basis (4/3) basis) rat_u_vec (4/3)"
      using full_babai_with_assms.LLL_output_babai_assms[of rat_u_vec "d + 1" basis] f by simp
    then have b1: "babai (LLL_Impl.reduce_basis (4/3) basis) rat_u_vec" unfolding babai_with_assms_def by auto
    have b2: "babai basis rat_u_vec" using basis_length rat_u_dim unfolding babai_def by simp
    have "0 \<le> babai.closest_distance_sq (LLL_Impl.reduce_basis (4/3) basis) rat_u_vec"
      using b babai_with_assms_epsilon.closest_distance_sq_pos[of "(LLL_Impl.reduce_basis (4/3) basis)" rat_u_vec "4/3" 2] 
              babai_with_assms.babai_with_assms_epsilon_connect[of "(LLL_Impl.reduce_basis (4/3) basis)" rat_u_vec "4/3"] by simp
    moreover have "LLL.L (d + 1) basis = LLL.L (d + 1) (LLL_Impl.reduce_basis (4/3) basis)"
      using LLL_with_assms.reduce_basis(1)[of "d + 1" "d + 1" basis "4/3" "(LLL_Impl.reduce_basis (4/3) basis)"] LLL_assms
      unfolding LLL.L_def by argo
    moreover have "length (LLL_Impl.reduce_basis (4/3) basis) = d + 1"
      using LLL_with_assms.reduce_basis(4)[of "d+1" "d+1" basis "4/3"] LLL_assms by fast
    ultimately show ?thesis 
      using babai.closest_distance_sq_def basis_length b1 b2 by algebra
  qed
  moreover have "babai.closest_distance_sq basis rat_u_vec
      \<le> p^2 * (of_nat ((d+1) * p^2))/2^(2*k)"
  proof-
    let ?rat_basis = "gen_basis ts"
    let ?unscaled_u = "ts_to_u ts"
    obtain "w" where w: "w \<in> gen_lattice ts \<and> sq_norm (?unscaled_u - w) \<le> (of_nat ((d+1) * p^2))/2^(2*k)"
       using close_vector_exists[of ts] t_length
       by blast
     also have **: "sq_norm (?unscaled_u - w) = sq_norm (w - ?unscaled_u)"
     proof-
       have "?unscaled_u \<in> carrier_vec (d + 1)" using ts_to_u_carrier[of ts] t_length by fastforce
       moreover have carr_w: "w\<in> carrier_vec (d + 1)" using w gen_lattice_carrier[of ts] t_length by blast
       ultimately have "(w - ?unscaled_u) = (-1)\<cdot>\<^sub>v (?unscaled_u - w)" by fastforce
       then have "sq_norm_conjugate (-1) * sq_norm (?unscaled_u - w) =  sq_norm (w - ?unscaled_u)"
         using sq_norm_smult_vec by metis
       then show ?thesis by auto
     qed
     finally have *: "real_of_rat (sq_norm (w - ?unscaled_u)) \<le> real_of_rat ( (of_nat ((d+1) * p^2))/2^(2*k) )" 
       using of_rat_less_eq by blast
    have "\<forall>x\<in>{real_of_rat (sq_norm (y - ?unscaled_u))| y. y\<in> gen_lattice ts}. 0\<le>x"
      using sq_norm_vec_ge_0 by fastforce
    then have "bdd_below {real_of_rat (sq_norm (x - ?unscaled_u))| x. x\<in> gen_lattice ts}" by fast
    then have "Inf{real_of_rat (sq_norm (x - ?unscaled_u))| x. x\<in> gen_lattice ts} \<le> real_of_rat \<parallel>w - ts_to_u ts\<parallel>\<^sup>2"
      using w cInf_lower[of "real_of_rat (sq_norm (w - ?unscaled_u))" "{real_of_rat (sq_norm (x - ?unscaled_u))| x. x\<in> gen_lattice ts}"]
      by fast
    then have 1: "Inf{real_of_rat (sq_norm (x - ?unscaled_u))| x. x\<in> gen_lattice ts} \<le> real_of_rat ( (of_nat ((d+1) * p^2))/2^(2*k) )" using *
      by auto
    have "rat_u_vec = ((of_nat p)\<cdot>\<^sub>v (ts_to_u ts))"
      using assms(2) unfolding u_vec_is_msbs_def rat_u_vec_def u_vec_def ts_def by auto
    then have "babai.closest_distance_sq basis rat_u_vec = real(p^2) * (Inf{real_of_rat (sq_norm (x - ?unscaled_u))| x. x\<in> gen_lattice ts})"
      using gen_lattice_int_gen_lattice_closest[of ts "ts_to_u ts"] t_length ts_to_u_carrier[of ts] unfolding basis_def by auto
    then have "babai.closest_distance_sq basis rat_u_vec \<le> real(p^2) * real_of_rat ((of_nat ((d+1) * p^2))/2^(2*k) )" 
      using 1 mult_left_mono[of "Inf{real_of_rat (sq_norm (x - ?unscaled_u))| x. x\<in> gen_lattice ts}"
                                "real_of_rat ((of_nat ((d+1) * p^2))/2^(2*k) )" "p^2"] p_le by presburger
    then show ?thesis
      by (metis of_nat_id of_nat_numeral of_nat_simps(5) of_rat_divide of_rat_of_nat_eq of_rat_power power2_eq_square times_divide_eq_right)
  qed
  ultimately have " (4/3)^(d+1) * real(d + 1) * 11/10 * babai.closest_distance_sq basis rat_u_vec 
                  \<le> (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k)" 
    using mult_mono[of 
                      "(4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10" 
                      "(4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10"
                      "babai.closest_distance_sq basis rat_u_vec"
                      "p^2 * (of_nat ((d+1) * p^2))/2^(2*k)"]
    by auto
  then have "real_of_int (sq_norm (full_babai basis rat_u_vec (4/3) - u_vec)) \<le> (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k)"
    using 1 by linarith
  then show ?thesis using 1 \<A>_vec.simps 
    unfolding basis_def u_vec_def rat_u_vec_def ts_def int_gen_lattice_def
    by presburger
qed

lemma ad_output_vec_class:
  fixes pairs :: "(nat \<times> nat) list"
  assumes "length pairs = d"
  assumes "u_vec_is_msbs pairs"
  shows "sq_norm ( (1/(rat_of_nat p))\<cdot>\<^sub>v(map_vec rat_of_int (\<A>_vec pairs)) - (ts_to_u (ts_from_pairs pairs)) ) < ((of_nat p)/2^(\<mu>))^2 
        \<and> ( (1/(rat_of_nat p))\<cdot>\<^sub>v(map_vec rat_of_int (\<A>_vec pairs)) \<in> vec_class_mod_p (ts_from_pairs pairs) (\<A> pairs))"
proof-
  let ?ts = "ts_from_pairs pairs"
  have tl: "length ?ts = d" using assms(1) unfolding ts_from_pairs_def by simp
  then have carrier_\<A>_vec: "(\<A>_vec pairs) \<in> carrier_vec (d + 1)"
    using ad_output_vec_close[of pairs] assms int_gen_lattice_carrier[of "ts_from_pairs pairs"] by fast
  then have rat_carrier_ad: "map_vec rat_of_int (\<A>_vec pairs) \<in> carrier_vec (d + 1)" by fastforce
  have carrier_scaled_u: "scaled_uvec_from_pairs pairs \<in> carrier_vec (d + 1)"
  proof-
    have "length ((map (\<lambda>(a,b). p*b) pairs) @ [0]) = d + 1"
      using assms by force
    then show ?thesis unfolding scaled_uvec_from_pairs_def
      by (metis length_map vec_of_list_carrier)
  qed
  then have rat_carrier_scaled_u: "map_vec rat_of_int (scaled_uvec_from_pairs pairs) \<in> carrier_vec (d + 1)" by force
  have close: "real_of_int(sq_norm 
            ((\<A>_vec pairs)
          - (scaled_uvec_from_pairs pairs))) \<le> 
    (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k) 
    \<and> (\<A>_vec pairs)  \<in> int_gen_lattice (ts_from_pairs pairs)"
    using ad_output_vec_close[of pairs] assms by simp
  moreover have "0 \<le> 1/(real_of_nat p^2)" by auto
  ultimately have "1/(real_of_nat p^2) * real_of_int(sq_norm ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs))) 
          \<le> 1/(real_of_nat p^2) * (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k)"
    using mult_mono[of "1/(real_of_nat p^2)" "1/(real_of_nat p^2)" "real_of_int(sq_norm ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs)))" "(4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k)"]
          sq_norm_vec_ge_0[of "((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs))"] by force
  moreover have "1/(real_of_nat p^2) * (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * p^2 * (of_nat ((d+1) * p^2))/2^(2*k) 
                = (4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * (of_nat ((d+1) * p^2))/2^(2*k)" by simp
  moreover have "(4 / 3) ^ (d + 1) * real (d + 1) * 11 / 10 * (of_nat ((d+1) * p^2))/2^(2*k) < ((of_nat p)/2^(\<mu>))^2"
  proof-
    have "(((4::real)/3) powr ((d + 1)/2) * (11/10) * (d + 1) * (p / (2 powr (real k - 1)))
        < p / (2 powr \<mu>))"
      using final_ineq by simp
    moreover have "0\<le> (((4::real)/3) powr ((d + 1)/2) * (11/10) * (d + 1) * (p / (2 powr (real k - 1))))"
      by fastforce
    ultimately have "(((4::real)/3) powr ((d + 1)/2) * (11/10) * (d + 1) * (p / (2 powr (real k - 1))))^2
    < (p / (2 powr \<mu>))^2" 
      using Power.linordered_semidom_class.power_strict_mono pos2 by blast
    moreover have "(((4::real)/3) powr ((d + 1)/2) * (11/10) * (d + 1) * (p / (2 powr (real k - 1))))^2 = 
          ( ((4::real)/3) powr ((d + 1)/2) )^2 * (11/10)^2 * (d + 1)^2 * ( (p / (2 powr (real k - 1))) )^2"
      by (metis (no_types, opaque_lifting) Power.semiring_1_class.of_nat_power power_mult_distrib)
    moreover have "(((4::real)/3) powr ((d + 1)/2) )^2 = ((4::real)/3) ^ (d + 1)"
      by (metis add_le_cancel_left divide_nonneg_nonneg le0 powr_ge_zero powr_half_sqrt_powr powr_realpow' real_sqrt_pow2 rel_simps(45) semiring_norm(94))
    moreover have "( (p / (2 powr (real k - 1))) )^2 = p^2 / (2 ^ (2*k)) * 4"
    proof-
      have k: "2 \<le> 2*k" using k_geq_1 by auto
      have 2: "(2::real) \<noteq> 0" by simp
      have "( (p / (2 powr (real k - 1))) )^2 = p^2 / (2 ^ (2*(k - 1)))"
        using powr_realpow[of "2" "k - 1"] power_divide[of p "2 ^ (k - 1)" 2]
        by (smt (verit) Multiseries_Expansion.intyness_1 Multiseries_Expansion.intyness_simps(3) Multiseries_Expansion.intyness_simps(5) k_geq_1 le_trans of_nat_le_0_iff of_nat_le_iff power_diff' power_divide power_even_eq powr_diff powr_realpow' semiring_norm(112) semiring_norm(159))
      moreover have "((2::real) ^ (2*(k - 1))) = 2^(2*k-2)"
        by auto
      moreover have "(2::real)^(2*k-2) = 2^(2*k)/(2^2)"
        using k power_diff'[of "2" "2*k" 2] 2 by meson
      moreover have " (2::real)^(2*k)/(2^2) =  2^(2*k)/(4)"
        using power2_eq_square[of 2] by simp
      ultimately show ?thesis 
        by (metis divide_divide_eq_right times_divide_eq_left)
    qed
    moreover have "(p / (2 powr \<mu>))^2 \<le> ((of_nat p)/2^\<mu>)^2" by (simp add: powr_realpow)
    ultimately have "((4::real)/3) ^ (d + 1) *  (11/10)^2 * (d + 1)^2 * (p^2 / (2 ^ (2*k)) * 4) < ((of_nat p)/2^\<mu>)^2"
      by (smt (verit))
    moreover have "((11::real)/10)^2 = (11/10)*(11/10)"
      using power2_eq_square by blast
    moreover have "((4::real)/3) ^ (d + 1) *  (11/10)*(11/10) * (d + 1)^2 * (p^2 / (2 ^ (2*k)) * 4) 
             = ((4::real)/3) ^ (d + 1) *  (11/10)*(11/10) * (d + 1)^2 * (p^2 / (2 ^ (2*k))) * 4" by argo
    moreover have "(d + 1)^2 * (p^2 / (2 ^ (2*k))) = (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k)))"
      using power2_eq_square[of "d + 1"] mult_ac(1)[of "d + 1" "d + 1" "(p^2 / (2 ^ (2*k)))"]
      by (metis (no_types, lifting) more_arith_simps(11) of_nat_simps(5) times_divide_eq_right)
    ultimately have *: "(4 * (11/10))* ( ((4::real)/3) ^ (d + 1) *  (11/10) * (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k)))) < ((of_nat p)/2^\<mu>)^2"
      using mult_ac by auto
    have "1 < (4::real) * (11/10)" by simp
    moreover have "0 < (4::real) * (11/10)" by simp
    moreover have "0 \<le> ( ((4::real)/3) ^ (d + 1) *  (11/10) * (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k))))" by force
    ultimately have "1 * ( ((4::real)/3) ^ (d + 1) *  (11/10) * (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k)))) \<le> (4 * (11/10))* ( ((4::real)/3) ^ (d + 1) *  (11/10) * (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k))))"
      using mult_mono[of 1 "(4::real) * (11/10)" "( ((4::real)/3) ^ (d + 1) *  (11/10) * (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k))))" "( ((4::real)/3) ^ (d + 1) *  (11/10) * (d + 1) * (of_nat ((d + 1) * p^2) / (2 ^ (2*k))))"]
      by argo
    then show ?thesis using * by argo
  qed
  ultimately have rhs: "1/(real_of_nat p^2) * real_of_int(sq_norm ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs))) < ((of_nat p)/2^(\<mu>))^2" by argo
  have "1/(real_of_nat p^2) * real_of_int(sq_norm ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs)))
                = real_of_rat (1/(rat_of_nat p^2) * ((sq_norm (map_vec rat_of_int ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs)))  )))"
    by (simp add: of_rat_divide of_rat_power sq_norm_of_int)
  moreover have "sq_norm_conjugate (1/(rat_of_nat p)) = (1/(rat_of_nat p^2))"
    using conjugatable_ring_1_abs_real_line_class.sq_norm_as_sq_abs[of "1/(rat_of_nat p)"]
          power2_abs[of "1 / rat_of_nat p"]
    by (simp add: power_divide)
  ultimately have "1/(real_of_nat p^2) * real_of_int(sq_norm ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs))) 
                =  real_of_rat( (sq_norm ((1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs))))  ) )"
    using sq_norm_smult_vec by metis
  moreover have "(real p / 2 ^ \<mu>)\<^sup>2 = real_of_rat ((rat_of_nat p / 2 ^ \<mu>)\<^sup>2)"
    by (simp add: of_rat_divide of_rat_power)
  ultimately have "(sq_norm ((1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs))))  )
            < ((of_nat p)/2^(\<mu>))^2" using rhs
    by (simp add: of_rat_less)
  moreover have "(1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int ((\<A>_vec pairs) - (scaled_uvec_from_pairs pairs)))
                = (1 / rat_of_nat p) \<cdot>\<^sub>v ((map_vec rat_of_int (\<A>_vec pairs)) - (map_vec rat_of_int (scaled_uvec_from_pairs pairs)))"
    by fastforce
  moreover have "(1 / rat_of_nat p) \<cdot>\<^sub>v ((map_vec rat_of_int (\<A>_vec pairs)) - (map_vec rat_of_int (scaled_uvec_from_pairs pairs)))
               = (1 / rat_of_nat p) \<cdot>\<^sub>v ((map_vec rat_of_int (\<A>_vec pairs)) + -(map_vec rat_of_int (scaled_uvec_from_pairs pairs)))"
    by force
  moreover have "(1 / rat_of_nat p) \<cdot>\<^sub>v ((map_vec rat_of_int (\<A>_vec pairs)) + -(map_vec rat_of_int (scaled_uvec_from_pairs pairs)))
               = (1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int (\<A>_vec pairs)) - (1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int (scaled_uvec_from_pairs pairs))"
    using smult_add_distrib_vec[of "(map_vec rat_of_int (\<A>_vec pairs))" "d + 1" "-(map_vec rat_of_int (scaled_uvec_from_pairs pairs))"]
          rat_carrier_scaled_u rat_carrier_ad
    by (metis calculation(3) smult_sub_distrib_vec)
  moreover have "(1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int (scaled_uvec_from_pairs pairs)) = ts_to_u (ts_from_pairs pairs)"
  proof-
    have "(1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int (scaled_uvec_from_pairs pairs)) 
        = (1 / rat_of_nat p) \<cdot>\<^sub>v ( ((of_nat p) \<cdot>\<^sub>v (ts_to_u (ts_from_pairs pairs))))"
      using assms(2) unfolding u_vec_is_msbs_def by argo
    then show ?thesis using tl smult_smult_assoc[of "(1 / rat_of_nat p)" "(of_nat p)"] p
      by auto
  qed
  ultimately have part1: "sq_norm ((1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int (\<A>_vec pairs)) - ts_to_u (ts_from_pairs pairs))
                  < ((of_nat p)/2^(\<mu>))^2" by argo
  let ?v = "(1 / rat_of_nat p) \<cdot>\<^sub>v (map_vec rat_of_int (\<A>_vec pairs))"
  have "?v \<in> gen_lattice ?ts" using tl
    using gen_lattice_int_gen_lattice_vec[of "?ts" "\<A>_vec pairs"] close by fastforce
  then obtain c where c: "?v = (sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i)) [0 ..< length (gen_basis ?ts)]))"
    unfolding gen_lattice_def lattice_of_def by blast
  then have "?v$d = (rat_of_int (c d)) / rat_of_nat p"
    using coordinates_of_gen_lattice[of d ?ts] tl by simp
  moreover have "?v$d = (1 / rat_of_nat p) * (rat_of_int ((\<A>_vec pairs)$d))" 
    using rat_carrier_ad carrier_\<A>_vec 
          index_map_vec(1)[of d "\<A>_vec pairs" "rat_of_int"] index_smult_vec(1)[of d "map_vec rat_of_int (\<A>_vec pairs)" "1 / (rat_of_nat p)"]
          carrier_vecD[of _ "d + 1"] by force
  ultimately have "c d = (\<A>_vec pairs)$d"
    using mult_cancel_right2 not_one_le_zero of_nat_eq_0_iff p prime_ge_1_nat times_divide_eq_left by auto
  then have "[int (\<A> pairs) = (c d)] (mod p)"
    using \<A>.simps[of pairs] int_to_nat_residue.simps[of "\<A>_vec pairs $d" p] of_nat_0_less_iff p pos_mod_bound prime_gt_0_nat by auto
  moreover have"?v \<in> vec_class ?ts (c d)"
  proof-
    have "[0 ..< length (gen_basis ?ts)] = [0 ..< d] @ [d]" 
      using gen_basis_length[of ?ts] d by simp
    moreover have "set (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i)) [0 ..< d]) \<subseteq> carrier_vec (d + 1)"
      using gen_basis_carrier[of ?ts] tl
    proof-
      have "v \<in> carrier_vec (d + 1)" if v: "v \<in> set (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i)) [0 ..< d])" for v
      proof-
        obtain i where i: "v = of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i) \<and> i\<in>{0..<d}" using v by auto
        then show "v \<in> carrier_vec (d + 1)" using gen_basis_vecs_carrier[of ?ts i] tl by simp
      qed
    then show ?thesis by fast
    qed
    moreover have "(of_int (c d) \<cdot>\<^sub>v ((gen_basis ?ts) ! d)) \<in> carrier_vec (d + 1)" using gen_basis_vecs_carrier[of ?ts d] tl by simp
    ultimately have *: "?v = (sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i)) [0 ..< d])) + (of_int (c d) \<cdot>\<^sub>v ((gen_basis ?ts) ! d))"
      using gen_basis_carrier[of ?ts] tl c
            sumlist_snoc[of "(map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i)) [0 ..< d])" "(of_int (c d) \<cdot>\<^sub>v ((gen_basis ?ts) ! d))"]
      by fastforce
    have "(gen_basis ?ts)!i = p_vecs!i" if i: "i\<in>{0..<d}" for i
      unfolding gen_basis_def 
      using i length_p_vecs append_Cons_nth_left[of i p_vecs "vec_of_list (map rat_of_nat (ts_from_pairs pairs) @ [1 / rat_of_nat p])" "[]"]
      by force
    then have "(sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ((gen_basis ?ts) ! i)) [0 ..< d])) =  (sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v (p_vecs ! i)) [0 ..< d]))"
      by (smt (verit) List.List.list.map_cong atLeastLessThan_upt)
    moreover have "(sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v (p_vecs ! i)) [0 ..< d])) = (sumlist (map (\<lambda>i. ((of_int \<circ> c) i) \<cdot>\<^sub>v (p_vecs ! i)) [0 ..< d]))"
      by auto
    moreover have "(sumlist (map (\<lambda>i. ((of_int \<circ> c) i) \<cdot>\<^sub>v (p_vecs ! i)) [0 ..< d])) = lincomb_list (of_int \<circ> c) p_vecs"
      unfolding lincomb_list_def using length_p_vecs by presburger
    moreover have "((gen_basis ?ts) ! d) = t_vec ?ts" 
      unfolding gen_basis_def t_vec_def 
      using append_Cons_nth_middle[of d p_vecs] length_p_vecs by presburger
    ultimately have "?v = lincomb_list (of_int \<circ> c) p_vecs + (of_int (c d) \<cdot>\<^sub>v (t_vec ?ts))" 
      using * by argo
    moreover have "lincomb_list (rat_of_int \<circ> c) p_vecs \<in> carrier_vec (d + 1)" 
      using p_vecs_carrier carrier_vecI lincomb_list_carrier[of p_vecs "of_int \<circ> c"] by fast
    moreover have "of_int (c d) \<cdot>\<^sub>v (t_vec ?ts) \<in> carrier_vec (d + 1)"
      using t_vec_dim[of ?ts] carrier_vecI[of "t_vec ?ts" "d + 1"] assms(1) unfolding ts_from_pairs_def by force
    ultimately have "?v = (of_int (c d) \<cdot>\<^sub>v (t_vec ?ts)) + lincomb_list (of_int \<circ> c) p_vecs"
      by force
    then show ?thesis unfolding vec_class_def by blast
  qed
  ultimately have "?v \<in> vec_class_mod_p ?ts (int (\<A> pairs))"
    unfolding vec_class_mod_p_def by blast
  then show ?thesis using part1 by blast
qed

text "If we get a good lattice (which is likely), the adversary finds the hidden number"
lemma hnp_adversary_exists_helper:
  assumes "ts \<in> set_pmf ts_pmf"
  defines "ts_Ots \<equiv> map (\<lambda>t. (t, \<O> t)) ts"
  assumes "good_lattice ts"
  shows "\<alpha> = \<A> ts_Ots"
proof-
  let ?\<A>_vec = "(1/(rat_of_nat p))\<cdot>\<^sub>v(map_vec rat_of_int (\<A>_vec ts_Ots))"
  let ?vec1 = "rat_of_nat p \<cdot>\<^sub>v vec_of_list
   (map rat_of_nat
     (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts))) @ [0])"
  let ?vec2 = "Matrix.of_int_hom.vec_hom (vec_of_list
    (map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts) @ [0])))"

  have dim_v1: "dim_vec ?vec1 = length ts + 1"
    unfolding ts_to_as_def by auto
  have dim_v2: "dim_vec ?vec2 = length ts + 1"
    by auto

  have l: "length ts = d" using assms(1) set_pmf_ts by blast
  then have ts_l: "length ts_Ots = d" unfolding ts_Ots_def by simp
  have ts_from_pairs: "ts_from_pairs ts_Ots = ts" 
  proof-
    have "map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts) = map ( (\<lambda>(a, b). a) \<circ> (\<lambda>t. (t, \<O> t)) ) ts" by simp
    moreover have "(\<lambda>(a, b). a) \<circ> (\<lambda>t. (t, \<O> t)) = (\<lambda>t. t)" by fastforce
    ultimately show ?thesis unfolding ts_from_pairs_def ts_Ots_def fst_def by simp
  qed

  have "?vec1$i = ?vec2$i" if in_range: "i\<in>{0..<(d + 1)}" for i
  proof(-)
    have "?vec1$i
           = (rat_of_nat p) * (vec_of_list (map rat_of_nat (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts))) @ [0]) $ i)"
      using in_range dim_v1 l by simp
    then have vec1_help: "?vec1$i = (rat_of_nat p) * ((map rat_of_nat (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts))) @ [0])!i)" by simp
    have vec2_help: "?vec2$i = rat_of_int ((map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts) @ [0]))!i)"
      using in_range dim_v2 l by auto
    have l1: "length (map rat_of_nat (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts)))) = d" using l unfolding ts_to_as_def by simp
    have l2: "length (map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts))) = d" using l by simp
    show ?thesis
    proof(cases "i = d")
      case t:True
      then have "(map rat_of_nat (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts))) @ [0]) ! i = 0"
        using append_Cons_nth_middle[of i "map rat_of_nat (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts)))" "0" "[]"] using l1 by blast
      then have 1: "?vec1$i = 0" using vec1_help by auto
      then show ?thesis
        using vec2_help l2 append_Cons_nth_middle[of i "(map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts)))" "0" "[]"] t 
        by fastforce
    next
      case f:False
      then have "?vec1$i = (rat_of_nat p) * (rat_of_nat ( (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts))) ! i) )"
        using vec1_help in_range l1 append_Cons_nth_left[of i "map rat_of_nat (ts_to_as (map (\<lambda>(a, b). a) (map (\<lambda>t. (t, \<O> t)) ts)))" "0" "[]"] by simp
      also have "\<dots> = (rat_of_nat p) * rat_of_nat ( (msb_p (\<alpha> * (ts!i) mod p) ) )" 
        using l f in_range ts_from_pairs unfolding ts_to_as_def ts_from_pairs_def ts_Ots_def by simp
      also have "\<dots> = (rat_of_nat p) * rat_of_nat (\<O> (ts!i))" unfolding \<O>_def by blast
      also have "\<dots> = rat_of_int (map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts)) ! i)"
        using l f in_range ts_from_pairs unfolding ts_to_as_def ts_from_pairs_def ts_Ots_def by simp
      also have "\<dots> = rat_of_int (map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts) @ [0]) ! i)"
        using l2 in_range append_Cons_nth_left[of i "(map int (map (\<lambda>(a, b). p * b) (map (\<lambda>t. (t, \<O> t)) ts)))" "0" "[]"] f by simp
      finally show ?thesis using vec2_help by linarith
    qed
  qed
  then have vec1_is_vec2: "?vec1 = ?vec2"
    using dim_v1 dim_v2 l by auto
  then have "u_vec_is_msbs ts_Ots"
    unfolding u_vec_is_msbs_def 
    unfolding ts_Ots_def 
    unfolding scaled_uvec_from_pairs_def ts_from_pairs_def fst_def ts_to_u_def
    by argo
  then have *: "\<parallel>?\<A>_vec - ts_to_u ts\<parallel>\<^sup>2 < (rat_of_nat p / 2 ^ \<mu>)\<^sup>2 \<and>  ?\<A>_vec \<in> vec_class_mod_p ts (int (\<A> ts_Ots))"
    unfolding close_vec_def
    using ad_output_vec_class[of ts_Ots] ts_l ts_from_pairs
    by blast 
  then have close: "close_vec ts ?\<A>_vec" unfolding close_vec_def using uminus_sq_norm 
    by (metis (no_types, lifting) int_gen_lattice_carrier ts_to_u_carrier \<open>ts_from_pairs ts_Ots = ts\<close> \<open>u_vec_is_msbs ts_Ots\<close> ad_output_vec_close assms(2) basic_trans_rules(31) carrier_dim_vec index_smult_vec(2) length_map map_carrier_vec ts_l)
  obtain c where "?\<A>_vec \<in> vec_class ts c"
    using * unfolding vec_class_mod_p_def by fast
  then have gl: "?\<A>_vec \<in> gen_lattice ts" 
    using vec_class_union[of ts] assms(1) by blast
  then have dim: "dim_vec (\<A>_vec ts_Ots) = d + 1" using gen_lattice_carrier[of ts] assms(1) l by fastforce
  have "good_vec ?\<A>_vec" using assms(3) close gl unfolding good_lattice_def by blast
  then obtain \<beta> where b: "[int \<alpha> = \<beta>] (mod int p) \<and> real_of_rat (?\<A>_vec $ d) = real_of_int \<beta> / real p" unfolding good_vec_def by blast
  then have "p * real_of_rat (?\<A>_vec $ d) = \<beta>" using p by simp
  then have "real p * real_of_rat ( (1/(rat_of_nat p)) * ((map_vec rat_of_int ((\<A>_vec ts_Ots)) $ d)) ) = \<beta>"
    using index_smult_vec(1)[of d "(\<A>_vec ts_Ots)"] dim by force
  then have "real p * real_of_rat (1/(rat_of_nat p) *  (rat_of_int ((\<A>_vec ts_Ots) $ d))) = \<beta>"
    using dim index_map_vec(1)[of d "(\<A>_vec ts_Ots)" rat_of_int] by simp
  then have "real p * real_of_rat (1/(rat_of_nat p)) * real_of_rat (rat_of_int ((\<A>_vec ts_Ots) $ d)) = \<beta>"
    by (metis more_arith_simps(11) of_rat_mult)
  moreover have "real p * real_of_rat (1/(rat_of_nat p)) = 1"
    by (metis (no_types, lifting) Ring_Hom.of_rat_hom.hom_div Ring_Hom.of_rat_hom.hom_one divide_cancel_right nonzero_mult_div_cancel_left not_prime_0 of_nat_eq_0_iff of_rat_of_nat_eq p)
  ultimately have "(\<A>_vec ts_Ots) $ d = \<beta>"
    by fastforce
  then have "[int (\<A> ts_Ots) = \<beta>] (mod int p)" using \<A>.simps[of ts_Ots] int_to_nat_residue.simps[of "(\<A>_vec ts_Ots $ d)" p]
    by (metis (no_types, lifting) Cong.unique_euclidean_semiring_class.cong_def int_mod_eq int_nat_eq local.\<A>.elims local.int_to_nat_residue.simps m2pths(1) of_nat_0_less_iff p pos_mod_bound prime_gt_0_nat)
  then have "[(\<A> ts_Ots) = \<alpha>] (mod p)" using b
    by (meson cong_int_iff cong_sym cong_trans)
  moreover have "\<A> ts_Ots \<in> {0..<p}"
    using \<A>.simps[of ts_Ots] int_to_nat_residue.simps[of "(\<A>_vec ts_Ots $ d)" p]
    by (metis Cong.unique_euclidean_semiring_class.cong_def \<alpha> \<open>\<A>_vec ts_Ots $ d = \<beta>\<close> atLeastLessThan_iff b int_ops(9) le0 local.int_to_nat_residue.simps mod_less nat_int)
  ultimately show ?thesis
    by (metis \<alpha> atLeastLessThan_iff cong_less_modulus_unique_nat)
qed


subsubsection "Main theorem statement"

text "The cryptographic game which the adversary should win with high probability."
definition game :: "adversary \<Rightarrow> bool pmf" where
  "game \<A>' = do {
    ts \<leftarrow> replicate_pmf d (pmf_of_set {1..<p});
    return_pmf (\<alpha> = \<A>' (map (\<lambda>t. (t, \<O> t)) ts))
  }"

text "The adversary finds the hidden number with probability at least 1/2."
theorem hnp_adversary_exists: "pmf (game \<A>) True \<ge> 1/2"
proof-
  define game' where "game' \<equiv>
    do {
      ts \<leftarrow> replicate_pmf d (pmf_of_set {1..<p});
      return_pmf (good_lattice ts)
    }"

  have 1: "\<forall>ts \<in> set_pmf ts_pmf. good_lattice ts \<longrightarrow> (\<alpha> = \<A> (map (\<lambda>t. (t, \<O> t)) ts))"
    using hnp_adversary_exists_helper by simp

  have "1 / 2 \<le> pmf game' True"
    using sampled_lattice_likely_good
    unfolding sampled_lattice_good_def game'_def ts_pmf_def .
  also have "\<dots> \<le> pmf (game \<A>) True"
    unfolding game'_def game_def
    using pmf_subset[OF 1, unfolded ts_pmf_def]
    by presburger
  finally show ?thesis .
qed

text "Alternative definition of \<open>game\<close>, written as a \<open>map_pmf\<close>"
definition game' :: "adversary \<Rightarrow> bool pmf" where
  "game' \<A>' = map_pmf ((\<lambda>ts. (\<alpha> = \<A>' (map (\<lambda>t. (t, \<O> t)) ts)))) (replicate_pmf d (pmf_of_set {1..<p}))"

lemma "game' = game"
  unfolding game'_def game_def map_pmf_def by argo

end

section "Some MSB instantiations and lemmas"

subsection "Bit-shift MSB"

definition msb :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "msb k n x \<equiv> (x div 2^(n - k)) * 2^(n - k)"

lemma msb_dist:
  fixes k n :: nat
  assumes "k < n"
  assumes "1 \<le> k"
  shows "\<bar>int (x) - int (msb k n x)\<bar> < 2^n / (2^k)"
proof-
  define z where "z = msb k n x"
  have k_small: "k \<in>{1..<n}"
    by (meson assms atLeastLessThan_iff nat_ceiling_le_eq not_le)
  have "abs(int(x) - int(z)) < real(2^(n - k))"
  proof-
    have "z = int x div 2 ^ (n - k) * 2 ^ (n - k)"
      unfolding z_def msb_def
      by (metis int_ops(7) int_ops(8) numeral_power_eq_of_nat_cancel_iff)
    then have "int(x) - int(z) = int(x) mod 2^(n - k)" 
      using minus_div_mult_eq_mod[of "int(x)" "2^(n - k)"] by presburger
    then show ?thesis by fastforce
  qed
  also have "\<dots> = 2^n / 2^k"
    by (metis Suc_leI assms(1) ge_trans le_add2 numeral_power_eq_of_nat_cancel_iff plus_1_eq_Suc power_diff semiring_norm(142))
  finally show ?thesis unfolding z_def .
qed

lemma (in hnp_arith) msb_kp1_dist_hnp:
  defines "msb_k \<equiv> msb (k + 1) n"
  shows "\<bar>int (x) - int (msb_k x)\<bar> < p / (2^k)"
proof-
  have 1: "k + 1 < n" using k_plus_1_lt n unfolding hnp_def by linarith
  have 2: "1 \<le> k + 1" using \<mu>_le_k by linarith

  have "\<bar>int (x) - int(msb_k x)\<bar> < 2 ^ n / 2 ^ (k + 1)"
    using msb_dist[OF 1 2, of x, folded msb_k_def] .
  also have "\<dots> < p / (2^k)"
  proof-
    have "2^(n - 1) < p"
    proof-
      have "2 powr (floor (log 2 p)) \<le> 2 powr (log 2 p)" by simp
      moreover have "n - 1 \<le> floor (log 2 p)" using n n_geq_1 by linarith
      ultimately have "2 powr (n - 1) \<le> 2 powr (log 2 p)" by (simp add: le_floor_iff)
      hence "2^(n - 1) \<le> 2 powr (log 2 p)" by (simp add: powr_realpow)
      thus ?thesis using p_geq_2 less_le_trans n n_geq_1 by fastforce
    qed
    hence "2^(n - 1) / 2^k < p / 2^k" by (simp add: divide_strict_right_mono)
    thus ?thesis using le_imp_diff_is_add n_geq_1 by fastforce
  qed
  finally show ?thesis .
qed

lemma msb_kp1_valid_hnp:
  assumes "hnp_arith n \<alpha> d p k"
  shows "hnp n \<alpha> d p k (msb (k + 1) n)"
  using hnp_arith.msb_kp1_dist_hnp[OF assms(1)] assms(1)
  unfolding hnp_def hnp_arith_def hnp_axioms_def
  by presburger

subsection "MSB-p"

definition msb_p :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "msb_p p k x =
    (let t = (THE t. (t - 1) * (p / 2^k) \<le> x \<and> x < t * p / 2^k)
    in nat (floor (t * p / 2^k)) - 1)"

lemma msb_p_defined:
  fixes p k :: nat
  fixes x :: nat
  assumes "p > 0"
  assumes "k > 0"
  shows "(\<exists>!t. (t - 1) * (p / 2^k) \<le> x \<and> x < t * p / 2^k)"
proof safe
  show "\<exists>t. (real t - 1) * (real p / 2 ^ k) \<le> real x \<and> real x < real (t * p) / 2 ^ k"
  proof
    let ?S = "{t. (real t - 1) * (real p / 2 ^ k) \<le> real x}"
    define t where "t = Max ?S"
    have "?S \<noteq> {}"
      by (metis Multiseries_Expansion.intyness_1 arith_simps(62) empty_iff mem_Collect_eq of_nat_0_le_iff verit_minus_simplify(1))
    moreover have "finite ?S"
    proof-
      obtain M where "?S \<subseteq> {0..<M}" 
      proof-
        let ?M = "nat (ceiling (x / (p / 2^k) + 1)) + 1"
        have "?S \<subseteq> {0..<?M}"
        proof
          fix t assume "t \<in> ?S"
          moreover have "p / 2^k > 0" by (simp add: assms(1))
          ultimately have "real t - 1 \<le> x / (p / 2^k)" using mult_imp_le_div_pos by blast
          hence "t \<le> x / (p / 2^k) + 1" by argo
          hence "t < nat (ceiling (x / (p / 2^k) + 1)) + 1" by linarith
          moreover have "0 \<le> t" by simp
          ultimately show "t \<in> {0..<?M}" by fastforce
        qed
        thus ?thesis using that[of ?M] by blast
      qed
      moreover have "finite {0..<M}" by blast
      ultimately show ?thesis using rev_finite_subset[of "{0..<M}" ?S] by fast
    qed
    ultimately have "t \<in> ?S \<and> (\<forall>t' \<in> ?S. t' \<le> t)" using Max_eq_iff t_def by blast
    moreover then have "t + 1 \<notin> ?S" by (metis Suc_eq_plus1 not_less_eq_eq)
    ultimately show "(real t - 1) * (real p / 2 ^ k) \<le> real x \<and> real x < real (t * p) / 2 ^ k"
      by force
  qed
next
  fix x t t'
  assume t: "(real t - 1) * (real p / 2 ^ k) \<le> real x" "real x < real (t * p) / 2 ^ k"
  assume t': "(real t' - 1) * (real p / 2 ^ k) \<le> real x" "real x < real (t' * p) / 2 ^ k"

  have *: "p / 2^k > 0" by (simp add: assms(1))

  have "(real t' - 1) * (real p / 2 ^ k) < real (t * p) / 2 ^ k"
    using t(2) t'(1) by linarith
  also have "\<dots> = t * (p / 2^k)" by fastforce
  finally have "(real t' - 1) < t" 
    by (meson * le_less_trans less_eq_real_def mult_imp_le_div_pos pos_divide_less_eq)
  hence 1: "t' - 1 < t" using le_less t(2) by fastforce

  have "(real t - 1) * (real p / 2 ^ k) < real (t' * p) / 2 ^ k"
    using t(1) t'(2) by linarith
  also have "\<dots> = t' * (p / 2^k)" by fastforce
  finally have "(real t - 1) < t'" 
    by (meson * le_less_trans less_eq_real_def mult_imp_le_div_pos pos_divide_less_eq)
  hence 2: "t - 1 < t'" using 1 by linarith

  show "t = t'" using 1 2 by linarith
qed

lemma (in hnp_arith) msb_p_dist_hnp:
  defines "msb_k \<equiv> msb_p p k"
  shows "\<bar>int x - int (msb_k x)\<bar> < p / 2^k"
proof-
  let ?P = "\<lambda>t. (t - 1) * (p / 2^k) \<le> x \<and> x < t * p / 2^k"
  define t where "t = (THE t. ?P t)"
  have 1: "p > 0" using p_geq_2 by simp
  have 2: "k > 0" using \<mu>_le_k by linarith
  have *: "(t - 1) * (p / 2^k) \<le> x \<and> x < t * p / 2^k"
    using theI_unique[OF msb_p_defined[OF 1 2, of x], of t, folded t_def] of_nat_diff_real
    by fastforce
  moreover have "(t - 1) * (p / 2^k) = (t * (p / 2^k)) - (p / 2^k)"
    by (metis (no_types, opaque_lifting) Nat.bot_nat_0.not_eq_extremum One_nat_def Suc_pred * diff_is_0_eq' divide_eq_0_iff left_diff_distrib more_arith_simps(5) mult_eq_0_iff nat_le_linear not_le numeral_One of_nat_diff of_nat_eq_0_iff of_nat_numeral)
  moreover have "t * p / 2^k - ((t * (p / 2^k)) - p / 2^k) = p / 2^k" by simp
  ultimately have "nat (floor (t * p / 2^k) - 1) - x < p / 2^k" by linarith
  moreover have "p / 2^k > 1"
    by (smt (verit, ccfv_threshold) 1 k_plus_1_lt less_divide_eq_1_pos log_of_power_le of_nat_0_le_iff of_nat_add zero_less_power)
  ultimately show ?thesis
    unfolding msb_k_def msb_p_def t_def
    by (smt (verit, ccfv_SIG) * int_ops(6) le_nat_floor le_nat_iff nat_diff_distrib' nat_less_as_int nat_one_as_int of_int_1_less_iff of_nat_0_le_iff of_nat_less_of_int_iff t_def zero_le_floor zless_nat_eq_int_zless)
qed

lemma msb_p_valid_hnp:
  assumes "hnp_arith n \<alpha> d p k"
  defines "msb_k \<equiv> msb_p p k"
  shows "hnp n \<alpha> d p k msb_k"
  using hnp_arith.msb_p_dist_hnp[OF assms(1)] assms(1)
  unfolding hnp_def msb_k_def hnp_arith_def hnp_axioms_def
  by presburger

end
