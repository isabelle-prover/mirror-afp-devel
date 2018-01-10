(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Executable Representation of Polynomial Mappings as Association Lists\<close>

theory Poly_Lists
imports Abstract_Poly "HOL-Library.AList"
begin

text \<open>In this theory, power-products of type @{typ "('a, nat) poly_mapping"} and multivariate polynomials of type
  @{typ "('a, 'b) poly_mapping"} are represented as association lists. Code equations are proved in order
  to actually perform computations (addition, multiplication, etc.).\<close>

text \<open>In principle, one could also build upon theory \<open>Polynomials\<close>, although there the representations of
  power-products and polynomials additionally have to satisfy certain invariants, which we do not
  require here.\<close>

subsection \<open>Utilities\<close>

hide_const (open) lookup

definition "lookup = (\<lambda>xs i. case map_of xs i of Some i \<Rightarrow> i | None \<Rightarrow> 0)"
definition normalize::"('a * 'b::zero) list \<Rightarrow> ('a * 'b) list" where
  "normalize xs \<equiv> filter (\<lambda>(k, v). v \<noteq> 0) (AList.clearjunk xs)"
  
lemma not_list_ex:
  "(\<not> list_ex P xs) = (list_all (\<lambda>x. \<not> P x) xs)"
unfolding list_ex_iff list_all_iff by simp

lemma foldl_assoc:
  assumes "\<And>x y z. f (f x y) z = f x (f y z)"
  shows "foldl f (f a b) xs = f a (foldl f b xs)"
proof (induct xs arbitrary: a b)
  fix a b
  show "foldl f (f a b) [] = f a (foldl f b [])" by simp
next
  fix a b x xs
  assume "\<And>a b. foldl f (f a b) xs = f a (foldl f b xs)"
  from assms[of a b x] this[of a "f b x"]
    show "foldl f (f a b) (x # xs) = f a (foldl f b (x # xs))" unfolding foldl_Cons by simp
qed

lemma map_of_filter_NoneI:
  assumes "map_of xs k = None"
  shows "map_of (filter (\<lambda>(k, v). P k v) xs) k = None"
proof (cases "map_of (filter (\<lambda>(k, v). P k v) xs) k")
  case None
  thus ?thesis .
next
  case Some
  fix v
  assume "map_of [(k, v)\<leftarrow>xs . P k v] k = Some v"
  from map_of_SomeD[OF this] have "(k, v) \<in> set xs" by simp
  from weak_map_of_SomeI[OF this] obtain v0 where "map_of xs k = Some v0" ..
  from this assms show ?thesis by simp
qed

lemma clearjunk_distinct:
  shows "distinct (AList.clearjunk xs)"
  using distinct_clearjunk[of xs] distinct_map[of fst] by blast

lemma finite_lookup:
  "finite {x. lookup xs x \<noteq> 0}"
proof -
  fix xs::"('a * 'b::zero) list"
  have a: "finite (fst ` set xs)" by simp
  have "{t. lookup xs t \<noteq> 0} \<subseteq> fst ` set xs"
  proof
    fix x
    assume "x \<in> {t. lookup xs t \<noteq> 0}"
    hence "lookup xs x \<noteq> 0" by simp
    from this obtain c where c: "map_of xs x = Some c" unfolding lookup_def by fastforce
    show "x \<in> fst ` set xs"
    proof
      show "x = fst (x, c)" by simp
    next
      from map_of_SomeD[OF c] show "(x, c) \<in> set xs" .
    qed
  qed
  from finite_subset[OF this a] show "finite {t. lookup xs t \<noteq> 0}" .
qed

lemma map_lookup_map_fst:
  assumes "distinct (map fst xs)"
  shows "map (lookup xs) (map fst xs) = map snd xs"
using assms
proof (induct xs, simp)
  fix x and xs::"('a * 'b) list"
  assume IH: "distinct (map fst xs) \<Longrightarrow> map (lookup xs) (map fst xs) = map snd xs"
    and dist_Cons: "distinct (map fst (x # xs))"
  from dist_Cons have dist: "distinct (map fst xs)" by simp

  obtain k1 v1 where x: "x = (k1, v1)" by fastforce
  from x dist_Cons have k1: "k1 \<notin> set (map fst xs)" by simp

  from x have eq1: "lookup (x # xs) (fst x) = snd x" unfolding lookup_def by simp

  have eq2: "map (lookup (x # xs)) (map fst xs) = map (lookup xs) (map fst xs)"
  proof (rule map_cong, simp, simp only: x)
    fix k
    assume "k \<in> set (map fst xs)"
    from this k1 have "k \<noteq> k1" by auto
    thus "lookup ((k1, v1) # xs) k = lookup xs k" unfolding lookup_def map_of_Cons_code by simp
  qed

  from eq1 eq2 IH[OF dist] show "map (lookup (x # xs)) (map fst (x # xs)) = map snd (x # xs)"
    by simp
qed

lemma list_all_merge_comm:
  assumes "list_all (\<lambda>(k, v). P (lookup xs k) (lookup ys k)) (AList.merge xs ys)"
  shows "list_all (\<lambda>(k, v). P (lookup xs k) (lookup ys k)) (AList.merge ys xs)"
unfolding list_all_def
proof (rule, rule)
  fix x k v
  assume "x \<in> set (AList.merge ys xs)" and "x = (k, v)"
  have "k \<in> fst ` set (AList.merge ys xs)"
  proof
    from \<open>x = (k, v)\<close> show "k = fst x" by simp
  qed (fact)
  hence "k \<in> fst ` set (AList.merge xs ys)"
    by (simp add: dom_merge Un_commute[of "fst ` set xs" "fst ` set ys"])
  from this obtain v' where a: "(k, v') \<in> set (AList.merge xs ys)" by auto
  from assms have "\<forall>(k, v)\<in>set (AList.merge xs ys). P (lookup xs k) (lookup ys k)"
    unfolding list_all_def .
  from this a show "P (lookup xs k) (lookup ys k)" by auto
qed

lemma distinct_normalize:
  assumes "distinct (map fst xs)"
  shows "normalize xs = filter (\<lambda>(k, v). v \<noteq> 0) xs"
by (simp add: normalize_def distinct_clearjunk_id[OF assms])

lemma normalize_distinct:
  shows "distinct (map fst (normalize xs))"
unfolding normalize_def
proof (simp add: distinct_map distinct_filter[OF clearjunk_distinct] inj_on_def, (intro allI, intro impI)+)
  fix a b c
  assume "(a, b) \<in> set (AList.clearjunk xs) \<and> b \<noteq> 0"
  hence b: "(a, b) \<in> set (AList.clearjunk xs)" ..
  assume "(a, c) \<in> set (AList.clearjunk xs) \<and> c \<noteq> 0"
  hence c: "(a, c) \<in> set (AList.clearjunk xs)" ..
  from map_of_is_SomeI[OF distinct_clearjunk[of xs] b] map_of_is_SomeI[OF distinct_clearjunk[of xs] c]
    show "b = c" by simp
qed

lemma lookup_normalize:
  shows "lookup xs s = lookup (normalize xs) s"
unfolding normalize_def lookup_def
proof (split option.split, intro conjI, intro impI)
  assume none: "map_of [(k, v)\<leftarrow>AList.clearjunk xs . v \<noteq> 0] s = None"
  show "(case map_of xs s of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = 0"
  proof (split option.split, intro conjI, simp, intro allI, intro impI, rule ccontr)
    fix c
    assume a: "map_of xs s = Some c" and "c \<noteq> 0"
    from a map_of_clearjunk[of xs] have "map_of (AList.clearjunk xs) s = Some c" by simp
    from none map_of_filter_in[OF this, of "\<lambda>x y. y \<noteq> 0", OF \<open>c \<noteq> 0\<close>] show False by simp
  qed
next
  show "\<forall>x2. map_of [(k, v)\<leftarrow>AList.clearjunk xs . v \<noteq> 0] s = Some x2 \<longrightarrow>
          (case map_of xs s of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = x2"
  proof (intro allI, intro impI)
    fix c
    assume "map_of [(k, v)\<leftarrow>AList.clearjunk xs . v \<noteq> 0] s = Some c"
    from map_of_SomeD[OF this] have c: "(s, c) \<in> set (AList.clearjunk xs)" by simp
    from map_of_is_SomeI[OF distinct_clearjunk[of xs] this] map_of_clearjunk[of xs]
      show "(case map_of xs s of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = c" by simp
  qed
qed

lemma normalize_nonzero:
  assumes "(t, c) \<in> set (normalize xs)"
  shows "c \<noteq> 0"
using assms unfolding normalize_def by simp

lemma normalize_map_of_SomeI:
  assumes "(t, c) \<in> set (normalize xs)"
  shows "map_of xs t = Some c"
proof -
  from map_of_is_SomeI[OF normalize_distinct assms] lookup_normalize[of xs t]
    have a: "(case map_of xs t of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = c" unfolding lookup_def by simp
  show ?thesis
  proof (cases "map_of xs t")
    case None
    thus ?thesis using a normalize_nonzero[OF assms] by simp
  next
    case Some
    fix b
    assume "map_of xs t = Some b"
    thus ?thesis using a by simp
  qed
qed

lemma normalize_map_of_SomeD:
  assumes a1: "map_of xs t = Some c" and "c \<noteq> 0"
  shows "(t, c) \<in> set (normalize xs)"
proof -
  from lookup_normalize[of xs t] a1
    have a: "c = (case map_of (normalize xs) t of None \<Rightarrow> 0 | Some i \<Rightarrow> i)"
    unfolding lookup_def by simp
  show ?thesis
  proof (cases "map_of (normalize xs) t")
    case None
    thus ?thesis using a \<open>c \<noteq> 0\<close> by simp
  next
    case Some
    fix b
    assume b: "map_of (normalize xs) t = Some b"
    from this a map_of_SomeD[OF this] show ?thesis by simp
  qed
qed

lemma in_fst_set_mapI:
  assumes "k \<in> fst ` set xs"
  shows "f1 k \<in> fst ` set (map (\<lambda>(k, v). (f1 k, f2 v)) xs)"
proof -
  from assms obtain v where v: "(k, v) \<in> set xs" by auto
  show ?thesis
  proof
    show "f1 k = fst (f1 k, f2 v)" by simp
  next
    from v show "(f1 k, f2 v) \<in> set (map (\<lambda>(k, v). (f1 k, f2 v)) xs)" by auto
  qed
qed

lemma in_set_mapD:
  assumes "map_of (map (\<lambda>(k, v). (f1 k, f2 v)) xs) k = Some v"
  shows "\<exists>k' v'. k = f1 k' \<and> v = f2 v' \<and> map_of xs k' = Some v'"
using assms
proof (induct xs, simp)
  fix a xs
  assume IH: "map_of (map (\<lambda>(k, v). (f1 k, f2 v)) xs) k = Some v \<Longrightarrow>
                \<exists>k' v'. k = f1 k' \<and> v = f2 v' \<and> map_of xs k' = Some v'"
    and a0: "map_of (map (\<lambda>(k, v). (f1 k, f2 v)) (a # xs)) k = Some v"
  from prod.exhaust_sel obtain x1 x2 where "a = (x1, x2)" by blast
  with a0 have a: "(if k = f1 x1 then Some (f2 x2) else map_of (map (\<lambda>(k, v). (f1 k, f2 v)) xs) k) = Some v"
    by simp
  thus "\<exists>k' v'. k = f1 k' \<and> v = f2 v' \<and> map_of (a # xs) k' = Some v'" unfolding \<open>a = (x1, x2)\<close>
  proof (split if_splits)
    assume k: "k = f1 x1" and "Some (f2 x2) = Some v"
    hence v: "v = f2 x2" by simp
    show "\<exists>k' v'. k = f1 k' \<and> v = f2 v' \<and> map_of ((x1, x2) # xs) k' = Some v'"
      by (rule exI[of _ x1], simp, intro conjI, fact+)
  next
    assume "k \<noteq> f1 x1" and b: "map_of (map (\<lambda>(k, v). (f1 k, f2 v)) xs) k = Some v"
    from IH[OF b] obtain k' where k': "k = f1 k'" and exv': "\<exists>v'. v = f2 v' \<and> map_of xs k' = Some v'"
      by auto
    from exv' obtain v' where v': "v = f2 v'" and m: "map_of xs k' = Some v'" by auto
    from \<open>k \<noteq> f1 x1\<close> k' have "k' \<noteq> x1" by auto
    show "\<exists>k' v'. k = f1 k' \<and> v = f2 v' \<and> map_of ((x1, x2) # xs) k' = Some v'"
    proof (rule exI[of _ k'], simp add: \<open>k' \<noteq> x1\<close>, intro conjI)
      show "\<exists>v'. v = f2 v' \<and> map_of xs k' = Some v'" by (rule exI[of _ v'], intro conjI, fact+)
    qed (fact)
  qed
qed

lemma lookup_0_merge:
  assumes "\<forall>e. (x, e) \<notin> set (AList.merge xs ys)"
  shows "lookup xs x = 0 \<and> lookup ys x = 0"
proof -
  from assms have "x \<notin> fst `set (AList.merge xs ys)" by auto
  from this dom_merge[of xs ys] have tx: "x \<notin> fst `set xs" and ty: "x \<notin> fst `set ys" by simp_all
  from tx map_of_eq_None_iff[of xs x] have "lookup xs x = 0" unfolding lookup_def by simp
  also from ty map_of_eq_None_iff[of ys x] have "lookup ys x = 0" unfolding lookup_def by simp
  ultimately show ?thesis by simp
qed

subsection \<open>Implementation of Power-Products as Association Lists\<close>

lift_definition PP::"('a \<times> 'b::zero) list \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b" is Poly_Lists.lookup by (rule finite_lookup)

code_datatype PP

lemma PP_normalize_cong:
  "PP (normalize xs) = PP xs"
proof (transfer, rule)
  fix xs::"('a * 'b) list" and x
  from lookup_normalize[of xs x] show "lookup (normalize xs) x = lookup xs x" by simp
qed

lemma PP_all_2:
  assumes "P 0 0"
  shows "(\<forall>x. P (PP_Poly_Mapping.lookup (PP xs) x) (PP_Poly_Mapping.lookup (PP ys) x)) =
    list_all (\<lambda>(k, v). P (lookup xs k) (lookup ys k)) (AList.merge xs ys)"
using assms unfolding list_all_def
proof transfer
  fix xs ys::"('b * 'a) list" and P::"'a \<Rightarrow> 'a \<Rightarrow> bool"
  assume "P 0 0"
  show "(\<forall>x. P (lookup xs x) (lookup ys x)) =
       (\<forall>(k, v)\<in>set (AList.merge xs ys). P (lookup xs k) (lookup ys k))"
  proof (intro iffI, clarsimp split: option.split)
    assume a1: "\<forall>(k, v)\<in>set (AList.merge xs ys). P (lookup xs k) (lookup ys k)"
    show "\<forall>x. P (lookup xs x) (lookup ys x)"
    proof (intro allI)
      fix x
      show "P (lookup xs x) (lookup ys x)"
      proof (cases "\<exists>e. (x, e) \<in> set (AList.merge xs ys)")
        case True
        from this obtain e where "(x, e) \<in> set (AList.merge xs ys)" ..
        from this a1 show ?thesis by auto
      next
        case False
        hence b: "\<forall>e. (x, e) \<notin> set (AList.merge xs ys)" by simp
        from lookup_0_merge[OF this] have "lookup xs x = 0" and "lookup ys x = 0" by simp_all
        with \<open>P 0 0\<close> show ?thesis by simp
      qed
    qed
  qed
qed

lemma compute_keys_pp[code]:
  "keys (PP (xs::('a * 'b::zero) list)) = set (map fst (normalize xs))"
proof (transfer, clarsimp simp: lookup_def split: option.split)
  fix xs::"('a * 'b) list"
  show "{k. (\<exists>y. map_of xs k = Some y) \<and> (\<forall>x2. map_of xs k = Some x2 \<longrightarrow> x2 \<noteq> 0)} =
          fst ` set (Poly_Lists.normalize xs)"
  proof
    show "{x. (\<exists>y. map_of xs x = Some y) \<and> (\<forall>x2. map_of xs x = Some x2 \<longrightarrow> x2 \<noteq> 0)} \<subseteq>
          fst ` set (normalize xs)"
    proof
      fix x
      assume "x \<in> {t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)}"
      hence ex: "\<exists>y. map_of xs x = Some y" and all: "\<forall>x2. map_of xs x = Some x2 \<longrightarrow> x2 \<noteq> 0" by auto
      from ex obtain c where c: "map_of xs x = Some c" ..
      from all this have "c \<noteq> 0" by simp
      from normalize_map_of_SomeD[OF c this] show "x \<in> fst ` set (normalize xs)"
        by (simp add: Domain.intros fst_eq_Domain)
    qed
  next
    show "fst ` set (normalize xs) \<subseteq>
          {x. (\<exists>y. map_of xs x = Some y) \<and> (\<forall>x2. map_of xs x = Some x2 \<longrightarrow> x2 \<noteq> 0)}"
    proof
      fix x
      assume "x \<in> fst ` set (normalize xs)"
      from this obtain c where a: "(x, c) \<in> set (normalize xs)" by auto
      show "x \<in> {t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)}"
      proof (rule, intro conjI)
        show "\<exists>y. map_of xs x = Some y" by (rule exI[of _ c], rule normalize_map_of_SomeI, fact)
      next
        show "\<forall>c2. map_of xs x = Some c2 \<longrightarrow> c2 \<noteq> 0"
        proof (intro allI, intro impI)
          fix c2
          assume "map_of xs x = Some c2"
          with normalize_map_of_SomeI[OF a] normalize_nonzero[OF a] show "c2 \<noteq> 0" by simp
        qed
      qed
    qed
  qed
qed

lemma compute_zero_pp[code]: "0 = PP []"
  by transfer (simp add: lookup_def)

lemma compute_plus_pp[code]:
  "PP xs + PP ys = PP (map_ran (\<lambda>k v. lookup xs k + lookup ys k) (AList.merge xs ys))"
  by transfer (auto simp: lookup_def map_ran_conv split: option.split)

lemma compute_lcs_pp[code]:
  "lcs (PP xs) (PP ys) =
  PP (map_ran (\<lambda>k v. Orderings.max (lookup xs k) (lookup ys k)) (AList.merge xs ys))"
  by transfer (auto simp: lookup_def map_ran_conv split: option.split)

lemma compute_lookup_pp[code]:
  "PP_Poly_Mapping.lookup (PP xs) x = lookup xs x"
  by (transfer, simp)

lemma compute_deg_pp[code]:
  "deg (PP xs) = sum_list (map snd (AList.clearjunk xs))"
proof -
  from map_lookup_map_fst[OF distinct_clearjunk, of xs] map_of_clearjunk[of xs]
    have eq: "map (PP_Poly_Mapping.lookup (PP xs)) (map fst (AList.clearjunk xs)) = map snd (AList.clearjunk xs)"
      unfolding compute_lookup_pp lookup_def by simp
    
  have "(keys (PP xs)) \<subseteq> (set (map fst (AList.clearjunk xs)))"
  proof (transfer, rule)
    fix xs::"('b * 'a) list" and x
    assume "x \<in> {x. lookup xs x \<noteq> 0}"
    hence "lookup xs x \<noteq> 0" by simp
    thus "x \<in> set (map fst (AList.clearjunk xs))"
      by (metis Poly_Lists.normalize_def compute_lookup_pp compute_keys_pp image_set in_keys_iff
          map_of_eq_None_iff map_of_filter_NoneI)
  qed

  from deg_superset[OF this]
    have "deg (PP xs) = sum (PP_Poly_Mapping.lookup (PP xs)) (set (map fst (AList.clearjunk xs)))" by simp
  moreover have "\<dots> = sum_list (map (PP_Poly_Mapping.lookup (PP xs)) (map fst (AList.clearjunk xs)))"
    using distinct_clearjunk sum.distinct_set_conv_list by blast
  moreover have "\<dots> = sum_list (map snd (AList.clearjunk xs))" using eq by presburger
  ultimately show ?thesis by (simp only:)
qed

definition adds_pp_canonically_ordered_monoid_add_ordered_ab_semigroup_monoid_add_imp_le::"('b \<Rightarrow>\<^sub>0 'a::{canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}) \<Rightarrow> _ \<Rightarrow> bool"
  where [code_abbrev]: "adds_pp_canonically_ordered_monoid_add_ordered_ab_semigroup_monoid_add_imp_le = (adds)"

lemma compute_adds_pp[code]:
  "adds_pp_canonically_ordered_monoid_add_ordered_ab_semigroup_monoid_add_imp_le (PP xs) (PP ys) =
    (list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys))"
  for xs ys::"('a \<times> 'b::{canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}) list"
  unfolding adds_pp_canonically_ordered_monoid_add_ordered_ab_semigroup_monoid_add_imp_le_def
  unfolding adds_pp
proof transfer
  fix xs ys::"('a * 'b) list"
  show "(\<forall>x. lookup xs x \<le> lookup ys x) = list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys)"
  proof
    assume a1: "\<forall>x. lookup xs x \<le> lookup ys x"
    show "list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys)" unfolding list_all_def
    proof (rule, rule)
      fix x k v
      from a1 show "lookup xs k \<le> lookup ys k" ..
    qed
  next
    assume "list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys)"
    hence a2: "\<forall>(k, v)\<in>(set (AList.merge xs ys)). lookup xs k \<le> lookup ys k"
      unfolding list_all_def by simp
    show "\<forall>x. lookup xs x \<le> lookup ys x"
    proof
      fix x
      show "lookup xs x \<le> lookup ys x"
      proof (cases "x \<in> fst ` (set (AList.merge xs ys))")
        case True
        from this obtain v where "(x, v) \<in> set (AList.merge xs ys)" by auto
        from a2[rule_format, OF this] show ?thesis by simp
      next
        case False
        from False dom_merge[of xs ys] have "x \<notin> fst`set xs" by simp
        hence "map_of xs x = None" by (simp add: map_of_eq_None_iff) 
        hence lxs: "lookup xs x = 0" unfolding lookup_def by simp
        from False dom_merge[of xs ys] have "x \<notin> fst`set ys" by simp
        hence "map_of ys x = None" by (simp add: map_of_eq_None_iff) 
        hence lys: "lookup ys x = 0" unfolding lookup_def by simp
        from lxs lys show ?thesis by simp
      qed
    qed
  qed
qed

lemma compute_minus_pp[code]:
  "PP xs - PP ys = PP (map_ran (\<lambda>k v. lookup xs k - lookup ys k) (AList.merge xs ys))"
  by (intro poly_mapping_eqI) (auto simp add: lookup_minus compute_lookup_pp lookup_def
      map_ran_conv split: option.split)

lemma compute_uminus_pp[code]:
  "- PP ys = PP (map_ran (\<lambda>k v. - lookup ys k) ys)"
  by (intro poly_mapping_eqI) (auto simp add: lookup_minus compute_lookup_pp lookup_def
      map_ran_conv split: option.split)

lemma compute_equal_pp[code]:
  "(equal_class.equal (PP xs) (PP (ys::('a * 'b::{zero,equal}) list))) =
    list_all (\<lambda>(k, v). lookup xs k = lookup ys k) (AList.merge xs ys)"
  unfolding equal_poly_mapping_def by (simp only: PP_all_2)


text\<open>Computing @{term lex} as below is certainly not the most efficient way, but it works.\<close>

lemma compute_lex_pp[code]:
  "(lex (PP xs) (PP (ys::('a::wellorder * 'b::ordered_comm_monoid_add) list))) =
    (let zs = AList.merge xs ys in
      list_all (\<lambda>(x, v). lookup xs x \<le> lookup ys x \<or> list_ex (\<lambda>(y, w). y < x \<and> lookup xs y \<noteq> lookup ys y) zs) zs
    )"
unfolding lex_def Let_def proof transfer
  fix xs ys::"('a * 'b) list"
  show "(\<forall>x. lookup xs x \<le> lookup ys x \<or>
            (\<exists>y<x. lookup xs y \<noteq> lookup ys y)) =
       list_all
        (\<lambda>(x, v).
            lookup xs x \<le> lookup ys x \<or>
            list_ex (\<lambda>(y, w). y < x \<and> lookup xs y \<noteq> lookup ys y)
             (AList.merge xs ys))
        (AList.merge xs ys)" (is "?L = ?R")
  proof (intro iffI)
    assume ?L
    thus ?R unfolding list_all_iff
    proof (intro ballI, clarsimp)
      fix x e
      assume x_in: "(x, e) \<in> set (AList.merge xs ys)"
      assume "\<forall>x. lookup xs x \<le> lookup ys x \<or> (\<exists>y<x. lookup xs y \<noteq> lookup ys y)"
      hence a: "lookup xs x \<le> lookup ys x \<or> (\<exists>y<x. lookup xs y \<noteq> lookup ys y)" by simp
      assume "\<not> list_ex (\<lambda>(y, w). y < x \<and> lookup xs y \<noteq> lookup ys y) (AList.merge xs ys)"
      hence b: "\<forall>(y, w)\<in>(set (AList.merge xs ys)). \<not> (y < x \<and> lookup xs y \<noteq> lookup ys y)"
        unfolding list_ex_iff by auto
      from a show "lookup xs x \<le> lookup ys x"
      proof (rule disjE, simp)
        assume "\<exists>y<x. lookup xs y \<noteq> lookup ys y"
        from this obtain y where y: "y < x \<and> lookup xs y \<noteq> lookup ys y" ..
        show ?thesis
        proof (cases "\<exists>f. (y, f) \<in> set (AList.merge xs ys)")
          case True
          from this obtain f where "(y, f) \<in> set (AList.merge xs ys)" ..
          with b have "\<not> (y < x \<and> lookup xs y \<noteq> lookup ys y)" by auto
          with y show ?thesis by simp
        next
          case False
          hence "\<forall>f. (y, f) \<notin> set (AList.merge xs ys)" by simp
          from lookup_0_merge[OF this] y show ?thesis by simp
        qed
      qed
    qed
  next
    assume ?R
    show ?L
    proof (intro allI)
      fix x
      show "lookup xs x \<le> lookup ys x \<or> (\<exists>y<x. lookup xs y \<noteq> lookup ys y)"
      proof (cases "\<exists>e. (x, e) \<in> set (AList.merge xs ys)")
        case True
        from this obtain e where "(x, e) \<in> set (AList.merge xs ys)" ..
        from this \<open>?R\<close> have "lookup xs x \<le> lookup ys x \<or>
          list_ex (\<lambda>(y, w). y < x \<and> lookup xs y \<noteq> lookup ys y) (AList.merge xs ys)"
          unfolding list_all_iff by auto
        thus ?thesis
        proof
          assume "lookup xs x \<le> lookup ys x"
          thus ?thesis by simp
        next
          assume "list_ex (\<lambda>(y, w). y < x \<and> lookup xs y \<noteq> lookup ys y) (AList.merge xs ys)"
          from this obtain y where "y < x" and "lookup xs y \<noteq> lookup ys y"
            unfolding list_ex_iff by auto
          thus ?thesis by blast
        qed
      next
        case False
        hence b: "\<forall>e. (x, e) \<notin> set (AList.merge xs ys)" by simp
        from lookup_0_merge[OF this] have "lookup xs x = 0" and "lookup ys x = 0" by simp_all
        thus ?thesis by simp
      qed
    qed
  qed
qed

subsubsection \<open>Trivariate Power-Products\<close>

datatype var3 = X | Y | Z

lemma UNIV_var3: "UNIV = {X, Y, Z}"
proof (rule set_eqI)
  fix x::var3
  show "(x \<in> UNIV) = (x \<in> {X, Y, Z})" by (rule, cases x, simp_all)
qed

(*
instantiation var3 :: enum
begin
definition enum_var3::"var3 list" where "enum_var3 \<equiv> [X, Y, Z]"
definition enum_all_var3::"(var3 \<Rightarrow> bool) \<Rightarrow> bool" where "enum_all_var3 p \<equiv> p X \<and> p Y \<and> p Z"
definition enum_ex_var3::"(var3 \<Rightarrow> bool) \<Rightarrow> bool" where "enum_ex_var3 p \<equiv> p X \<or> p Y \<or> p Z"

instance proof (standard, simp_all add: enum_var3_def enum_all_var3_def enum_ex_var3_def, rule UNIV_var3)
  fix P
  show "(P X \<and> P Y \<and> P Z) = All P" by (metis var3.exhaust)
next
  fix P
  show "(P X \<or> P Y \<or> P Z) = Ex P" by (metis var3.exhaust)
qed
end
*)

instantiation var3 :: finite_linorder
begin
fun less_eq_var3::"var3 \<Rightarrow> var3 \<Rightarrow> bool" where
  "less_eq_var3 X X = True"|
  "less_eq_var3 X Y = True"|
  "less_eq_var3 X Z = True"|
  "less_eq_var3 Y X = False"|
  "less_eq_var3 Y Y = True"|
  "less_eq_var3 Y Z = True"|
  "less_eq_var3 Z X = False"|
  "less_eq_var3 Z Y = False"|
  "less_eq_var3 Z Z = True"

definition less_var3::"var3 \<Rightarrow> var3 \<Rightarrow> bool" where "less_var3 a b \<equiv> a \<le> b \<and> \<not> b \<le> a"

lemma Z_less_eq:
  shows "Z \<le> x \<longleftrightarrow> (x = Z)"
by (cases x, simp_all)

lemma Y_less_eq:
  shows "Y \<le> x \<longleftrightarrow> (x \<noteq> X)"
by (cases x, simp_all)

lemma X_less_eq:
  shows "X \<le> x"
by (cases x, simp_all)

lemma less_eq_Z:
  shows "x \<le> Z"
by (cases x, simp_all)

lemma less_eq_Y:
  shows "x \<le> Y \<longleftrightarrow> (x \<noteq> Z)"
by (cases x, simp_all)

lemma less_eq_X:
  shows "x \<le> X \<longleftrightarrow> (x = X)"
by (cases x, simp_all)

lemma less_eq_var3_alt:
  shows "x \<le> y \<longleftrightarrow> ((x = Z \<and> y = Z) \<or> (x = Y \<and> y \<noteq> X) \<or> x = X)"
using X_less_eq Y_less_eq Z_less_eq
by (cases x, simp_all)

instance proof
  fix a b::var3
  show "a < b \<longleftrightarrow> (a \<le> b \<and> \<not> b \<le> a)" unfolding less_var3_def ..
next
  fix a::var3
  show "a \<le> a" by (cases a, simp_all)
next
  fix a b c::var3
  assume "a \<le> b" and "b \<le> c"
  thus "a \<le> c" using less_eq_var3_alt[of a b] less_eq_var3_alt[of b c] less_eq_var3_alt[of a c] by auto
next
  fix a b::var3
  assume "a \<le> b" and "b \<le> a"
  thus "a = b" using less_eq_var3_alt[of a b] less_eq_var3_alt[of b a] by auto
next
  fix a b::var3
  show "a \<le> b \<or> b \<le> a" using X_less_eq[of b] Y_less_eq[of b] less_eq_Z[of b] by (cases a, simp_all)
qed (simp add: UNIV_var3)

end

instantiation var3 :: enum begin
definition "enum_var3 = [X, Y, Z]"
definition "enum_all_var3 P \<longleftrightarrow> P X \<and> P Y \<and> P Z"
definition "enum_ex_var3 P \<longleftrightarrow> P X \<or> P Y \<or> P Z"
instance apply standard
     apply (auto simp: enum_var3_def enum_all_var3_def enum_ex_var3_def)
    apply (metis var3.exhaust)+
  done
end

subsubsection \<open>Computations\<close>

lemma
  "PP [(X, 2::nat), (Z, 7)] + PP [(Y, 3), (Z, 2)] = PP [(X, 2), (Z, 9), (Y, 3)]"
  by eval

lemma
  "PP [(X, 2::nat), (Z, 7)] - PP [(X, 2), (Z, 2)] = PP [(Z, 5)]"
  by eval

lemma
  "lcs (PP [(X, 2::nat), (Y, 1), (Z, 7)]) (PP [(Y, 3), (Z, 2)]) = PP [(X, 2), (Y, 3), (Z, 7)]"
  by eval

lemma
  "(PP [(X, 2::nat), (Z, 1)]) adds (PP [(X, 3), (Y, 2), (Z, 1)])"
  by eval

lemma
  "PP_Poly_Mapping.lookup (PP [(X, 2::nat), (Z, 3)]) X = 2"
  by eval

lemma
  "deg (PP [(X, 2::nat), (Y, 1), (Z, 3), (X, 1)]) = 6"
  by eval

lemma
  "lex (PP [(X, 2::nat), (Y, 1), (Z, 3)]) (PP [(X, 4)])"
by eval

lemma
  "(PP [(X, 2::nat), (Y, 1), (Z, 3)]) \<le> (PP [(X, 4)])"
  by eval

lemma
  "\<not> (dlex (PP [(X, 2::nat), (Y, 1), (Z, 3)]) (PP [(X, 4)]))"
  by eval

text\<open>It is possible to index the indeterminates by natural numbers:\<close>

lemma
  "PP [(0, 2::nat), (2, 7)] + PP [(1, 3), (2, 2)] = PP [(0, 2), (2, 9), (1::nat, 3)]"
  by eval

lemma
  "PP [(0, 2), (2, 7)] - PP [(0, 2), (2, 2)] = PP [(2::nat, 5::nat)]"
  by eval

lemma
  "lcs (PP [(0, 2), (1, 1), (2, 7)]) (PP [(1, 3), (2, 2)]) = PP [(0, 2), (1, 3), (2::nat, 7::nat)]"
  by eval

lemma
  "(PP [(0, 2), (2, 1)]) adds (PP [(0, 3), (1, 2), (2::nat, 1::nat)])"
  by eval

lemma
  "PP_Poly_Mapping.lookup (PP [(0, 2::nat), (2, 3)]) (0::nat) = 2"
by eval

lemma
  "deg (PP [(0, 2), (1, 1), (2, 3), (0::nat, 1::nat)]) = 6"
by eval

lemma
  "lex (PP [(0, 2), (1, 1), (2, 3)]) (PP [(0::nat, 4::nat)])"
by eval

lemma
  "\<not> (dlex (PP [(0, 2), (1, 1), (2, 3)]) (PP [(0::nat, 4::nat)]))"
by eval

subsection \<open>Implementation of Multivariate Polynomials as Association Lists\<close>

subsubsection \<open>Unordered Power-Products\<close>

abbreviation "MP \<equiv> PP"

lemma compute_monom_mult_mpoly[code]:
  "monom_mult c t (MP xs) = (if c = 0 then 0 else MP (map (\<lambda>(k, v). (t + k, c * v)) xs))"
proof (cases "c = 0")
  case True
  hence "monom_mult c t (MP xs) = 0" using monom_mult_left0 by simp
  thus ?thesis using True by simp
next
  case False
  thus ?thesis
  proof (simp, transfer)
    fix c::'b and t::"'a" and xs::"('a * 'b) list"
    show "(\<lambda>s. if t adds s then c * lookup xs (s - t) else 0) =
            lookup (map (\<lambda>(k, v). (t + k, c * v)) xs)"
    proof
      fix s::"'a"
      show "(if t adds s then c * lookup xs (s - t) else 0) =
              lookup (map (\<lambda>(k, v). (t + k, c * v)) xs) s"
      proof (simp add: if_splits(1), intro conjI, intro impI)
        assume "t adds s"
        from this obtain k where k: "s = t + k" unfolding dvd_def ..
        hence div: "s - t = k" by (simp add: ac_simps)
        show "c * lookup xs (s - t) = lookup (map (\<lambda>(k, v). (t + k, c * v)) xs) s"
          unfolding lookup_def div
        proof (split option.split, intro conjI, intro impI)
          assume "map_of (map (\<lambda>(k, v). (t + k, c * v)) xs) s = None"
          hence "s \<notin> fst ` set (map (\<lambda>(k, v). (t + k, c * v)) xs)" by (simp add: map_of_eq_None_iff)
          with k in_fst_set_mapI[of k xs "\<lambda>k. t + k" "\<lambda>v. c * v"] have "k \<notin> fst ` set xs" by auto
          hence "map_of xs k = None" by (simp add: map_of_eq_None_iff)
          thus "c * (case map_of xs k of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = 0" by simp
        next
          show "\<forall>x2. map_of (map (\<lambda>(k, v). (t + k, c * v)) xs) s = Some x2 \<longrightarrow>
                  c * (case map_of xs k of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = x2"
          proof (intro allI, intro impI)
            fix b
            assume "map_of (map (\<lambda>(k, v). (t + k, c * v)) xs) s = Some b"
            from in_set_mapD[OF this] obtain k' and v' where
              k': "s = t + k'" and v': "b = c * v'" and m: "map_of xs k' = Some v'" by auto
            from k k' have "k' = k" by (simp add: ac_simps)
            from this m v' show "c * (case map_of xs k of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = b" by simp
          qed
        qed
      next
        show "\<not> t adds s \<longrightarrow> lookup (map (\<lambda>(k, v). (t + k, c * v)) xs) s = 0"
        proof
          assume ndvd: "\<not> t adds s"
          show "lookup (map (\<lambda>(k, v). (t + k, c * v)) xs) s = 0" unfolding lookup_def
          proof (split option.split, simp, intro allI, intro impI)
            fix b
            assume "map_of (map (\<lambda>(k, v). (t + k, c * v)) xs) s = Some b"
            from in_set_mapD[OF this] obtain k' where "s = t + k'" by auto
            from this ndvd show "b = 0" by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma compute_single_mpoly[code]:
  "PP_Poly_Mapping.single t c = (if c = 0 then 0 else MP [(t, c)])"
  by transfer (auto simp: when_def lookup_def intro!: ext)

lemma compute_except_mpoly[code]:
  "except (MP xs) t = MP (filter (\<lambda>(k, v). k \<noteq> t) xs)"
proof (transfer, rule)
  fix xs::"('a * 'b) list" and t s
  {
    fix c1 c2
    assume "map_of [(k, v)\<leftarrow>xs . k \<noteq> t] t = Some c1"
    from map_of_SomeD[OF this] have False by simp
  }
  thus "(if s = t then 0 else lookup xs s) = lookup [(k, v)\<leftarrow>xs . k \<noteq> t] s"
    by (auto simp add: lookup_def map_of_filter_NoneI map_of_filter_in split: option.split)
qed

subsubsection \<open>Computations\<close>

lemma
  "keys (MP [(PP [(X, 2::nat), (Z, 3)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (PP [(X, 1), (Y, 1)], 0)]) =
    {PP [(X, 2), (Z, 3)], PP [(Y, 3), (Z, 2)]}"
  by eval

lemma
  "- MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] =
    MP [(PP [(X, 2), (Z, 7)], - 1), (PP [(Y, 3), (Z, 2)], - 2)]"
by eval

lemma
  "MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] + MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)] =
    MP [(PP [(X, 2), (Z, 7)], 1), (PP [(X, 2), (Z, 4)], 1)]"
by eval

lemma
  "MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] - MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)] =
    MP [(PP [(X, 2), (Z, 7)], 1), (PP [(Y, 3), (Z, 2)], 4), (PP [(X, 2), (Z, 4)], - 1)]"
by eval

lemma
  "PP_Poly_Mapping.lookup (MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (PP [], 2)]) (PP [(X, 2), (Z, 7)]) = 1"
by eval

lemma
  "MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] \<noteq> MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]"
by eval

lemma
  "MP [(PP [(X, 2::nat), (Z, 7)], 0::rat), (PP [(Y, 3), (Z, 2)], 0)] = 0"
by eval

lemma
  "monom_mult (3::rat) (PP [(Y, 2::nat)]) (MP [(PP [(X, 2), (Z, 1)], 1), (PP [(Y, 3), (Z, 2)], 2)]) =
    MP [(PP [(Y, 2), (Z, 1), (X, 2)], 3), (PP [(Y, 5), (Z, 2)], 6)]"
by eval

lemma
  "PP_Poly_Mapping.single  (PP [(X, 2::nat)]) (-4::rat) = MP [(PP [(X, 2)], - 4)]"
by eval

lemma
  "PP_Poly_Mapping.single (PP [(X, 2::nat)])  (0::rat) = 0"
by eval

lemma
  "some_term (MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3::nat), (Z, 2)], 2), (0, 2)]) =
    PP [(X, 2::nat), (Z, 7)]"
  by eval

lemma
  "rest_mpoly (MP [(PP [(X, 2::nat), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (0, 2)]) =
    MP [(PP [(Y, 3), (Z, 2)], 2), (0, 2)]"
  by eval

lemma
  "MP [(PP [(X, 2::nat), (Z, 1)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] *pm
      MP [(PP [(X, 2), (Z, 3)], 1), (PP [(Y, 3), (Z, 2)], -2)] =
    MP [(PP [(X, 4), (Z, 4)], 1), (PP [(X, 2), (Z, 3), (Y, 3)], - 2), (PP [(Y, 6), (Z, 4)], - 4), (PP [(Y, 3), (Z, 5), (X, 2)], 2)]"
  by eval

subsubsection \<open>Ordered Power-Products\<close>

context ordered_powerprod
begin

definition list_max::"'a list \<Rightarrow> 'a" where
  "list_max xs \<equiv> foldl ordered_powerprod_lin.max 0 xs"

lemma list_max_Cons:
  shows "list_max (x # xs) = ordered_powerprod_lin.max x (list_max xs)"
unfolding list_max_def foldl_Cons
proof -
  have "foldl ordered_powerprod_lin.max (ordered_powerprod_lin.max x 0) xs =
          ordered_powerprod_lin.max x (foldl ordered_powerprod_lin.max 0 xs)"
    by (rule foldl_assoc, rule ordered_powerprod_lin.max.assoc)
  from this ordered_powerprod_lin.max.commute[of 0 x]
    show "foldl ordered_powerprod_lin.max (ordered_powerprod_lin.max 0 x) xs =
            ordered_powerprod_lin.max x (foldl ordered_powerprod_lin.max 0 xs)" by simp
qed

lemma list_max_empty:
  shows "list_max [] = 0"
unfolding list_max_def by simp

lemma list_max_in_list:
  fixes xs::"'a list"
  assumes "xs \<noteq> []"
  shows "list_max xs \<in> set xs"
using assms
proof (induct xs, simp)
  fix x xs
  assume IH: "xs \<noteq> [] \<Longrightarrow> list_max xs \<in> set xs"
  show "list_max (x # xs) \<in> set (x # xs)"
  proof (cases "xs = []")
    case True
    hence "list_max (x # xs) = ordered_powerprod_lin.max 0 x" unfolding list_max_def by simp
    also have "\<dots> = x" unfolding ordered_powerprod_lin.max_def by (simp add: one_min)
    finally show ?thesis by simp
  next
    assume "xs \<noteq> []"
    show ?thesis
    proof (cases "x \<preceq> list_max xs")
      case True
      hence "list_max (x # xs) = list_max xs"
        unfolding list_max_Cons ordered_powerprod_lin.max_def by simp
      thus ?thesis using IH[OF \<open>xs \<noteq> []\<close>] by simp
    next
      case False
      hence "list_max (x # xs) = x" unfolding list_max_Cons ordered_powerprod_lin.max_def by simp
      thus ?thesis by simp
    qed
  qed
qed

lemma list_max_maximum:
  fixes xs::"'a list"
  assumes "a \<in> set xs"
  shows "a \<preceq> (list_max xs)"
using assms
proof (induct xs)
  assume "a \<in> set []"
  thus "a \<preceq> list_max []" by simp
next
  fix x xs
  assume IH: "a \<in> set xs \<Longrightarrow> a \<preceq> list_max xs" and a_in: "a \<in> set (x # xs)"
  from a_in have "a = x \<or> a \<in> set xs" by simp
  thus "a \<preceq> list_max (x # xs)" unfolding list_max_Cons
  proof
    assume "a = x"
    thus "a \<preceq> ordered_powerprod_lin.max x (list_max xs)" by simp
  next
    assume "a \<in> set xs"
    from IH[OF this] show "a \<preceq> ordered_powerprod_lin.max x (list_max xs)"
      by (simp add: ordered_powerprod_lin.le_max_iff_disj)
  qed
qed

lemma list_max_nonempty:
  fixes xs::"'a list"
  assumes "xs \<noteq> []"
  shows "list_max xs = ordered_powerprod_lin.Max (set xs)"
proof -
  have fin: "finite (set xs)" by simp
  have "ordered_powerprod_lin.Max (set xs) = list_max xs"
  proof (rule ordered_powerprod_lin.Max_eqI[OF fin, of "list_max xs"])
    fix y
    assume "y \<in> set xs"
    from list_max_maximum[OF this] show "y \<preceq> list_max xs" .
  next
    from list_max_in_list[OF assms] show "list_max xs \<in> set xs" .
  qed
  thus ?thesis by simp
qed

lemma compute_lp_mpoly[code]:
  "lp (MP xs) = list_max (map fst (normalize xs))"
unfolding lp_def compute_keys_pp
proof (split if_splits, intro conjI, intro impI)
  assume "MP xs = 0"
  from this have "keys (MP xs) = {}" by simp
  hence "map fst (normalize xs) = []" unfolding compute_keys_pp by simp
  thus "0 = list_max (map fst (normalize xs))" using list_max_empty by simp
next
  show "MP xs \<noteq> 0 \<longrightarrow>
    ordered_powerprod_lin.Max (set (map fst (normalize xs))) = list_max (map fst (normalize xs))"
  proof (intro impI)
    assume "MP xs \<noteq> 0"
    from this have "keys (MP xs) \<noteq> {}" by simp
    hence "map fst (normalize xs) \<noteq> []" unfolding compute_keys_pp by simp
    from list_max_nonempty[OF this]
      show "ordered_powerprod_lin.Max (set (map fst (normalize xs))) =
            list_max (map fst (normalize xs))" by simp
  qed
qed

lemma compute_higher_mpoly[code]:
  "higher (MP xs) t = MP (filter (\<lambda>(k, v). t \<prec> k) xs)"
proof (transfer, rule)
  fix xs::"('a * 'b) list" and t s
  {
    fix c1 c2
    assume a: "map_of [(k, v)\<leftarrow>xs . t \<prec> k] s = Some c2" and "\<not> t \<prec> s"
    from map_of_SomeD[OF a] \<open>\<not> t \<prec> s\<close> have False by simp
  }
  thus "(if t \<prec> s then lookup xs s else 0) = lookup [(k, v)\<leftarrow>xs . t \<prec> k] s"
    by (auto simp add: lookup_def map_of_filter_in map_of_filter_NoneI split: option.split)
qed

lemma compute_lower_mpoly[code]:
  "lower (MP xs) t = MP (filter (\<lambda>(k, v). k \<prec> t) xs)"
proof (transfer, rule)
  fix xs::"('a * 'b) list" and t s
  {
    fix c1 c2
    assume a: "map_of [(k, v)\<leftarrow>xs . k \<prec> t] s = Some c2" and "\<not> s \<prec> t"
    from map_of_SomeD[OF a] \<open>\<not> s \<prec> t\<close> have False by simp
  }
  thus "(if s \<prec> t then lookup xs s else 0) = lookup [(k, v)\<leftarrow>xs . k \<prec> t] s"
    by (auto simp add: lookup_def map_of_filter_in map_of_filter_NoneI split: option.split)
qed

end (* ordered_powerprod *)

lifting_update mpoly.lifting
lifting_forget mpoly.lifting

end (* theory *)
