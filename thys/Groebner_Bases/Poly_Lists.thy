(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Executable Representation of Multivariate Polynomials for Computing Gr\"obner Bases\<close>

theory Poly_Lists
imports Groebner_Bases "~~/src/HOL/Library/AList"
begin

text \<open>In this theory, power-products of type @{typ "'a pp"} and multivariate polynomials of type
  @{typ "('a, 'b) mpoly"} are represented as association lists. Code equations are proved in order
  to actually compute Gr\"obner bases of polynomial ideals.
  In principle, one could also build upon @{cite Sternagel2010}, although there the representations of
  power-products and polynomials additionally have to satisfy certain invariants, which we do not
  require here.\<close>

subsection \<open>General-Purpose Lemmas\<close>

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

subsection \<open>Implementation of Power-Products as Association Lists\<close>

definition "lookup = (\<lambda>xs i. case map_of xs i of Some i \<Rightarrow> i | None \<Rightarrow> 0)"

lift_definition PP::"('a \<times> nat) list \<Rightarrow> 'a pp" is lookup .

code_datatype PP

lemma compute_one_pp[code]: "(1::'v pp) = PP []"
  by transfer (simp add: lookup_def)

lemma compute_times_pp[code]:
  "PP xs * PP ys = PP (map_ran (\<lambda>k v. lookup xs k + lookup ys k) (AList.merge xs ys))"
  by transfer (auto simp: lookup_def map_ran_conv split: option.split)

lemma compute_lcm_pp[code]:
  "lcm (PP xs) (PP ys) =
  PP (map_ran (\<lambda>k v. Orderings.max (lookup xs k) (lookup ys k)) (AList.merge xs ys))"
  by transfer (auto simp: lookup_def map_ran_conv split: option.split)

lemma compute_exp_pp[code]:
  "exp (PP xs) x = lookup xs x"
by (transfer, simp)

lemma clearjunk_distinct:
  shows "distinct (AList.clearjunk xs)"
using distinct_clearjunk[of xs] distinct_map[of fst] by blast

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

lemma compute_deg_pp[code]:
  "deg (PP xs) = listsum (map snd (AList.clearjunk xs))"
unfolding deg_def
proof transfer
  fix xs::"('a * nat) list"

  from map_lookup_map_fst[OF distinct_clearjunk, of xs] map_of_clearjunk[of xs]
    have eq: "map (lookup xs) (map fst (AList.clearjunk xs)) = map snd (AList.clearjunk xs)"
      unfolding lookup_def by simp

  have "setsum (lookup xs) UNIV = setsum (lookup xs) (set (map fst xs))"
  proof (rule setsum.mono_neutral_right, simp_all, intro ballI)
    fix x
    assume "x \<in> UNIV - fst ` set xs"
    hence a: "x \<notin> (fst ` set xs)" by simp
    show "lookup xs x = 0" unfolding lookup_def
    proof (clarsimp split: option.split)
      fix e
      assume "map_of xs x = Some e"
      from map_of_SomeD[OF this] have "x \<in> (fst ` set xs)" by (simp add: rev_image_eqI)
      from this a show "e = 0" by simp
    qed
  qed
  also have "\<dots> = setsum (lookup xs) (set (map fst (AList.clearjunk xs)))"
    using clearjunk_keys_set[of xs] by simp
  also have "\<dots> = listsum (map (lookup xs) (map fst (AList.clearjunk xs)))"
    using setsum_code[of "lookup xs" "map fst (AList.clearjunk xs)"]
          distinct_remdups_id[OF distinct_clearjunk[of xs]] by simp
  also have "\<dots> = listsum (map snd (AList.clearjunk xs))" by (simp only: eq)
  finally show "setsum (lookup xs) UNIV = listsum (map snd (AList.clearjunk xs))" .
qed

lemma compute_dvd_pp:
  "(PP xs) dvd (PP ys) = (list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys))"
unfolding dvd_pp
proof transfer
  fix xs ys::"('a * nat) list"
  show "(\<forall>x. lookup xs x \<le> lookup ys x) = list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys)"
  proof
    assume a1: "\<forall>x. lookup xs x \<le> lookup ys x"
    show "list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys)" unfolding pred_list_def
    proof (rule, rule)
      fix x k v
      from a1 show "lookup xs k \<le> lookup ys k" ..
    qed
  next
    assume "list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys)"
    hence a2: "\<forall>(k, v)\<in>(set (AList.merge xs ys)). lookup xs k \<le> lookup ys k"
      unfolding pred_list_def by simp
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

lemma compute_dummy_dvd_pp[code]:
  "dummy_dvd (PP xs) (PP ys) = (list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge xs ys))"
unfolding dummy_dvd_iff by (rule compute_dvd_pp)

lemma list_all_merge_comm:
  assumes "list_all (\<lambda>(k, v). P (lookup xs k) (lookup ys k)) (AList.merge xs ys)"
  shows "list_all (\<lambda>(k, v). P (lookup xs k) (lookup ys k)) (AList.merge ys xs)"
unfolding pred_list_def
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
    unfolding pred_list_def .
  from this a show "P (lookup xs k) (lookup ys k)" by auto
qed

lemma compute_dvd_pp_alt:
  "(PP xs dvd PP ys) = (list_all (\<lambda>(k, v). lookup xs k \<le> lookup ys k) (AList.merge ys xs))"
unfolding compute_dvd_pp by (rule, erule list_all_merge_comm, erule list_all_merge_comm)

lemma compute_div_pp_1:
  assumes "(PP ys) dvd (PP xs)"
  shows "PP xs divide PP ys = PP (map_ran (\<lambda>k v. lookup xs k - lookup ys k) (AList.merge xs ys))"
proof (intro pp_eq_intro)
  fix x
  show "exp (PP xs divide PP ys) x = exp (PP (map_ran (\<lambda>k v. lookup xs k - lookup ys k) (AList.merge xs ys))) x"
    by (auto simp add: exp_div_pp assms compute_exp_pp lookup_def map_ran_conv split: option.split)
qed

lemma compute_div_pp_2:
  assumes "\<not> (PP ys) dvd (PP xs)"
  shows "PP xs divide PP ys = PP []"
proof (intro pp_eq_intro)
  fix x
  show "exp (PP xs divide PP ys) x = exp (PP []) x"
    by (auto simp add: exp_div_pp assms compute_exp_pp lookup_def map_ran_conv split: option.split)
qed

lemma compute_div_pp[code]:
  "PP xs divide PP ys =
    (let m = (AList.merge xs ys) in
      (if (list_all (\<lambda>(k, v). lookup ys k \<le> lookup xs k) m) then
        PP (map_ran (\<lambda>k v. lookup xs k - lookup ys k) m)
      else
        PP []
      )
    )"
proof (simp add: Let_def, intro conjI)
  show "list_all (\<lambda>(k, v). lookup ys k \<le> lookup xs k) (AList.merge xs ys) \<longrightarrow>
          PP xs divide PP ys =
          PP (map_ran (\<lambda>k v. lookup xs k - lookup ys k) (AList.merge xs ys))"
  proof
    assume a: "list_all (\<lambda>(k::'a, v::nat). lookup ys k \<le> lookup xs k) (AList.merge xs ys)"
    hence "PP ys dvd PP xs" unfolding compute_dvd_pp_alt[of ys xs] .
    from compute_div_pp_1[OF this]
      show "PP xs divide PP ys = PP (map_ran (\<lambda>k v. lookup xs k - lookup ys k) (AList.merge xs ys))" .
  qed
next
  show "\<not> list_all (\<lambda>(k, v). lookup ys k \<le> lookup xs k) (AList.merge xs ys) \<longrightarrow>
          PP xs divide PP ys = PP []"
  proof
    assume "\<not> list_all (\<lambda>(k, v). lookup ys k \<le> lookup xs k) (AList.merge xs ys)"
    hence "\<not> PP ys dvd PP xs" unfolding compute_dvd_pp_alt .
    from compute_div_pp_2[OF this] show "PP xs divide PP ys = PP []" .
  qed
qed

subsubsection \<open>Trivariate Power-Products\<close>

datatype var = X | Y | Z

instantiation var :: enum
begin
definition enum_var::"var list" where "enum_var \<equiv> [X, Y, Z]"
definition enum_all_var::"(var \<Rightarrow> bool) \<Rightarrow> bool" where "enum_all_var p \<equiv> p X \<and> p Y \<and> p Z"
definition enum_ex_var::"(var \<Rightarrow> bool) \<Rightarrow> bool" where "enum_ex_var p \<equiv> p X \<or> p Y \<or> p Z"

instance proof (standard, simp_all add: enum_var_def enum_all_var_def enum_ex_var_def)
  show "UNIV = {X, Y, Z}"
  proof (rule set_eqI)
    fix x::var
    show "(x \<in> UNIV) = (x \<in> {X, Y, Z})" by (rule, cases x, simp_all)
  qed
next
  fix P
  show "(P X \<and> P Y \<and> P Z) = All P" by (metis var.exhaust)
next
  fix P
  show "(P X \<or> P Y \<or> P Z) = Ex P" by (metis var.exhaust)
qed
end

instantiation var :: finite_linorder
begin
fun less_eq_var::"var \<Rightarrow> var \<Rightarrow> bool" where
  "less_eq_var X X = True"|
  "less_eq_var X Y = False"|
  "less_eq_var X Z = False"|
  "less_eq_var Y X = True"|
  "less_eq_var Y Y = True"|
  "less_eq_var Y Z = False"|
  "less_eq_var Z X = True"|
  "less_eq_var Z Y = True"|
  "less_eq_var Z Z = True"

definition less_var::"var \<Rightarrow> var \<Rightarrow> bool" where "less_var a b \<equiv> a \<le> b \<and> \<not> b \<le> a"

lemma X_less_eq:
  shows "X \<le> x \<longleftrightarrow> (x = X)"
by (cases x, simp_all)

lemma Y_less_eq:
  shows "Y \<le> x \<longleftrightarrow> (x \<noteq> Z)"
by (cases x, simp_all)

lemma Z_less_eq:
  shows "Z \<le> x"
by (cases x, simp_all)

lemma less_eq_X:
  shows "x \<le> X"
by (cases x, simp_all)

lemma less_eq_Y:
  shows "x \<le> Y \<longleftrightarrow> (x \<noteq> X)"
by (cases x, simp_all)

lemma less_eq_Z:
  shows "x \<le> Z \<longleftrightarrow> (x = Z)"
by (cases x, simp_all)

lemma less_eq_var_alt:
  shows "x \<le> y \<longleftrightarrow> ((x = X \<and> y = X) \<or> (x = Y \<and> y \<noteq> Z) \<or> x = Z)"
using X_less_eq Y_less_eq Z_less_eq
by (cases x, simp_all)

instance proof
  fix a b::var
  show "a < b \<longleftrightarrow> (a \<le> b \<and> \<not> b \<le> a)" unfolding less_var_def ..
next
  fix a::var
  show "a \<le> a" by (cases a, simp_all)
next
  fix a b c::var
  assume "a \<le> b" and "b \<le> c"
  thus "a \<le> c" using less_eq_var_alt[of a b] less_eq_var_alt[of b c] less_eq_var_alt[of a c] by auto
next
  fix a b::var
  assume "a \<le> b" and "b \<le> a"
  thus "a = b" using less_eq_var_alt[of a b] less_eq_var_alt[of b a] by auto
next
  fix a b::var
  show "a \<le> b \<or> b \<le> a" using less_eq_X[of b] Y_less_eq[of b] Z_less_eq[of b] by (cases a, simp_all)
qed

end

lifting_update pp.lifting
lifting_forget pp.lifting

subsubsection \<open>Computations\<close>

lemma
  "PP [(X, 2), (Z, 7)] * PP [(Y, 3), (Z, 2)] = PP [(X, 2), (Z, 9), (Y, 3)]"
by eval

lemma
  "PP [(X, 2), (Z, 7)] divide PP [(Y, 3), (Z, 2)] = 1"
by eval

lemma
  "PP [(X, 2), (Z, 7)] divide PP [(X, 2), (Z, 2)] = PP [(Z, 5)]"
by eval

lemma
  "lcm (PP [(X, 2), (Y, 1), (Z, 7)]) (PP [(Y, 3), (Z, 2)]) = PP [(X, 2), (Y, 3), (Z, 7)]"
by eval

lemma
  "dummy_dvd (PP [(X, 2), (Z, 1)]) (PP [(X, 3), (Y, 2), (Z, 1)])"
by eval

lemma
  "exp (PP [(X, 2), (Z, 3)]) X = 2"
by eval

lemma
  "deg (PP [(X, 2), (Y, 1), (Z, 3), (X, 1)]) = 6"
by eval

lemma
  "lex (PP [(X, 2), (Y, 1), (Z, 3)]) (PP [(X, 4)])"
by eval

lemma
  "(PP [(X, 2), (Y, 1), (Z, 3)]) \<le> (PP [(X, 4)])"
by eval

lemma
  "\<not> (dlex (PP [(X, 2), (Y, 1), (Z, 3)]) (PP [(X, 4)]))"
by eval

subsection \<open>Implementation of Multivariate Polynomials as Association Lists\<close>

subsubsection \<open>Unordered Power-Products\<close>

definition "lookup_mpoly = (\<lambda>xs i. case map_of xs i of Some i \<Rightarrow> i | None \<Rightarrow> 0)"

lift_definition MP::"('a * 'b) list \<Rightarrow> ('a, 'b::zero) mpoly" is lookup_mpoly
proof -
  fix xs::"('a * 'b) list"
  have a: "finite (fst ` set xs)" by simp
  have "{t. lookup_mpoly xs t \<noteq> 0} \<subseteq> fst ` set xs"
  proof
    fix x
    assume "x \<in> {t. lookup_mpoly xs t \<noteq> 0}"
    hence "lookup_mpoly xs x \<noteq> 0" by simp
    from this obtain c where c: "map_of xs x = Some c" unfolding lookup_mpoly_def by fastforce
    show "x \<in> fst ` set xs"
    proof
      show "x = fst (x, c)" by simp
    next
      from map_of_SomeD[OF c] show "(x, c) \<in> set xs" .
    qed
  qed
  from finite_subset[OF this a] show "finite {t. lookup_mpoly xs t \<noteq> 0}" .
qed

code_datatype MP

definition normalize_MP::"('a * 'b::zero) list \<Rightarrow> ('a * 'b) list" where
  "normalize_MP xs \<equiv> filter (\<lambda>(k, v). v \<noteq> 0) (AList.clearjunk xs)"

lemma distinct_normalize_MP:
  assumes "distinct (map fst xs)"
  shows "normalize_MP xs = filter (\<lambda>(k, v). v \<noteq> 0) xs"
by (simp add: normalize_MP_def distinct_clearjunk_id[OF assms])

lemma normalize_MP_distinct:
  shows "distinct (map fst (normalize_MP xs))"
unfolding normalize_MP_def
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
  shows "lookup_mpoly xs s = lookup_mpoly (normalize_MP xs) s"
unfolding normalize_MP_def lookup_mpoly_def
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
  assumes "(t, c) \<in> set (normalize_MP xs)"
  shows "c \<noteq> 0"
using assms unfolding normalize_MP_def by simp

lemma normalize_map_of_SomeI:
  assumes "(t, c) \<in> set (normalize_MP xs)"
  shows "map_of xs t = Some c"
proof -
  from map_of_is_SomeI[OF normalize_MP_distinct assms] lookup_normalize[of xs t]
    have a: "(case map_of xs t of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = c" unfolding lookup_mpoly_def by simp
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

lemma normalize_cong:
  "MP (normalize_MP xs) = MP xs"
proof (transfer, rule)
  fix xs::"('a * 'b) list" and x
  from lookup_normalize[of xs x] show "lookup_mpoly (normalize_MP xs) x = lookup_mpoly xs x" by simp
qed

lemma normalize_map_of_SomeD:
  assumes a1: "map_of xs t = Some c" and "c \<noteq> 0"
  shows "(t, c) \<in> set (normalize_MP xs)"
proof -
  from lookup_normalize[of xs t] a1
    have a: "c = (case map_of (normalize_MP xs) t of None \<Rightarrow> 0 | Some i \<Rightarrow> i)"
    unfolding lookup_mpoly_def by simp
  show ?thesis
  proof (cases "map_of (normalize_MP xs) t")
    case None
    thus ?thesis using a \<open>c \<noteq> 0\<close> by simp
  next
    case Some
    fix b
    assume b: "map_of (normalize_MP xs) t = Some b"
    from this a map_of_SomeD[OF this] show ?thesis by simp
  qed
qed

lemma compute_supp_mpoly[code]:
  "supp (MP (xs::('a * 'b::zero) list)) = set (map fst (normalize_MP xs))"
proof (transfer, clarsimp simp: lookup_mpoly_def split: option.split)
  fix xs::"('a * 'b) list"
  show "{t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)} =
        fst ` set (normalize_MP xs)"
  proof
    show "{t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)} \<subseteq>
          fst ` set (normalize_MP xs)"
    proof
      fix t
      assume "t \<in> {t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)}"
      hence ex: "\<exists>y. map_of xs t = Some y" and all: "\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0" by auto
      from ex obtain c where c: "map_of xs t = Some c" ..
      from all this have "c \<noteq> 0" by simp
      from normalize_map_of_SomeD[OF c this] show "t \<in> fst ` set (normalize_MP xs)"
        by (simp add: Domain.intros fst_eq_Domain)
    qed
  next
    show "fst ` set (normalize_MP xs) \<subseteq>
          {t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)}"
    proof
      fix t
      assume "t \<in> fst ` set (normalize_MP xs)"
      from this obtain c where a: "(t, c) \<in> set (normalize_MP xs)" by auto
      show "t \<in> {t. (\<exists>y. map_of xs t = Some y) \<and> (\<forall>x2. map_of xs t = Some x2 \<longrightarrow> x2 \<noteq> 0)}"
      proof (rule, intro conjI)
        show "\<exists>y. map_of xs t = Some y" by (rule exI[of _ c], rule normalize_map_of_SomeI, fact)
      next
        show "\<forall>c2. map_of xs t = Some c2 \<longrightarrow> c2 \<noteq> 0"
        proof (intro allI, intro impI, intro notI)
          fix c2
          assume "map_of xs t = Some c2" and "c2 = 0"
          hence "map_of xs t = Some 0" by simp
          from normalize_map_of_SomeI[OF a] normalize_nonzero[OF a] this show False by simp
        qed
      qed
    qed
  qed
qed

lemma compute_zero_mpoly[code]: "(0::('a, 'b::zero) mpoly) = MP []"
  by transfer (simp add: lookup_mpoly_def)

lemma compute_plus_mpoly[code]:
  "MP xs + MP ys =
    MP (normalize_MP (map_ran (\<lambda>k v. lookup_mpoly xs k + lookup_mpoly ys k) (AList.merge xs ys)))"
unfolding normalize_cong
by transfer (auto simp: lookup_mpoly_def map_ran_conv split: option.split)

lemma compute_uminus_mpoly[code]:
  "- MP xs = MP (map (\<lambda>(k, v). (k, -v)) xs)"
by (transfer, auto simp: lookup_mpoly_def map_of_map split: option.split)

lemma compute_coeff_mpoly[code]:
  "coeff (MP xs) t = lookup_mpoly xs t"
by (transfer, simp)

lemma compute_equal_mpoly[code]:
  "(equal_class.equal (MP xs) (MP (ys::('a * 'b::{equal, zero}) list))) =
    list_all (\<lambda>(k, v). lookup_mpoly xs k = lookup_mpoly ys k) (AList.merge xs ys)"
unfolding equal_mpoly_def pred_list_def
proof (rule, clarsimp split: option.split)
  fix k v
  assume "\<forall>t. coeff (MP xs) t = coeff (MP ys) t"
  hence "coeff (MP xs) k = coeff (MP ys) k" ..
  thus "lookup_mpoly xs k = lookup_mpoly ys k" unfolding compute_coeff_mpoly .
next
  assume a: "\<forall>(k, v)\<in>set (AList.merge xs ys). lookup_mpoly xs k = lookup_mpoly ys k"
  show "\<forall>t. coeff (MP xs) t = coeff (MP ys) t"
  proof
    fix t
    show "coeff (MP xs) t = coeff (MP ys) t"
    proof (cases "\<exists>c. (t, c) \<in> set (AList.merge xs ys)")
      case True
      from this obtain c where "(t, c) \<in> set (AList.merge xs ys)" ..
      from this a have "lookup_mpoly xs t = lookup_mpoly ys t" by auto
      thus ?thesis unfolding compute_coeff_mpoly .
    next
      case False
      hence b: "\<forall>c. (t, c) \<notin> set (AList.merge xs ys)" by simp
      hence "t \<notin> fst `set (AList.merge xs ys)" by auto
      from this dom_merge[of xs ys] have tx: "t \<notin> fst `set xs" and ty: "t \<notin> fst `set ys" by simp_all
      from tx map_of_eq_None_iff[of xs t] have "coeff (MP xs) t = 0"
        unfolding compute_coeff_mpoly lookup_mpoly_def by simp
      also from ty map_of_eq_None_iff[of ys t] have "coeff (MP ys) t = 0"
        unfolding compute_coeff_mpoly lookup_mpoly_def by simp
      finally show ?thesis by simp
    qed
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

lemma compute_monom_mult_mpoly[code]:
  "monom_mult c t (MP xs) = (if c = 0 then 0 else MP (map (\<lambda>(k, v). (t * k, c * v)) xs))"
proof (cases "c = 0")
  case True
  hence "monom_mult c t (MP xs) = 0" using monom_mult_left0 by simp
  thus ?thesis using True by simp
next
  case False
  thus ?thesis
  proof (simp, transfer)
    fix c::'b and t::"'a" and xs::"('a * 'b) list"
    show "(\<lambda>s. if t dvd s then c * lookup_mpoly xs (s divide t) else 0) =
            lookup_mpoly (map (\<lambda>(k, v). (t * k, c * v)) xs)"
    proof
      fix s::"'a"
      show "(if t dvd s then c * lookup_mpoly xs (s divide t) else 0) =
              lookup_mpoly (map (\<lambda>(k, v). (t * k, c * v)) xs) s"
      proof (simp add: if_splits(1), intro conjI, intro impI)
        assume "t dvd s"
        from this obtain k where k: "s = t * k" unfolding dvd_def ..
        hence div: "s divide t = k" using times_divide[of k t] by (simp add: ac_simps)
        show "c * lookup_mpoly xs (s divide t) = lookup_mpoly (map (\<lambda>(k, v). (t * k, c * v)) xs) s"
          unfolding lookup_mpoly_def div
        proof (split option.split, intro conjI, intro impI)
          assume "map_of (map (\<lambda>(k, v). (t * k, c * v)) xs) s = None"
          hence "s \<notin> fst ` set (map (\<lambda>(k, v). (t * k, c * v)) xs)" by (simp add: map_of_eq_None_iff)
          with k in_fst_set_mapI[of k xs "\<lambda>k. t * k" "\<lambda>v. c * v"] have "k \<notin> fst ` set xs" by auto
          hence "map_of xs k = None" by (simp add: map_of_eq_None_iff)
          thus "c * (case map_of xs k of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = 0" by simp
        next
          show "\<forall>x2. map_of (map (\<lambda>(k, v). (t * k, c * v)) xs) s = Some x2 \<longrightarrow>
                  c * (case map_of xs k of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = x2"
          proof (intro allI, intro impI)
            fix b
            assume "map_of (map (\<lambda>(k, v). (t * k, c * v)) xs) s = Some b"
            from in_set_mapD[OF this] obtain k' and v' where
              k': "s = t * k'" and v': "b = c * v'" and m: "map_of xs k' = Some v'" by auto
            from k k' cancel[of k t k'] have "k' = k" by (simp add: ac_simps)
            from this m v' show "c * (case map_of xs k of None \<Rightarrow> 0 | Some i \<Rightarrow> i) = b" by simp
          qed
        qed
      next
        show "\<not> t dvd s \<longrightarrow> lookup_mpoly (map (\<lambda>(k, v). (t * k, c * v)) xs) s = 0"
        proof
          assume ndvd: "\<not> t dvd s"
          show "lookup_mpoly (map (\<lambda>(k, v). (t * k, c * v)) xs) s = 0" unfolding lookup_mpoly_def
          proof (split option.split, simp, intro allI, intro impI)
            fix b
            assume "map_of (map (\<lambda>(k, v). (t * k, c * v)) xs) s = Some b"
            from in_set_mapD[OF this] obtain k' where "s = t * k'" by auto
            from this ndvd show "b = 0" by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma compute_monom_mpoly[code]:
  "monom c t = (if c = 0 then 0 else MP [(t, c)])"
by (transfer, auto simp: lookup_mpoly_def)

lemma compute_except_mpoly[code]:
  "except (MP xs) t = MP (filter (\<lambda>(k, v). k \<noteq> t) xs)"
proof (transfer, rule)
  fix xs::"('a * 'b) list" and t s
  {
    fix c1 c2
    assume "map_of [(k, v)\<leftarrow>xs . k \<noteq> t] t = Some c1"
    from map_of_SomeD[OF this] have False by simp
  }
  thus "(if s = t then 0 else lookup_mpoly xs s) = lookup_mpoly [(k, v)\<leftarrow>xs . k \<noteq> t] s"
    by (auto simp add: lookup_mpoly_def map_of_filter_NoneI map_of_filter_in split: option.split)
qed

subsubsection \<open>Computations\<close>

lemma
  "supp (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (PP [(X, 1), (Y, 1)], 0)]) =
    {PP [(X, 2), (Z, 3)], PP [(Y, 3), (Z, 2)]}"
by eval

lemma
  "- MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] =
    MP [(PP [(X, 2), (Z, 7)], - 1), (PP [(Y, 3), (Z, 2)], - 2)]"
by eval

lemma
  "MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] + MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)] =
    MP [(PP [(X, 2), (Z, 7)], 1), (PP [(X, 2), (Z, 4)], 1)]"
by eval

lemma
  "MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] - MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)] =
    MP [(PP [(X, 2), (Z, 7)], 1), (PP [(Y, 3), (Z, 2)], 4), (PP [(X, 2), (Z, 4)], - 1)]"
by eval

lemma
  "coeff (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (PP [], 2)]) (PP [(X, 2), (Z, 7)]) = 1"
by eval

lemma
  "MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] \<noteq> MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]"
by eval

lemma
  "MP [(PP [(X, 2), (Z, 7)], 0::rat), (PP [(Y, 3), (Z, 2)], 0)] = 0"
by eval

lemma
  "monom_mult (3::rat) (PP [(Y, 2)]) (MP [(PP [(X, 2), (Z, 1)], 1), (PP [(Y, 3), (Z, 2)], 2)]) =
    MP [(PP [(Y, 2), (Z, 1), (X, 2)], 3), (PP [(Y, 5), (Z, 2)], 6)]"
by eval

lemma
  "monom (-4::rat) (PP [(X, 2)]) = MP [(PP [(X, 2)], - 4)]"
by eval

lemma
  "monom (0::rat) (PP [(X, 2)]) = 0"
by eval

lemma
  "some_term (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (1, 2)]) = PP [(X, 2), (Z, 7)]"
by eval

lemma
  "rest_mpoly (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2), (1, 2)]) =
    MP [(PP [(Y, 3), (Z, 2)], 2), (1, 2)]"
by eval

lemma
  "MP [(PP [(X, 2), (Z, 1)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)] *
      MP [(PP [(X, 2), (Z, 3)], 1), (PP [(Y, 3), (Z, 2)], -2)] =
    MP [(PP [(X, 4), (Z, 4)], 1), (PP [(X, 2), (Z, 3), (Y, 3)], - 2), (PP [(Y, 6), (Z, 4)], - 4), (PP [(Y, 3), (Z, 5), (X, 2)], 2)]"
by eval

subsubsection \<open>Ordered Power-Products\<close>

context ordered_powerprod
begin

definition list_max::"'a list \<Rightarrow> 'a" where
  "list_max xs \<equiv> foldl ordered_powerprod_lin.max 1 xs"

lemma list_max_Cons:
  shows "list_max (x # xs) = ordered_powerprod_lin.max x (list_max xs)"
unfolding list_max_def foldl_Cons
proof -
  have "foldl ordered_powerprod_lin.max (ordered_powerprod_lin.max x 1) xs =
          ordered_powerprod_lin.max x (foldl ordered_powerprod_lin.max 1 xs)"
    by (rule foldl_assoc, rule ordered_powerprod_lin.max.assoc)
  from this ordered_powerprod_lin.max.commute[of 1 x]
    show "foldl ordered_powerprod_lin.max (ordered_powerprod_lin.max 1 x) xs =
            ordered_powerprod_lin.max x (foldl ordered_powerprod_lin.max 1 xs)" by simp
qed

lemma list_max_empty:
  shows "list_max [] = 1"
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
    hence "list_max (x # xs) = ordered_powerprod_lin.max 1 x" unfolding list_max_def by simp
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
  "lp (MP xs) = list_max (map fst (normalize_MP xs))"
unfolding lp_def compute_supp_mpoly
proof (split if_splits, intro conjI, intro impI)
  assume "MP xs = 0"
  from this supp_0[of "MP xs"] have "supp (MP xs) = {}" by simp
  hence "map fst (normalize_MP xs) = []" unfolding compute_supp_mpoly by simp
  thus "1 = list_max (map fst (normalize_MP xs))" using list_max_empty by simp
next
  show "MP xs \<noteq> 0 \<longrightarrow>
    ordered_powerprod_lin.Max (set (map fst (normalize_MP xs))) = list_max (map fst (normalize_MP xs))"
  proof (intro impI)
    assume "MP xs \<noteq> 0"
    from this supp_0[of "MP xs"] have "supp (MP xs) \<noteq> {}" by simp
    hence "map fst (normalize_MP xs) \<noteq> []" unfolding compute_supp_mpoly by simp
    from list_max_nonempty[OF this]
      show "ordered_powerprod_lin.Max (set (map fst (normalize_MP xs))) =
            list_max (map fst (normalize_MP xs))" by simp
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
  thus "(if t \<prec> s then lookup_mpoly xs s else 0) = lookup_mpoly [(k, v)\<leftarrow>xs . t \<prec> k] s"
    by (auto simp add: lookup_mpoly_def map_of_filter_in map_of_filter_NoneI split: option.split)
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
  thus "(if s \<prec> t then lookup_mpoly xs s else 0) = lookup_mpoly [(k, v)\<leftarrow>xs . k \<prec> t] s"
    by (auto simp add: lookup_mpoly_def map_of_filter_in map_of_filter_NoneI split: option.split)
qed

end (* ordered_powerprod *)

lifting_update mpoly.lifting
lifting_forget mpoly.lifting

subsection \<open>Lexicographic Order\<close>

global_interpretation opp_lex: ordered_powerprod lex
  defines lex_strict = opp_lex.ord_strict
  and lp_lex = opp_lex.lp
  and max_lex = opp_lex.ordered_powerprod_lin.max
  and list_max_lex = opp_lex.list_max
  and higher_lex = opp_lex.higher
  and lower_lex = opp_lex.lower
  and lc_lex = opp_lex.lc
  and tail_lex = opp_lex.tail
  and ord_lex = opp_lex.ord_p
  and ord_strict_lex = opp_lex.ord_strict_p
  and rd_mult_lex = opp_lex.rd_mult
  and rd_lex = opp_lex.rd
  and rd_list_lex = opp_lex.rd_list
  and trd_lex = opp_lex.trd
  and spoly_lex = opp_lex.spoly
  and trdsp_lex = opp_lex.trdsp
  and gbaux_lex = opp_lex.gbaux
  and gb_lex = opp_lex.gb
apply standard
subgoal by (rule lex_refl)
subgoal by (erule lex_antisym, simp)
subgoal by (erule lex_trans, simp)
subgoal by (rule lex_lin)
subgoal by (rule lex_one_min)
subgoal by (erule lex_times_monotone)
done

subsubsection \<open>Computations\<close>

lemma
  "lp_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = PP [(X, 2), (Y, 1)]"
by eval

lemma
  "lc_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = 3"
by eval

lemma
  "tail_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) =
    MP [(PP [(X, 2), (Z, 3)], 1::rat)]"
by eval

lemma
  "higher_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) (PP [(X, 2)]) =
    MP [(PP [(X, 2), (Z, 3)], 1), (PP [(X,2), (Y,1)], 3)]"
by eval

lemma
  "ord_strict_lex
    (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
    (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)])"
by eval

lemma
  "rd_mult_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    (- 2, PP [(Y, 1), (Z, 1)])"
by eval

lemma
  "rd_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "rd_list_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "trd_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Y, 1), (Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 6)], - 8)]"
by eval

lemma
  "spoly_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(Z, 2), (Y, 5)], - 2), (PP [(X, 2), (Z, 6)], - 2)]"
by eval

lemma
  "trdsp_lex
      [(MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]), (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)])]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    0"
by eval

lemma
  "up [] [MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]] (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    [(MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)], MP [(PP [(Y, 2), (Z, 1)], 1), (PP [(Z, 3)], 2)])]"
by eval

lemma
  "gb_lex
    [
     MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)],
     MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]
    ] =
    [
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)],
    MP [(PP [(Y,2), (Z, 1)], 1), (PP [(Z, 3)], 2)]
   ]"
by eval

lemma
  "gb_lex
    [
     MP [(PP [(X, 2), (Z, 2)], 1), (PP [(Y, 1)], -1)],
     MP [(PP [(Y, 2), (Z, 1)], 1::rat), (1, -1)]
    ] =
    [
     MP [(PP [(X, 2)], - 1), (PP [(Y, 5)], 1)],
     MP [(PP [(Y, 3)], - 1), (PP [(X, 2), (Z, 1)], 1)],
     MP [(PP [(X, 2), (Z, 2)], 1), (PP [(Y, 1)], - 1)], MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

lemma
  "gb_lex
    [
     MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)],
     MP [(PP [(Y, 2), (Z, 1)], 1::rat), (1, -1)]
    ] =
    [
     MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], - 1)],
     MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

subsection \<open>Degree-Lexicographic Order\<close>

global_interpretation opp_dlex: ordered_powerprod dlex
  defines dlex_strict = opp_dlex.ord_strict
  and lp_dlex = opp_dlex.lp
  and max_dlex = opp_dlex.ordered_powerprod_lin.max
  and list_max_dlex = opp_dlex.list_max
  and higher_dlex = opp_dlex.higher
  and lower_dlex = opp_dlex.lower
  and lc_dlex = opp_dlex.lc
  and tail_dlex = opp_dlex.tail
  and ord_dlex = opp_dlex.ord_p
  and ord_strict_dlex = opp_dlex.ord_strict_p
  and rd_mult_dlex = opp_dlex.rd_mult
  and rd_dlex = opp_dlex.rd
  and rd_list_dlex = opp_dlex.rd_list
  and trd_dlex = opp_dlex.trd
  and spoly_dlex = opp_dlex.spoly
  and trdsp_dlex = opp_dlex.trdsp
  and gbaux_dlex = opp_dlex.gbaux
  and gb_dlex = opp_dlex.gb
apply standard
subgoal by (rule dlex_refl)
subgoal by (erule dlex_antisym, simp)
subgoal by (erule dlex_trans, simp)
subgoal by (rule dlex_lin)
subgoal by (rule dlex_one_min)
subgoal by (erule dlex_times_monotone)
done

subsubsection \<open>Computations\<close>

lemma
  "lp_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = PP [(X, Suc (Suc 0)), (Y, Suc 0)]"
by eval

lemma
  "lc_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = 3"
by eval

lemma
  "tail_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = MP [(PP [(X, 2), (Z, 3)], 1)]"
by eval

lemma
  "higher_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) (PP [(X, 2)]) =
    MP [(PP [(X, 2), (Z, 3)], 1), (PP [(X, 2), (Y, 1)], 3)]"
by eval

lemma
  "ord_strict_lex
    (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
    (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)])"
by eval

lemma
  "rd_mult_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    (- 2, PP [(Y, 1), (Z, 1)])"
by eval

lemma
  "rd_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "rd_list_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "trd_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Y, 1), (Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 6)], - 8)]"
by eval

lemma
  "spoly_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(Z, 2), (Y, 5)], - 2), (PP [(X, 2), (Z, 6)], - 2)]"
by eval

lemma
  "trdsp_lex
      [(MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]), (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)])]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    0"
by eval

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)])
    ] =
    [
     MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)],
     MP [(PP [(Y, 2), (Z, 1)], 1), (PP [(Z, 3)], 2)]
    ]"
by eval

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 2), (Z, 2)], 1), (PP [(X, 1)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ] =
    [
     MP [(PP [(X, 2)], - 1), (PP [(Y, 4), (X, 1)], 1)],
     MP [(PP [(X, 1), (Y, 2)], - 1), (PP [(X, 2), (Z, 1)], 1)],
     MP [(PP [(X, 2), (Z, 2)], 1), (PP [(X, 1)], - 1)], MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

text \<open>The following Gr\"obner basis differs from the one obtained w.r.t. the purely lexicographic
  term-order.\<close>

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ] =
    [
     MP [(PP [(X, 5)], - 1), (PP [(X, 1), (Z, 3)], 1)],
     MP [(PP [(X, 3), (Y, 1)], - 1), (PP [(X, 1), (Z, 1)], 1)],
     MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], - 1)], MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ]
   \<noteq>
   gb_lex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ]"
by eval

end (* theory *)