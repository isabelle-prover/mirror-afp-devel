section \<open>Utilities\<close>

theory Utilities
  imports
    "Finite-Map-Extras.Finite_Map_Extras"
begin

subsection \<open>Utilities for lists\<close>

fun foldr1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "foldr1 f [x] = x"
| "foldr1 f (x # xs) = f x (foldr1 f xs)"
| "foldr1 f [] = undefined f"

abbreviation lset where "lset \<equiv> List.set"

lemma rev_induct2 [consumes 1, case_names Nil snoc]:
  assumes "length xs = length ys"
  and "P [] []"
  and "\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
using assms proof (induction xs arbitrary: ys rule: rev_induct)
  case (snoc x xs)
  then show ?case by (cases ys rule: rev_cases) simp_all
qed simp

subsection \<open>Utilities for finite maps\<close>

no_syntax
  "_fmaplet" :: "['a, 'a] \<Rightarrow> fmaplet" ("_ /$$:=/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet" ("_ /[$$:=]/ _")

syntax
  "_fmaplet" :: "['a, 'a] \<Rightarrow> fmaplet" ("_ /\<Zinj>/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet" ("_ /[\<Zinj>]/ _")

lemma fmdom'_fmap_of_list [simp]:
  shows "fmdom' (fmap_of_list ps) = lset (map fst ps)"
  by (induction ps) force+

lemma fmran'_singleton [simp]:
  shows "fmran' {k \<Zinj> v} = {v}"
proof -
  have "v' \<in> fmran' {k \<Zinj> v} \<Longrightarrow> v' = v" for v'
  proof -
    assume "v' \<in> fmran' {k \<Zinj> v}"
    fix k'
    have "fmdom' {k \<Zinj> v} = {k}"
      by simp
    then show "v' = v"
    proof (cases "k' = k")
      case True
      with \<open>v' \<in> fmran' {k \<Zinj> v}\<close> show ?thesis
        using fmdom'I by fastforce
    next
      case False
      with \<open>fmdom' {k \<Zinj> v} = {k}\<close> and \<open>v' \<in> fmran' {k \<Zinj> v}\<close> show ?thesis
        using fmdom'I by fastforce
    qed
  qed
  moreover have "v \<in> fmran' {k \<Zinj> v}"
    by (simp add: fmran'I)
  ultimately show ?thesis
    by blast
qed

lemma fmran'_fmupd [simp]:
  assumes "m $$ x = None"
  shows "fmran' (m(x \<Zinj> y)) = {y} \<union> fmran' m"
using assms proof (intro subset_antisym subsetI)
  fix x'
  assume "m $$ x = None" and "x' \<in> fmran' (m(x \<Zinj> y))"
  then show "x' \<in> {y} \<union> fmran' m"
    by (auto simp add: fmlookup_ran'_iff, metis option.inject)
next
  fix x'
  assume "m $$ x = None" and "x' \<in> {y} \<union> fmran' m"
  then show "x' \<in> fmran' (m(x \<Zinj> y))"
    by (force simp add: fmlookup_ran'_iff)
qed

lemma fmran'_fmadd [simp]:
  assumes "fmdom' m \<inter> fmdom' m' = {}"
  shows "fmran' (m ++\<^sub>f m') = fmran' m \<union> fmran' m'"
using assms proof (intro subset_antisym subsetI)
  fix x
  assume "fmdom' m \<inter> fmdom' m' = {}" and "x \<in> fmran' (m ++\<^sub>f m')"
  then show "x \<in> fmran' m \<union> fmran' m'"
    by (auto simp add: fmlookup_ran'_iff) meson
next
  fix x
  assume "fmdom' m \<inter> fmdom' m' = {}" and "x \<in> fmran' m \<union> fmran' m'"
  then show "x \<in> fmran' (m ++\<^sub>f m')"
    using fmap_disj_comm and fmlookup_ran'_iff by fastforce
qed

lemma finite_fmran':
  shows "finite (fmran' m)"
  by (simp add: fmran'_alt_def)

lemma fmap_of_zipped_list_range:
  assumes "length ks = length vs"
  and "m = fmap_of_list (zip ks vs)"
  and "k \<in> fmdom' m"
  shows "m $$! k \<in> lset vs"
  using assms by (induction arbitrary: m rule: list_induct2) auto

lemma fmap_of_zip_nth [simp]:
  assumes "length ks = length vs"
  and "distinct ks"
  and "i < length ks"
  shows "fmap_of_list (zip ks vs) $$! (ks ! i) = vs ! i"
  using assms by (simp add: fmap_of_list.rep_eq map_of_zip_nth)

lemma fmap_of_zipped_list_fmran' [simp]:
  assumes "distinct (map fst ps)"
  shows "fmran' (fmap_of_list ps) = lset (map snd ps)"
using assms proof (induction ps)
  case Nil
  then show ?case
    by auto
next
  case (Cons p ps)
  then show ?case
  proof (cases "p \<in> lset ps")
    case True
    then show ?thesis
      using Cons.prems by auto
  next
    case False
    obtain k and v where "p = (k, v)"
      by fastforce
    with Cons.prems have "k \<notin> fmdom' (fmap_of_list ps)"
      by auto
    then have "fmap_of_list (p # ps) = {k \<Zinj> v} ++\<^sub>f fmap_of_list ps"
      using \<open>p = (k, v)\<close> and fmap_singleton_comm by fastforce
    with Cons.prems have "fmran' (fmap_of_list (p # ps)) = {v} \<union> fmran' (fmap_of_list ps)"
      by (simp add: \<open>p = (k, v)\<close>)
    then have "fmran' (fmap_of_list (p # ps)) = {v} \<union> lset (map snd ps)"
      using Cons.IH and Cons.prems by force
    then show ?thesis
      by (simp add: \<open>p = (k, v)\<close>)
  qed
qed

lemma fmap_of_list_nth [simp]:
  assumes "distinct (map fst ps)"
    and "j < length ps"
  shows "fmap_of_list ps $$ ((map fst ps) ! j) = Some (map snd ps ! j)"
  using assms by (induction j) (simp_all add: fmap_of_list.rep_eq)

lemma fmap_of_list_nth_split [simp]:
  assumes "distinct xs"
    and "j < length xs"
    and "length ys = length xs" and "length zs = length xs"
  shows "fmap_of_list (zip xs (take k ys @ drop k zs)) $$ (xs ! j) =
          (if j < k then Some (take k ys ! j) else Some (drop k zs ! (j - k)))"
using assms proof (induction k arbitrary: xs ys zs j)
  case 0
  then show ?case
    by (simp add: fmap_of_list.rep_eq map_of_zip_nth)
next
  case (Suc k)
  then show ?case
  proof (cases xs)
    case Nil
    with Suc.prems(2) show ?thesis
      by auto
  next
    case (Cons x xs')
    let ?ps = "zip xs (take (Suc k) ys @ drop (Suc k) zs)"
    from Cons and Suc.prems(3,4) obtain y and z and ys' and zs'
      where "ys = y # ys'" and "zs = z # zs'"
      by (metis length_0_conv neq_Nil_conv)
    let ?ps' = "zip xs' (take k ys' @ drop k zs')"
    from Cons have *: "fmap_of_list ?ps = fmap_of_list ((x, y) # ?ps')"
      using \<open>ys = y # ys'\<close> and \<open>zs = z # zs'\<close> by fastforce
    also have "\<dots> = {x \<Zinj> y} ++\<^sub>f fmap_of_list ?ps'"
    proof -
      from \<open>ys = y # ys'\<close> and \<open>zs = z # zs'\<close> have "fmap_of_list ?ps' $$ x = None"
        using Cons and Suc.prems(1,3,4) by (simp add: fmdom'_notD)
      then show ?thesis
        using fmap_singleton_comm by fastforce
    qed
    finally have "fmap_of_list ?ps = {x \<Zinj> y} ++\<^sub>f fmap_of_list ?ps'" .
    then show ?thesis
    proof (cases "j = 0")
      case True
      with \<open>ys = y # ys'\<close> and Cons show ?thesis
        by simp
    next
      case False
      then have "xs ! j = xs' ! (j - 1)"
        by (simp add: Cons)
      moreover from \<open>ys = y # ys'\<close> and \<open>zs = z # zs'\<close> have "fmdom' (fmap_of_list ?ps') = lset xs'"
        using Cons and Suc.prems(3,4) by force
      moreover from False and Suc.prems(2) and Cons have "j - 1 < length xs'"
        using le_simps(2) by auto
      ultimately have "fmap_of_list ?ps $$ (xs ! j) = fmap_of_list ?ps' $$ (xs' ! (j - 1))"
        using Cons and * and Suc.prems(1) by auto
      with Suc.IH and Suc.prems(1,3,4) and Cons have **: "fmap_of_list ?ps $$ (xs ! j) =
        (if j - 1 < k then Some (take k ys' ! (j - 1)) else Some (drop k zs' ! ((j - 1) - k)))"
        using \<open>j - 1 < length xs'\<close> and \<open>ys = y # ys'\<close> and \<open>zs = z # zs'\<close> by simp
      then show ?thesis
      proof (cases "j - 1 < k")
        case True
        with False and ** show ?thesis
          using \<open>ys = y # ys'\<close> by auto
      next
        case False
        from Suc.prems(1) and Cons and \<open>j - 1 < length xs'\<close> and \<open>xs ! j = xs' ! (j - 1)\<close> have "j > 0"
          using nth_non_equal_first_eq by fastforce
        with False have "j \<ge> Suc k"
          by simp
        moreover have "fmap_of_list ?ps $$ (xs ! j) = Some (drop (Suc k) zs ! (j - Suc k))"
          using ** and False and \<open>zs = z # zs'\<close> by fastforce
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma fmadd_drop_cancellation [simp]:
  assumes "m $$ k = Some v"
  shows "{k \<Zinj> v} ++\<^sub>f fmdrop k m = m"
using assms proof (induction m)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k' v' m')
  then show ?case
  proof (cases "k' = k")
    case True
    with fmupd.prems have "v = v'"
      by fastforce
    have "fmdrop k' (m'(k' \<Zinj> v')) = m'"
      unfolding fmdrop_fmupd_same using fmdrop_idle'[OF fmdom'_notI[OF fmupd.hyps]] by (unfold True)
    then have "{k \<Zinj> v} ++\<^sub>f fmdrop k' (m'(k' \<Zinj> v')) = {k \<Zinj> v} ++\<^sub>f m'"
      by simp
    then show ?thesis
      using fmap_singleton_comm[OF fmupd.hyps] by (simp add: True \<open>v = v'\<close>)
  next
    case False
    with fmupd.prems have "m' $$ k = Some v"
      by force
    from False have "{k \<Zinj> v} ++\<^sub>f fmdrop k (m'(k' \<Zinj> v')) = {k \<Zinj> v} ++\<^sub>f (fmdrop k m')(k' \<Zinj> v')"
      by (simp add: fmdrop_fmupd)
    also have "\<dots> = ({k \<Zinj> v} ++\<^sub>f fmdrop k m')(k' \<Zinj> v')"
      by fastforce
    also from fmupd.prems and fmupd.IH[OF \<open>m' $$ k = Some v\<close>] have "\<dots> = m'(k' \<Zinj> v')"
      by force
    finally show ?thesis .
  qed
qed

lemma fmap_of_list_fmmap [simp]:
  shows "fmap_of_list (map2 (\<lambda>v' A'. (v', f A')) xs ys) = fmmap f (fmap_of_list (zip xs ys))"
  unfolding fmmap_of_list
  using cond_case_prod_eta
    [where f = "\<lambda>v' A'.(v', f A')" and g = "apsnd f", unfolded apsnd_conv, simplified]
  by (rule arg_cong)

end
