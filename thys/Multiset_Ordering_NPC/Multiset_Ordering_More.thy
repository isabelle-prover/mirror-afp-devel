section \<open>Properties of the Generalized Multiset Ordering\<close>

theory Multiset_Ordering_More
  imports
    Weighted_Path_Order.Multiset_Extension2
begin

text \<open>We provide characterizations of @{const s_mul_ext} and @{const ns_mul_ext} via 
  introduction and elimination rules that are based on lists.\<close>


lemma s_mul_ext_intro: 
  assumes "xs = mset xs1 + mset xs2" 
  and "ys = mset ys1 + mset ys2"
  and "length xs1 = length ys1" 
  and "\<And>i. i < length ys1 \<Longrightarrow> (xs1 ! i, ys1 ! i) \<in> NS" 
  and "xs2 \<noteq> []" 
  and "\<And>y. y \<in> set ys2 \<Longrightarrow> \<exists>a \<in> set xs2. (a, y) \<in> S" 
shows "(xs, ys) \<in> s_mul_ext NS S" 
  by (rule s_mul_extI[OF assms(1-2) multpw_listI[OF assms(3)]], insert assms(4-), auto)

lemma ns_mul_ext_intro: 
  assumes "xs = mset xs1 + mset xs2" 
  and "ys = mset ys1 + mset ys2"
  and "length xs1 = length ys1" 
  and "\<And>i. i < length ys1 \<Longrightarrow> (xs1 ! i, ys1 ! i) \<in> NS" 
  and "\<And>y. y \<in> set ys2 \<Longrightarrow> \<exists>x \<in> set xs2. (x, y) \<in> S" 
shows "(xs, ys) \<in> ns_mul_ext NS S" 
  by (rule ns_mul_extI[OF assms(1-2) multpw_listI[OF assms(3)]], insert assms(4-), auto)

lemma ns_mul_ext_elim: assumes "(xs, ys) \<in> ns_mul_ext NS S" 
  shows "\<exists> xs1 xs2 ys1 ys2.
    xs = mset xs1 + mset xs2
  \<and> ys = mset ys1 + mset ys2
  \<and> length xs1 = length ys1
  \<and> (\<forall> i. i < length ys1 \<longrightarrow> (xs1 ! i, ys1 ! i) \<in> NS)
  \<and> (\<forall> y \<in> set ys2. \<exists>x \<in> set xs2. (x, y) \<in> S)"
proof -
  from ns_mul_extE[OF assms] obtain 
    A1 A2 B1 B2 where *: "xs = A1 + A2" "ys = B1 + B2"
    and NS: "(A1, B1) \<in> multpw NS"
      and S: "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> S" 
    by blast
  from multpw_listE[OF NS] obtain xs1 ys1 where **: "length xs1 = length ys1" "A1 = mset xs1" "B1 = mset ys1" 
    and NS: "\<And> i. i < length ys1 \<Longrightarrow> (xs1 ! i, ys1 ! i) \<in> NS" by auto
  from surj_mset obtain xs2 where A2: "A2 = mset xs2" by auto
  from surj_mset obtain ys2 where B2: "B2 = mset ys2" by auto
  show ?thesis
  proof (rule exI[of _ xs1], rule exI[of _ xs2], rule exI[of _ ys1], rule exI[of _ ys2], intro conjI)
    show "xs = mset xs1 + mset xs2" using * ** A2 B2 by auto
    show "ys = mset ys1 + mset ys2" using * ** A2 B2 by auto
    show "length xs1 = length ys1"  by fact
    show "\<forall>i<length ys1. (xs1 ! i, ys1 ! i) \<in> NS" using * ** A2 B2 NS by auto
    show "\<forall>y\<in>set ys2. \<exists>x\<in>set xs2. (x, y) \<in> S" using * ** A2 B2 S by auto
  qed
qed

lemma s_mul_ext_elim: assumes "(xs, ys) \<in> s_mul_ext NS S" 
  shows "\<exists> xs1 xs2 ys1 ys2.
    xs = mset xs1 + mset xs2
  \<and> ys = mset ys1 + mset ys2
  \<and> length xs1 = length ys1
  \<and> xs2 \<noteq> []
  \<and> (\<forall> i. i < length ys1 \<longrightarrow> (xs1 ! i, ys1 ! i) \<in> NS)
  \<and> (\<forall> y \<in> set ys2. \<exists>x \<in> set xs2. (x, y) \<in> S)"
proof -
  from s_mul_extE[OF assms] obtain 
    A1 A2 B1 B2 where *: "xs = A1 + A2" "ys = B1 + B2"  
    and NS: "(A1, B1) \<in> multpw NS" and nonempty: "A2 \<noteq> {#}"
      and S: "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> S" 
    by blast
  from multpw_listE[OF NS] obtain xs1 ys1 where **: "length xs1 = length ys1" "A1 = mset xs1" "B1 = mset ys1" 
    and NS: "\<And> i. i < length ys1 \<Longrightarrow> (xs1 ! i, ys1 ! i) \<in> NS" by auto
  from surj_mset obtain xs2 where A2: "A2 = mset xs2" by auto
  from surj_mset obtain ys2 where B2: "B2 = mset ys2" by auto
  show ?thesis
  proof (rule exI[of _ xs1], rule exI[of _ xs2], rule exI[of _ ys1], rule exI[of _ ys2], intro conjI)
    show "xs = mset xs1 + mset xs2" using * ** A2 B2 by auto
    show "ys = mset ys1 + mset ys2" using * ** A2 B2 by auto
    show "length xs1 = length ys1"  by fact
    show "\<forall>i<length ys1. (xs1 ! i, ys1 ! i) \<in> NS" using * ** A2 B2 NS by auto
    show "\<forall>y\<in>set ys2. \<exists>x\<in>set xs2. (x, y) \<in> S" using * ** A2 B2 S by auto
    show "xs2 \<noteq> []" using nonempty A2 by auto
  qed
qed

text \<open>We further add a lemma that shows, that it does not matter whether one adds the
  strict relation to the non-strict relation or not.\<close>

lemma ns_mul_ext_some_S_in_NS: assumes "S' \<subseteq> S" 
  shows "ns_mul_ext (NS \<union> S') S = ns_mul_ext NS S" 
proof
  show "ns_mul_ext NS S \<subseteq> ns_mul_ext (NS \<union> S') S"
    by (simp add: ns_mul_ext_mono)
  show "ns_mul_ext (NS \<union> S') S \<subseteq> ns_mul_ext NS S" 
  proof
    fix as bs 
    assume "(as, bs) \<in> ns_mul_ext (NS \<union> S') S" 
    from ns_mul_extE[OF this] obtain nas sas nbs sbs where
       as: "as = nas + sas" and bs: "bs = nbs + sbs" 
       and ns: "(nas,nbs) \<in> multpw (NS \<union> S')" 
       and s: "(\<And>b. b \<in># sbs \<Longrightarrow> \<exists>a. a \<in># sas \<and> (a, b) \<in> S)" by blast
    from ns have "\<exists> nas2 sas2 nbs2 sbs2. nas = nas2 + sas2 \<and> nbs = nbs2 + sbs2 \<and> (nas2,nbs2) \<in> multpw NS
          \<and> (\<forall> b \<in># sbs2. (\<exists>a. a \<in># sas2 \<and> (a,b) \<in> S))" 
    proof (induct)
      case (add a b nas nbs)
      from add(3) obtain nas2 sas2 nbs2 sbs2 where *: "nas = nas2 + sas2 \<and> nbs = nbs2 + sbs2 \<and> (nas2,nbs2) \<in> multpw NS
          \<and> (\<forall> b \<in># sbs2. (\<exists>a. a \<in># sas2 \<and> (a,b) \<in> S))" by blast
      from add(1)
      show ?case
      proof
        assume "(a,b) \<in> S'"
        with assms have ab: "(a,b) \<in> S" by auto
        have one: "add_mset a nas = nas2 + (add_mset a sas2)" using * by auto
        have two: "add_mset b nbs = nbs2 + (add_mset b sbs2)" using * by auto
        show ?thesis
          by (intro exI conjI, rule one, rule two, insert ab *, auto)
      next
        assume ab: "(a,b) \<in> NS" 
        have one: "add_mset a nas = (add_mset a nas2) + sas2" using * by auto
        have two: "add_mset b nbs = (add_mset b nbs2) + sbs2" using * by auto
        show ?thesis
          by (intro exI conjI, rule one, rule two, insert ab *, auto intro: multpw.add) 
      qed
    qed auto
    then obtain nas2 sas2 nbs2 sbs2 where *: "nas = nas2 + sas2 \<and> nbs = nbs2 + sbs2 \<and> (nas2,nbs2) \<in> multpw NS
          \<and> (\<forall> b \<in># sbs2. (\<exists>a. a \<in># sas2 \<and> (a,b) \<in> S))" by auto
    have as: "as = nas2 + (sas2 + sas)" and bs: "bs = nbs2 + (sbs2 + sbs)" 
      unfolding as bs using * by auto
    show "(as, bs) \<in> ns_mul_ext NS S"
      by (intro ns_mul_extI[OF as bs], insert * s, auto)
  qed
qed


lemma ns_mul_ext_NS_union_S:  "ns_mul_ext (NS \<union> S) S = ns_mul_ext NS S" 
  by (rule ns_mul_ext_some_S_in_NS, auto)

text \<open>Some further lemmas on multisets\<close>

lemma mset_map_filter: "mset (map v (filter (\<lambda>e. c e) t)) + mset (map v (filter (\<lambda>e. \<not>(c e)) t)) = mset (map v t)"
  by (induct t, auto)

lemma mset_map_split: assumes "mset (map f xs) = mset ys1 + mset ys2"
  shows "\<exists> zs1 zs2. mset xs = mset zs1 + mset zs2 \<and> ys1 = map f zs1 \<and> ys2 = map f zs2" 
  using assms 
proof (induct xs arbitrary: ys1 ys2)
  case (Cons x xs ys1 ys2)
  have "f x \<in># mset (map f (x # xs))" by simp
  from this[unfolded Cons(2)] 
  have "f x \<in> set ys1 \<union> set ys2" by auto
  thus ?case
  proof
    let ?ys1 = ys1 let ?ys2 = ys2
    assume "f x \<in> set ?ys1" 
    from split_list[OF this] obtain us1 us2 where ys1: "?ys1 = us1 @ f x # us2" by auto
    let ?us = "us1 @ us2" 
    from Cons(2)[unfolded ys1] have "mset (map f xs) = mset ?us + mset ?ys2" by auto
    from Cons(1)[OF this] obtain zs1 zs2 where xs: "mset xs = mset zs1 + mset zs2"
      and us: "?us = map f zs1" and ys: "?ys2 = map f zs2" 
      by auto
    let ?zs1 = "take (length us1) zs1" let ?zs2 = "drop (length us1) zs1" 
    show ?thesis 
      apply (rule exI[of _ "?zs1 @ x # ?zs2"], rule exI[of _ zs2])
      apply (unfold ys1, unfold ys, intro conjI refl)
    proof -
      have "mset (x # xs) = {# x #} + mset xs" by simp
      also have "\<dots> = mset (x # zs1) + mset zs2" using xs by simp
      also have "zs1 = ?zs1 @ ?zs2" by simp
      also have "mset (x # \<dots>) = mset (?zs1 @ x # ?zs2)" by (simp add: union_code)
      finally show "mset (x # xs) = mset (?zs1 @ x # ?zs2) + mset zs2" .
      show "us1 @ f x # us2 = map f (?zs1 @ x # ?zs2)" using us
        by (smt (verit, best) \<open>zs1 = take (length us1) zs1 @ drop (length us1) zs1\<close> add_diff_cancel_left' append_eq_append_conv length_append length_drop length_map list.simps(9) map_eq_append_conv)
    qed
  next
    let ?ys1 = ys2 let ?ys2 = ys1
    assume "f x \<in> set ?ys1" 
    from split_list[OF this] obtain us1 us2 where ys1: "?ys1 = us1 @ f x # us2" by auto
    let ?us = "us1 @ us2" 
    from Cons(2)[unfolded ys1] have "mset (map f xs) = mset ?us + mset ?ys2" by auto
    from Cons(1)[OF this] obtain zs1 zs2 where xs: "mset xs = mset zs1 + mset zs2"
      and us: "?us = map f zs1" and ys: "?ys2 = map f zs2" 
      by auto
    let ?zs1 = "take (length us1) zs1" let ?zs2 = "drop (length us1) zs1" 
    show ?thesis
      apply (rule exI[of _ zs2], rule exI[of _ "?zs1 @ x # ?zs2"])
      apply (unfold ys1, unfold ys, intro conjI refl)
    proof -
      have "mset (x # xs) = {# x #} + mset xs" by simp
      also have "\<dots> = mset zs2 + mset (x # zs1)" using xs by simp
      also have "zs1 = ?zs1 @ ?zs2" by simp
      also have "mset (x # \<dots>) = mset (?zs1 @ x # ?zs2)" by (simp add: union_code)
      finally show "mset (x # xs) = mset zs2 + mset (?zs1 @ x # ?zs2)" .
      show "us1 @ f x # us2 = map f (?zs1 @ x # ?zs2)" using us
        by (smt (verit, best) \<open>zs1 = take (length us1) zs1 @ drop (length us1) zs1\<close> add_diff_cancel_left' append_eq_append_conv length_append length_drop length_map list.simps(9) map_eq_append_conv)
    qed
  qed
qed auto

lemma deciding_mult: 
  assumes tr: "trans S" and ir: "irrefl S"
  shows "(N,M) \<in> mult S = (M \<noteq> N \<and> (\<forall> b \<in># N - M. \<exists> a \<in># M - N. (b,a) \<in> S))"
proof -
  define I where "I = M \<inter># N"   
  have N: "N = (N - M) + I" unfolding I_def
    by (metis add.commute diff_intersect_left_idem multiset_inter_commute subset_mset.add_diff_inverse subset_mset.inf_le1)
  have M: "M = (M - N) + I" unfolding I_def
    by (metis add.commute diff_intersect_left_idem subset_mset.add_diff_inverse subset_mset.inf_le1)
  have "(N,M) \<in> mult S \<longleftrightarrow>
     ((N - M) + I, (M - N) + I) \<in> mult S" 
    using N M by auto
  also have "\<dots> \<longleftrightarrow> (N - M, M - N) \<in> mult S" 
    by (rule mult_cancel[OF tr irrefl_on_subset[OF ir, simplified]])
  also have "\<dots> \<longleftrightarrow> (M \<noteq> N \<and> (\<forall> b \<in># N - M. \<exists> a \<in># M - N. (b,a) \<in> S))" 
  proof
    assume *: "(M \<noteq> N \<and> (\<forall> b \<in># N - M. \<exists> a \<in># M - N. (b,a) \<in> S))" 
    have "({#} + (N - M), {#} + (M - N)) \<in> mult S" 
      apply (rule one_step_implies_mult, insert *, auto) 
      using M N by auto
    thus "(N - M, M - N) \<in> mult S" by auto
  next
    assume "(N - M, M - N) \<in> mult S" 
    from mult_implies_one_step[OF tr this]
    obtain E J K
      where *: " M - N = E + J \<and>
     N - M = E + K"  and rel: "J \<noteq> {#} \<and> (\<forall>k\<in>#K. \<exists>j\<in>#J. (k, j) \<in> S) " by auto
    from * have "E = {#}"
      by (metis (full_types) M N add_diff_cancel_right add_implies_diff cancel_ab_semigroup_add_class.diff_right_commute diff_add_zero)
    with * have JK: "J = M - N" "K = N - M" by auto
    show "(M \<noteq> N \<and> (\<forall> b \<in># N - M. \<exists> a \<in># M - N. (b,a) \<in> S))" 
      using rel unfolding JK by auto
  qed
  finally show ?thesis .
qed  

lemma s_mul_ext_map: "(\<And>a b. a \<in> set as \<Longrightarrow> b \<in> set bs \<Longrightarrow> (a, b) \<in> S \<Longrightarrow> (f a, f b) \<in> S') \<Longrightarrow>
  (\<And>a b. a \<in> set as \<Longrightarrow> b \<in> set bs \<Longrightarrow> (a, b) \<in> NS \<Longrightarrow> (f a, f b) \<in> NS') \<Longrightarrow>
  (as, bs) \<in> {(as, bs). (mset as, mset bs) \<in> s_mul_ext NS S} \<Longrightarrow>
  (map f as, map f bs) \<in> {(as, bs). (mset as, mset bs) \<in> s_mul_ext NS' S'}" 
  using mult2_alt_map[of _ _ "NS\<inverse>" f f "(NS')\<inverse>" "S\<inverse>" "S'\<inverse>" False] unfolding s_mul_ext_def
  by fastforce

lemma fst_mul_ext_imp_fst: assumes "fst (mul_ext f xs ys)" 
  and "length xs \<le> length ys" 
shows "\<exists> x y. x \<in> set xs \<and> y \<in> set ys \<and> fst (f x y)" 
proof -
  from assms(1)[unfolded mul_ext_def Let_def fst_conv]
  have "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}" by auto
  from s_mul_ext_elim[OF this] obtain xs1 xs2 ys1 ys2
    where *: "mset xs = mset xs1 + mset xs2" 
     "mset ys = mset ys1 + mset ys2" 
     "length xs1 = length ys1" 
     "xs2 \<noteq> []" 
     "(\<forall>y\<in>set ys2. \<exists>x\<in>set xs2. (x, y) \<in> {(x, y). fst (f x y)})" by auto
  from *(1-3) assms(2) have "length xs2 \<le> length ys2" 
    by (metis add_le_cancel_left size_mset size_union)
  with *(4) have "hd ys2 \<in> set ys2" by (cases ys2, auto)
  with *(5,1,2) show ?thesis
    by (metis Un_iff mem_Collect_eq prod.simps(2) set_mset_mset set_mset_union)
qed

lemma ns_mul_ext_point: assumes "(as,bs) \<in> ns_mul_ext NS S" 
  and "b \<in># bs" 
shows "\<exists> a \<in># as. (a,b) \<in> NS \<union> S" 
proof -
  from ns_mul_ext_elim[OF assms(1)]
  obtain xs1 xs2 ys1 ys2
    where *: "as = mset xs1 + mset xs2" 
     "bs = mset ys1 + mset ys2" 
     "length xs1 = length ys1" 
     "(\<forall>i<length ys1. (xs1 ! i, ys1 ! i) \<in> NS)" "(\<forall>y\<in>set ys2. \<exists>x\<in>set xs2. (x, y) \<in> S)" by auto
  from assms(2)[unfolded *] have "b \<in> set ys1 \<or> b \<in> set ys2" by auto
  thus ?thesis
  proof
    assume "b \<in> set ys2" 
    with * obtain a where "a \<in> set xs2" and "(a,b) \<in> S" by auto
    with *(1) show ?thesis by auto
  next
    assume "b \<in> set ys1" 
    from this[unfolded set_conv_nth] obtain i where i: "i < length ys1" and "b = ys1 ! i" by auto
    with *(4) have "(xs1 ! i, b) \<in> NS" by auto
    moreover from i *(3) have "xs1 ! i \<in> set xs1" by auto
    ultimately show ?thesis using *(1) by auto
  qed
qed

lemma s_mul_ext_point: assumes "(as,bs) \<in> s_mul_ext NS S" 
  and "b \<in># bs" 
shows "\<exists> a \<in># as. (a,b) \<in> NS \<union> S" 
  by (rule ns_mul_ext_point, insert assms s_ns_mul_ext, auto)


end
