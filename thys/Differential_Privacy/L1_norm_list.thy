(*
 Title:L1_norm_list.thy
 Last Updated: July 3, 2024
 Author: Tetsuya Sato
*)

theory L1_norm_list
  imports "HOL-Analysis.Abstract_Metric_Spaces"
    "HOL-Library.Extended_Real"
begin

section\<open> L1-norm on Lists with fixed length \<close>

lemma list_sum_dist_Cons:
  fixes a b xs ys n assumes xn: "length xs = n" and yn: "length ys = n"
  shows "(\<Sum>i = 1..Suc n. d ((a # xs) ! (i - 1)) ((b # ys) ! (i - 1))) = d a b + (\<Sum>i = 1..n. d (xs ! (i - 1)) (ys ! (i - 1)))"
proof-
  have 0: "{ 0.. n} = {0}\<union> {1.. n}"
    by auto
  show "(\<Sum>i = 1..(Suc n). d ((a # xs) ! (i - 1)) ((b # ys) ! (i - 1))) = d a b + (\<Sum>i = 1.. n. d (xs ! (i - 1)) (ys ! (i - 1)))"
    by(subst sum.reindex_bij_witness[of _ Suc "\<lambda>i. i - 1" "{0..n}"],auto simp: 0)
qed

subsection\<open> A locale for L1-norm of Lists \<close>

locale L1_norm_list = Metric_space +
  fixes n::nat
begin

definition space_L1_norm_list ::"('a list) set" where
  "space_L1_norm_list = {xs. xs\<in> lists M \<and> length xs = n}"

lemma in_space_L1_norm_list_iff:
  shows "x \<in> space_L1_norm_list \<longleftrightarrow>(x\<in> lists M \<and> length x = n) "
  unfolding space_L1_norm_list_def by auto

definition dist_L1_norm_list ::"('a list) \<Rightarrow> ('a list) \<Rightarrow> real" where
  "dist_L1_norm_list xs ys = (\<Sum> i\<in>{1..n}. d (nth xs (i-1)) (nth ys (i-1)))"

lemma dist_L1_norm_list_nonneg:
  shows "\<And> x y. 0 \<le> dist_L1_norm_list x y "
  unfolding dist_L1_norm_list_def by(auto intro!: sum_nonneg)

lemma dist_L1_norm_list_commute:
  shows "\<And> x y. dist_L1_norm_list x y = dist_L1_norm_list y x "
  unfolding dist_L1_norm_list_def using commute by presburger

lemma dist_L1_norm_list_zero:
  shows "\<And> x y. length x = n \<Longrightarrow> length y = n \<Longrightarrow> x \<in> lists M \<Longrightarrow> y \<in> lists M \<Longrightarrow> (dist_L1_norm_list x y = 0 = (x = y))"
proof-
  fix x y::"'a list" assume xm: "length x = n" and x: "x \<in> lists M" and ym: "length y = n" and y: "y \<in> lists M"
  show "(dist_L1_norm_list x y = 0) = (x = y)"
    using xm ym x y
  proof(intro iffI)
    show "length x = n \<Longrightarrow> length y = n \<Longrightarrow> x \<in> lists M \<Longrightarrow> y \<in> lists M \<Longrightarrow> x = y \<Longrightarrow> dist_L1_norm_list x y = 0"
      unfolding dist_L1_norm_list_def
    proof(induction x arbitrary: n y)
      case Nil
      then show ?case by auto
    next
      case (Cons a x2)
      then obtain m where n: "n = Suc m" and y: "y = (a # x2)" and x2m: "length x2 = m" and x2M: "x2 \<in> lists M" and aM: "a \<in> M"
        by fastforce
      have *: "(\<Sum>i = 1..n. d ((a # x2) ! (i - 1)) (y ! (i - 1))) = (d a a) + (\<Sum>i = 1..m. d ( x2 ! (i-1)) (x2 ! (i-1)))"
        unfolding n y using list_sum_dist_Cons[OF x2m x2m] by blast
      then show ?case
        using Cons.IH[of m x2, OF x2m x2m x2M x2M] aM by auto
    qed
  next
    show " length x = n \<Longrightarrow> length y = n \<Longrightarrow> x \<in> lists M \<Longrightarrow> y \<in> lists M \<Longrightarrow> dist_L1_norm_list x y = 0 \<Longrightarrow> x = y"
      unfolding dist_L1_norm_list_def
    proof(induction x arbitrary: n y)
      case Nil
      then show ?case by auto
    next
      case (Cons a x2)
      then obtain m b y2 where n: "n = Suc m" and y: "y = (b # y2)" and x2m: "length x2 = m" and y2m: "length y2 = m" and aM: "a \<in> M" and bM: "b \<in> M" and x2M: "x2 \<in> lists M" and y2M:"y2 \<in>lists M"
        by (metis (no_types, opaque_lifting) Cons_in_lists_iff Suc_length_conv)
      have "0 \<le> (\<Sum>i = 1..n. d ((a # x2) ! (i - 1)) (y ! (i - 1)))" and 1: "0 \<le> (\<Sum>i = 1..m. d (x2 ! (i - 1)) (y2 ! (i - 1))) "
        by(rule sum_nonneg,auto)+
      hence 0: "(\<Sum>i = 1..n. d ((a # x2) ! (i - 1)) (y ! (i - 1))) = 0"
        using Cons.prems(5) by blast
      have *: "(\<Sum>i = 1..n. d ((a # x2) ! (i - 1)) (y ! (i - 1))) = (d a b) + (\<Sum>i = 1..m. d ( x2 ! (i-1)) (y2 ! (i-1)))"
        unfolding y n using list_sum_dist_Cons[of x2 m y2 d a b , OF x2m y2m ] by blast
      have 2: " (\<Sum>i = 1..m. d (x2 ! (i - 1)) (y2 ! (i - 1))) \<le> 0"
        using nonneg[of a b] Cons.prems(5) unfolding * by linarith
      with 1 have 3: "(\<Sum>i = 1..m. d (x2 ! (i - 1)) (y2 ! (i - 1))) = 0"
        by auto
      have "a = b" and "y2 = x2"
        unfolding y using 0 * nonneg[of a b] zero[of a b,OF aM bM] Cons.IH[of m y2,OF x2m y2m x2M y2M] 3 by auto
      thus ?case by(auto simp: y)
    qed
  qed
qed

lemma dist_L1_norm_list_trans:
  shows"\<And> x y z. length x = n \<Longrightarrow> length y = n \<Longrightarrow> length z = n\<Longrightarrow> x \<in> lists M \<Longrightarrow> y \<in> lists M \<Longrightarrow> z \<in> lists M \<Longrightarrow> (dist_L1_norm_list x z \<le> dist_L1_norm_list x y + dist_L1_norm_list y z)"
proof-
  fix x y z::"'a list" assume xm: "length x = n" and x: "x \<in> lists M" and ym: "length y = n" and y: "y \<in> lists M" and zm: "length z = n" and z: "z \<in> lists M"
  show "dist_L1_norm_list x z \<le> dist_L1_norm_list x y + dist_L1_norm_list y z"
    using xm ym zm x y z triangle unfolding dist_L1_norm_list_def
  proof(induction n arbitrary:x y z)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then obtain a b c::'a and xs ys zs::"'a list" where x: "x = a#xs" and y: "y = b#ys" and z:"z = c#zs"
      and xn: "length xs = n" and yn: "length ys = n" and zn: "length zs = n"
      using Suc_length_conv[of n x] Suc_length_conv[of n y] Suc_length_conv[of n z] by auto
    hence aM: "a \<in> M" and bM: "b \<in> M" and cM: "c \<in> M" and xsM: "xs \<in> lists M" and ysM: "ys \<in> lists M" and zsM: "zs \<in> lists M"
      using listsE Suc.prems(4,5,6) unfolding x y z by auto
    have " (\<Sum>i = 1..Suc n. d (x ! (i - 1)) (z ! (i - 1))) = d a c + (\<Sum>i = 1..n. d (xs ! (i - 1)) (zs ! (i - 1)))"
      unfolding x z using list_sum_dist_Cons[of xs n zs d a c, OF xn zn] by blast
    also have "... \<le> (d a b + d b c) + ( (\<Sum>i = 1.. n. d (xs ! (i - 1)) (ys ! (i - 1))) + (\<Sum>i = 1.. n. d (ys ! (i - 1)) (zs ! (i - 1))))"
      using Suc.IH[of xs ys zs, OF xn yn zn xsM ysM zsM] Suc.prems(7)
        triangle[of a b c, OF aM bM cM] by auto
    also have "... \<le> (d a b + (\<Sum>i = 1.. n. d (xs ! (i - 1)) (ys ! (i - 1)))) + ( d b c + (\<Sum>i = 1.. n. d (ys ! (i - 1)) (zs ! (i - 1))))"
      by auto
    also have "... = (\<Sum>i = 1..Suc n. d (x ! (i - 1)) (y ! (i - 1))) + (\<Sum>i = 1..Suc n. d (y ! (i - 1)) (z ! (i - 1)))"
      unfolding x y z using list_sum_dist_Cons[of ys n zs d b c, OF yn zn,THEN sym] list_sum_dist_Cons[of xs n ys d a b, OF xn yn,THEN sym] by presburger
    finally show ?case.
  qed
qed

lemma Metric_L1_norm_list : "Metric_space space_L1_norm_list dist_L1_norm_list"
  by (simp add: Metric_space_def dist_L1_norm_list_commute dist_L1_norm_list_nonneg dist_L1_norm_list_trans dist_L1_norm_list_zero in_space_L1_norm_list_iff)

end (*end of locale L1_norm_list *)

sublocale L1_norm_list \<subseteq> MetL1: Metric_space "space_L1_norm_list" "dist_L1_norm_list"
  by (simp add: Metric_L1_norm_list)

subsection\<open> Lemmas on L1-norm on lists of natural numbers \<close>

lemma L1_dist_k:
  fixes x y k::nat
  assumes "real_of_int \<bar>int x - int y\<bar> \<le> k"
  shows "(x,y) \<in> {(x,y) | x y. \<bar>int x - int y\<bar> \<le> 1} ^^ k"
  using assms proof(induction k arbitrary: x y)
  case 0
  then have " x = y"
    by auto
  then show ?case
    by auto
next
  case (Suc k)
  then show ?case
  proof(cases "real_of_int \<bar>int x - int y\<bar> \<le> k" )
    case True
    then have "(x,y) \<in> {(x,y) | x y. \<bar>int x - int y\<bar> \<le> 1} ^^ k"
      using Suc.IH[of x y] by auto
    thus ?thesis
      by auto
  next
    case False
    hence "\<bar>int x - int y\<bar> > k"
      by auto
    moreover have " \<bar>int x - int y\<bar> \<le> Suc k"
      using Suc.prems by linarith
    ultimately have absSuck: "\<bar> int x - int y\<bar> = Suc k"
      unfolding Int.zabs_def using int_ops(4) of_int_of_nat_eq of_nat_less_of_int_iff by linarith
    have "\<exists>z::nat. \<bar> int x - int z\<bar> = k \<and> \<bar> int z - int y\<bar> = 1"
    proof(cases "x \<le> y")
      case True
      thus ?thesis
        using absSuck by(intro exI[of _ "x + k"],auto)
    next
      case False
      thus ?thesis
        using absSuck by(intro exI[of _ "y + 1"],auto)
    qed
    then obtain z::nat where a: "\<bar> int x - int z\<bar> = k" and b: "\<bar> int z - int y\<bar> = 1"
      by blast
    then have "(x,z) \<in> {(x,y) | x y. \<bar>int x - int y\<bar> \<le> 1} ^^ k" and "(z,y) \<in> {(x,y) | x y. \<bar>int x - int y\<bar> \<le> 1} ^^ 1"
      using Suc.IH[of x z] by auto
    thus ?thesis
      by auto
  qed
qed

context
  fixes n::nat
begin

interpretation L11nat: L1_norm_list "(UNIV::nat set)" "(\<lambda>x y. \<bar>int x - int y\<bar>)" n
  by(unfold_locales,auto)
interpretation L11nat2: L1_norm_list "(UNIV::nat set)" "(\<lambda>x y. \<bar>int x - int y\<bar>)" "Suc n"
  by(unfold_locales,auto)

abbreviation "adj_L11nat \<equiv> {(xs, ys) |xs ys. xs \<in> L11nat.space_L1_norm_list \<and> ys \<in> L11nat.space_L1_norm_list \<and> L11nat.dist_L1_norm_list xs ys \<le> 1}"
abbreviation "adj_L11nat2 \<equiv> {(xs, ys) |xs ys. xs \<in> L11nat2.space_L1_norm_list \<and> ys \<in> L11nat2.space_L1_norm_list \<and> L11nat2.dist_L1_norm_list xs ys \<le> 1}"

lemma L1_adj_iterate_Cons1:
  assumes "xs \<in> L11nat.space_L1_norm_list" 
    and "ys \<in> L11nat.space_L1_norm_list"
    and "(xs, ys) \<in> adj_L11nat ^^ k"
  shows "(x#xs, x#ys) \<in> adj_L11nat2 ^^ k"
  using assms
proof(induction k arbitrary: xs ys)
  case 0
  then have 1: "x # xs = x # ys" and "x # xs \<in> L11nat2.space_L1_norm_list"
    by (auto simp: L11nat.space_L1_norm_list_def L11nat2.space_L1_norm_list_def)
  then show ?case
    by auto
next
  case (Suc k)
  then obtain zs where k: "(xs , zs) \<in> adj_L11nat ^^ k" and 1: "(zs , ys) \<in> adj_L11nat" and zs: "zs \<in> L11nat.space_L1_norm_list"
    by auto
  have A: "(x # xs , x # zs) \<in> adj_L11nat2 ^^ k"
    by(rule Suc.IH [of xs zs,OF Suc(2) zs, OF k])
  have "x # zs \<in> L11nat2.space_L1_norm_list " and "x # ys \<in> L11nat2.space_L1_norm_list "
    using Suc(3) zs by(auto simp: L11nat2.space_L1_norm_list_def L11nat.space_L1_norm_list_def )
  moreover have "L11nat2.dist_L1_norm_list (x # zs)(x # ys) \<le> 1"
    using 1 L1_norm_list.list_sum_dist_Cons[of zs n ys "(\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)" x x] Suc(3) zs L11nat.space_L1_norm_list_def
      L11nat2.dist_L1_norm_list_def L11nat.dist_L1_norm_list_def
    by auto
  ultimately show ?case
    using A by auto
qed

lemma L1_adj_Cons1:
  assumes "xs \<in> L11nat.space_L1_norm_list" 
    and "real_of_int \<bar>int x - int y\<bar> \<le> 1"
  shows "(x # xs, y # xs) \<in> adj_L11nat2"
  using L1_norm_list.list_sum_dist_Cons[of xs n xs "(\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)" x y] assms
  unfolding L11nat.dist_L1_norm_list_def L11nat2.space_L1_norm_list_def L11nat2.dist_L1_norm_list_def L11nat.space_L1_norm_list_def lists_UNIV by auto

lemma L1_adj_iterate_Cons2:
  assumes "xs \<in> L11nat.space_L1_norm_list" and "real_of_int \<bar>int x - int y\<bar> \<le> k"
  shows "(x # xs, y # xs) \<in> adj_L11nat2 ^^ k"
proof-
  have "(x,y) \<in> {(x,y) | x y. \<bar>int x - int y\<bar> \<le> 1} ^^ k"
    using L1_dist_k[of x y k] assms(2) by auto
  thus ?thesis
  proof(induction k arbitrary: x y)
    case 0
    then have "x = y"
      by auto
    then show ?case
      by auto
  next
    case (Suc k)
    then obtain z where k: "(x, z) \<in> {(x, y) |x y. \<bar>int x - int y\<bar> \<le> 1} ^^ k" and "(z, y) \<in> {(x, y) |x y. \<bar>int x - int y\<bar> \<le> 1}"
      using L1_dist_k[of x y k] by auto
    then have "(x#xs, z#xs) \<in> adj_L11nat2 ^^ k" and "(z#xs, y#xs) \<in> adj_L11nat2"
      using Suc.IH[of x z, OF k] L1_adj_Cons1[of xs z y, OF assms(1)]
      by auto
    then show ?case
      by auto
  qed
qed

lemma L1_adj_iterate:
  fixes k::nat
  assumes "xs \<in> L11nat.space_L1_norm_list"
    and "ys \<in> L11nat.space_L1_norm_list"
    and " L11nat.dist_L1_norm_list xs ys \<le> k"
  shows "(xs,ys) \<in> adj_L11nat ^^ k"
  using assms
proof(induction n arbitrary: xs ys k)
  case 0
  interpret L1_norm_list "UNIV::nat set" "(\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)" 0
    by(unfold_locales,auto)
  let ?R = "{(xs, ys) |xs ys. xs \<in> space_L1_norm_list \<and> ys \<in> space_L1_norm_list \<and> dist_L1_norm_list xs ys \<le> 1}"
  from 0 have 1: "xs = []" and 2: "ys = []"
    by (auto simp: space_L1_norm_list_def)
  then show ?case
  proof(induction k)
    case 0
    then show ?case
      by auto
  next
    case (Suc k)
    then have 1: "(xs, ys) \<in> ?R ^^ k"
      by auto
    moreover from Suc have "dist_L1_norm_list ys ys = 0"
      by(subst MetL1.mdist_zero,auto simp: space_L1_norm_list_def)
    moreover hence 2: "(ys, ys) \<in> ?R"
      using space_L1_norm_list_def 2 unfolding lists_UNIV by auto
    ultimately show ?case
      by auto
  qed
next
  case (Suc n)
  interpret sp: L1_norm_list "UNIV::nat set" "(\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)" n
    by(unfold_locales,auto)
  interpret sp2: L1_norm_list "UNIV::nat set" "(\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)" "Suc n"
    by(unfold_locales,auto)
  let ?R = "{(xs, ys) |xs ys. xs \<in> sp.space_L1_norm_list \<and> ys \<in> sp.space_L1_norm_list \<and> sp.dist_L1_norm_list xs ys \<le> 1}"
  let ?R2 = "{(xs, ys) |xs ys. xs \<in> sp2.space_L1_norm_list \<and> ys \<in> sp2.space_L1_norm_list \<and> sp2.dist_L1_norm_list xs ys \<le> 1}"
  show ?case
    using Suc proof(induction k)
    case 0
    from 0(2,3,4) have "sp2.dist_L1_norm_list xs ys = 0"
      using sp2.MetL1.mdist_pos_eq sp2.MetL1.mdist_zero by fastforce
    moreover have "sp2.dist_L1_norm_list xs ys \<ge> 0"
      by(rule sp2.MetL1.nonneg)
    ultimately have "sp2.dist_L1_norm_list xs ys = 0"
      by auto
    hence "xs = ys"
      using sp2.MetL1.zero[of xs ys] 0(2,3) by auto
    then show ?case by auto
  next
    case (Suc k)
    then obtain x y xs2 ys2 where xs: "xs = x # xs2" and ys: "ys = y # ys2" and xs2: "xs2 \<in> sp.space_L1_norm_list" and ys2: "ys2 \<in> sp.space_L1_norm_list"
      using Suc.prems(1) Suc.prems(2) length_Suc_conv[of xs n] length_Suc_conv[of ys n] sp.space_L1_norm_list_def sp2.space_L1_norm_list_def by auto
    hence *: " \<bar>int x - int y\<bar> + sp.dist_L1_norm_list xs2 ys2 = sp2.dist_L1_norm_list xs ys"
      using L1_norm_list.list_sum_dist_Cons[of xs2 n ys2 "(\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)" x y] xs2 ys2
      unfolding sp.dist_L1_norm_list_def sp2.dist_L1_norm_list_def xs ys sp.space_L1_norm_list_def lists_UNIV by auto
    show ?case
    proof(cases "x = y")
      case True
      hence "sp.dist_L1_norm_list xs2 ys2 \<le> (Suc k)"
        using Suc(5) * by auto
      with Suc.prems(1)[of xs2 ys2 "Suc k"] xs2 ys2 have "(xs2, ys2) \<in> ?R ^^ Suc k"
        by auto
      thus ?thesis
        unfolding True xs ys
        using L1_norm_list.L1_adj_iterate_Cons1[of xs2 n ys2 "Suc k" y,OF xs2 ys2] by blast
    next
      case False
      then obtain k2::nat where k2: "\<bar>int x - int y\<bar> = k2"
        by (meson abs_ge_zero nonneg_int_cases)
      moreover then have en: "sp.dist_L1_norm_list xs2 ys2 \<le> Suc k - k2"
        using * Suc.prems(4) by auto
      moreover have "0 \<le> sp.dist_L1_norm_list xs2 ys2"
        by(rule sp.MetL1.nonneg)
      ultimately have plus: "Suc k \<ge> k2"
        using * Suc.prems(4) by linarith
      have p: "k2 \<ge> 1"
        using * False k2 by auto
      then obtain k3::nat where k3: "k2 = Suc k3"
        using not0_implies_Suc by force
      with plus en have en: "k \<ge> k3" and "sp.dist_L1_norm_list xs2 ys2 \<le> k - k3"
        by auto
      hence "(xs2, ys2) \<in> ?R ^^ (k - k3)"
        using Suc.prems(1)[of xs2 ys2 "k - k3" ] xs2 ys2 by auto
      hence A: "(y # xs2, y # ys2) \<in> ?R2 ^^ (k - k3)"
        using L1_norm_list.L1_adj_iterate_Cons1[of xs2 n ys2 " (k - k3)" y ] xs2 ys2 by blast

      have "\<bar>int x - int y\<bar> = (Suc k3)"
        by(auto simp: k2 k3)
      then have B: "(x # xs2, y # xs2) \<in> ?R2 ^^ Suc k3"
        by(intro L1_norm_list.L1_adj_iterate_Cons2 xs2,auto)

      have "(x # xs2, y # ys2) \<in> ?R2 ^^ (Suc k3 + (k - k3))"
        by(intro relpow_trans[of _ "y#xs2"] A B )
      thus "(xs, ys) \<in> ?R2 ^^ (Suc k)"
        unfolding xs ys using en k3 by auto
    qed
  qed
qed

end (*end of context*)

hide_fact (open) list_sum_dist_Cons

end
