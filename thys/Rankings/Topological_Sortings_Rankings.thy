subsection \<open>Topological sorting\<close>
theory Topological_Sortings_Rankings
  imports Rankings
begin

text \<open>
  The following returns the set of all rankings of the given set \<open>A\<close> that are extensions of the
  given relation \<open>R\<close>, i.e.\ all topological sortings of \<open>R\<close>.

  Note that there are no requirements about \<open>R\<close>; in particular it does not have to be reflexive,
  antisymmetric, or transitive. If it is not antisymmetric or not transitive, the result set will
  simply be empty.
\<close>

function topo_sorts :: "'a set \<Rightarrow> 'a relation \<Rightarrow> 'a list set" where
  "topo_sorts A R =
     (if infinite A then {} else if A = {} then {[]} else
      \<Union>x\<in>{x\<in>A. \<forall>z\<in>A. R x z \<longrightarrow> z = x}. (\<lambda>xs. x # xs) ` topo_sorts (A - {x}) (\<lambda>y z. R y z \<and> y \<noteq> x \<and> z \<noteq> x))"
  by auto
termination
proof (relation "Wellfounded.measure (card \<circ> fst)", goal_cases)
  case (2 A R x)
  show ?case
  proof (cases "infinite A \<or> A = {}")
    case False
    have "A - {x} \<subset> A"
      using 2 by auto
    with False have "card (A - {x}) < card A"
      by (intro psubset_card_mono) auto
    thus ?thesis
      using False 2 by simp
  qed (use 2 in auto)
qed auto

lemmas [simp del] = topo_sorts.simps

lemma topo_sorts_empty [simp]: "topo_sorts {} R = {[]}"
  by (subst topo_sorts.simps) auto

lemma topo_sorts_infinite: "infinite A \<Longrightarrow> topo_sorts A R = {}"
  by (subst topo_sorts.simps) auto

lemma topo_sorts_rec:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> 
     topo_sorts A R = (\<Union>x\<in>{x\<in>A. \<forall>z\<in>A. R x z \<longrightarrow> z = x}. 
       (\<lambda>xs. x # xs) ` topo_sorts (A - {x}) (\<lambda>y z. R y z \<and> y \<noteq> x \<and> z \<noteq> x))"
  by (subst topo_sorts.simps) simp_all

lemma topo_sorts_cong [cong]:
  assumes "A = B" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y = R' x y"
  shows   "topo_sorts A R = topo_sorts B R'"
proof (cases "finite A")
  case True
  from this and assms(2) show ?thesis
    unfolding assms(1)[symmetric]
  proof (induction arbitrary: R R' rule: finite_psubset_induct)
    case (psubset A R R')
    show ?case
    proof (cases "A = {}")
      case False
      have "(\<Union>x\<in>{x \<in> A. \<forall>z\<in>A. R x z \<longrightarrow> z = x}. (#) x ` topo_sorts (A - {x}) (\<lambda>y z. R y z \<and> y \<noteq> x \<and> z \<noteq> x)) =
            (\<Union>x\<in>{x \<in> A. \<forall>z\<in>A. R' x z \<longrightarrow> z = x}. (#) x ` topo_sorts (A - {x}) (\<lambda>y z. R' y z \<and> y \<noteq> x \<and> z \<noteq> x))"
        using psubset.prems psubset.hyps
        by (intro arg_cong[of _ _ "\<Union>"] image_cong refl psubset.IH) auto
      thus ?thesis
        by (subst (1 2) topo_sorts_rec) (use False psubset.hyps in simp_all)
    qed auto
  qed
qed (simp_all add: assms(1) topo_sorts_infinite)

lemma topo_sorts_correct:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<in> A \<and> y \<in> A"
  shows   "topo_sorts A R = {xs\<in>permutations_of_set A. R \<le> of_ranking xs}"
  using assms
proof (induction A R rule: topo_sorts.induct)
  case (1 A R)
  note R = "1.prems"

  show ?case
  proof (cases "A = {} \<or> infinite A")
    case True
    thus ?thesis using R
      by (auto simp: topo_sorts_infinite permutations_of_set_infinite)
  next
    case False
    define M where "M = {x\<in>A. \<forall>z\<in>A. R x z \<longrightarrow> z = x}"
    define R' where "R' = (\<lambda>x y z. R y z \<and> y \<noteq> x \<and> z \<noteq> x)"

    have IH: "topo_sorts (A - {x}) (R' x) = {xs \<in> permutations_of_set (A - {x}). (R' x) \<le> of_ranking xs}"
      if x: "x \<in> M" for x
      unfolding R'_def by (rule "1.IH") (use False x R in \<open>auto simp: M_def\<close>)

    have "{xs\<in>permutations_of_set A. R \<le> of_ranking xs} =
            (\<Union>x\<in>A. ((#) x) ` {xs \<in> permutations_of_set (A - {x}). R \<le> of_ranking (x # xs)})"
      by (subst permutations_of_set_nonempty) (use False in auto)
    also have "\<dots> = (\<Union>x\<in>A. ((#) x) ` {xs \<in> permutations_of_set (A - {x}). x \<in> M \<and> R' x \<le> of_ranking xs})"
    proof (intro arg_cong[of _ _ "\<Union>"] image_cong Collect_cong conj_cong refl)
      fix x xs
      assume x: "x \<in> A" and xs: "xs \<in> permutations_of_set (A - {x})"
      from xs have xs': "set xs = A - {x}" "distinct xs"
        by (auto simp: permutations_of_set_def)

      have "R \<le> of_ranking (x # xs) \<longleftrightarrow> (\<forall>y z. R y z \<longrightarrow> z = x \<and> y \<in> set (x # xs) \<or> of_ranking xs y z)"
        unfolding le_fun_def of_ranking_Cons by auto
      also have "(\<lambda>y z. R y z \<longrightarrow> z = x \<and> y \<in> set (x # xs) \<or> of_ranking xs y z) =
                 (\<lambda>y z. R y z \<longrightarrow> ((y = x \<longrightarrow> z = x) \<and> (y \<noteq> x \<and> z \<noteq> x \<longrightarrow> of_ranking xs y z)))"
        unfolding fun_eq_iff using R of_ranking_altdef' xs'(1,2) by fastforce
      also have "(\<forall>y z. \<dots> y z) \<longleftrightarrow> (\<forall>z. R x z \<longrightarrow> z = x) \<and> R' x \<le> of_ranking xs"
        unfolding le_fun_def of_ranking_Cons R'_def by auto
      also have "(\<forall>z. R x z \<longrightarrow> z = x) \<longleftrightarrow> x \<in> M"
        unfolding M_def using x R by auto
      finally show "(R \<le> of_ranking (x # xs)) = (x \<in> M \<and> R' x \<le> of_ranking xs)" .
    qed
    also have "\<dots> = (\<Union>x\<in>M. ((#) x) ` {xs\<in>permutations_of_set (A - {x}). R' x \<le> of_ranking xs})"
      unfolding M_def by blast
    also have "\<dots> = (\<Union>x\<in>M. ((#) x) ` topo_sorts (A - {x}) (R' x))"
      using IH by blast
    also have "\<dots> = topo_sorts A R"
      unfolding R'_def M_def using False by (subst (2) topo_sorts_rec) simp_all
    finally show ?thesis ..
  qed
qed

lemma topo_sorts_nonempty:
  assumes "finite A" "\<And>x y. R x y \<Longrightarrow> x \<in> A \<and> y \<in> A" "\<And>x y. R x y \<Longrightarrow> \<not>R y x" "transp R"
  shows   "topo_sorts A R \<noteq> {}"
  using assms
proof (induction A R rule: topo_sorts.induct)
  case (1 A R)
  define R' where "R' = (\<lambda>x y. x \<in> A \<and> y \<in> A \<and> x = y \<or> R x y)"
  interpret R': order_on A R' 
    by standard (use "1.prems"(2,3) in \<open>auto simp: R'_def intro: transpD[OF \<open>transp R\<close>]\<close>)

  show ?case
  proof (cases "A = {}")
    case False
    define M where "M = Max_wrt_among R' A"
    have "M \<noteq> {}"
      unfolding M_def by (rule R'.Max_wrt_among_nonempty) (use False \<open>finite A\<close> in simp_all)
    obtain x where x: "x \<in> M"
      using \<open>M \<noteq> {}\<close> by blast
    have M_altdef: "M = {x\<in>A. \<forall>z\<in>A. R x z \<longrightarrow> z = x}"
      unfolding M_def Max_wrt_among_def R'_def using "1.prems" by blast

    define L where "L = topo_sorts (A - {x}) (\<lambda>y z. R y z \<and> y \<noteq> x \<and> z \<noteq> x)"
    have "L \<noteq> {}"
      unfolding L_def
    proof (rule "1.IH")
      show "transp (\<lambda>a b. R a b \<and> a \<noteq> x \<and> b \<noteq> x)"
        using \<open>transp R\<close> unfolding transp_def by blast
    qed (use "1.prems"(2,3) False x \<open>finite A\<close> in \<open>auto simp: M_altdef\<close>)

    have "topo_sorts A R = 
            (\<Union>x\<in>{x\<in>A. \<forall>z\<in>A. R x z \<longrightarrow> z = x}. 
              (\<lambda>xs. x # xs) ` topo_sorts (A - {x}) (\<lambda>y z. R y z \<and> y \<noteq> x \<and> z \<noteq> x))"
      by (subst topo_sorts.simps) (use False \<open>finite A\<close> in simp_all)
    also have "{x\<in>A. \<forall>z\<in>A. R x z \<longrightarrow> z = x} = M"
      unfolding M_altdef ..
    finally show "topo_sorts A R \<noteq> {}"
      using \<open>L \<noteq> {}\<close> \<open>x \<in> M\<close> unfolding L_def by blast
  qed auto
qed

lemma bij_betw_topo_sorts_linorders_on:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<in> A \<and> y \<in> A"
  shows   "bij_betw of_ranking (topo_sorts A R) {R'. finite_linorder_on A R' \<and> R \<le> R'}"
proof -
  have "bij_betw of_ranking {xs\<in>permutations_of_set A. R \<le> of_ranking xs}
          {R'\<in>{R'. finite_linorder_on A R'}. R \<le> R'}"
    using bij_betw_permutations_of_set_finite_linorders_on
    by (rule bij_betw_Collect) auto
  also have "{xs\<in>permutations_of_set A. R \<le> of_ranking xs} = topo_sorts A R"
    by (subst topo_sorts_correct) (use assms in auto)
  finally show ?thesis
    by simp
qed


text \<open>
  In the following, we give a more convenient formulation of this for computation. 

  The input is a relation represented as a list of pairs $(x, \textit{ys})$ where $\textit{ys}$ 
  is the set of all elements such that $(x,y)$ is in the relation.
\<close>

function topo_sorts_aux :: "('a \<times> 'a set) list \<Rightarrow> 'a list list" where
  "topo_sorts_aux xs =
     (if xs = [] then [[]] else
      List.bind (map fst (filter (\<lambda>(_,ys). ys = {}) xs))
        (\<lambda>x. map ((#) x) (topo_sorts_aux 
          (map (map_prod id (Set.filter (\<lambda>y. y \<noteq> x))) (filter (\<lambda>(y,_). y \<noteq> x) xs)))))"
  by auto
termination
  by (relation "Wellfounded.measure length")
     (auto simp: length_filter_less)

lemmas [simp del] = topo_sorts_aux.simps

lemma topo_sorts_aux_Nil [simp]: "topo_sorts_aux [] = [[]]"
  by (subst topo_sorts_aux.simps) auto

lemma topo_sorts_aux_rec:
  "xs \<noteq> [] \<Longrightarrow> topo_sorts_aux xs =
     List.bind (map fst (filter (\<lambda>(_,ys). ys = {}) xs))
        (\<lambda>x. map ((#) x) (topo_sorts_aux 
          (map (map_prod id (Set.filter (\<lambda>y. y \<noteq> x))) (filter (\<lambda>(y,_). y \<noteq> x) xs))))"
  by (subst topo_sorts_aux.simps) auto

lemma topo_sorts_aux_Cons:
  "topo_sorts_aux (y#xs) =
     List.bind (map fst (filter (\<lambda>(_,ys). ys = {}) (y#xs)))
        (\<lambda>x. map ((#) x) (topo_sorts_aux 
          (map (map_prod id (Set.filter (\<lambda>y. y \<noteq> x))) (filter (\<lambda>(y,_). y \<noteq> x) (y#xs)))))"
  by (rule topo_sorts_aux_rec) auto

lemma set_topo_sorts_aux:
  assumes "distinct (map fst xs)"
  assumes "\<And>x ys. (x, ys) \<in> set xs \<Longrightarrow> ys \<subseteq> set (map fst xs) - {x}"
  shows   "set (topo_sorts_aux xs) = 
             topo_sorts (set (map fst xs)) (\<lambda>x y. \<exists>ys. (x, ys) \<in> set xs \<and> y \<in> ys)"
  using assms
proof (induction xs rule: topo_sorts_aux.induct)
  case (1 xs)
  show ?case
  proof (cases "xs = []")
    case True
    thus ?thesis
      by (simp add: topo_sorts.simps[of "{}"] topo_sorts_aux.simps[of "[]"])
  next
    case False
    define M where "M = set (map fst (filter (\<lambda>(_,ys). ys = {}) xs))"
    define xs' where "xs' = (\<lambda>x. map (map_prod id (Set.filter (\<lambda>y. y \<noteq> x))) (filter (\<lambda>(y,_). y \<noteq> x) xs))"
    define R' where "R' = (\<lambda>x a b. \<exists>ys. (a, ys) \<in> set (xs' x) \<and> b \<in> ys)"

    have IH: "set (topo_sorts_aux (xs' x)) = topo_sorts (set (map fst (xs' x))) (R' x)"
      if "x \<in> M" for x
      unfolding xs'_def R'_def
    proof (rule "1.IH", goal_cases)
      case 2
      show ?case using that by (auto simp: M_def)
    next
      case 3
      thus ?case using "1.prems"
        by (auto intro!: distinct_filter simp: distinct_map intro: inj_on_subset)
    next
      case 4
      thus ?case using "1.prems" by fastforce
    qed fact+

    have "topo_sorts (set (map fst xs)) (\<lambda>x y. \<exists>ys. (x, ys) \<in> set xs \<and> y \<in> ys) =
            (\<Union>x\<in>{x \<in> set (map fst xs). \<forall>z\<in>set (map fst xs). (\<exists>ys. (x, ys) \<in> set xs \<and> z \<in> ys) \<longrightarrow> z = x}.
               (#) x ` topo_sorts (set (map fst xs) - {x}) (\<lambda>y z. (\<exists>ys. (y, ys) \<in> set xs \<and> z \<in> ys) \<and> y \<noteq> x \<and> z \<noteq> x))"
      by (subst topo_sorts_rec) (use False in simp_all)
    also have "{x \<in> set (map fst xs). \<forall>z\<in>set (map fst xs). (\<exists>ys. (x, ys) \<in> set xs \<and> z \<in> ys) \<longrightarrow> z = x} = M"
      (is "?lhs = ?rhs")
    proof (intro equalityI subsetI)
      fix x assume "x \<in> ?rhs"
      thus "x \<in> ?lhs"
        using "1.prems" by (fastforce simp: M_def distinct_map inj_on_def)
    next
      fix x assume "x \<in> ?lhs"
      hence x: "x \<in> set (map fst xs)" "\<And>z ys. z \<in> set (map fst xs) \<Longrightarrow> (x, ys) \<in> set xs \<and> z \<in> ys \<Longrightarrow> z = x"
        by blast+
      from x(1) obtain ys where ys: "(x, ys) \<in> set xs"
        by force
      have "ys \<subseteq> {}"
      proof
        fix y assume "y \<in> ys"
        with ys show "y \<in> {}"
          using x(2)[of y ys] "1.prems" by auto
      qed
      thus "x \<in> ?rhs"
        unfolding M_def using x(1) ys by (auto simp: image_iff)
    qed
    also have "(\<lambda>x. set (map fst xs) - {x}) = (\<lambda>x. set (map fst (xs' x)))"
      by (force simp: xs'_def fun_eq_iff)
    also have "(\<lambda>x y z. (\<exists>ys. (y, ys) \<in> set xs \<and> z \<in> ys) \<and> y \<noteq> x \<and> z \<noteq> x) = R'"
      unfolding R'_def using "1.prems"
      by (auto simp: fun_eq_iff distinct_map inj_on_def xs'_def map_prod_def
                           case_prod_unfold image_iff)
    also have "(\<Union>x\<in>M. (#) x ` topo_sorts (set (map fst (xs' x))) (R' x)) =
               (\<Union>x\<in>M. (#) x ` set (topo_sorts_aux (xs' x)))"
      using IH by blast
    also have "\<dots> = set (topo_sorts_aux xs)"
      by (subst (2) topo_sorts_aux_rec) (use False in \<open>auto simp: M_def xs'_def List.bind_def\<close>)
    finally show ?thesis ..
  qed
qed

lemma topo_sorts_code [code]:
  "topo_sorts (set xs) R = (let xs' = remdups xs in
     set (topo_sorts_aux (map (\<lambda>x. (x, set (filter (\<lambda>y. y \<noteq> x \<and> R x y) xs'))) xs')))"
proof -
  define xs' where "xs' = remdups xs"
  have "set (topo_sorts_aux (map (\<lambda>x. (x, set (filter (\<lambda>y. y \<noteq> x \<and> R x y) xs'))) xs')) = 
        topo_sorts (set xs) (\<lambda>x y. \<exists>ys. (x, ys) \<in> (\<lambda>x. (x, set (filter (\<lambda>y. y \<noteq> x \<and> R x y) xs'))) ` set xs' \<and> y \<in> ys)"
    by (subst set_topo_sorts_aux) (auto simp: o_def xs'_def)
  also have "(\<lambda>x y. \<exists>ys. (x, ys) \<in> (\<lambda>x. (x, set (filter (\<lambda>y. y \<noteq> x \<and> R x y) xs'))) ` set xs' \<and> y \<in> ys) =
             (\<lambda>x y. x \<in> set xs \<and> y \<in> set xs \<and> x \<noteq> y \<and> R x y)"
    by (auto simp: xs'_def image_iff)
  also have "topo_sorts (set xs) \<dots> = topo_sorts (set xs) R"
    by (rule topo_sorts_cong) auto
  finally show ?thesis
    by (simp add: Let_def xs'_def)
qed

end