(*
 Title:Differential_Privacy_Laplace_Mechanism_Multi.thy
 Author: Tetsuya Sato
*)

theory Differential_Privacy_Laplace_Mechanism_Multi
  imports "List_Space/List_Space"
    "Differential_Privacy_Laplace_Mechanism"
begin

subsection \<open>Bundled Laplace Noise\<close>

lemma space_listM_borel_UNIV[measurable,simp]:
  shows "space (listM borel) = UNIV"
  unfolding space_listM by auto

context
  fixes b::real (* scale *)
begin

paragraph \<open> The list of Laplace distribution with scale \<open>b\<close> and average \<open>0\<close> \<close>

primrec Lap_dist0_list :: "nat \<Rightarrow> (real list) measure" where
  "Lap_dist0_list 0 = return (listM borel) []" |
  "Lap_dist0_list (Suc n) = do{x1 \<leftarrow> (Lap_dist0 b); x2 \<leftarrow> (Lap_dist0_list n); return (listM borel) (x1 # x2)}"

paragraph \<open> A function adding Laplace noise to each element of a real list \<close>

primrec Lap_dist_list :: "real list \<Rightarrow> (real list) measure" where
  "Lap_dist_list [] = return (listM borel) []"|
  "Lap_dist_list (x # xs) = do{x1 \<leftarrow> (Lap_dist b x); x2 \<leftarrow> (Lap_dist_list xs); return (listM borel) (x1 # x2)}"

lemma measurable_Lap_dist_list[measurable]:
  shows "Lap_dist_list \<in> listM borel \<rightarrow>\<^sub>M prob_algebra (listM borel)"
proof-
  have 1: "(return (listM borel) []) \<in> space (prob_algebra (listM borel))"
    by (metis UNIV_I lists_UNIV measurable_return_prob_space measurable_space space_borel space_listM)
  show ?thesis
    unfolding Lap_dist_list_def using 1 measurable_rec_list''' by measurable
qed

lemma prob_space_Lap_dist_list[measurable,simp]:
  shows "prob_space (Lap_dist_list xs)"
  using space_listM_borel_UNIV measurable_Lap_dist_list measurable_space[of Lap_dist_list] actual_prob_space by blast

lemma Laprepsp'[measurable,simp]:
  shows "Lap_dist_list xs \<in> space (prob_algebra (listM borel))"
  by (metis UNIV_I measurable_Lap_dist_list measurable_space space_listM_borel_UNIV)

lemma Laprepsp[measurable,simp]:
  shows "Lap_dist_list xs \<in> space (subprob_algebra (listM borel))"
  by (simp add: prob_space_imp_subprob_space space_prob_algebra_sets space_subprob_algebra)

lemma sets_Lap_dist_list[measurable_cong]:
  shows "\<And>zs. sets(Lap_dist_list zs) = sets(listM borel)"
  by (simp add: space_prob_algebra_sets)

lemma space_Lap_dist_list:
  shows "\<And>zs. space(Lap_dist_list zs) = space (listM borel)"
  by (simp add: sets_Lap_dist_list sets_eq_imp_space_eq)

lemma emeasure_Lap_dist_list_length:
  shows "emeasure (Lap_dist_list ys) {xs. length xs = length ys} = 1"
proof(induction ys)
  case Nil
  have 1: "{xs. length xs = length []} = {[]}"
    by auto
  have 2: "{[]} \<in> sets (listM borel)"
    using sets_listM_length[of borel"0"] unfolding space_listM by auto
  thus ?case by(auto simp: 2 1)
next
  case (Cons a ys)
  note [simp] = sets_Lap_dist_list sets_Lap_dist space_pair_measure space_Lap_dist
  have [measurable]: "return (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys) \<in> borel \<Otimes>\<^sub>M listM borel \<rightarrow>\<^sub>M subprob_algebra (borel \<Otimes>\<^sub>M listM borel)"
    by (metis (mono_tags, opaque_lifting) sets_Lap_dist_list return_measurable return_sets_cong sets_Lap_dist sets_pair_measure_cong)
  have "Lap_dist_list (a # ys) = Lap_dist b a \<bind> (\<lambda>x1. Lap_dist_list ys \<bind> (\<lambda>x2. return (listM borel) (x1 # x2)))"
    unfolding Lap_dist_list.simps(2) by auto
  also have "... = ((Lap_dist b a) \<Otimes>\<^sub>M (Lap_dist_list ys)) \<bind> (\<lambda>(x1,x2). return (listM borel) (x1 # x2))"
  proof(subst pair_prob_space.pair_measure_eq_bind)
    show "Lap_dist b a \<bind> (\<lambda>x1. Lap_dist_list ys \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))) = Lap_dist b a \<bind> (\<lambda>x. Lap_dist_list ys \<bind> (\<lambda>y. return (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys) (x, y))) \<bind> (\<lambda>(x1, x2). return (listM borel) (x1 # x2))"
    proof(subst bind_assoc)
      show "Lap_dist b a \<bind> (\<lambda>x1. Lap_dist_list ys \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))) = Lap_dist b a \<bind> (\<lambda>x. Lap_dist_list ys \<bind> (\<lambda>y. return (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys) (x, y)) \<bind> (\<lambda>(x1, x2). return (listM borel) (x1 # x2)))"
        by(subst bind_assoc,measurable)(subst bind_return[where N ="(listM borel)"],auto simp: sets_eq_imp_space_eq)
      show "(\<lambda>(x1, x2). return (listM borel) (x1 # x2)) \<in> borel \<Otimes>\<^sub>M listM borel \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
        by measurable
      show "(\<lambda>x. Lap_dist_list ys \<bind> (\<lambda>y. return (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys) (x, y))) \<in> Lap_dist b a \<rightarrow>\<^sub>M subprob_algebra (borel \<Otimes>\<^sub>M listM borel)"
      proof(subst measurable_bind)
        show "(\<lambda>x. return (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys) (fst x, snd x)) \<in> Lap_dist b a \<Otimes>\<^sub>M (Lap_dist_list ys) \<rightarrow>\<^sub>M subprob_algebra (borel \<Otimes>\<^sub>M listM borel)"
          by(rule measurable_compose,measurable)
        show "(\<lambda>x. Lap_dist_list ys) \<in> Lap_dist b a \<rightarrow>\<^sub>M subprob_algebra (Lap_dist_list ys)"
          by (auto simp: prob_space.M_in_subprob)
      qed(auto)
    qed
    show "pair_prob_space (Lap_dist b a) (Lap_dist_list ys)"
      unfolding pair_prob_space_def pair_sigma_finite_def using prob_space_Lap_dist prob_space_Lap_dist_list
      by (auto simp: prob_space_imp_sigma_finite)
  qed
  finally have eq1: "Lap_dist_list (a # ys) = Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys \<bind> (\<lambda>(x1, x2). return (listM borel) (x1 # x2))".

  show "emeasure (Lap_dist_list (a # ys)) {xs. length xs = length (a # ys)} = (1 :: ennreal)"unfolding eq1
  proof(subst Giry_Monad.emeasure_bind emeasure_return)
    show "(\<integral>\<^sup>+ x. emeasure (case x of (x1, x2) \<Rightarrow> (return (listM borel) (x1 # x2))) {xs. (length xs) = (length (a # ys))} \<partial>((Lap_dist b a) \<Otimes>\<^sub>M (Lap_dist_list ys))) = 1"
    proof(subst pair_sigma_finite.nn_integral_snd[THEN sym])
      show "(\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. emeasure (case (x, y) of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) {xs. length xs = length (a # ys)} \<partial>Lap_dist b a \<partial>Lap_dist_list ys) = 1"
      proof-
        {
          fix y :: "real list"
          have "(\<integral>\<^sup>+ x. emeasure (case (x, y) of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) {xs. length xs = length (a # ys)} \<partial>Lap_dist b a) = (\<integral>\<^sup>+ x. emeasure (return (listM borel) (x # y)) {xs. length xs = length (a # ys)} \<partial>Lap_dist b a)"by auto
          also have "... = (\<integral>\<^sup>+ x. indicator {x. length (x # y) = length (a # ys)} x \<partial>Lap_dist b a)"
          proof(subst emeasure_return)
            show "\<And>x. {xs. length xs = length (a # ys)} \<in> sets (listM borel)"
              by (metis (no_types, lifting) Collect_cong iso_tuple_UNIV_I sets_listM_length space_listM_borel_UNIV)
            show "(\<integral>\<^sup>+ x. indicator {xs. length xs = length (a # ys)} (x # y) \<partial>Lap_dist b a) = (\<integral>\<^sup>+ x. indicator {x. length (x # y) = length (a # ys)} x \<partial>Lap_dist b a)"
              by(rule nn_integral_cong,auto)
          qed
          also have "... = (\<integral>\<^sup>+ x. indicator {x. length y = length ys} x \<partial>Lap_dist b a)"
            by auto
          also have "... = indicator {z. length z = length ys} y"
          proof(split split_indicator,intro conjI impI)
            show "y \<notin> {z. length z = length ys} \<Longrightarrow> integral\<^sup>N (Lap_dist b a) (indicator {x. length y = length ys}) = 0"
              by auto
            show "y \<in> {z. length z = length ys} \<Longrightarrow> integral\<^sup>N (Lap_dist b a) (indicator {x. length y = length ys}) = 1"
              using prob_space_Lap_dist prob_space.emeasure_space_1 by fastforce
          qed
          finally have "(\<integral>\<^sup>+ x. emeasure (case (x, y) of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) {xs. length xs = length (a # ys)} \<partial>Lap_dist b a) = indicator {z. length z = length ys} y".
        }note * = this

        hence "(\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. emeasure (case (x, y) of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) {xs. length xs = length (a # ys)} \<partial>Lap_dist b a \<partial>Lap_dist_list ys) = (\<integral>\<^sup>+ y. indicator {z. length z = length ys} y \<partial>Lap_dist_list ys)"
          by auto
        also have "... = emeasure (Lap_dist_list ys) {z. length z = length ys}"
          by(subst nn_integral_indicator)(use sets_listM_length[of borel"length ys"] in auto)
        also have "... = 1"
          by(auto simp:Cons.IH)
        finally show ?thesis.
      qed
      show "pair_sigma_finite (Lap_dist b a) (Lap_dist_list ys)"
        by (auto simp: pair_sigma_finite_def prob_space_imp_subprob_space subprob_space_imp_sigma_finite)

      have "(\<lambda>x. emeasure (case x of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) {xs. length xs = length (a # ys)}) = (\<lambda>x. emeasure x {xs. length xs = length (a # ys)}) o (\<lambda>x. (case x of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)))"
        by auto
      also have "... \<in> borel_measurable (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys)"
      proof(intro measurable_comp)
        show "(\<lambda>x. case x of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) \<in> Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys \<rightarrow>\<^sub>M subprob_algebra(listM borel)"
          by measurable
        show "(\<lambda>x. emeasure x {xs. length xs = length (a # ys)}) \<in> borel_measurable (subprob_algebra (listM borel))"
          by(rule measurable_emeasure_subprob_algebra)(use sets_listM_length[of borel"length (a#ys)"] in auto)
      qed
      finally show "(\<lambda>x. emeasure (case x of (x1, x2) \<Rightarrow> return (listM borel) (x1 # x2)) {xs. length xs = length (a # ys)}) \<in> borel_measurable (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys)".
    qed
    show "space (Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys) \<noteq> {}"
      by (auto simp: prob_space.not_empty prob_space_pair)
    show "{xs. length xs = length (a # ys)} \<in> sets (listM borel)"
      by (use sets_listM_length[of borel"length (a#ys)"] in auto)
    show "(\<lambda>(x1, x2). return (listM borel) (x1 # x2)) \<in> Lap_dist b a \<Otimes>\<^sub>M Lap_dist_list ys \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
      by measurable
  qed
qed

lemma Lap_dist0_list_Lap_dist_list:
  shows "Lap_dist_list (replicate n 0) = Lap_dist0_list n"
  by(induction n,auto simp: Lap_dist0_def)

corollary
  shows prob_space_Lap_dist0_list[measurable,simp]: "prob_space ( Lap_dist0_list n)"
    and prob_algebra_Lap_dist0_list[measurable,simp]: " Lap_dist0_list n \<in> space (prob_algebra (listM borel))"
    and subprob_algebra_Lap_dist0_list[measurable,simp]: " Lap_dist0_list n \<in> space (subprob_algebra (listM borel))"
    and sets_Lap_dist0_list[measurable_cong]:"sets(Lap_dist0_list n) = sets(listM borel)"
  by(auto simp add: Lap_dist0_list_Lap_dist_list[symmetric] sets_Lap_dist_list)

corollary emeasure_Lap_dist0_list_length:
  shows "emeasure (Lap_dist0_list n) {xs. length xs = n} = 1"
  using emeasure_Lap_dist_list_length[of " (replicate n 0)"]
  by(auto simp: Lap_dist0_list_Lap_dist_list[symmetric] )

lemma Lap_dist_list_def2:
  shows "Lap_dist_list xs = do{ys \<leftarrow> (Lap_dist0_list (length xs)); return (listM borel) (map2 (+) xs ys)}"
proof(induction xs)
  case Nil
  thus ?case unfolding Lap_dist_list.simps(1) list.map(1) zip_Nil by(subst Giry_Monad.bind_const',auto intro!: prob_space_return subprob_space_return simp: space_listM)
next
  case (Cons a xs)
  note [measurable del] = borel_measurable_count_space

  have [simp]: "(replicate (length xs) 0) \<in> space(listM borel)"
    unfolding space_listM by auto
  have 4[measurable]: "sets (Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x))) = sets borel"
    unfolding Lap_dist_shift[symmetric] sets_Lap_dist by auto
  have 5[measurable]: "sets (Lap_dist_list (replicate (length xs) 0)) = sets (listM borel)"
    by(simp add:sets_Lap_dist_list)
  hence [measurable]: "(map2 (+) (a#xs)) \<in> listM borel \<rightarrow>\<^sub>M listM borel"
    by measurable
  have [simp]: "prob_space (Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x)))"
    by(rule prob_space_bind'[of _ borel _ borel],auto)

  have "Lap_dist_list (a # xs) = Lap_dist b a \<bind> (\<lambda>x1. Lap_dist0_list (length xs) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) xs ys)) \<bind> (\<lambda>x2. return (listM borel) (x1 # x2)))"
    unfolding Lap_dist_list.simps(2) Cons by auto
  also have "... = Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x)) \<bind> (\<lambda>x1. Lap_dist0_list (length xs) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) xs ys)) \<bind> (\<lambda>x2. return (listM borel) (x1 # x2)))"
    unfolding Lap_dist_shift[of b 0 a,simplified] by auto
  also have "... = Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x)) \<bind> (\<lambda>x1. Lap_dist0_list (length xs) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) xs ys) \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))))"
  proof(subst bind_assoc[THEN sym])
    show "\<And>x1. (\<lambda>x2. return (listM borel) (x1 # x2)) \<in>(listM borel) \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
      by measurable
    have "sets (Lap_dist0_list (length xs)) = sets (listM borel)"
      by(auto simp: sets_Lap_dist0_list)
    thus"(\<lambda>ys. return (listM borel) (map2 (+) xs ys)) \<in> Lap_dist0_list (length xs) \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
      by measurable
  qed(auto)
  also have "... = Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x)) \<bind> (\<lambda>x1. Lap_dist0_list (length xs) \<bind> (\<lambda>ys. return (listM borel) (x1 # (map2 (+) xs ys))))"
    by(subst bind_return[where N ="listM borel"],auto)
  also have "... = Lap_dist0_list (length xs) \<bind> (\<lambda>y. Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x)) \<bind> (\<lambda>x. return (listM borel) (x # map2 (+) xs y)))"
  proof(subst pair_prob_space.bind_rotate[where N ="listM borel"])
    show "pair_prob_space (Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x))) (Lap_dist0_list(length xs))"
      by (auto simp: prob_space_imp_sigma_finite pair_prob_space_def pair_sigma_finite_def)
    have 6: "sets ((Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x))) \<Otimes>\<^sub>M Lap_dist0_list (length xs)) = sets(borel \<Otimes>\<^sub>M listM borel)"
      using 4 5 by(auto simp: Lap_dist0_list_Lap_dist_list)
    show "(\<lambda>(x, y). return (listM borel) (x # map2 (+) xs y)) \<in> (Lap_dist b 0 \<bind> (\<lambda>x. return borel (a + x))) \<Otimes>\<^sub>M Lap_dist0_list (length xs) \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
      by(subst measurable_cong_sets[OF 6],auto simp: Lap_dist0_list_Lap_dist_list)
  qed(auto)
  also have "... = Lap_dist0_list (length xs) \<bind> (\<lambda>y. Lap_dist b 0 \<bind> (\<lambda>x. (return borel (a + x)) \<bind> (\<lambda>x. return (listM borel) (x # map2 (+) xs y))))"
    by(subst bind_assoc,measurable)
  also have "... = Lap_dist0_list (length xs) \<bind> (\<lambda>y. Lap_dist b 0 \<bind> (\<lambda>x. (return (listM borel) ((a + x) # map2 (+) xs y))))"
    by(subst bind_return,measurable)
  also have "... = Lap_dist b 0 \<bind> (\<lambda>x. Lap_dist0_list (length xs) \<bind> (\<lambda>ys. (return (listM borel) (map2 (+) (a#xs) (x#ys)))))"
    by(subst pair_prob_space.bind_rotate[where N ="listM borel"],auto simp: prob_space_imp_sigma_finite pair_prob_space_def pair_sigma_finite_def)
  also have "... = Lap_dist b 0 \<bind> (\<lambda>x. Lap_dist0_list (length xs) \<bind> (\<lambda>zs. (return (listM borel)(x # zs)) \<bind> (\<lambda>ys. (return (listM borel) (map2 (+) (a#xs) (ys))))))"
    by(subst bind_return[where N ="listM borel"],auto)
  also have "... = (Lap_dist b 0 \<bind> (\<lambda>x. Lap_dist0_list (length xs) \<bind> (\<lambda>zs. (return (listM borel)(x # zs))) \<bind> (\<lambda>ys. (return (listM borel) (map2 (+) (a#xs) (ys))))))"
    by(subst bind_assoc[THEN sym],measurable)
  also have "... = Lap_dist0_list (length (a # xs)) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) (a # xs) ys))"
    unfolding Lap_dist_list.simps(2) length_Cons Lap_dist0_list.simps(2) Lap_dist0_def
    by(subst bind_assoc[THEN sym],measurable)
  finally show ?case by auto
qed

end(*end of context*)

lemma sum_list_cons:
  fixes xs ys :: "'a list" and n :: nat
  assumes "length xs = n" and "length ys = n"
  shows "(\<Sum> i\<in>{1..Suc n}. d (nth (x # xs) (i-1)) (nth (y # ys) (i-1) )) = d x y + (\<Sum> i\<in>{1..n}. d (nth xs (i-1)) (nth ys (i-1)))"
proof-
  have 0: "{0..n} = {0..0} \<union> {1..n}"
    by auto
  show "(\<Sum>i = 1..Suc n. d (nth (x # xs) (i-1)) (nth (y # ys) (i-1))) = d x y + (\<Sum>(i :: nat)\<in>{1..n}. d (nth (xs) (i-1)) (nth (ys ) (i-1)))"
    by(subst sum.reindex_bij_witness[ of "{1..Suc n}" Suc "\<lambda>i. i - 1" "{0..n}"],auto simp: 0)
qed

lemma adj_Cons_partition:
  fixes xs ys :: "real list" and n :: nat and r :: real
  assumes "length xs = n" and "length ys = n"
    and adj: "(\<Sum> i\<in>{1..Suc n}. \<bar> nth (x # xs) (i-1) - nth (y # ys) (i-1) \<bar>) \<le> r"
    and posr: "r \<ge> 0"
  obtains r1 r2::real where "0 \<le> r1" and "0 \<le> r2" and "\<bar>x - y\<bar> \<le> r1" and "(\<Sum>i = 1..n. \<bar>xs ! (i - 1) - ys ! (i - 1)\<bar>) \<le> r2 " and "r1 + r2 \<le> r"
proof-
  have "(\<Sum>i = 1..Suc n. \<bar>(x # xs) ! (i - 1) - (y # ys) ! (i - 1)\<bar>) = \<bar> x - y\<bar> + (\<Sum>(i :: nat)\<in>{1..n}. \<bar>xs ! (i-1) - ys ! (i-1)\<bar>)"
    using sum_list_cons[OF assms(1,2)] by auto
  with adj have " \<bar>x - y\<bar> + (\<Sum>i = 1..n. \<bar>xs ! (i - 1) - ys ! (i - 1)\<bar>) \<le> r" and "0 \<le> \<bar>x - y\<bar>" and "0 \<le> (\<Sum>i = 1..n. \<bar>xs ! (i - 1) - ys ! (i - 1)\<bar>) "
    by auto
  thus " (\<And>r1 r2. 0 \<le> r1 \<Longrightarrow> 0 \<le> r2 \<Longrightarrow> \<bar>x - y\<bar> \<le> r1 \<Longrightarrow> (\<Sum>i = 1..n. \<bar>xs ! (i - 1) - ys ! (i - 1)\<bar>) \<le> r2 \<Longrightarrow> r1 + r2 \<le> r \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by blast
qed

lemma adj_list_0:
  fixes xs ys :: "real list" and n :: nat
  shows "length xs = n \<Longrightarrow> length ys = n \<Longrightarrow> (\<Sum> i\<in>{1..n}. \<bar> nth xs (i-1) - nth ys (i-1) \<bar>) \<le> 0 \<Longrightarrow> xs = ys"
proof(induction xs arbitrary: ys n )
  case Nil
  thus ?case by auto
next
  case (Cons x xs2)
  then obtain m y ys2 where n: "n = Suc m" and ys: "ys = (y # ys2)" and xs2: "length xs2 = m" and ys2: "length ys2 = m"
    by (metis length_Suc_conv)
  hence *: " (\<Sum> i\<in>{1..Suc m}. \<bar> nth (x # xs2) (i-1) - nth (y # ys2) (i-1) \<bar>) \<le> 0"
    using Cons.prems(3) unfolding ys n by auto
  then obtain r1 r2::real where r1: "0 \<le> r1" and r2: "0 \<le> r2" and r1a: "\<bar>x - y\<bar> \<le> r1" and r2a: "(\<Sum>i = 1..m. \<bar>xs2 ! (i - 1) - ys2 ! (i - 1)\<bar>) \<le> r2 " and req: "r1 + r2 \<le> 0"
    using adj_Cons_partition[of xs2 m ys2 x y 0, OF xs2 ys2 *] by auto
  hence "r1 = 0" and "r2 = 0" and "x = y" and "xs2 = ys2"
    using Cons.IH[of m ys2, OF xs2 ys2] r2a r1a by auto
  thus "x # xs2 = ys" unfolding ys by auto
qed

lemma DP_Lap_dist_list:
  fixes xs ys :: "real list" and n :: nat and r :: real and b::real
  assumes posb: "b > (0 :: real)"
    and "length xs = n" and "length ys = n"
    and adj: "(\<Sum> i\<in>{1..n}. \<bar> nth xs (i-1) - nth ys (i-1) \<bar>) \<le> r"
    and posr: "r \<ge> 0"
  shows "DP_divergence (Lap_dist_list b xs) (Lap_dist_list b ys) (r / b) \<le> 0"
  using assms
proof(induction xs arbitrary: ys n r b)
  case Nil
  hence "n = 0" and "ys = []"
    by auto
  hence 1: "Lap_dist_list b ys = (Lap_dist_list b [])"
    by auto
  have 2: " 0 \<le> r / b"
    using Nil by auto
  have "DP_divergence (Lap_dist_list b []) (Lap_dist_list b ys) (r/b) \<le> DP_divergence (Lap_dist_list b []) (Lap_dist_list b []) 0"
    by(unfold 1, rule DP_divergence_monotonicity)
      (auto simp: prob_space_return space_prob_algebra 2)
  then show ?case
    by (simp add: DP_divergence_reflexivity)
next
  case (Cons x xs2)
  then obtain y ys2 m where n: "n = Suc m" and ys: "ys = y # ys2" and xs2: "length xs2 = m" and ys2: "length ys2 = m"
    by (auto simp: length_Suc_conv)
  then obtain r1 r2::real
    where r1: "0 \<le> r1"
      and r2: "0 \<le> r2"
      and r1a: "\<bar>x - y\<bar> \<le> r1"
      and r2a: "(\<Sum>i = 1..m. \<bar>xs2 ! (i - 1) - ys2 ! (i - 1)\<bar>) \<le> r2 "
      and req: "r1 + r2 \<le> r"
    using adj_Cons_partition[of xs2 m ys2 x y r] Cons by blast
  have DPr2: "DP_divergence (Lap_dist_list b xs2) (Lap_dist_list b ys2) (r2 / b) \<le> 0"
    by (auto simp: Cons.IH[of b m ys2 r2, OF Cons.prems(1) xs2 ys2 r2a r2])
  have DPr1: "DP_divergence (Lap_dist b x) (Lap_dist b y) (r1 / b) \<le> 0"
    by (auto simp: DP_divergence_Lap_dist'[of b x y r1 , OF Cons.prems(1) r1a] zero_ereal_def)
  have " r1 / b + r2 / b \<le> r / b"
    by (metis Cons.prems(1) add_divide_distrib divide_right_mono leI order_trans_rules(20) req)
  hence "DP_divergence (Lap_dist_list b (x # xs2)) (Lap_dist_list b ys) (r / b) \<le> DP_divergence (Lap_dist_list b (x # xs2)) (Lap_dist_list b ys) (r1 / b + r2 / b)"
    by(intro DP_divergence_monotonicity Laprepsp') auto
  also have " ... \<le> ereal (0 + 0)"
    unfolding ys Lap_dist_list.simps(2)
  proof(rule DP_divergence_composability[of "Lap_dist b x" borel "Lap_dist b y" _ _ _ "r1 / b" 0 "r2 / b" 0])
    show "Lap_dist b x \<in> space (prob_algebra borel)"
      and "Lap_dist b y \<in> space (prob_algebra borel)"
      and "(\<lambda>x1. Lap_dist_list b xs2 \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))) \<in> borel \<rightarrow>\<^sub>M prob_algebra (listM borel)"
      and "(\<lambda>x1. Lap_dist_list b ys2 \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))) \<in> borel \<rightarrow>\<^sub>M prob_algebra (listM borel)"
      by auto
    show " \<forall>x\<in>space borel.
 DP_divergence (Lap_dist_list b xs2 \<bind> (\<lambda>x2. return (listM borel) (x # x2))) (Lap_dist_list b ys2 \<bind> (\<lambda>x2. return (listM borel) (x # x2))) (r2 / b) \<le> ereal 0"
    proof
      fix z::real assume "z \<in> space borel"
      have " DP_divergence (Lap_dist_list b xs2 \<bind> (\<lambda>x2. return (listM borel) (z # x2))) (Lap_dist_list b ys2 \<bind> (\<lambda>x2. return (listM borel) (z # x2))) (r2 / b + 0) \<le> ereal (0 + 0)"
      proof(rule DP_divergence_composability[of "Lap_dist_list b xs2" "listM borel" "Lap_dist_list b ys2" _ _ _ "r2 / b" 0 ])
        show "Lap_dist_list b xs2 \<in> space (prob_algebra (listM borel))"
          and "Lap_dist_list b ys2 \<in> space (prob_algebra (listM borel))"
          and "(\<lambda>x2. return (listM borel) (z # x2)) \<in> listM borel \<rightarrow>\<^sub>M prob_algebra (listM borel)"
          and "(\<lambda>x2. return (listM borel) (z # x2)) \<in> listM borel \<rightarrow>\<^sub>M prob_algebra (listM borel)"
          and "(0::real) \<le> 0 "
          by auto
        show " DP_divergence (Lap_dist_list b xs2) (Lap_dist_list b ys2) (r2 / b) \<le> ereal 0"
          using DPr2 by(auto simp: zero_ereal_def)
        show "\<forall>x\<in>space (listM borel). DP_divergence (return (listM borel) (z # x)) (return (listM borel) (z # x)) 0 \<le> ereal 0"
          by (auto simp: DP_divergence_reflexivity order.refl zero_ereal_def)
        show " 0 \<le> r2 / b"
          by (auto simp: Cons.prems(1) r2 divide_nonneg_pos)
      qed
      thus "DP_divergence (Lap_dist_list b xs2 \<bind> (\<lambda>x2. return (listM borel) (z # x2))) (Lap_dist_list b ys2 \<bind> (\<lambda>x2. return (listM borel) (z # x2))) (r2 / b) \<le> ereal 0"
        by auto
    qed
    show "DP_divergence (Lap_dist b x) (Lap_dist b y) (r1 / b) \<le> ereal 0"
      using DPr1 by(auto simp: zero_ereal_def)
    show " 0 \<le> r1 / b"
      and " 0 \<le> r2 / b"
      by (auto simp: Cons.prems(1) r1 r2 divide_nonneg_pos)
  qed
  also have "... = 0"
    by auto
  finally show " DP_divergence (Lap_dist_list b (x # xs2)) (Lap_dist_list b ys) (r / b) \<le> 0" .
qed

corollary DP_Lap_dist_list_eps:
  fixes xs ys :: "real list" and n :: nat and r :: real
  assumes pose: "\<epsilon> > (0 :: real)"
    and "length xs = n" and "length ys = n"
    and adj: "(\<Sum> i\<in>{1..n}. \<bar> nth xs (i-1) - nth ys (i-1) \<bar>) \<le> r"
    and posr: "r \<ge> 0"
  shows "DP_divergence (Lap_dist_list (r / \<epsilon>) xs) (Lap_dist_list (r / \<epsilon>) ys) \<epsilon> \<le> 0"
proof(cases "r = 0")
  case True
  with assms adj_list_0 have *: "xs = ys"
    by blast
  have nne: "0 \<le> \<epsilon>"
    using pose by auto
  then show ?thesis
    unfolding * using DP_divergence_reflexivity'[of \<epsilon>  "Lap_dist_list (r / \<epsilon>) ys"] by auto
next
  case False
  with posr have posr': "0 < r"
    by auto
  note * = DP_Lap_dist_list[of " (r / \<epsilon>)" xs n ys r , OF _ assms(2,3,4) posr]
  from posr' pose have 1: "r / (r / \<epsilon>) = \<epsilon>" and 2: "0 < r / \<epsilon>"
    by auto
  then show ?thesis using *[OF 2] unfolding 1 by blast
qed

hide_fact(open) adj_Cons_partition sum_list_cons adj_list_0

end