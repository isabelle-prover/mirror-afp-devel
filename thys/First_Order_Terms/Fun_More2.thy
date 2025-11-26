(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>Results on Bijections\<close>

theory Fun_More2 imports Main begin

lemma finite_card_eq_imp_bij_betw:
  assumes "finite A"
    and "card (f ` A) = card A"
  shows "bij_betw f A (f ` A)"
  using \<open>card (f ` A) = card A\<close>
  unfolding inj_on_iff_eq_card [OF \<open>finite A\<close>, symmetric]
  by (rule inj_on_imp_bij_betw)

text \<open>Every bijective function between two subsets of a set can be turned
into a compatible renaming (with finite domain) on the full set.\<close>
lemma bij_betw_extend:
  assumes *: "bij_betw f A B"
    and "A \<subseteq> V"
    and "B \<subseteq> V"
    and "finite A"
  shows "\<exists>g. finite {x. g x \<noteq> x} \<and>
    (\<forall>x\<in>UNIV - (A \<union> B). g x = x) \<and>
    (\<forall>x\<in>A. g x = f x) \<and>
    bij_betw g V V"
proof -
  have "finite B" using assms by (metis bij_betw_finite)
  have [simp]: "card A = card B" by (metis * bij_betw_same_card)
  have "card (A - B) = card (B - A)"
  proof -
    have "card (A - B) = card A - card (A \<inter> B)"
      by (metis \<open>finite A\<close> card_Diff_subset_Int finite_Int)
    moreover have "card (B - A) = card B - card (A \<inter> B)"
      by (metis \<open>finite A\<close> card_Diff_subset_Int finite_Int inf_commute)
    ultimately show ?thesis by simp
  qed
  then obtain g where **: "bij_betw g (B - A) (A - B)"
    by (metis \<open>finite A\<close> \<open>finite B\<close> bij_betw_iff_card finite_Diff)
  define h where "h = (\<lambda>x. if x \<in> A then f x else if x \<in> B - A then g x else x)"
  have "bij_betw h A B"
    by (metis (full_types) * bij_betw_cong h_def)
  moreover have "bij_betw h (V - (A \<union> B)) (V - (A \<union> B))"
    by (auto simp: bij_betw_def h_def inj_on_def)
  moreover have "B \<inter> (V - (A \<union> B)) = {}" by blast
  ultimately have "bij_betw h (A \<union> (V - (A \<union> B))) (B \<union> (V - (A \<union> B)))"
    by (rule bij_betw_combine)
  moreover have "A \<union> (V - (A \<union> B)) = V - (B - A)"
    and "B \<union> (V - (A \<union> B)) = V - (A - B)"
    using \<open>A \<subseteq> V\<close> and \<open>B \<subseteq> V\<close> by blast+
  ultimately have "bij_betw h (V - (B - A)) (V - (A - B))" by simp
  moreover have "bij_betw h (B - A) (A - B)"
    using ** by (auto simp: bij_betw_def h_def inj_on_def)
  moreover have "(V - (A - B)) \<inter> (A - B) = {}" by blast
  ultimately have "bij_betw h ((V - (B - A)) \<union> (B - A)) ((V - (A - B)) \<union> (A - B))"
    by (rule bij_betw_combine)
  moreover have "(V - (B - A)) \<union> (B - A) = V"
    and "(V - (A - B)) \<union> (A - B) = V"
    using \<open>A \<subseteq> V\<close> and \<open>B \<subseteq> V\<close> by auto
  ultimately have "bij_betw h V V" by simp
  moreover have "\<forall>x\<in>A. h x = f x" by (auto simp: h_def)
  moreover have "finite {x. h x \<noteq> x}"
  proof -
    have "finite (A \<union> (B - A))" using \<open>finite A\<close> and \<open>finite B\<close> by auto
    moreover have "{x. h x \<noteq> x} \<subseteq> (A \<union> (B - A))" by (auto simp: h_def)
    ultimately show ?thesis by (metis finite_subset)
  qed
  moreover have "\<forall>x\<in>UNIV - (A \<union> B). h x = x" by (simp add: h_def)
  ultimately show ?thesis by blast
qed

lemma bij_betw_to_bij: assumes "bij_betw f A B" 
  and "finite A" 
  shows "\<exists> r. bij r \<and> (\<forall> x \<in> A. f x = r x) \<and> (\<forall> x. x \<notin> A \<union> B \<longrightarrow> r x = x)" 
proof -
  define S where "S = A \<union> B" 
  have "A \<subseteq> S" "B \<subseteq> S" by (auto simp: S_def)
  from bij_betw_extend[OF assms(1) this assms(2), folded S_def]
  obtain g where g: "(\<forall>x\<in>UNIV - S. g x = x)" "(\<forall>x\<in>A. g x = f x)" "bij_betw g S S" 
    by blast
  show ?thesis 
  proof (rule exI[of _ g], intro conjI)
    show "\<forall>x. x \<notin> A \<union> B \<longrightarrow> g x = x" using g S_def by auto
    show "\<forall>x\<in>A. f x = g x" using g by auto
    have "bij_betw g (UNIV - S) (UNIV - S)" using g(1)
      unfolding bij_betw_def by (auto simp: inj_on_def)
    from bij_betw_combine[OF this g(3)]
    show "bij g" by auto
  qed
qed



subsection \<open>Merging Functions\<close>
(* Copied and canonized from IsaFoR's Term theory and Polynomial Factorization in the AFP. *)
definition fun_merge :: "('a \<Rightarrow> 'b)list \<Rightarrow> 'a set list \<Rightarrow> 'a \<Rightarrow> 'b"
  where
    "fun_merge fs as a = (fs ! (LEAST i. i < length as \<and> a \<in> as ! i)) a"

lemma fun_merge_eq_nth:
  assumes i: "i < length as"
    and a: "a \<in> as ! i"
    and ident: "\<And> i j a. i < length as \<Longrightarrow> j < length as \<Longrightarrow> a \<in> as ! i \<Longrightarrow> a \<in> as ! j \<Longrightarrow> (fs ! i) a = (fs ! j) a"
  shows "fun_merge fs as a = (fs ! i) a"
proof -
  let ?p = "\<lambda> i. i < length as \<and> a \<in> as ! i"
  let ?l = "LEAST i. ?p i"
  have p: "?p ?l"
    by (rule LeastI, insert i a, auto)
  show ?thesis unfolding fun_merge_def
    by (rule ident[OF _ i _ a], insert p, auto)
qed

lemma fun_merge_part:
  assumes "\<forall>i<length as.\<forall>j<length as. i \<noteq> j \<longrightarrow> as ! i \<inter> as ! j = {}"
    and "i < length as"
    and "a \<in> as ! i"
  shows "fun_merge fs as a = (fs ! i) a"
proof(rule fun_merge_eq_nth [OF assms(2, 3)])
  fix i j a
  assume "i < length as" and "j < length as" and "a \<in> as ! i" and "a \<in> as ! j"
  then have "i = j" using assms by (cases "i = j") auto
  then show "(fs ! i) a = (fs ! j) a" by simp
qed

lemma fun_merge:
  assumes part: "\<forall>i<length Xs.\<forall>j<length Xs. i \<noteq> j \<longrightarrow> Xs ! i \<inter> Xs ! j = {}"
  shows "\<exists>\<sigma>. \<forall>i<length Xs. \<forall>x\<in> Xs ! i. \<sigma> x = \<tau> i x"
proof -
  let ?\<tau> = "map \<tau> [0 ..< length Xs]"
  let ?\<sigma> = "fun_merge ?\<tau> Xs"
  show ?thesis
    by (rule exI[of _ ?\<sigma>], intro allI impI ballI,
      insert fun_merge_part[OF part, of _ _ ?\<tau>], auto)
qed


lemma dependent_nat_choice_start:
  assumes 1: "P 0 x0"
    and 2: "\<And>x n. P n x \<Longrightarrow> \<exists>y. P (Suc n) y \<and> Q n x y"
  shows "\<exists>f. f 0 = x0 \<and> (\<forall>n. P n (f n) \<and> Q n (f n) (f (Suc n)))"
proof (intro exI allI conjI)
  fix n
  define f where "f = rec_nat x0 (\<lambda>n x. SOME y. P (Suc n) y \<and> Q n x y)"
  then have "P 0 (f 0)" "\<And>n. P n (f n) \<Longrightarrow> P (Suc n) (f (Suc n)) \<and> Q n (f n) (f (Suc n))"
    using 1 someI_ex[OF 2] by simp_all
  then show "P n (f n)" "Q n (f n) (f (Suc n))"
    by (induct n) auto
qed auto

lemma dependent_nat_choice2_start:
  assumes 1: "P 0 x0 y0"
    and 2: "\<And>x y n. P n x y \<Longrightarrow> \<exists>x' y'. P (Suc n) x' y' \<and> Q n x y x' y'"
  shows "\<exists> x y. x 0 = x0 \<and> y 0 = y0 \<and> (\<forall>n. P n (x n) (y n) \<and> Q n (x n) (y n) (x (Suc n)) (y (Suc n)))"
proof -
  have "\<exists>f. f 0 = (x0, y0) \<and>
      (\<forall>n. P n (fst (f n)) (snd (f n)) \<and>
           Q n (fst (f n)) (snd (f n)) (fst (f (Suc n))) (snd (f (Suc n))))" (is "\<exists> f. ?Prop f")
    by (rule dependent_nat_choice_start[of "\<lambda> i xy. P i (fst xy) (snd xy)" "(x0,y0)" 
      "\<lambda> i xy xy'. Q i (fst xy) (snd xy) (fst xy') (snd xy')"], insert 1 2, auto)
  then obtain f where f: "?Prop f" by blast
  show ?thesis by (rule exI[of _ "\<lambda> i. fst (f i)"], rule exI[of _ "\<lambda> i. snd (f i)"], insert f, auto)
qed


end
