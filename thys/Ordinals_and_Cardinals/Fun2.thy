header {* More on injections, bijections and inverses   *}

(* author: Andrei Popescu *)

theory Fun2 imports "~~/src/HOL/Library/Infinite_Set"
begin


text {* This section proves more facts (additional to those in @{text "Fun.thy"},
@{text "Hilbert_Choice.thy"} @{text "Finite_Set.thy"} and @{text "Infinite_Set.thy"}),
mainly concerning injections, bijections, inverses and (numeric) cardinals of
finite sets. *}


subsection {* Purely functional properties  *}


(*2*)lemma bij_betw_empty1:
assumes "bij_betw f {} A"
shows "A = {}"
using assms unfolding bij_betw_def by blast


(*2*)lemma bij_betw_empty2:
assumes "bij_betw f A {}"
shows "A = {}"
using assms unfolding bij_betw_def by blast


(*2*)lemma inj_on_imp_bij_betw:
"inj_on f A \<Longrightarrow> bij_betw f A (f ` A)"
unfolding bij_betw_def inj_on_def by blast


(*3*)lemma inj_on_cong[fundef_cong]:
"(\<And> a. a : A \<Longrightarrow> f a = g a) \<Longrightarrow> inj_on f A = inj_on g A"
unfolding inj_on_def by auto


(*1*)lemma inj_on_strict_subset:
"\<lbrakk>inj_on f B; A < B\<rbrakk> \<Longrightarrow> f`A < f`B"
unfolding inj_on_def unfolding image_def by blast


(*3*)lemma bij_betw_cong[fundef_cong]:
"(\<And> a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> bij_betw f A A' = bij_betw g A A'"
unfolding bij_betw_def inj_on_def by force


(*3*)lemma bij_betw_id: "bij_betw id A A"
unfolding bij_betw_def id_def by auto


(*2*)lemma bij_betw_id_iff:
"(A = B) = (bij_betw id A B)"
by(auto simp add: bij_betw_def)


(*2*)lemma bij_betw_byWitness:
assumes LEFT: "\<forall>a \<in> A. f'(f a) = a" and
        RIGHT: "\<forall>a' \<in> A'. f(f' a') = a'" and
        IM1: "f ` A \<le> A'" and IM2: "f' ` A' \<le> A"
shows "bij_betw f A A'"
using assms
proof(unfold bij_betw_def inj_on_def, auto)
  fix a b assume *: "a \<in> A" "b \<in> A" and **: "f a = f b"
  have "a = f'(f a) \<and> b = f'(f b)" using * LEFT by auto
  with ** show "a = b" by simp
next
  fix a' assume *: "a' \<in> A'"
  hence "f' a' \<in> A" using IM2 by auto
  moreover
  have "a' = f(f' a')" using * RIGHT by auto
  ultimately show "a' \<in> f ` A" by blast
qed


(*2*)lemma Int_inj_on: "\<lbrakk>inj_on f A; inj_on f B\<rbrakk> \<Longrightarrow> inj_on f (A Int B)"
unfolding inj_on_def by blast


(*2*)lemma INTER_inj_on:
"\<lbrakk>I \<noteq> {}; \<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)\<rbrakk> \<Longrightarrow> inj_on f (\<Inter> i \<in> I. A i)"
unfolding inj_on_def by blast


(*2*)lemma Inter_inj_on:
"\<lbrakk>S \<noteq> {}; \<And> A. A \<in> S \<Longrightarrow> inj_on f A\<rbrakk> \<Longrightarrow> inj_on f (Inter S)"
unfolding inj_on_def by blast


(*2*)lemma UNION_inj_on:
assumes CH: "\<And> i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> A i \<le> A j \<or> A j \<le> A i" and
       INJ: "\<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)"
shows "inj_on f (\<Union> i \<in> I. A i)"
proof(unfold inj_on_def UNION_def, auto)
  fix i j x y
  assume *: "i \<in> I" "j \<in> I" and **: "x \<in> A i" "y \<in> A j"
         and ***: "f x = f y"
  show "x = y"
  proof-
    {assume "A i \<le> A j"
     with ** have "x \<in> A j" by auto
     with INJ * ** *** have ?thesis
     by(auto simp add: inj_on_def)
    }
    moreover
    {assume "A j \<le> A i"
     with ** have "y \<in> A i" by auto
     with INJ * ** *** have ?thesis
     by(auto simp add: inj_on_def)
    }
    ultimately show ?thesis using  CH * by blast
  qed
qed


(*3*)lemma bij_betw_comp:
"\<lbrakk>bij_betw f A A'; bij_betw f' A' A''\<rbrakk> \<Longrightarrow> bij_betw (f' o f) A A''"
using comp_inj_on[of f A f']
by(auto simp add: bij_betw_def comp_def)


(*2*)lemma UNION_bij_betw:
assumes CH: "\<And> i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> A i \<le> A j \<or> A j \<le> A i" and
       BIJ: "\<And> i. i \<in> I \<Longrightarrow> bij_betw f (A i) (A' i)"
shows "bij_betw f (\<Union> i \<in> I. A i) (\<Union> i \<in> I. A' i)"
proof(unfold bij_betw_def, auto simp add: image_def)
  have "\<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)"
  using BIJ bij_betw_def[of f] by auto
  thus "inj_on f (\<Union> i \<in> I. A i)"
  using CH UNION_inj_on[of I A f] by auto
next
  fix i x
  assume *: "i \<in> I" "x \<in> A i"
  hence "f x \<in> A' i" using BIJ bij_betw_def[of f] by auto
  thus "\<exists>j \<in> I. f x \<in> A' j" using * by blast
next
  fix i x'
  assume *: "i \<in> I" "x' \<in> A' i"
  hence "\<exists>x \<in> A i. x' = f x" using BIJ bij_betw_def[of f] by blast
  thus "\<exists>j \<in> I. \<exists>x \<in> A j. x' = f x"
  using * by blast
qed


(*3*)lemma Disj_Un_bij_betw:
assumes DISJ: "A Int B = {}" and DISJ': "A' Int B' = {}" and
        B1: "bij_betw f A A'" and B2: "bij_betw f B B'"
shows "bij_betw f (A \<union> B) (A' \<union> B')"
proof-
  have 1: "inj_on f A \<and> inj_on f B"
  using B1 B2 by (auto simp add: bij_betw_def)
  have 2: "f`A = A' \<and> f`B = B'"
  using B1 B2 by (auto simp add: bij_betw_def)
  hence "f`(A - B) Int f`(B - A) = {}"
  using DISJ DISJ' by blast
  hence "inj_on f (A \<union> B)"
  using 1 by (auto simp add: inj_on_Un)
  (*  *)
  moreover
  have "f`(A \<union> B) = A' \<union> B'"
  using 2 by auto
  ultimately show ?thesis
  unfolding bij_betw_def by auto
qed


(*3*)corollary notIn_Un_bij_betw:
assumes NIN: "b \<notin> A" and NIN': "f b \<notin> A'" and
       BIJ: "bij_betw f A A'"
shows "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
proof-
  have "bij_betw f {b} {f b}"
  unfolding bij_betw_def inj_on_def by auto
  with assms show ?thesis
  using Disj_Un_bij_betw[of A "{b}" A' "{f b}" f] by blast
qed


(*1*)lemma bij_betw_subset:
assumes BIJ: "bij_betw f A A'" and
        SUB: "B \<le> A" and IM: "f ` B = B'"
shows "bij_betw f B B'"
using assms
by(unfold bij_betw_def inj_on_def, auto simp add: inj_on_def)


(*1*)lemma notIn_Un_bij_betw2:
assumes NIN: "b \<notin> A" and NIN': "b' \<notin> A'" and
        BIJ: "bij_betw f A A'"
shows "bij_betw f (A \<union> {b}) (A' \<union> {b'}) = (f b = b')"
proof
  assume "f b = b'"
  thus "bij_betw f (A \<union> {b}) (A' \<union> {b'})"
  using assms notIn_Un_bij_betw[of b A f A'] by auto
next
  assume *: "bij_betw f (A \<union> {b}) (A' \<union> {b'})"
  hence "f b \<in> A' \<union> {b'}"
  unfolding bij_betw_def by auto
  moreover
  {assume "f b \<in> A'"
   then obtain b1 where 1: "b1 \<in> A" and 2: "f b1 = f b" using BIJ
   by (auto simp add: bij_betw_def)
   hence "b = b1" using *
   by (auto simp add: bij_betw_def inj_on_def)
   with 1 NIN have False by auto
  }
  ultimately show "f b = b'" by blast
qed


(*1*)lemma notIn_Un_bij_betw3:
assumes NIN: "b \<notin> A" and NIN': "f b \<notin> A'"
shows "bij_betw f A A' = bij_betw f (A \<union> {b}) (A' \<union> {f b})"
proof
  assume "bij_betw f A A'"
  thus "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
  using assms notIn_Un_bij_betw[of b A f A'] by auto
next
  assume *: "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
  have "f ` A = A'"
  proof(auto)
    fix a assume **: "a \<in> A"
    hence "f a \<in> A' \<union> {f b}" using *
    by (auto simp add: bij_betw_def)
    moreover
    {assume "f a = f b"
     hence "a = b" using * **
     by(auto simp add: bij_betw_def inj_on_def)
     with NIN ** have False by auto
    }
    ultimately show "f a \<in> A'" by blast
  next
    fix a' assume **: "a' \<in> A'"
    hence "a' \<in> f`(A \<union> {b})"
    using * by (auto simp add: bij_betw_def)
    then obtain a where 1: "a \<in> A \<union> {b} \<and> f a = a'" by blast
    moreover
    {assume "a = b" with 1 ** NIN' have False by blast
    }
    ultimately have "a \<in> A" by blast
    with 1 show "a' \<in> f ` A" by auto
  qed
  thus "bij_betw f A A'" using * bij_betw_subset[of f "A \<union> {b}" _ A] by auto
qed


(*1*)lemma bij_betw_diff_singl:
assumes BIJ: "bij_betw f A A'" and IN: "a \<in> A"
shows "bij_betw f (A - {a}) (A' - {f a})"
proof-
  let ?B = "A - {a}"   let ?B' = "A' - {f a}"
  have "f a \<in> A'" using IN BIJ unfolding bij_betw_def by auto
  hence "a \<notin> ?B \<and> f a \<notin> ?B' \<and> A = ?B \<union> {a} \<and> A' = ?B' \<union> {f a}"
  using IN by blast
  thus ?thesis using notIn_Un_bij_betw3[of a ?B f ?B'] BIJ by auto
qed


(*2*)lemma comp_inj_on2:
"inj_on f A \<Longrightarrow> inj_on f' (f ` A) = inj_on (f' o f) A"
by(auto simp add: comp_inj_on inj_on_def)


(*2*)lemma comp_inj_on3:
"inj_on (f' o f) A \<Longrightarrow> inj_on f A"
by(auto simp add: comp_inj_on inj_on_def)


(*2*)lemma comp_bij_betw2:
"bij_betw f A A' \<Longrightarrow> bij_betw f' A' A'' = bij_betw (f' o f) A A''"
by(auto simp add: bij_betw_def inj_on_def)


(*2*)lemma comp_bij_betw3:
assumes BIJ: "bij_betw f' A' A''" and IM: "f ` A \<le> A'"
shows "bij_betw f A A' = bij_betw (f' o f) A A''"
using assms
proof(auto simp add: bij_betw_comp)
  assume *: "bij_betw (f' \<circ> f) A A''"
  thus "bij_betw f A A'"
  using IM
  proof(auto simp add: bij_betw_def)
    assume "inj_on (f' \<circ> f) A"
    thus "inj_on f A" using comp_inj_on3 by blast
  next
    fix a' assume **: "a' \<in> A'"
    hence "f' a' \<in> A''" using BIJ unfolding bij_betw_def by auto
    then obtain a where 1: "a \<in> A \<and> f'(f a) = f' a'" using *
    unfolding bij_betw_def by force
    hence "f a \<in> A'" using IM by auto
    hence "f a = a'" using BIJ ** 1 unfolding bij_betw_def inj_on_def by auto
    thus "a' \<in> f ` A" using 1 by auto
  qed
qed


(*1*)lemma bij_betw_ball:
assumes BIJ: "bij_betw f A B"
shows "(\<forall>b \<in> B. phi b) = (\<forall>a \<in> A. phi(f a))"
using assms unfolding bij_betw_def inj_on_def by blast


subsection {* Properties involving finite and infinite sets *}


(*3*)lemma inj_on_finite:
assumes INJ: "inj_on f A" and SUB: "f ` A \<le> B" and
        FIN: "finite B"
shows "finite A"
proof-
  from SUB FIN have "finite (f ` A)" by (rule finite_subset)
  from this INJ show "finite A" by (rule finite_imageD)
qed


(*3*)lemma bij_betw_finite:
assumes "bij_betw f A B"
shows "finite A = finite B"
using assms unfolding bij_betw_def
using inj_on_finite[of f A B] by auto


(*3*)lemma infinite_imp_bij_betw:
assumes INF: "infinite A"
shows "\<exists>h. bij_betw h A (A - {a})"
proof(cases "a \<in> A")
  assume Case1: "a \<notin> A"  hence "A - {a} = A" by blast
  thus ?thesis using bij_betw_id[of A] by auto
next
  assume Case2: "a \<in> A"
  have "infinite (A - {a})" using INF infinite_remove by auto
  with infinite_iff_countable_subset[of "A - {a}"] obtain f::"nat \<Rightarrow> 'a"
  where 1: "inj f" and 2: "f ` UNIV \<le> A - {a}" by blast
  obtain g where g_def: "g = (\<lambda> n. if n = 0 then a else f (Suc n))" by blast
  obtain A' where A'_def: "A' = g ` UNIV" by blast
  have temp: "\<forall>y. f y \<noteq> a" using 2 by blast
  have 3: "inj_on g UNIV \<and> g ` UNIV \<le> A \<and> a \<in> g ` UNIV"
  proof(auto simp add: Case2 g_def, unfold inj_on_def, intro ballI impI,
        case_tac "x = 0", auto simp add: 2)
    fix y  assume "a = (if y = 0 then a else f (Suc y))"
    thus "y = 0" using temp by (case_tac "y = 0", auto)
  next
    fix x y
    assume "f (Suc x) = (if y = 0 then a else f (Suc y))"
    thus "x = y" using 1 temp unfolding inj_on_def by (case_tac "y = 0", auto)
  next
    fix n show "f (Suc n) \<in> A" using 2 by blast
  qed
  hence 4: "bij_betw g UNIV A' \<and> a \<in> A' \<and> A' \<le> A"
  using inj_on_imp_bij_betw[of g] unfolding A'_def by auto
  hence 5: "bij_betw (inv g) A' UNIV"
  by (auto simp add: bij_betw_inv_into)
  (*  *)
  obtain n where "g n = a" using 3 by auto
  hence 6: "bij_betw g (UNIV - {n}) (A' - {a})"
  using 4 bij_betw_diff_singl[of g] by blast
  (*  *)
  obtain v where v_def: "v = (\<lambda> m. if m < n then m else Suc m)" by blast
  have 7: "bij_betw v UNIV (UNIV - {n})"
  proof(unfold bij_betw_def inj_on_def, intro conjI, clarify)
    fix m1 m2 assume "v m1 = v m2"
    thus "m1 = m2"
    by(case_tac "m1 < n", case_tac "m2 < n",
       auto simp add: inj_on_def v_def, case_tac "m2 < n", auto)
  next
    show "v ` UNIV = UNIV - {n}"
    proof(auto simp add: v_def)
      fix m assume *: "m \<noteq> n" and **: "m \<notin> Suc ` {m'. \<not> m' < n}"
      {assume "n \<le> m" with * have 71: "Suc n \<le> m" by auto
       then obtain m' where 72: "m = Suc m'" using Suc_le_D by auto
       with 71 have "n \<le> m'" by auto
       with 72 ** have False by auto
      }
      thus "m < n" by force
    qed
  qed
  (*  *)
  obtain h' where h'_def: "h' = g o v o (inv g)" by blast
  hence 8: "bij_betw h' A' (A' - {a})" using 5 7 6
  by (auto simp add: bij_betw_comp)
  (*  *)
  obtain h where h_def: "h = (\<lambda> b. if b \<in> A' then h' b else b)" by blast
  have "\<forall>b \<in> A'. h b = h' b" unfolding h_def by auto
  hence "bij_betw h  A' (A' - {a})" using 8 bij_betw_cong[of A' h] by auto
  moreover
  {have "\<forall>b \<in> A - A'. h b = b" unfolding h_def by auto
   hence "bij_betw h  (A - A') (A - A')"
   using bij_betw_cong[of "A - A'" h id] bij_betw_id[of "A - A'"] by auto
  }
  moreover
  have "(A' Int (A - A') = {} \<and> A' \<union> (A - A') = A) \<and>
        ((A' - {a}) Int (A - A') = {} \<and> (A' - {a}) \<union> (A - A') = A - {a})"
  using 4 by blast
  ultimately have "bij_betw h A (A - {a})"
  using Disj_Un_bij_betw[of A' "A - A'" "A' - {a}" "A - A'" h] by auto
  thus ?thesis by blast
qed


(*3*)lemma infinite_imp_bij_betw2:
assumes INF: "infinite A"
shows "\<exists>h. bij_betw h A (A \<union> {a})"
proof(cases "a \<in> A")
  assume Case1: "a \<in> A"  hence "A \<union> {a} = A" by blast
  thus ?thesis using bij_betw_id[of A] by auto
next
  let ?A' = "A \<union> {a}"
  assume Case2: "a \<notin> A" hence "A = ?A' - {a}" by blast
  moreover have "infinite ?A'" using INF by auto
  ultimately obtain f where "bij_betw f ?A' A"
  using infinite_imp_bij_betw[of ?A' a] by auto
  hence "bij_betw(inv_into ?A' f) A ?A'" using bij_betw_inv_into by blast
  thus ?thesis by auto
qed


(*3*)lemma bij_betw_imp_card:
assumes FIN: "finite A" and BIJ: "bij_betw f A B"
shows "card A = card B"
proof-
  have "finite A \<Longrightarrow> \<forall>B. bij_betw f A B \<longrightarrow> card A = card B"
  proof (erule finite.induct, auto)
    fix B assume "bij_betw f {} B"
    thus "card B = 0" using bij_betw_empty1 card_empty by blast
  next
    fix A a B'
    assume *: "finite A" and **: "bij_betw f (insert a A) B'" and
           IH: "\<forall>B. bij_betw f A B \<longrightarrow> card A = card B"
    show "card (insert a A) = card B'"
    proof(cases "a \<in> A")
      assume "a \<in> A" hence 1: "insert a A = A" by auto
      hence "bij_betw f A B'" using ** by auto
      thus ?thesis using IH * 1 by auto
    next
      assume ***: "a \<notin> A"
      hence 2: "card(insert a A) = card A + 1" using * by auto
      obtain b and B where b_def: "b = f a" and B_def: "B = B' - {b}" by blast
      have 3: "b \<in> B'" using ** unfolding bij_betw_def  b_def by auto
      have "(insert a A) - {a} = A" using *** by auto
      hence "bij_betw f A B" unfolding B_def b_def
      using ** bij_betw_diff_singl[of f "insert a A" B' a] by auto
      hence 5: "card A = card B" using * IH by auto
      have "B' = insert b B \<and> b \<notin> B" unfolding B_def using insert_Diff 3 by blast
      moreover have "finite B" unfolding B_def
      using bij_betw_finite[of f _ B'] finite_subset[of B B'] * ** by auto
      ultimately have "card B' = card B + 1" by auto
      (*  *)
      with 2 5 show ?thesis by auto
    qed
  qed
  thus ?thesis using assms by blast
qed


(*3*)lemma bij_betw_iff_card:
assumes FIN: "finite A" and FIN': "finite B"
shows BIJ: "(\<exists>f. bij_betw f A B) = (card A = card B)"
using assms
proof(auto simp add: bij_betw_imp_card)
  assume *: "card A = card B"
  obtain f where "bij_betw f A {0 ..< card A}"
  using FIN ex_bij_betw_finite_nat by blast
  moreover obtain g where "bij_betw g {0 ..< card B} B"
  using FIN' ex_bij_betw_nat_finite by blast
  ultimately have "bij_betw (g o f) A B"
  using * by (auto simp add: bij_betw_comp)
  thus "(\<exists>f. bij_betw f A B)" by blast
qed


(*3*)lemma inj_on_iff_card:
assumes FIN: "finite A" and FIN': "finite B"
shows "(\<exists>f. inj_on f A \<and> f ` A \<le> B) = (card A \<le> card B)"
using assms
proof(auto simp add: card_inj_on_le)
  assume *: "card A \<le> card B"
  obtain f where 1: "inj_on f A" and 2: "f ` A = {0 ..< card A}"
  using FIN ex_bij_betw_finite_nat unfolding bij_betw_def by force
  moreover obtain g where "inj_on g {0 ..< card B}" and 3: "g ` {0 ..< card B} = B"
  using FIN' ex_bij_betw_nat_finite unfolding bij_betw_def by force
  ultimately have "inj_on g (f ` A)" using subset_inj_on[of g _ "f ` A"] * by force
  hence "inj_on (g o f) A" using 1 comp_inj_on by blast
  moreover
  {have "{0 ..< card A} \<le> {0 ..< card B}" using * by force
   with 2 have "f ` A  \<le> {0 ..< card B}" by blast
   hence "(g o f) ` A \<le> B" unfolding comp_def using 3 by force
  }
  ultimately show "(\<exists>f. inj_on f A \<and> f ` A \<le> B)" by blast
qed


(*3*)lemma inj_on_image_Pow:
assumes "inj_on f A"
shows "inj_on (image f) (Pow A)"
unfolding Pow_def inj_on_def proof(clarsimp)
  fix X Y assume *: "X \<le> A" and **: "Y \<le> A" and
                 ***: "f ` X = f ` Y"
  show "X = Y"
  proof(auto)
    fix x assume ****: "x \<in> X"
    with *** obtain y where "y \<in> Y \<and> f x = f y" by blast
    with **** * ** assms show "x \<in> Y"
    unfolding inj_on_def by auto
  next
    fix y assume ****: "y \<in> Y"
    with *** obtain x where "x \<in> X \<and> f x = f y" by force
    with **** * ** assms show "y \<in> X"
    unfolding inj_on_def by auto
  qed
qed


(*2*)lemma image_Pow_mono:
assumes "f ` A \<le> B"
shows "(image f) ` (Pow A) \<le> Pow B"
using assms by blast


(*2*)lemma image_Pow_surjective:
assumes "f ` A = B"
shows "(image f) ` (Pow A) = Pow B"
using assms unfolding Pow_def proof(auto)
  fix Y assume *: "Y \<le> f ` A"
  obtain X where X_def: "X = {x \<in> A. f x \<in> Y}" by blast
  have "f ` X = Y \<and> X \<le> A" unfolding X_def using * by auto
  thus "Y \<in> (image f) ` {X. X \<le> A}" by blast
qed


(*2*)lemma bij_betw_image_Pow:
assumes "bij_betw f A B"
shows "bij_betw (image f) (Pow A) (Pow B)"
using assms unfolding bij_betw_def
by (auto simp add: inj_on_image_Pow image_Pow_surjective)


subsection {* Properties involving Hilbert choice *}


(*2*)lemma bij_betw_inv_into_left:
assumes BIJ: "bij_betw f A A'" and IN: "a \<in> A"
shows "(inv_into A f) (f a) = a"
proof(unfold inv_into_def)
  let ?phi = "(\<lambda> b. b \<in> A \<and> f b = f a)"
  have "?phi a" using IN by auto
  moreover
  have "\<And> b. ?phi b \<Longrightarrow> b = a"
  using assms by (auto simp add: bij_betw_def inj_on_def)
  ultimately
  show "(SOME a. ?phi a) = a"
  by (auto simp add: some_equality)
qed


(*2*)lemma bij_betw_inv_into_right:
assumes BIJ: "bij_betw f A A'" and IN: "a' \<in> A'"
shows "f(inv_into A f a') = a'"
proof-
  let ?f' = "(inv_into A f)"
  have 1: "bij_betw ?f' A' A"
  using BIJ by (auto simp add: bij_betw_inv_into)
  hence 2: "?f' a' \<in> A"
  using IN by (auto simp add: bij_betw_def)
  hence "?f'(f(?f' a')) = ?f' a'"
  using BIJ by (auto simp add: bij_betw_inv_into_left)
  moreover
  have "f(?f' a') \<in> A'"
  using BIJ 2 by (auto simp add: bij_betw_def)
  ultimately show "f(?f' a') = a'"
  using IN 1 by (auto simp add: bij_betw_def inj_on_def)
qed


(*1*)lemma bij_betw_inv_into_LEFT:
assumes BIJ: "bij_betw f A A'" and SUB: "B \<le> A"
shows "(inv_into A f)`(f ` B) = B"
using assms
proof(auto simp add: bij_betw_inv_into_left)
  let ?f' = "(inv_into A f)"
  fix a assume *: "a \<in> B"
  hence "a \<in> A" using SUB by auto
  hence "a = ?f' (f a)"
  using BIJ by (auto simp add: bij_betw_inv_into_left)
  thus "a \<in> ?f' ` (f ` B)" using * by blast
qed


(*1*)lemma bij_betw_inv_into_RIGHT:
assumes BIJ: "bij_betw f A A'" and SUB: "B' \<le> A'"
shows "f `((inv_into A f)`B') = B'"
using assms
proof(auto simp add: bij_betw_inv_into_right)
  let ?f' = "(inv_into A f)"
  fix a' assume *: "a' \<in> B'"
  hence "a' \<in> A'" using SUB by auto
  hence "a' = f (?f' a')"
  using BIJ by (auto simp add: bij_betw_inv_into_right)
  thus "a' \<in> f ` (?f' ` B')" using * by blast
qed


(*1*)lemma bij_betw_inv_into_LEFT_RIGHT:
assumes BIJ: "bij_betw f A A'" and SUB: "B \<le> A" and
        IM: "f ` B = B'"
shows "(inv_into A f) ` B' = B"
proof-
  have "(inv_into A f)`(f ` B) = B"
  using assms bij_betw_inv_into_LEFT[of f A A' B] by auto
  thus ?thesis using IM by auto
qed


(*1*)lemma bij_betw_inv_into_RIGHT_LEFT:
assumes BIJ: "bij_betw f A A'" and SUB: "B' \<le> A'" and
        IM: "(inv_into A f) ` B' = B"
shows "f ` B = B'"
proof-
  have "f`((inv_into A f)` B') = B'"
  using assms bij_betw_inv_into_RIGHT[of f A A' B'] by auto
  thus ?thesis using IM by auto
qed


(*1*)lemma bij_betw_inv_into_subset:
assumes BIJ: "bij_betw f A A'" and
        SUB: "B \<le> A" and IM: "f ` B = B'"
shows "bij_betw (inv_into A f) B' B"
proof-
  let ?f' = "(inv_into A f)"
  have "?f' ` B' = B " using assms
  by (auto simp add: bij_betw_inv_into_LEFT_RIGHT)
  moreover
  {have "bij_betw ?f' A' A"
   using BIJ by (auto simp add: bij_betw_inv_into)
   hence "inj_on ?f' A'" unfolding bij_betw_def by auto
   moreover have "B' \<le> A'"
   using SUB IM BIJ by (auto simp add: bij_betw_def)
   ultimately have "inj_on ?f' B'" using SUB
   by (auto simp add: subset_inj_on)
  }
  ultimately show ?thesis
  unfolding bij_betw_def by blast
qed


(*2*)lemma bij_betw_inv_into_twice:
assumes "bij_betw f A A'"
shows "\<forall>a \<in> A. inv_into A' (inv_into A f) a = f a"
proof
  let ?f' = "inv_into A f"   let ?f'' = "inv_into A' ?f'"
  have 1: "bij_betw ?f' A' A" using assms
  by (auto simp add: bij_betw_inv_into)
  fix a assume *: "a \<in> A"
  then obtain a' where 2: "a' \<in> A'" and 3: "?f' a' = a"
  using 1 unfolding bij_betw_def by force
  hence "?f'' a = a'"
  using * 1 3 by (auto simp add: bij_betw_inv_into_left)
  moreover have "f a = a'" using assms 2 3
  by (auto simp add: bij_betw_inv_into_right)
  ultimately show "?f'' a = f a" by simp
qed


(*3*)lemma inj_on_iff_surjective:
assumes "A \<noteq> {}"
shows "(\<exists>f. inj_on f A \<and> f ` A \<le> A') = (\<exists>g. g ` A' = A)"
proof(safe)
  fix f assume INJ: "inj_on f A" and INCL: "f ` A \<le> A'"
  let ?phi = "\<lambda>a' a. a \<in> A \<and> f a = a'"  let ?csi = "\<lambda>a. a \<in> A"
  let ?g = "\<lambda>a'. if a' \<in> f ` A then (SOME a. ?phi a' a) else (SOME a. ?csi a)"
  have "?g ` A' = A"
  proof
    show "?g ` A' \<le> A"
    proof(clarify)
      fix a' assume *: "a' \<in> A'"
      show "?g a' \<in> A"
      proof(cases "a' \<in> f ` A")
        assume Case1: "a' \<in> f ` A"
        then obtain a where "?phi a' a" by blast
        hence "?phi a' (SOME a. ?phi a' a)" using someI[of "?phi a'" a] by blast
        with Case1 show ?thesis by auto
      next
        assume Case2: "a' \<notin> f ` A"
        hence "?csi (SOME a. ?csi a)" using assms someI_ex[of ?csi] by blast
        with Case2 show ?thesis by auto
      qed
    qed
  next
    show "A \<le> ?g ` A'"
    proof-
      {fix a assume *: "a \<in> A"
       let ?b = "SOME aa. ?phi (f a) aa"
       have "?phi (f a) a" using * by auto
       hence 1: "?phi (f a) ?b" using someI[of "?phi(f a)" a] by blast
       hence "?g(f a) = ?b" using * by auto
       moreover have "a = ?b" using 1 INJ * by (auto simp add: inj_on_def)
       ultimately have "?g(f a) = a" by simp
       with INCL * have "?g(f a) = a \<and> f a \<in> A'" by auto
      }
      thus ?thesis by force
    qed
  qed
  thus "\<exists>g. g ` A' = A" by blast
next
  fix g  let ?f = "inv_into A' g"
  have "inj_on ?f (g ` A')"
  by (auto simp add: inj_on_inv_into)
  moreover
  {fix a' assume *: "a' \<in> A'"
   let ?phi = "\<lambda> b'. b' \<in> A' \<and> g b' = g a'"
   have "?phi a'" using * by auto
   hence "?phi(SOME b'. ?phi b')" using someI[of ?phi] by blast
   hence "?f(g a') \<in> A'" unfolding inv_into_def by auto
  }
  ultimately show "\<exists>f. inj_on f (g ` A') \<and> f ` g ` A' \<subseteq> A'" by auto
qed


(*2*)lemma UNION_inj_on_Sigma:
"\<exists>f. (inj_on f (\<Union> i \<in> I. A i) \<and> f ` (\<Union> i \<in> I. A i) \<le> (SIGMA i : I. A i))"
proof
  let ?phi = "\<lambda> a i. i \<in> I \<and> a \<in> A i"
  let ?sm = "\<lambda> a. SOME i. ?phi a i"
  let ?f = "\<lambda>a. (?sm a, a)"
  have "inj_on ?f (\<Union> i \<in> I. A i)" unfolding inj_on_def by auto
  moreover
  {{fix i a assume "i \<in> I" and "a \<in> A i"
    hence "?sm a \<in> I \<and> a \<in> A(?sm a)" using someI[of "?phi a" i] by auto
   }
  hence "?f ` (\<Union> i \<in> I. A i) \<le> (SIGMA i : I. A i)" by auto
  }
  ultimately
  show "inj_on ?f (\<Union> i \<in> I. A i) \<and> ?f ` (\<Union> i \<in> I. A i) \<le> (SIGMA i : I. A i)"
  by auto
qed


subsection {* Cantor's Paradox *}


(*3*)lemma Cantors_paradox:
"\<not>(\<exists>f. f ` A = Pow A)"
proof(clarify)
  fix f assume "f ` A = Pow A" hence *: "Pow A \<le> f ` A" by blast
  let ?X = "{a \<in> A. a \<notin> f a}"
  have "?X \<in> Pow A" unfolding Pow_def by auto
  with * obtain x where "x \<in> A \<and> f x = ?X" by blast
  thus False by best
qed


subsection {* The Cantor-Bernstein Theorem *}


lemma Cantor_Bernstein_aux:
shows "\<exists>A' h. A' \<le> A \<and>
                (\<forall>a \<in> A'. a \<notin> g`(B - f ` A')) \<and>
                (\<forall>a \<in> A'. h a = f a) \<and>
                (\<forall>a \<in> A - A'. h a \<in> B - (f ` A') \<and> a = g(h a))"
proof-
  obtain H where H_def: "H = (\<lambda> A'. A - (g`(B - (f ` A'))))" by blast
  have 0: "mono H" unfolding mono_def H_def by blast
  then obtain A' where 1: "H A' = A'" using lfp_unfold by blast
  hence 2: "A' = A - (g`(B - (f ` A')))" unfolding H_def by simp
  hence 3: "A' \<le> A" by blast
  have 4: "\<forall>a \<in> A'.  a \<notin> g`(B - f ` A')"
  using 2 by blast
  have 5: "\<forall>a \<in> A - A'. \<exists>b \<in> B - (f ` A'). a = g b"
  using 2 by blast
  (*  *)
  obtain h where h_def:
  "h = (\<lambda> a. if a \<in> A' then f a else (SOME b. b \<in> B - (f ` A') \<and> a = g b))" by blast
  hence "\<forall>a \<in> A'. h a = f a" by auto
  moreover
  have "\<forall>a \<in> A - A'. h a \<in> B - (f ` A') \<and> a = g(h a)"
  proof
    fix a assume *: "a \<in> A - A'"
    let ?phi = "\<lambda> b. b \<in> B - (f ` A') \<and> a = g b"
    have "h a = (SOME b. ?phi b)" using h_def * by auto
    moreover have "\<exists>b. ?phi b" using 5 *  by auto
    ultimately show  "?phi (h a)" using someI_ex[of ?phi] by auto
  qed
  ultimately show ?thesis using 3 4 by blast
qed


(*3*)theorem Cantor_Bernstein:
assumes INJ1: "inj_on f A" and SUB1: "f ` A \<le> B" and
        INJ2: "inj_on g B" and SUB2: "g ` B \<le> A"
shows "\<exists>h. bij_betw h A B"
proof-
  obtain A' and h where 0: "A' \<le> A" and
  1: "\<forall>a \<in> A'. a \<notin> g`(B - f ` A')" and
  2: "\<forall>a \<in> A'. h a = f a" and
  3: "\<forall>a \<in> A - A'. h a \<in> B - (f ` A') \<and> a = g(h a)"
  using Cantor_Bernstein_aux[of A g B f] by blast
  have "inj_on h A"
  proof(unfold inj_on_def, auto)
    fix a1 a2
    assume 4: "a1 \<in> A" and 5: "a2 \<in> A" and 6: "h a1 = h a2"
    show "a1 = a2"
    proof(cases "a1 \<in> A'")
      assume Case1: "a1 \<in> A'"
      show ?thesis
      proof(cases "a2 \<in> A'")
        assume Case11: "a2 \<in> A'"
        hence "f a1 = f a2" using Case1 2 6 by auto
        thus ?thesis using INJ1 Case1 Case11 0
        unfolding inj_on_def by blast
      next
        assume Case12: "a2 \<notin> A'"
        hence False using 3 5 2 6 Case1 by force
        thus ?thesis by simp
      qed
    next
    assume Case2: "a1 \<notin> A'"
      show ?thesis
      proof(cases "a2 \<in> A'")
        assume Case21: "a2 \<in> A'"
        hence False using 3 4 2 6 Case2 by auto
        thus ?thesis by simp
      next
        assume Case22: "a2 \<notin> A'"
        hence "a1 = g(h a1) \<and> a2 = g(h a2)" using Case2 4 5 3 by auto
        thus ?thesis using 6 by simp
      qed
    qed
  qed
  (*  *)
  moreover
  have "h ` A = B"
  proof(auto)
    fix a assume "a \<in> A"
    thus "h a \<in> B" using SUB1 2 3 by (case_tac "a \<in> A'", auto)
  next
    fix b assume *: "b \<in> B"
    show "b \<in> h ` A"
    proof(cases "b \<in> f ` A'")
      assume Case1: "b \<in> f ` A'"
      then obtain a where "a \<in> A' \<and> b = f a" by blast
      thus ?thesis using 2 0 by force
    next
      assume Case2: "b \<notin> f ` A'"
      hence "g b \<notin> A'" using 1 * by auto
      hence 4: "g b \<in> A - A'" using * SUB2 by auto
      hence "h(g b) \<in> B \<and> g(h(g b)) = g b"
      using 3 by auto
      hence "h(g b) = b" using * INJ2 unfolding inj_on_def by auto
      thus ?thesis using 4 by force
    qed
  qed
  (*  *)
  ultimately show ?thesis unfolding bij_betw_def by auto
qed


subsection {* Other facts  *}


(*3*)lemma Pow_not_empty: "Pow A \<noteq> {}"
using Pow_top by blast


(*3*)lemma atLeastLessThan_injective:
assumes "{0 ..< m::nat} = {0 ..< n}"
shows "m = n"
proof-
  {assume "m < n"
   hence "m \<in> {0 ..< n}" by auto
   hence "{0 ..< m} < {0 ..< n}" by auto
   hence False using assms by blast
  }
  moreover
  {assume "n < m"
   hence "n \<in> {0 ..< m}" by auto
   hence "{0 ..< n} < {0 ..< m}" by auto
   hence False using assms by blast
  }
  ultimately show ?thesis by force
qed


(*2*)lemma atLeastLessThan_injective2:
"bij_betw f {0 ..< m::nat} {0 ..< n} \<Longrightarrow> m = n"
using finite_atLeastLessThan[of m] finite_atLeastLessThan[of n]
      card_atLeastLessThan[of m] card_atLeastLessThan[of n]
      bij_betw_iff_card[of "{0 ..< m}" "{0 ..< n}"] by auto


(*2*)lemma atLeastLessThan_less_eq:
"({0..<m} \<le> {0..<n}) = ((m::nat) \<le> n)"
unfolding ivl_subset by arith


(*2*)lemma atLeastLessThan_less_eq2:
assumes "inj_on f {0..<(m::nat)} \<and> f ` {0..<m} \<le> {0..<n}"
shows "m \<le> n"
using assms
using finite_atLeastLessThan[of m] finite_atLeastLessThan[of n]
      card_atLeastLessThan[of m] card_atLeastLessThan[of n]
      card_inj_on_le[of f "{0 ..< m}" "{0 ..< n}"] by auto


(*2*)lemma atLeastLessThan_less_eq3:
"(\<exists>f. inj_on f {0..<(m::nat)} \<and> f ` {0..<m} \<le> {0..<n}) = (m \<le> n)"
using atLeastLessThan_less_eq2
proof(auto)
  assume "m \<le> n"
  hence "inj_on id {0..<m} \<and> id ` {0..<m} \<subseteq> {0..<n}" unfolding inj_on_def by force
  thus "\<exists>f. inj_on f {0..<m} \<and> f ` {0..<m} \<subseteq> {0..<n}" by blast
qed


(*3*)lemma atLeastLessThan_less:
"({0..<m} < {0..<n}) = ((m::nat) < n)"
proof-
  have "({0..<m} < {0..<n}) = ({0..<m} \<le> {0..<n} \<and> {0..<m} ~= {0..<n})"
  using subset_iff_psubset_eq by blast
  also have "\<dots> = (m \<le> n \<and> m ~= n)"
  using atLeastLessThan_less_eq atLeastLessThan_injective by blast
  also have "\<dots> = (m < n)" by auto
  finally show ?thesis .
qed



end


