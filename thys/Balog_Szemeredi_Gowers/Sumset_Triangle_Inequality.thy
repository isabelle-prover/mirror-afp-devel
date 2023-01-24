section\<open>A triangle inequality for sumsets\<close>

(*
  Session: Balog_Szemeredi_Gowers
  Title:   Sumset_Triangle_Inequality.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds 
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Sumset_Triangle_Inequality
  imports 
    Pluennecke_Ruzsa_Inequality.Pluennecke_Ruzsa_Inequality
begin

context additive_abelian_group 

begin

text\<open>We show a useful triangle inequality for sumsets that does *not* follow from the Ruzsa triangle
inequality. The proof follows the exposition in Zhao's book \cite{Zhaobook}. \<close>

text\<open>The following auxiliary lemma corresponds to Lemma 7.3.4 in Zhao's book \cite{Zhaobook}.\<close>

lemma triangle_ineq_sumsets_aux:
  fixes X B Y :: "'a set"
  assumes hX: "finite X" and hB: "finite B" and hXG: "X \<subseteq> G" and hBG: "B \<subseteq> G" and 
    hXne: "X \<noteq> {}" and hYX: "\<And> Y. Y \<subseteq> X \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> card (sumset Y B) / card Y \<ge> 
    card (sumset X B) / card X" and hC: "finite C" and hCne: "C \<noteq> {}" and hCG: "C \<subseteq> G"
  shows "card (sumset X (sumset C B)) / card (sumset X C) \<le> card (sumset X B) / card X"
  using hC hCne hCG proof (induct)
  case empty
  then show ?case by blast
next
  case hcase: (insert c C)
  have hc : "c \<in> G" using hcase by auto
  show "card (sumset X B) / card X \<ge>                    
    card (sumset X (sumset (insert c C) B)) / card (sumset X (insert c C))"
  proof(cases "C = {}")
    case True
    then have "card (sumset X (insert c C)) = card X" using hc hXG hX
      by (simp add: card_sumset_singleton_eq le_iff_inf)
    moreover have "card (sumset X (sumset (insert c C) B)) \<le> card (sumset X B)" using hX hB hBG hXG 
      hc by (metis True card_sumset_le finite_sumset sumset_assoc sumset_commute)
    ultimately show ?thesis by (simp add: divide_right_mono) 
  next
    case hCne: False
    have hCG : "C \<subseteq> G" using hcase by auto
    have hstep: "card (sumset X (sumset {c} B) - sumset X (sumset C B)) \<le> 
      card (sumset X B) * card (sumset X {c} - sumset X C) / card X"
    proof-
      let ?Y = "{x \<in> X. sumset {x} (sumset {c} B) \<subseteq> sumset X (sumset C B)}"
      have hYX : "?Y \<subseteq> X" and hY: "finite ?Y" using finite_subset hX by auto
      have hsub1: "sumset X (sumset {c} B) - sumset X (sumset C B) \<subseteq> 
        sumset (sumset X {c} - sumset X C) B"
        by (metis Diff_subset_conv Un_Diff_cancel sumset_assoc sumset_subset_Un1 sup.cobounded2)
      have hcard1 : "card (sumset X B) = card (sumset X (sumset {c} B))"
        by (metis card_sumset_singleton_eq finite_sumset hB hX hc sumset_Int_carrier sumset_assoc 
            sumset_commute)
      have hcard2 : "card (sumset ?Y B) = card (sumset (sumset ?Y {c}) B)"
        using card_sumset_singleton_eq finite_sumset hB hY hc sumset_Int_carrier sumset_assoc 
        sumset_commute by (smt (verit, ccfv_threshold))
      have "sumset (sumset ?Y {c}) B \<subseteq> sumset X (sumset C B)"
      proof
        fix d assume "d \<in> sumset (sumset ?Y {c}) B"     
        then obtain a b where ha: "a \<in> ?Y" and "b \<in> B" and hd: "d = a \<oplus> c \<oplus> b"
          by (smt (verit) empty_iff insert_iff sumset.cases)
        then have "a \<oplus> c \<oplus> b \<in> sumset {a} (sumset {c} B)"
          by (smt (verit) associative composition_closed hBG hXG hc insertCI mem_Collect_eq subsetD
            sumset.sumsetI)
        then show "d \<in> sumset X (sumset C B)" using ha hd by blast
      qed
      then have hdisj : "disjnt ((sumset X (sumset {c} B)) - (sumset X (sumset C B)))
        (sumset (sumset ?Y {c}) B)"
        by (auto simp add : disjnt_iff)
      have hsub2 : "sumset (sumset X {c} - sumset X C) B \<union> sumset (sumset ?Y {c}) B \<subseteq> 
        sumset (sumset X {c}) B" by (simp add: sumset_mono)
      then have ineq1: "card (sumset X (sumset {c} B) - sumset X (sumset C B)) + card (sumset ?Y B) \<le> 
        card (sumset X B)"
      proof-
      have "card (sumset X (sumset {c} B) - sumset X (sumset C B)) + card (sumset ?Y B) = 
        card ((sumset X (sumset {c} B) - sumset X (sumset C B)) \<union> sumset (sumset ?Y {c}) B)" 
          using hdisj hcard2 card_Un_disjnt finite_sumset hX hYX finite_subset hB
          by (metis (no_types, lifting) finite.emptyI finite.insertI finite_Diff)
      also have "... \<le> card (sumset X (sumset {c} B))" using card_mono finite_sumset hX hB
        by (metis (no_types, lifting) Diff_subset Un_subset_iff finite.emptyI finite.insertI 
            hsub2 sumset_assoc)
      finally show "card (sumset X (sumset {c} B) - sumset X (sumset C B)) + card (sumset ?Y B) \<le> 
        card (sumset X B)" using hcard1 by auto
    qed
    have ineq2: "card (sumset X {c} - sumset X C)  \<ge> card X - card ?Y"
    proof-
      let ?Z = "{x \<in> X. sumset {x} {c} \<subseteq> sumset X C}"
      have hZY: "?Z \<subseteq> ?Y"
        by (smt (verit, del_insts) Collect_mono_iff subset_refl sumset_assoc sumset_mono)
      have hinj: "inj_on (\<lambda> x. x \<oplus> c) (X - ?Z)" 
      proof (intro inj_onI)
        fix x y assume "x \<in> X - ?Z" and "y \<in> X - ?Z" and h: "x \<oplus> c = y \<oplus> c"
        then have "x \<in> G" and "y \<in> G" using hXG by auto
        then show "x = y" using h hc by simp
      qed
      have himage: "(\<lambda> x. x \<oplus> c) ` (X - ?Z) = sumset X {c} - sumset X C"
      proof
        show "(\<lambda>x. x \<oplus> c) ` (X - ?Z) \<subseteq> sumset X {c} - sumset X C"
        proof(intro image_subsetI)
          fix x assume hx: "x \<in> X - ?Z"
          then have hxG : "x \<in> G" using hXG by auto
          then have hxc1: "x \<oplus> c \<in> sumset X {c}" using hXG hc hx by auto
          have "x \<oplus> c \<in> sumset {x} {c}" using hxG hc by auto
          then have hxc2: "x \<oplus> c \<notin> sumset X C" using hx hXG hc hCG
            using DiffD2 sumset.simps sumset.sumsetI by auto
          then show "x \<oplus> c \<in> sumset X {c} - sumset X C" using hxc1 hxc2 by simp
        qed
        show "sumset X {c} - sumset X C \<subseteq> (\<lambda>x. x \<oplus> c) ` (X - ?Z)"
        proof
          fix d assume "d \<in> sumset X {c} - sumset X C"
          then obtain x where hd: "d = x \<oplus> c" and hxc: "x \<oplus> c \<notin> sumset X C" and hx: "x \<in> X"
            using sumset.cases by force
          then show "d \<in> (\<lambda>x. x \<oplus> c) ` (X - ?Z)" using hd hxc hx hXG hc by auto          
        qed
      qed
      have hcard3: "card (X - ?Z) = card (sumset X {c} - sumset X C)" 
        using card_image hinj himage by fastforce
      have "card X = card ?Z + card (X - ?Z)" 
        by (simp add: card_Diff_subset card_mono hX)
      also have "... \<le> card ?Y + card (sumset X {c} - sumset X C)" 
        using hcard3 card_mono hZY hY by auto
      finally show ?thesis by simp
    qed
    have ineq3: "card (sumset X B) - card (sumset ?Y B) \<le> 
      card (sumset X B) * (card X - card ?Y) / card X"
    proof(cases "?Y = {}")
      case True
      then show ?thesis using card_eq_0_iff 
        by (smt (verit) hX hXne minus_nat.diff_0 nonzero_mult_div_cancel_right of_nat_eq_0_iff 
        of_nat_mult sumset_empty(2))
    next
      case hYne: False
      have "card (sumset ?Y B) \<ge> card (sumset X B) / card X * card ?Y" using assms(6)[OF hYX hYne] 
        hX hYne hX hYX finite_subset divide_le_eq
        by (smt (z3) card_gt_0_iff hY mult_imp_div_pos_less of_nat_0_less_iff)
      moreover have "card (sumset X B) / card X * card ?Y = (card (sumset X B) * card ?Y) / card X"
        by auto
      moreover have "card (sumset X B) * card ?Y / card X  * card X = card (sumset X B) * card ?Y"
        using hX by (simp add: field_simps)
      ultimately have "card (sumset ?Y B) * card X \<ge> card (sumset X B) * card ?Y" 
        using hX hXne of_nat_0_less_iff le_divide_eq 
        by (smt (z3) card_sumset_0_iff hBG hXG mult_cancel1 mult_cancel2 of_nat_le_0_iff 
        of_nat_le_iff of_nat_mult)
      then have "real ((card (sumset X B) - card (sumset ?Y B)) * card X) \<le> 
        card (sumset X B) * (card X - card ?Y)"
        by (simp add: diff_mult_distrib diff_mult_distrib2)
      thus ?thesis using le_divide_eq card_eq_0_iff hX hXne
        by (smt (z3) of_nat_le_0_iff of_nat_mult)
    qed
    show ?thesis 
    proof-
      have "real (card ((sumset X (sumset {c} B)) - (sumset X (sumset C B)))) \<le> 
        card (sumset X B) - card (sumset ?Y B)" using ineq1 by auto
      also have "... \<le> card (sumset X B) * (card X - card ?Y) / card X" using ineq3 by auto
      also have "... \<le> card (sumset X B) * card (sumset X {c} - sumset X C) / card X" using ineq2
        divide_le_cancel of_nat_less_0_iff of_nat_mono by (smt (verit, del_insts) mult_le_mono2)
      finally show ?thesis by simp
    qed
  qed
  have hinsert: "real (card (sumset X (sumset (insert c C) B))) / real (card (sumset X (insert c C))) = 
  (card (sumset X (sumset {c} B) - sumset X (sumset C B)) + card (sumset X (sumset C B))) / 
  (card (sumset X {c} - sumset X C) + card (sumset X C))"
    using sumset_insert2 card_Un_disjoint finite_sumset hX hB hC Diff_disjoint Int_commute 
    Un_commute finite.emptyI finite.insertI finite_Diff hcase.hyps(1)
    by (smt (verit) Un_Diff_cancel2 insert_is_Un sumset_commute sumset_subset_Un2)
  have hsplit: "real (card (sumset X B)) * (card (sumset X {c} - sumset X C) + card (sumset X C)) / card X = 
  real (card (sumset X B)) * card (sumset X {c} - sumset X C) / card X + 
  card (sumset X B) * card (sumset X C) / card X"
    by (smt (verit, ccfv_threshold) add_divide_distrib add_mult_distrib2 of_nat_add of_nat_mult)
  have hind: "card (sumset X B) * card (sumset X C) / card X \<ge> card (sumset X (sumset C B))"
    using hcase(3)[OF hCne hCG] hXne hCne hcase(1) hX finite_sumset card_gt_0_iff
    add_mult_distrib2 of_nat_mult card_eq_0_iff card_sumset_0_iff hCG 
    hXG of_nat_0_less_iff by (metis (no_types, opaque_lifting) divide_le_eq times_divide_eq_left)
  have "real (card (sumset X B)) * (card (sumset X {c} - sumset X C) + card (sumset X C)) / card X \<ge>
  (card (sumset X (sumset {c} B) - sumset X (sumset C B)) + card (sumset X (sumset C B)))" 
    using hsplit hind hstep by simp
  then have "card (sumset X B) / card X \<ge> 
    (card (sumset X (sumset {c} B) - sumset X (sumset C B)) + card (sumset X (sumset C B))) / 
    (card (sumset X {c} - sumset X C) + card (sumset X C))" using card_sumset_0_iff hCG hXG 
    card_eq_0_iff hC hX hXne hCne divide_self le_divide_eq
    by (smt (z3) add_is_0 hcase.hyps(1) of_nat_le_0_iff times_divide_eq_left)
  thus "real (card (sumset X (sumset (insert c C) B))) / real (card (sumset X (insert c C))) \<le> 
    real (card (sumset X B)) / real (card X)" using hinsert by auto
  qed
qed


text\<open>The following inequality is the result corresponding to Corollary 7.3.6 in Zhao's book \cite{Zhaobook}.\<close>

lemma triangle_ineq_sumsets: 
  assumes hA: "finite A" and hB: "finite B" and hC: "finite C" and
  hAG : "A \<subseteq> G" and hBG: "B \<subseteq> G" and hCG: "C \<subseteq> G"
  shows "card A * card (sumset B C) \<le> card (sumset A B) * card (sumset A C)"

proof(cases "A = {}")
  case True
  then show ?thesis by simp
next
  case hAne: False
  show "card A * card (sumset B C) \<le> card (sumset A B) * card (sumset A C)"
  proof(cases "B = {}")
    case True
    then show ?thesis by simp
  next
    case hBne: False
    define KS where "KS \<equiv> (\<lambda>X. card (sumset X C) / real (card X)) ` (Pow A - {{}})"
    define K where "K \<equiv> Min KS"
    define X where "X \<equiv> @X. X \<in> Pow A - {{}} \<and> K = card (sumset X C) / real (card X)"
    obtain KS: "finite KS" "KS \<noteq> {}"
      using KS_def hA hAne by blast
    then have "K \<in> KS"
      using K_def Min_in by blast
    then have "\<exists>X. X \<in> Pow A - {{}} \<and> K = card (sumset X C) / real (card X)"
      using KS_def by blast
    then obtain "X \<in> Pow A - {{}}" and Keq: "K = card (sumset X C) / real (card X)"
      by (metis (mono_tags, lifting) X_def someI_ex)
    then have hX: "X \<subseteq> A" "X \<noteq> {}"
      by auto
    have hXmin : "\<And> Y. Y \<subseteq> A \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> 
      card (sumset X C) / card X \<le> card (sumset Y C) / card Y"
      using K_def KS_def Keq Min_le KS(1) by auto
    then have hXAineq: "card (sumset X C) / card X \<le> card (sumset A C) / card A"
      by (metis hAne subset_refl)
    have haux: "real (card (sumset X (sumset B C))) / real (card (sumset X B))
      \<le> real (card (sumset X C)) / real (card X)" using triangle_ineq_sumsets_aux[of "X" "C" "B"] 
      hXmin hX hA hAG finite_subset hB hC hBne hBG hC hCG subset_trans by metis
    have hXAsumset : "real (card (sumset X B)) \<le> card (sumset A B)" 
      using hX(1) card_mono hA finite_sumset hB order_refl sumset_mono
      by (metis of_nat_le_iff)
    have "card (sumset B C) \<le> card (sumset X (sumset B C))" using assms hX
      finite_sumset hAG card_le_sumset
      by (metis bot.extremum_uniqueI dual_order.trans infinite_super subsetD subsetI 
        sumset_subset_carrier)
    also have "... \<le> (card (sumset X C) / card X) * card (sumset X B)" using haux divide_le_eq
      card_sumset_0_iff hBne hX hB hA finite_subset card_0_eq by (smt (verit) hCG mult_eq_0_iff 
      of_nat_0_eq_iff of_nat_0_le_iff sumset_assoc sumset_subset_carrier)
    also have "... \<le> (card (sumset A C) / card A) * card (sumset A B)" 
      using hXAineq hXAsumset by (meson divide_nonneg_nonneg mult_mono' of_nat_0_le_iff)
    finally have "card (sumset B C) \<le> (card (sumset A C) * card (sumset A B)) / card A" by simp
    then have "card (sumset B C) * card A \<le> card (sumset A C) * card (sumset A B)" 
      using le_divide_eq hAne hA card_gt_0_iff by (smt (verit, ccfv_threshold) 
      card_0_eq of_nat_le_0_iff of_nat_le_iff of_nat_mult)
    thus "card A * card (sumset B C) \<le> card (sumset A B) * card (sumset A C)"
      by (simp add: mult.commute)
  qed
qed

end
end