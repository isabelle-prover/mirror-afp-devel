section\<open>Generalized Cauchy--Davenport theorem: main proof\<close>
(*
  Session: Generalized_Cauchy_Davenport
  Title: Generalized_Cauchy_Davenport_main_proof.thy
  Authors: Mantas Bakšys
  Affiliation: University of Cambridge
  Date: April 2023.
*)


theory Generalized_Cauchy_Davenport_main_proof
  imports Generalized_Cauchy_Davenport_preliminaries
begin

context group

begin

subsection\<open>The counterexample pair relation in \cite{DeVos2016OnAG}\<close>
definition devos_rel where 
  "devos_rel = (\<lambda> (A, B). card(A \<cdots> B)) <*mlex*> (inv_image ({(n, m). n > m} <*lex*> 
  measure (\<lambda> (A, B). card A))) (\<lambda> (A, B). (card A + card B, (A, B)))"

lemma devos_rel_iff: 
  "((A, B), (C, D)) \<in> devos_rel \<longleftrightarrow> card(A \<cdots> B) < card(C \<cdots> D) \<or> 
  (card(A \<cdots> B) = card(C \<cdots> D) \<and> card A + card B > card C + card D) \<or>
  (card(A \<cdots> B) = card(C \<cdots> D) \<and> card A + card B = card C + card D \<and> card A < card C)"
  using devos_rel_def mlex_iff[of _ _ "\<lambda> (A, B). card(A \<cdots> B)"] by fastforce

lemma devos_rel_le_smul:
  "((A, B), (C, D)) \<in> devos_rel \<Longrightarrow> card(A \<cdots> B) \<le> card(C \<cdots> D)"
  using devos_rel_iff by fastforce

text\<open>Lemma stating that the above relation due to DeVos is well-founded\<close>
lemma devos_rel_wf : "wf (Restr devos_rel 
  {(A, B). finite A \<and> A \<noteq> {} \<and> A \<subseteq> G \<and> finite B \<and> B \<noteq> {} \<and> B \<subseteq> G})" (is "wf (Restr devos_rel ?fin)")
proof-
  define f where "f = (\<lambda> (A, B). card(A\<cdots>B))"
  define g where "g = (\<lambda> (A :: 'a set, B :: 'a set). (card A + card B, (A, B)))"
  define h where "h = (\<lambda> (A :: 'a set, B :: 'a set). card A + card B)"
  define s where "s = ({(n :: nat, m :: nat). n > m} <*lex*> measure (\<lambda> (A :: 'a set, B :: 'a set). card A))"
  have hle2f: "\<And> x. x \<in> ?fin \<Longrightarrow> h x \<le> 2 * f x"
  proof-
    fix x assume hx: "x \<in> ?fin"
    then obtain A B where hxAB: "x = (A, B)" by blast
    then have "card A \<le> card (A \<cdots> B)" and "card B \<le> card (A \<cdots> B)" 
      using card_le_smul_left card_le_smul_right hx by auto
    then show "h x \<le> 2 * f x" using hxAB h_def f_def by force
  qed
  have "wf (Restr (measure f) ?fin)" by (simp add: wf_Int1)
  moreover have "\<And> a. a \<in> range f \<Longrightarrow> wf (Restr (Restr (inv_image s g) {x. f x = a}) ?fin)"
  proof-
    fix y assume "y \<in>  range f"
    then show "wf (Restr (Restr (inv_image s g) {x. f x = y}) ?fin)"
    proof-
      have "Restr ({x. f x = y} \<times> {x. f x = y} \<inter> (inv_image s g)) ?fin \<subseteq> 
        Restr (((\<lambda> x. 2 * f x - h x) <*mlex*> measure (\<lambda> (A :: 'a set, B :: 'a set). card A)) \<inter> 
        {x. f x = y} \<times> {x. f x = y}) ?fin"
      proof
        fix z assume hz: "z \<in> Restr ({x. f x = y} \<times> {x. f x = y} \<inter> (inv_image s g)) ?fin"
        then obtain a b where hzab: "z = (a, b)" and "f a = y" and "f b = y" and 
          "h a > h b \<or> h a = h b \<and> (a, b) \<in> measure (\<lambda> (A, B). card A)" and 
          "a \<in> ?fin" and "b \<in> ?fin"
          using s_def g_def h_def by force
        then obtain "2 * f a - h a < 2 * f b - h b \<or> 
          2 * f a - h a = 2 * f b - h b \<and> (a, b) \<in> measure (\<lambda> (A, B). card A)" 
          using hle2f by (smt (verit) diff_less_mono2 le_antisym nat_less_le)
        then show "z \<in> Restr (((\<lambda> x. 2 * f x - h x) <*mlex*> measure (\<lambda> (A, B). card A)) \<inter> 
        {x. f x = y} \<times> {x. f x = y}) ?fin" using hzab hz by (simp add: mlex_iff)
      qed
      moreover have "wf ((\<lambda> x. 2 * f x - h x) <*mlex*> measure (\<lambda> (A, B). card A))"
        by (simp add: wf_mlex)
      ultimately show ?thesis by (simp add: Int_commute wf_Int1 wf_subset)
    qed
  qed
  moreover have "trans (?fin \<times> ?fin)" using trans_def by fast
  ultimately have "wf (Restr (inv_image (less_than <*lex*> s) (\<lambda> c. (f c, g c))) ?fin)" 
    using wf_prod_lex_fibers_inter[of "less_than" "f" "?fin \<times> ?fin" "s" "g"] measure_def
    by (metis (no_types, lifting) inf_sup_aci(1))
  moreover have "(inv_image (less_than <*lex*> s) (\<lambda> c. (f c, g c))) = devos_rel"
    using s_def f_def g_def devos_rel_def mlex_prod_def by fastforce
  ultimately show ?thesis by simp
qed

subsection\<open>$p(G)$ -- the order of the smallest nontrivial finite subgroup of a group: definition and lemmas\<close>

text\<open>$p(G)$ -- the size of the smallest nontrivial finite subgroup of $G$, set to $\infty$ if none exist\<close>
definition p :: enat where "p = Inf (orderOf ` {H. subgroup H G (\<cdot>) \<one> \<and> H \<noteq> {\<one>}})"

lemma subgroup_finite_ge:
  assumes "subgroup H G (\<cdot>) \<one>" and "H \<noteq> {\<one>}" and "finite H"
  shows "card H \<ge> p"
  using assms p_def wellorder_Inf_le1 ecard_eq_card_finite
    by (metis (mono_tags, lifting) image_eqI mem_Collect_eq)

lemma subgroup_infinite_or_card_ge:
  assumes "subgroup H G (\<cdot>) \<one>" and "H \<noteq> {\<one>}"
  shows "infinite H \<or> card H \<ge> p" using subgroup_finite_ge assms by auto

end

subsection\<open>Proof of the generalized Cauchy--Davenport theorem for (non-abelian) groups\<close>
text\<open>Generalized Cauchy--Davenport theorem for (non-abelian) groups due to Matt DeVos \cite{DeVos2016OnAG}\<close>
theorem (in group) Generalized_Cauchy_Davenport:
  assumes hAne: "A \<noteq> {}" and hBne: "B \<noteq> {}" and hAG: "A \<subseteq> G" and hBG: "B \<subseteq> G" and
  hAfin: "finite A" and hBfin: "finite B"
  shows "card (A \<cdots> B) \<ge> min p (card A + card B - 1)"
proof(rule ccontr)
  text\<open>We will prove the theorem by contradiction\<close>
  assume hcontr: "\<not> min p (card A + card B - 1) \<le> card (A \<cdots> B)"
  let ?fin = "{(A, B). finite A \<and> A \<noteq> {} \<and> A \<subseteq> G \<and> finite B \<and> B \<noteq> {} \<and> B \<subseteq> G}"
  define M where "M = {(A, B). card (A \<cdots> B) < min p (card A + card B - 1)} \<inter> ?fin"
  have hmemM: "(A, B) \<in> M" using assms hcontr M_def not_le by blast
  text\<open>Firstly, extract sets $X$ and $Y$, which are minimal counterexamples of the DeVos relation defined above\<close>
  then obtain X Y where hXYM: "(X, Y) \<in> M" and hmin: "\<And>Z. Z \<in> M \<Longrightarrow> (Z, (X, Y)) \<notin> Restr devos_rel ?fin" 
    using devos_rel_wf wfE_min by (smt (verit, del_insts) old.prod.exhaust)
  have hXG: "X \<subseteq> G" and hYG: "Y \<subseteq> G" and hXfin: "finite X" and hYfin: "finite Y" and 
    hXYlt: "card (X \<cdots> Y) < min p (card X + card Y - 1)" using hXYM M_def by auto
  have hXY: "card X \<le> card Y"
  proof(rule ccontr)
    assume hcontr: "\<not> card X \<le> card Y"
    have hinvinj: "inj_on inverse G" using inj_onI invertible invertible_inverse_inverse by metis
    let ?M = "inverse ` X"
    let ?N = "inverse ` Y"
  have "?N \<cdots> ?M = inverse ` (X \<cdots> Y)" using set_inverse_composition_commute hXYM M_def by auto
  then have hNM: "card (?N \<cdots> ?M) = card (X \<cdots> Y)" 
    using hinvinj card_image subset_inj_on smul_subset_carrier by metis
  moreover have hM: "card ?M = card X"
    using hinvinj hXG hYG card_image subset_inj_on by metis
  moreover have hN: "card ?N = card Y" 
    using hinvinj hYG card_image subset_inj_on by metis
  moreover have hNplusM: "card ?N + card ?M = card X + card Y" using hM hN by auto
  ultimately have "card (?N \<cdots> ?M) < min p (card ?N + card ?M - 1)" 
    using hXYM M_def hXYlt by argo
  then have "(?N, ?M) \<in> M" using M_def hXYM by blast
    then have "((?N, ?M), (X, Y)) \<notin> devos_rel" using hmin hXYM M_def by blast
    then have "\<not> card Y < card X" using hN  hNM hNplusM devos_rel_iff by simp
    then show False using hcontr by simp
  qed
  text\<open>Observe that $X$ contains at least 2 elements, otherwise the proof is easy\<close>
  have hX2: "2 \<le> card X"
  proof(rule ccontr)
    assume " \<not> 2 \<le> card X"
    moreover have "card X > 0" using hXYM M_def card_gt_0_iff by blast
    ultimately have hX1: "card X = 1" by auto
    then obtain x where "X = {x}" and "x \<in> G" using hXG by (metis card_1_singletonE insert_subset)
    then have "card (X \<cdots> Y) = card X + card Y - 1" using card_smul_singleton_left_eq hYG hXYM M_def
      by (simp add: Int_absorb2)
    then show False using hXYlt by simp
  qed
  then obtain a b where habX: "{a, b} \<subseteq> X" and habne: "a \<noteq> b" by (metis card_2_iff obtain_subset_with_card_n)
  moreover have "b \<in> X \<cdots> {inverse a \<cdot> b}" by (smt (verit) habX composition_closed hXG insert_subset 
    invertible invertible_inverse_closed invertible_right_inverse2 singletonI smul.smulI subsetD)
  text\<open>From this, obtain an element $g \in G$ such that $Xg \cap X \neq \emptyset$\<close>
  then obtain g where hgG: "g \<in> G" and hg1: "g \<noteq> \<one>" and hXgne: "(X \<cdots> {g}) \<inter> X \<noteq> {}" 
    using habne habX hXG by (metis composition_closed insert_disjoint(2) insert_subset invertible 
      invertible_inverse_closed invertible_right_inverse2 mk_disjoint_insert right_unit)
  text\<open>Now we show that  $Xg \cap X$ is strict subset of $X$\<close>
  have hpsubX: "(X \<cdots> {g}) \<inter> X \<subset> X"
  proof(rule ccontr)
    assume "\<not> (X \<cdots> {g}) \<inter> X \<subset> X"
    then have hXsub: "X \<subseteq> X \<cdots> {g}" by auto
    then have "card X \<cdots> {g} = card X" using card_smul_sing_right_le hXYM M_def 
        Int_absorb2 \<open>g \<in> G\<close> card.infinite card_smul_singleton_right_eq finite_Int hXG by metis
    moreover have hXfin: "finite X" using hXYM M_def by auto
    ultimately have "X \<cdots> {g} = X" using hXsub card_subset_eq finite.emptyI finite.insertI
      finite_smul by metis
    then have hXpow: "X \<cdots> (powers g) = X" by (simp add: hXG hgG smul_singleton_eq_contains_powers)
    moreover have hfinpowers: "finite (powers g)"
    proof(rule ccontr)
      assume "infinite (powers g)"
      then have "infinite X" using hXG hX2 hXpow by (metis Int_absorb1 hXgne hXsub hgG 
        infinite_smul_right invertible le_iff_inf powers_submonoid submonoid.subset)
      then show False using hXYM M_def by auto
    qed
    ultimately have "card (powers g) \<le> card X" using card_le_smul_right 
      powers_submonoid submonoid.subset hXYM M_def habX hXG hXfin hgG insert_subset invertible 
      subsetD by (metis (no_types, lifting))
    then have "p \<le> card X" 
      using hfinpowers hg1 hgG le_trans powers_ne_one powers_subgroup subgroup_infinite_or_card_ge
      by (smt (verit) enat_ile enat_ord_simps(1))
    then have "p \<le> card (X \<cdots> Y)" using card_le_smul_left hXYM M_def 
      \<open>b \<in> smul X {inverse a \<cdot> b}\<close> bot_nat_0.extremum_uniqueI card.infinite 
      card_0_eq card_le_smul_right empty_iff hXY hXfin hYG le_trans smul.cases
      by (smt (verit) enat_ile enat_ord_simps(1)) 
    then show False using hXYlt by auto
  qed
  text\<open>Define auxiliary transformationms of sets $X$ and $Y$ to reach a contradiction\<close>
  let ?X1 = "(X \<cdots> {g}) \<inter> X"
  let ?X2 = "(X \<cdots> {g}) \<union> X"
  let ?Y1 = "({inverse g} \<cdots> Y) \<union> Y"
  let ?Y2 = "({inverse g} \<cdots> Y) \<inter> Y"
  have hY1G: "?Y1 \<subseteq> G" and hY1fin: "finite ?Y1" and hX2G: "?X2 \<subseteq> G" and hX2fin: "finite ?X2" 
    using hYfin hYG hXG finite_smul hXfin smul_subset_carrier by auto
  have hXY1: "?X1 \<cdots> ?Y1 \<subseteq> X \<cdots> Y"
  proof
    fix z assume "z \<in> ?X1 \<cdots> ?Y1"
    then obtain x y where hz: "z = x \<cdot> y" and hx: "x \<in> ?X1" and hy: "y \<in> ?Y1" by (meson smul.cases)
    show "z \<in> X \<cdots> Y"
    proof(cases "y \<in> Y")
      case True
      then show ?thesis using hz hx smulI hXG hYG by auto
    next
      case False
      then obtain w where "y = inverse g \<cdot>  w" and "w \<in> Y" using hy smul.cases by (metis UnE singletonD)
      moreover obtain v where "x = v \<cdot> g" and "v \<in> X" using hx smul.cases by blast
      ultimately show ?thesis using hz hXG hYG hgG associative invertible_right_inverse2
        by (simp add: smul.smulI subsetD)
    qed
  qed
  have hXY2: "?X2 \<cdots> ?Y2 \<subseteq> X \<cdots> Y"
  proof
    fix z assume "z \<in> ?X2 \<cdots> ?Y2"
    then obtain x y where hz: "z = x \<cdot> y" and hx: "x \<in> ?X2" and hy: "y \<in> ?Y2" by (meson smul.cases)
    show "z \<in> X \<cdots> Y"
    proof(cases "x \<in> X")
      case True
      then show ?thesis using hz hy smulI hXG hYG by auto
    next
      case False
      then obtain v where "x = v \<cdot> g" and "v \<in> X" using hx smul.cases by (metis UnE singletonD)
      moreover obtain w where "y = inverse g \<cdot> w" and "w \<in> Y" using hy smul.cases by blast
      ultimately show ?thesis using hz hXG hYG hgG associative invertible_right_inverse2
        by (simp add: smul.smulI subsetD)
    qed
  qed
  have hY2ne: "?Y2 \<noteq> {}"
  proof
    assume hY2: "?Y2 = {}"
    have "card X + card Y \<le> card Y + card Y" by (simp add: hXY)
    also have "... = card ?Y1" using card_Un_disjoint hYfin hYG hgG finite_smul inf.orderE invertible
      by (metis hY2 card_smul_singleton_left_eq finite.emptyI finite.insertI invertible_inverse_closed)
    also have "... \<le> card (?X1 \<cdots> ?Y1)" using card_le_smul_right[OF _ _ _ hY1fin hY1G] 
        hXgne hXG Int_assoc Int_commute ex_in_conv finite_Int hXfin smul.simps smul_D(2) 
        smul_Int_carrier unit_closed by auto
    also have "... \<le> card (X \<cdots> Y)" using hXY1 finite_smul card_mono by (metis hXfin hYfin)
    finally show False using hXYlt by auto
  qed
  have hXadd: "card ?X1 + card ?X2 = 2 * card X" 
    using card_smul_singleton_right_eq hgG hXfin hXG card_Un_Int
    by (metis Un_Int_eq(3) add.commute finite.emptyI finite.insertI finite_smul mult_2 subset_Un_eq)
  have hYadd: "card ?Y1 + card ?Y2 = 2 * card Y"
    using card_smul_singleton_left_eq hgG hYfin hYG card_Un_Int finite_smul
    by (metis Int_lower1 Un_Int_eq(3) card_0_eq card_Un_le card_seteq finite.emptyI finite.insertI  
      hY2ne le_add_same_cancel1 mult_2 subset_Un_eq)
  text\<open>Split the contradiction proof into the cases based on whether $|?X2| + |?Y2| > |X| + |Y|$ holds\<close>
  show False
  proof (cases "card ?X2 + card ?Y2 > card X + card Y")
    case hcase: True
    then have h : "card X + card Y - 1 \<le> card ?X2 + card ?Y2 - 1" by simp
    have hXY2le: "enat (card (?X2 \<cdots> ?Y2)) \<le> card (X \<cdots> Y)" 
      using hXY2 finite_smul card_mono hXfin hYfin enat_ile by (metis enat_ord_simps(1))
    moreover have "... < min p (card X + card Y - 1)" using hXYlt by auto
    moreover have "... \<le> min p (card ?X2 + card ?Y2 - 1)" 
      using h enat_ile enat_ord_simps(1) min_def
      by (smt (verit, ccfv_SIG) linorder_not_le order_le_less order_le_less_subst2)
    ultimately have "card (?X2 \<cdots> ?Y2) < min p (card ?X2 + card ?Y2 - 1)" by order
    then have hXY1M: "(?X2, ?Y2) \<in> M" using hY2ne hX2fin hX2G hXYM M_def by blast
    text\<open>Show that $(?X2, ?Y2)$ is a smaller counterexample for the DeVos relation\<close>
    moreover have "((?X2, ?Y2), (X, Y)) \<in>  Restr devos_rel ?fin" using hXYM M_def hXY1M h hXY2le 
        devos_rel_iff hcase by auto
    ultimately show False using hmin by blast 
  next
    case hcase: False
    then have h: "card ?X1 + card ?Y1 - 1 \<ge> card X + card Y - 1" using hXadd hYadd by linarith
    have hX1lt: "card ?X1 < card X" using hXfin by (simp add: hpsubX psubset_card_mono)
    have hXY1le: "enat (card (?X1 \<cdots> ?Y1)) \<le> card (X \<cdots> Y)" 
      using hXY1 finite_smul card_mono hYfin hXfin by (metis enat_ord_simps(1))
    also have "... < min p (card X + card Y - 1)" using hXYlt by auto
    also have "... \<le> min p (card ?X1 + card ?Y1 - 1)" using h enat_ile enat_ord_simps(1) min_def
      by (smt (verit, ccfv_threshold) linorder_le_less_linear order.asym order_le_less_trans)
    finally have hXY1M: "(?X1, ?Y1) \<in> M" using M_def hXgne hY1fin hY1G hXYM by blast
    text\<open>Show that $(?X1, ?Y1)$ is a smaller counterexample for the DeVos relation\<close>
    moreover have "((?X1, ?Y1), (X, Y)) \<in>  Restr devos_rel ?fin" using hXYM M_def hXY1M h hXY1le 
        devos_rel_iff hX1lt hXY1le hcase by force
    ultimately show ?thesis using hmin by blast
  qed
qed

end