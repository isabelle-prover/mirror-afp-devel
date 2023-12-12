(* Theory: LLL_Applications.thy
   Author: Chelsea Edmonds*)

section \<open>Lovasz Local Framework Application \<close>
theory LLL_Applications imports "Lovasz_Local.Lovasz_Local_Lemma"
  "Lovasz_Local.Indep_Events" "Twelvefold_Way.Twelvefold_Way_Core" 
  Design_Theory.Multisets_Extras Basic_Bounds_Application
begin

subsection \<open>More set extras \<close>

lemma multiset_remove1_filter:  "a \<in># A \<Longrightarrow> P a \<Longrightarrow> 
    {#b \<in># A . P b#} = {#b \<in># remove1_mset a A . P b#} + {#a#}"
  by auto

lemma card_partition_image: 
  assumes "finite C"
  assumes "finite (\<Union>c \<in> C . f c)"
  assumes "(\<And> c. c\<in>C \<Longrightarrow>  card (f c) = k)"
  assumes "(\<And> c1 c2. c1 \<in> C \<Longrightarrow> c2 \<in> C \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> f c1 \<inter> f c2 = {})"
  shows "k * card (f ` C) = card (\<Union>c \<in> C . f c)"
proof -
  have "card (\<Union>c \<in> C . f c) = card (\<Union>(f ` C))" by simp
  moreover have "finite (f ` C)" using assms(1) by auto
  moreover have "finite (\<Union>(f ` C))" using assms(2) by auto
  moreover have "\<And>c. c \<in> f ` C \<Longrightarrow> card c = k" using assms(3) by auto
  moreover have "(\<And>c1 c2. c1 \<in> f ` C \<Longrightarrow> c2 \<in> f ` C \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> c1 \<inter> c2 = {})" using assms(4) by auto
  ultimately show ?thesis using card_partition[of "f ` C" k] by auto
qed

lemma mset_set_implies:
  assumes "image_mset f (mset_set A) = B"
  assumes "\<And> a . a \<in> A \<Longrightarrow> P (f a)"
  shows "\<And> b. b \<in># B \<Longrightarrow> P b"
proof -
  fix b assume "b \<in># B"
  then obtain a where "a \<in> A" and eqb: "f a = b"
    using assms(1) by (meson bij_mset_obtain_set_elem) 
  then show "P b" using assms(2) by auto
qed

lemma card_partition_image_inj: 
  assumes "finite C"
  assumes "inj_on f C"
  assumes "finite (\<Union>c \<in> C . f c)"
  assumes "(\<And> c. c\<in>C \<Longrightarrow>  card (f c) = k)"
  assumes "(\<And> c1 c2. c1 \<in> C \<Longrightarrow> c2 \<in> C \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> f c1 \<inter> f c2 = {})"
  shows "k * card (C) = card (\<Union>c \<in> C . f c)"
proof -
  have "card C = card (f ` C)" using assms(2) card_image 
    by fastforce
  then show ?thesis using card_partition_image assms 
    by metis
qed

lemma size_big_union_sum2: 
  fixes M :: "'a \<Rightarrow> 'b multiset"   
  shows "size (\<Sum> x \<in># X . M x) = (\<Sum>x \<in>#X . size (M x))"
  by (induct X) auto

lemma size_big_union_sum2_const: 
  fixes M :: "'a \<Rightarrow> 'b multiset"
  assumes "\<And> x . x \<in># X  \<Longrightarrow>  size (M x) = k"
  shows "size (\<Sum> x \<in># X . M x) = size X * k"
proof -
  have "size (\<Sum> x \<in># X . M x) = (\<Sum>x \<in>#X . size (M x))"
    using size_big_union_sum2 by auto
  also have "... = (\<Sum>x \<in>#X . k)" using assms by auto
  finally show ?thesis by auto
qed

lemma count_sum_mset2: "count (\<Sum> x \<in># X . M x) a = (\<Sum> x \<in># X . count (M x) a)"
  using count_sum_mset by (smt (verit) image_image_mset sum_over_fun_eq) 

lemma mset_subset_eq_elemI:
  "(\<And>a . a \<in># A \<Longrightarrow> count A a \<le> count B a) \<Longrightarrow> A \<subseteq># B"
  by (intro mset_subset_eqI) (metis zero_le count_eq_zero_iff) 

lemma mset_obtain_from_filter:
  assumes "a \<in># {# b \<in># B . P b #}"
  shows "a \<in># B" and "P a"
  using assms apply (metis multiset_partition union_iff) 
  using assms by (metis (mono_tags, lifting) Multiset.set_mset_filter mem_Collect_eq) 

subsection \<open>Mutual Independence Principle for Hypergraphs \<close>

context fin_hypergraph_nt 
begin                                      

definition (in incidence_system) block_intersect_count :: "'a set \<Rightarrow> nat" where
"block_intersect_count b \<equiv> size {# b2 \<in># (\<B> - {#b#}) . b2 \<inter> b \<noteq> {} #}"

lemma (in hypergraph) edge_intersect_count_inc: 
  assumes "e \<in># E"
  shows "size {# f \<in># E . f \<inter> e \<noteq> {}#} = block_intersect_count e + 1"
  unfolding block_intersect_count_def
proof -
  have "e \<inter> e \<noteq> {}" using blocks_nempty assms(1) by simp
  then have "{#f \<in># E. f \<inter> e \<noteq> {}#} = {#f \<in># remove1_mset e E. f \<inter> e \<noteq> {}#} + {#e#}" 
    using multiset_remove1_filter[of e E "\<lambda> f. f \<inter> e \<noteq> {}"] assms(1) by blast
  then show "size {#f \<in># E. f \<inter> e \<noteq> {}#} = size {#b2 \<in># remove1_mset e E. b2 \<inter> e \<noteq> {}#} + 1"
    by (metis size_single size_union)
qed

lemma disjoint_set_is_mutually_independent: 
  assumes iin: "i \<in> {0..<(size E)}"
  assumes idffn: "idf \<in> {0..<size E} \<rightarrow>\<^sub>E set_mset E"
  assumes Aefn: "\<And> i. i \<in> {0..<size E} \<Longrightarrow> Ae i = {f \<in> \<C>\<^sup>2 . mono_edge f (idf i)}"
  shows "prob_space.mutual_indep_events (uniform_count_measure (\<C>\<^sup>2)) (Ae i) Ae 
    ({j \<in>{0..<(size E)} . (idf j \<inter> idf i) = {}})"
proof -
  interpret P: vertex_colour_space \<V> E 2 (* specific to this *)
    using order_ge_two by (unfold_locales) (auto)
  have "P.mutual_indep_events (Ae i) Ae ({j \<in>{0..<(size E)} . (idf j \<inter> idf i) = {}})"
  proof (intro P.mutual_indep_eventsI)
    show "Ae i \<in> P.events" using P.sets_eq iin Aefn by simp
  next 
    show "Ae ` {j \<in> {0..<\<b>}. idf j \<inter> idf i = {}} \<subseteq> P.events" using P.sets_eq Aefn by auto
  next
    show "\<And>J. J \<subseteq> {j \<in> {0..<\<b>}. idf j \<inter> idf i = {}} \<Longrightarrow> J \<noteq> {} \<Longrightarrow> 
      P.prob (Ae i \<inter> \<Inter> (Ae ` J)) = P.prob (Ae i) * P.prob (\<Inter> (Ae ` J))"
    proof -
      let ?e = "idf i"
      fix J assume jss: "J \<subseteq> {j \<in> {0..<\<b>}. idf j \<inter> ?e = {}}" and ne: "J \<noteq> {}"
      then have "finite J" using finite_subset finite_nat_set_iff_bounded_le mem_Collect_eq
        by (metis (full_types) finite_Collect_conjI finite_atLeastLessThan) 
      have jin: "\<And> j . j \<in> J \<Longrightarrow> j \<in> {0..<\<b>}" using jss by auto
      have iedge: "\<And>i. i \<in> {0..<size E} \<Longrightarrow> idf i \<in># E" using idffn by auto
      define P' where "P' \<equiv> (\<V> - ?e) \<rightarrow>\<^sub>E {0..<2::colour}"
      then have finP: "finite P'" using finite_PiE finite_sets by (metis P.finP finite_Diff) 
      define T where "T \<equiv> \<lambda> p. {f \<in> \<C>\<^sup>2 . \<forall> v \<in> (\<V> - ?e) . f v = p v}" 
      have Tss: "\<And> p. T p \<subseteq> \<C>\<^sup>2" unfolding T_def by auto
      have Pdjnt: "\<And> p1 p2. p1 \<in> P' \<Longrightarrow> p2 \<in> P' \<Longrightarrow> p1 \<noteq> p2 \<Longrightarrow> T p1 \<inter> T p2 = {}" 
      proof -
        fix p1 p2 assume p1in: "p1 \<in> P'" and p2in: "p2 \<in> P'" and pne: "p1 \<noteq> p2"
        have "\<And> x. x \<in> T p1 \<Longrightarrow> x \<notin> T p2" 
        proof (rule ccontr)
          fix x assume xin: "x \<in> T p1" and "\<not> x \<notin> T p2"
          then have xin2: "x \<in> T p2" by simp
          then have "x \<in> \<C>\<^sup>2" and "\<forall> v \<in> (\<V> - ?e) . x v = p1 v" and "\<forall> v \<in> (\<V> - ?e) . x v = p2 v" 
            using T_def xin by auto
          then have "\<And> v. v \<in> (\<V> - ?e) \<Longrightarrow> p1 v = p2 v" by auto
          then have "p1 = p2" using p1in p2in  unfolding P'_def 
            using PiE_ext  by metis 
          then show False using pne by simp
        qed
        then show "T p1 \<inter> T p2 = {}" by auto
      qed
      have cp: "\<And> p. p \<in> P' \<Longrightarrow> card (T p) = 2 powi (card ?e)" 
      proof -
        fix p assume pin: "p \<in> P'"
        have "card (\<V> - ?e) = card \<V> - card ?e" using iedge wellformed iin
          using block_complement_def block_complement_size by auto 
        moreover have "card \<V> \<ge> card ?e" using iedge wellformed iin
          by (simp add: block_size_lt_order) 
        ultimately  have "(card \<V> - card (\<V> - ?e)) = card ?e" by simp
        then have "card {0..<2::colour} ^ (card \<V> - card (\<V> - ?e)) = 2 powi (card ?e)" by auto 
        moreover have "(\<And>a. a \<in> (\<V> - ?e) \<Longrightarrow> p a \<in> {0..<2})" 
          using pin P'_def by auto
        ultimately show "card (T p) = 2 powi (card ?e)" 
          unfolding T_def using card_PiE_filter_range_set[of "\<V> - ?e"  p "{0..<2::colour}" \<V> ] 
            finite_sets all_n_vertex_colourings_alt by auto
      qed
      define Ps where "Ps \<equiv> {p \<in> P' . T p \<subseteq> \<Inter>(Ae ` J)}"
      have psss: "Ps \<subseteq> P'" unfolding Ps_def P'_def by auto
      have p1: "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow> P.prob(Ae i) = 1/(2 powi (int (card (idf i)) - 1))" 
        using Aefn P.prob_monochromatic_edge_inv iedge by simp
      have bunrep: "\<Inter>(Ae ` J) = (\<Union>p \<in> Ps . T p)"
      proof (intro subset_antisym subsetI)
        fix x assume "x \<in> \<Inter>(Ae ` J)"
        then have xin: "x \<in> \<C>\<^sup>2" and xmono: "\<And> j. j \<in> J \<Longrightarrow> mono_edge x (idf j)" 
          using jin Aefn ne by auto
        define p where "p = (\<lambda> v . if (v \<in> \<V> - ?e) then x v else undefined)"
        then have pin: "p \<in> P'" unfolding P'_def using xin all_n_vertex_colourings_alt by auto
        then have xtin: "x \<in> T p" unfolding T_def p_def
          by (simp add: xin) 
        have "T p \<subseteq> \<Inter>(Ae ` J)"
        proof (intro subsetI)
          fix y assume yin: "y \<in> T p"
          have "\<And> j . j \<in> J \<Longrightarrow> mono_edge y (idf j)"
          proof -
            fix j assume jin: "j \<in> J"
            then have "idf j \<inter> idf i = {}" using jss by auto
            then have "\<And> v . v \<in> idf j \<Longrightarrow> v \<notin> ?e" by auto
            then have "\<And> v . v \<in> idf j \<Longrightarrow> v \<in> \<V> - ?e" using jss wellformed
              by (metis (no_types, lifting) DiffI \<open>j \<in> J\<close> basic_trans_rules(31) iedge mem_Collect_eq)
            then have "\<And> v . v \<in> idf j \<Longrightarrow> y v = x v" using yin T_def p_def by auto
            then show "mono_edge y (idf j)" using xmono jin
              by (simp add: mono_edge_def) 
          qed
          moreover have "y \<in> \<C>\<^sup>2"
            using Tss yin by auto
          ultimately show "y \<in>\<Inter>(Ae ` J)" using Aefn jin by auto
        qed
        then have "p \<in> Ps" unfolding Ps_def using pin by auto
        then show "x \<in> (\<Union> p \<in> Ps . T p)"
          using xtin by auto
      next 
        fix x assume "x \<in> (\<Union> p \<in> Ps . T p)"
        then show "x \<in> \<Inter>(Ae ` J)" unfolding Ps_def by auto
      qed
      moreover have dfo: "disjoint_family_on (\<lambda> p. T p) Ps" 
        using psss Pdjnt disjoint_family_on_def by blast
      moreover have "(\<lambda> p . T p) ` Ps \<subseteq> P.events"
        unfolding T_def Ps_def using P.sets_eq by auto
      moreover have finPs: "finite Ps" using finP psss finite_subset by auto
      ultimately have "P.prob (\<Inter>(Ae ` J)) = (\<Sum> p \<in> Ps. P.prob (T p))"
        using P.finite_measure_finite_Union[of Ps "\<lambda> p . T p"] by simp
      moreover have "\<And> p. p \<in> Ps \<Longrightarrow> P.prob (T p) = card (T p)/card (\<C>\<^sup>2)" 
        using measure_uniform_count_measure[of "\<C>\<^sup>2"] Tss
        by (simp add: P.MU_def P.fin_\<Omega>)
      ultimately have "P.prob (\<Inter>(Ae ` J)) = (\<Sum> p \<in> Ps. real (card (T p)))/(card (\<C>\<^sup>2))" 
        using sum_divide_distrib[of _ Ps "card (\<C>\<^sup>2)"] by (simp)
      also have "... = (\<Sum> p \<in> Ps. 2 powi (card ?e))/(card (\<C>\<^sup>2))"
        using cp psss by (simp add: Ps_def)
      finally have "P.prob (\<Inter>(Ae ` J)) = (card Ps * (2 powi (card ?e)))/(card (\<C>\<^sup>2))"
        by simp
      then have "P.prob (Ae i) * P.prob (\<Inter>(Ae ` J)) = 
          1/(2 powi (int (card (?e)) - 1)) * ((card Ps * (2 powi (card ?e)))/(card (\<C>\<^sup>2)))"
        using iin p1 by simp
      also have "... = (((2 powi (card ?e)))/(2 powi (int (card (?e)) - 1))) * (card Ps/card (\<C>\<^sup>2))" 
        by (simp add: field_simps)
      also have "... = 2 * (card Ps/card (\<C>\<^sup>2))" 
        using power_int_diff[of "2::real" "int (card ?e)" "(int (card (?e)) - 1)"] by simp
      finally have prob: "P.prob (Ae i) * P.prob (\<Inter>(Ae ` J)) = (card Ps * 2)/(card (\<C>\<^sup>2))" by simp
      have "(Ae i) \<inter> (\<Inter>(Ae ` J)) = (\<Union>p \<in> Ps . ((Ae i) \<inter> T p))" 
        using bunrep by auto
      moreover have "disjoint_family_on (\<lambda> p. (Ae i) \<inter> T p) Ps" 
        using dfo disjoint_family_on_bisimulation[of T Ps "(\<lambda> p. (Ae i) \<inter> T p)"] by auto
      moreover have "(\<lambda> p . (Ae i) \<inter> T p) ` Ps \<subseteq> P.events"
        unfolding T_def using P.sets_eq by auto
      ultimately have "P.prob ((Ae i) \<inter> (\<Inter>(Ae ` J))) = (\<Sum> p \<in> Ps. P.prob ((Ae i) \<inter> T p))"
        using P.finite_measure_finite_Union[of Ps "\<lambda>p. (Ae i) \<inter> T p"] finPs by simp
      moreover have tss2: "\<And> p. (Ae i) \<inter> T p \<subseteq> \<C>\<^sup>2" using Tss by auto
      moreover have "\<And> p. p \<in> Ps \<Longrightarrow> P.prob ((Ae i) \<inter> T p) = card ((Ae i) \<inter> T p)/card (\<C>\<^sup>2)" 
        using measure_uniform_count_measure[of "\<C>\<^sup>2"] tss2 P.MU_def P.fin_\<Omega> by simp
      ultimately have "P.prob ((Ae i) \<inter> (\<Inter>(Ae ` J))) = (\<Sum> p \<in> Ps. card ((Ae i) \<inter> T p))/(card (\<C>\<^sup>2))"
        using sum_divide_distrib[of _ Ps "card (\<C>\<^sup>2)"] by (simp)
      moreover have "\<And> p. p \<in> Ps \<Longrightarrow> card ((Ae i) \<inter> (T p)) = 2"
      proof -
        fix p assume "p \<in> Ps"
        define h where "h \<equiv> \<lambda> c. (\<lambda> v. if (v \<in> \<V>) then (if (v \<in> ?e) then c else p v) else undefined)"
        have hc: "\<And> c v. v \<in> ?e \<Longrightarrow> h c v = c" unfolding h_def using wellformed iin iedge by auto
        have hne: "\<And> c1 c2. c1 \<noteq> c2 \<Longrightarrow> h c1 \<noteq> h c2"
        proof (rule ccontr)
          fix c1 c2 assume ne: "c1 \<noteq> c2" "\<not> h c1 \<noteq> h c2" 
          then have eq: "h c1 = h c2" by simp
          have "\<And> v . v \<in> ?e \<Longrightarrow> h c1 v = c1" using hc by simp
          then have "\<And> v . v \<in> ?e \<Longrightarrow> c1 = c2" using hc eq by auto
          then show False using ne eq using V_nempty blocks_nempty iedge iin by blast 
        qed
        then have hdjnt: "\<And> n. (\<forall>c1 \<in> {0..<n}. \<forall>c2 \<in> {0..<n}. c1 \<noteq> c2 \<longrightarrow> {h c1} \<inter> {h c2} = {})"
          by auto
        have heq: "\<And> c. c \<in> {0..<2} \<Longrightarrow> {f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c \<and> (\<forall> v \<in> (\<V> - ?e) . f v = p v)} = {h c}"
        proof -
          fix c assume "c \<in> {0..<2::nat}"
          have "\<And> x f. f \<in> {f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c \<and> (\<forall> v \<in> (\<V> - ?e) . f v = p v)} \<Longrightarrow> f x = h c x" 
            unfolding h_def using mono_edge_colD all_n_vertex_colourings_alt by auto
          then have "\<And> f . f \<in> {f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c \<and> (\<forall> v \<in> (\<V> - ?e) . f v = p v)} \<Longrightarrow> f = h c"
            by auto
          moreover have "h c \<in> {f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c \<and> (\<forall> v \<in> (\<V> - ?e) . f v = p v)}"
          proof -
            have "h c \<in> \<C>\<^sup>2" unfolding h_def using all_n_vertex_colourings_alt
              by (smt (verit, ccfv_SIG) DiffI P'_def PiE_I PiE_mem \<open>c \<in> {0..<2}\<close> \<open>p \<in> Ps\<close> psss subset_eq)
            moreover have "mono_edge_col (h c) ?e c" using mono_edge_colI hc by auto
            ultimately show ?thesis unfolding h_def  by auto 
          qed
          ultimately show "{f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c \<and> (\<forall> v \<in> (\<V> - ?e) . f v = p v)} = {h c}"
            by blast  
        qed
        have "Ae i = (\<Union> c \<in> {0..<2}. {f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c})"
          using Aefn iedge iin mono_edge_set_union[of ?e 2] by auto
        then have "(Ae i) \<inter> (T p) = (\<Union> c \<in> {0..<2}. {f \<in> \<C>\<^sup>2 . mono_edge_col f ?e c \<and> (\<forall> v \<in> (\<V> - ?e) . f v = p v)})"
          unfolding T_def by auto
        then have "card ((Ae i) \<inter> (T p)) = card ((\<Union> c \<in> {0..<2}. {h c}))" using heq by simp
        moreover have "(1:: nat) * card {0..<2::nat} = card ((\<Union> c \<in> {0..<2}. {h c}))"
        proof - 
          have "inj_on (\<lambda>c. {h c}) {0..<2}" using hdjnt inj_onI
            by (metis (mono_tags, lifting) hne insertI1 singletonD) 
          then  show ?thesis 
            using card_partition_image_inj[of "{0..<2}" "\<lambda> c . {h c}" "1:: nat"] hdjnt by auto
        qed
        ultimately show "card ((Ae i) \<inter> (T p)) = 2" by auto
      qed
      ultimately show "P.prob (Ae i \<inter> \<Inter> (Ae ` J)) = P.prob (Ae i) * P.prob (\<Inter> (Ae ` J))" 
        using prob by simp
    qed
  qed
  then show ?thesis using P.MU_def by auto
qed

lemma intersect_empty_set_size: 
  assumes "\<And> e . e \<in>#E \<Longrightarrow> size {# f \<in># (E - {#e#}) . f \<inter> e \<noteq> {}#} \<le> d"
  assumes "e2 \<in># E"
  shows "size {#e \<in># E . e \<inter> e2 = {} #} \<ge> size E - d - 1" (is "size ?S' \<ge> size E - d - 1")
proof -
  have a1alt: "\<And> e . e \<in>#E \<Longrightarrow> size {# f \<in># E . f \<inter> e \<noteq> {}#} \<le> d + 1"
    using edge_intersect_count_inc assms(1) block_intersect_count_def by force 
  have "E = ?S' + {#e \<in># E. e \<inter> e2 \<noteq> {}#}" by auto
  then have "size E = size ?S' + size {#e \<in># E. e \<inter> e2 \<noteq> {}#}"
    by (metis size_union) 
  then have "size ?S' = size E - size {#e \<in># E. e \<inter> e2 \<noteq> {}#}" by simp
  moreover have "size {#e \<in># E . e \<inter> e2 \<noteq> {} #} \<le> d + 1" using a1alt assms(2) by auto
  ultimately show ?thesis by auto
qed

subsection \<open>Application Property B \<close>
text \<open>Probabilistic framework clearly notated \<close>

proposition erdos_propertyB_LLL: 
  assumes "\<And> e. e \<in>#E \<Longrightarrow> card e \<ge> k"
  assumes "\<And> e . e \<in>#E \<Longrightarrow> size {# f \<in># (E - {#e#}) . f \<inter> e \<noteq> {}#} \<le> d"
  assumes "exp(1)*(d+1) \<le> (2 powi (k - 1))"
  assumes "k > 0"
  shows "has_property_B"
proof -
  \<comment> \<open> 1 set up probability space \<close>
  interpret P: vertex_colour_space \<V> E 2 (* Reuse set up *)
    by unfold_locales (auto simp add: order_ge_two)
  let ?N = "{0..<size E}"
  obtain id where ideq: "image_mset id (mset_set ?N) = E" and idin: "id \<in> ?N \<rightarrow>\<^sub>E set_mset E"
    using obtain_function_on_ext_funcset[of "?N" E] by auto
  then have iedge: "\<And>i. i \<in> ?N \<Longrightarrow> id i \<in># E" by auto
  \<comment> \<open>2 define event \<close>
  define Ae where "Ae \<equiv> \<lambda> i. {f \<in> \<C>\<^sup>2 . mono_edge f (id i)}"
  \<comment> \<open> (3)  Prove each event A is mutually independent of all other mono events for other 
    edges that don't intersect. \<close>
  have "0 < P.prob (\<Inter>Ai\<in>?N. space P.MU - Ae Ai)"
  proof (intro P.lovasz_local_symmetric[of ?N Ae d "(1/(2 powi (k-1)))"])  
    have mis: "\<And>i . i \<in> ?N \<Longrightarrow> P.mutual_indep_events (Ae i) Ae ({j \<in>?N . (id j \<inter> id i) = {}})"
      using disjoint_set_is_mutually_independent[of _ id Ae] P.MU_def assms idin by (simp add: Ae_def) 
    then show "\<And> i . i \<in> ?N \<Longrightarrow> \<exists> S. S \<subseteq> ?N - {i} \<and> card S \<ge> card ?N - d - 1 \<and> 
      P.mutual_indep_events (Ae i) Ae S"
    proof -
      fix i assume iin: "i \<in> ?N"
      define S' where "S' \<equiv> {j \<in> ?N.  (id j)  \<inter> (id i) = {}}"
      then have "S' \<subseteq> ?N - {i}" using iedge assms(1) using blocks_nempty iin by auto
      moreover have "P.mutual_indep_events (Ae i) Ae S'" using mis iin S'_def by simp
      moreover have "card S' \<ge> card ?N - d - 1"
        unfolding S'_def using function_map_multi_filter_size[of id ?N E "\<lambda> e . e \<inter> (id i) = {}"] 
          ideq intersect_empty_set_size[of d "id i"] iin iedge assms(2) by auto
      ultimately show "\<exists> S. S \<subseteq> ?N - {i} \<and> card S \<ge> card ?N - d - 1 \<and> P.mutual_indep_events (Ae i) Ae S"
        by blast
    qed
    show "\<And> i. i \<in> ?N \<Longrightarrow> P.prob(Ae i) \<le> 1/(2 powi (k-1))" 
      unfolding Ae_def using P.prob_monochromatic_edge_bound[of _ k] iedge assms(4) assms(1) by auto
    show "exp(1) * (1 / 2 powi int (k - 1)) * (d + 1) \<le> 1"
      using assms(3) by (simp add: field_simps del:One_nat_def)
      (metis Num.of_nat_simps(2) assms(4) diff_is_0_eq diff_less less_one of_nat_diff power_int_of_nat)
  qed (auto simp add: Ae_def E_nempty P.sets_eq P.space_eq)
  \<comment> \<open> 4 obtain \<close>
  then obtain f where fin: "f \<in> \<C>\<^sup>2" and "\<And> i. i \<in> ?N \<Longrightarrow> \<not> mono_edge f (id i)" using  Ae_def 
    P.obtain_intersection_prop[of Ae ?N "\<lambda> f i. mono_edge f (id i)"] P.space_eq P.sets_eq by auto
  then have "\<And> e. e \<in># E \<Longrightarrow> \<not> mono_edge f e"
    using  ideq mset_set_implies[of id ?N E "\<lambda> e. \<not> mono_edge f e"] by blast
  then show ?thesis unfolding is_n_colourable_def  
    using is_proper_colouring_alt2 fin all_n_vertex_colourings_def[of 2] by auto
qed

end


subsection \<open>Application Corollary \<close>
text \<open>A corollary on hypergraphs where k \ge 9\<close>

lemma exp_ineq_k9: 
  fixes k:: nat
  assumes "k \<ge> 9" 
  shows "exp(1::real) * (k *(k -1) + 1) < 2^(k-1)"
  using assms
proof (induct k rule: nat_induct_at_least)
  case base
  show ?case using exp_le by auto
next
  case (Suc n)
  have "Suc n * (Suc n - 1) + 1 = n * (n - 1) + 1 + 2*n" by (simp add: algebra_simps power2_eq_square)
  then have "exp (1::real) * (Suc n * (Suc n - 1) + 1) = exp 1 * (n * (n - 1) + 1) + exp 1 * 2*n" 
    by (simp add: field_simps)
  moreover have "exp (1::real) * (n * (n - 1) + 1) < 2^(n-1)" using Suc.hyps by simp
  moreover have "exp (1:: real) * 2*n \<le> exp (1::real) * (n * (n - 1) + 1)" 
  proof -
    have "2*n \<le> (n * (n - 1) + 1)" using Suc.hyps(1) Groups.mult_ac(2) diff_le_mono mult_le_mono1 
        nat_le_linear numeral_Bit1 numerals(1) ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add 
      by (metis (no_types, opaque_lifting) Suc_eq_plus1 not_less_eq_eq numeral_Bit0 trans_le_add1) 
    then have "2 * real n \<le> real (n * (n - 1) + 1)" using Suc.hyps by linarith 
    then show ?thesis using exp_gt_one[of "1::real"] by simp
  qed
  moreover have "2 ^ (Suc n - 1) = 2 * 2^(n-1)"
    by (metis Nat.le_imp_diff_is_add Suc(1) add_leD1 cross3_simps(8) diff_Suc_1 eval_nat_numeral(3) 
        power.simps(2) semiring_norm(174)) 
  ultimately show ?case by (smt (verit))
qed

context fin_kuniform_regular_hypgraph_nt
begin

text \<open>Good example of a combinatorial counting proof in a formal environment \<close>

lemma (in fin_dregular_hypergraph) hdeg_remove_one:
  assumes "e \<in># E"
  assumes "v \<in># mset_set e"
  shows "size {# f \<in># (E - {#e#}) . v \<in> f#} = d - 1"
proof -
  have "v \<in> e"
    using assms by (meson count_mset_set(3) not_in_iff) 
  then have vvertex: "v \<in> \<V>" using wellformed[of e] assms(1) by auto 
  then have "{# f \<in># (E - {#e#}) . v \<in> f#} = {# f \<in># E . v \<in> f#} - {#e#}"
    by (simp add: diff_union_cancelR assms(1) finite_blocks)
  then have "size {# f \<in># (E - {#e#}) . v \<in> f#} = size {# f \<in># E . v \<in> f#} - 1"
    by (metis \<open>v \<in># mset_set e\<close> count_eq_zero_iff count_mset_set(3) assms(1) multiset_remove1_filter 
        size_Diff_singleton union_iff union_single_eq_member)
  moreover have "size {# f \<in># E . v \<in> f#} = d" 
    using hdegree_def const_degree vvertex by auto
  ultimately show "size {# f \<in># (E - {#e#}) . v \<in> f#} =  d - 1" by simp
qed

lemma max_intersecting_edges:
  assumes "e \<in># E"
  shows "size {# f \<in># (E - {#e#}) . f \<inter> e \<noteq> {}#} \<le> k * (k -1)"
proof -
  have eq: "{# f \<in># (E - {#e#}) . f \<inter> e \<noteq> {}#} \<subseteq># (\<Sum> v \<in># (mset_set e) . {#f \<in># (E - {#e#}) . v \<in> f #})"
  proof (intro mset_subset_eq_elemI)
    fix a assume  "a \<in># {#f \<in># remove1_mset e E. f \<inter> e \<noteq> {}#}" (is "a \<in># ?E'")
    then have ain: "a \<in># remove1_mset e E" and "a \<inter> e \<noteq> {}"
      using mset_obtain_from_filter by fast+
    then obtain v where "v \<in> a" and "v \<in> e" by blast
    then have  vvertex: "v \<in> \<V>" using wellformed[of e] assms(1) by auto
    have "count ?E' a \<le> count {#f \<in># E - {#e#}. v \<in> f #} a"
      by (metis  \<open>a \<in># ?E'\<close> \<open>v \<in> a\<close> count_filter_mset le_eq_less_or_eq mset_obtain_from_filter(2))
    moreover have "count {#f \<in># E - {#e#}. v \<in> f #} a \<le> 
        (\<Sum> v \<in># (mset_set e) . count {#f \<in># (E - {#e#}) . v \<in> f #} a)"
      by (metis \<open>v \<in> e\<close> assms(1) finite_blocks finite_set_mset_mset_set sum_image_mset_mono_mem)      
    moreover have "count (\<Sum> v \<in># (mset_set e) . {#f \<in># (E - {#e#}) . v \<in> f #}) a = 
        (\<Sum> v \<in># (mset_set e) . count {#f \<in># (E - {#e#}) . v \<in> f #} a)"
      using count_sum_mset2 by fast
    ultimately show "count ?E' a \<le> count (\<Sum>v\<in>#mset_set e. filter_mset ((\<in>) v) (remove1_mset e E)) a"
      by linarith
  qed
  have "size (mset_set e) = k"
    using uniform assms(1) by auto
  then have "size (\<Sum> v \<in># (mset_set e) . {#f \<in># (E - {#e#}) . v \<in> f #}) = k * (k - 1)"
    using size_big_union_sum2_const[of "mset_set e" "\<lambda> v .{#f \<in># (E - {#e#}) . v \<in> f #}" "k - 1"] 
      hdeg_remove_one assms(1) by fast 
  then show ?thesis 
    using eq by (metis size_mset_mono) 
qed

corollary erdos_propertyB_LLL9:
  assumes "k \<ge> 9"
  shows "has_property_B"
proof -
  define d where "d = k*(k-1)"   
  have "\<And> e. e \<in># E \<Longrightarrow> card e \<ge> k" 
    using uniform by simp
  moreover have "\<And> e . e \<in># E \<Longrightarrow> size {# f \<in># (E - {#e#}) . f \<inter> e \<noteq> {}#} \<le> d"
    using max_intersecting_edges d_def by simp   
  moreover have "exp(1)*(d+1) < (2 powi ( k - 1))"
    unfolding d_def using exp_ineq_k9 assms(1) by simp
  moreover have "k > 0" using assms by auto
  ultimately show ?thesis using erdos_propertyB_LLL[of k d] assms
    using int_ops(1) int_ops(2) int_ops(6) less_eq_real_def nat_less_as_int by auto 
qed


end

end
