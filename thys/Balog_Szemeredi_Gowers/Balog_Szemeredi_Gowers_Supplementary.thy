section\<open>Supplementary results related to intermediate lemmas used in the proof of the
 Balog--Szemer\'{e}di--Gowers Theorem\<close>


(*
  Session: Balog_Szemeredi_Gowers
  Title: Balog_Szemeredi_Gowers_Supplementary.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds 
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Balog_Szemeredi_Gowers_Supplementary
  imports 
    Balog_Szemeredi_Gowers_Main_Proof
begin

context additive_abelian_group

begin

text\<open>Even though it is not applied anywhere in this development, for the sake of completeness we give 
the following analogous version of Lemma 2.17 (@{term popular_differences_card}) but for popular sums 
instead of popular differences. The proof is identical to that of Lemma 2.17, with the obvious 
modifications.\<close>

lemma popular_sums_card: 
  fixes A::"'a set" and c::real
  assumes "finite A" and "additive_energy A = 2 * c" and "A \<subseteq> G"
  shows "card (popular_sum_set c A) \<ge> c * card A" 

proof(cases "card A \<noteq> 0")
  assume hA: "card A \<noteq> 0"
  have hc: "c \<ge> 0" using assms additive_energy_def of_nat_0_le_iff 
    by (smt (verit, best) assms(3) divide_nonneg_nonneg of_nat_0_le_iff)
  have "(2 * c) * (card A)^3 = (\<Sum>d \<in> (sumset A A). (f_sum d A)^2)" 
    using assms f_sum_card_quadruple_set_additive_energy by auto
  also have "...= ((\<Sum>d \<in> (popular_sum_set c A). (f_sum d A)^2))
    +((\<Sum> d \<in> ((sumset A A) - (popular_sum_set c A)). (f_sum d A)^2))" 
    using popular_sum_set_def assms finite_sumset by (metis (no_types, lifting) 
      add.commute mem_Collect_eq subsetI sum.subset_diff)
  also have "... \<le> ((card (popular_sum_set c A)) * (card A)^2)
    + c * card A * ((\<Sum>d \<in> (sumset A A - (popular_sum_set c A)) . (f_sum d A)))" 
  proof-
    have "\<forall> d \<in> ((sumset A A) - (popular_sum_set c A)) . (f_sum d A)^2 \<le> 
      (c * (card A)) * (f_sum d A)"
    proof
     fix d assume hd1: "d \<in> sumset A A - popular_sum_set c A"
     have hnonneg: "f_sum d A \<ge> 0" by auto
     have "\<not> popular_sum d c A" using hd1 popular_sum_set_def by blast
     from this have "f_sum d A \<le> c * card A" using popular_sum_def by auto
     thus "real ((f_sum d A)\<^sup>2) \<le> c * real (card A) * real (f_sum d A)" 
       using power2_eq_square hnonneg mult_right_mono of_nat_0 of_nat_le_iff of_nat_mult by metis
   qed
   moreover have "\<forall> d \<in> (sumset A A) . f_sum d A \<le> (card A)^2" 
     using f_sum_def finite_sumset assms
     by (metis f_sum_le_card le_antisym nat_le_linear power2_nat_le_imp_le)
   ultimately have "((\<Sum>d \<in> ((sumset A A) - popular_sum_set c A) . (f_sum d A)^2)) \<le> 
     ((\<Sum>d \<in> ((sumset A A) - popular_sum_set c A). (c * card A) * (f_sum d A)))"
     using assms finite_sumset sum_distrib_left sum_mono by fastforce
   then have "((\<Sum>d \<in> ((sumset A A) - popular_sum_set c A) . (f_sum d A)^2)) \<le>  
     (c * card A) * ((\<Sum>d \<in> ((sumset A A) - popular_sum_set c A) . (f_sum d A)))"
     by (metis (no_types) of_nat_sum sum_distrib_left)
   moreover have "(\<Sum>d \<in> popular_sum_set c A. (f_sum d A)^2) \<le> 
    (\<Sum>d \<in> popular_sum_set c A. (card A)^2)" using f_sum_le_card assms sum_mono assms popular_sum_set_def
     by (metis (no_types, lifting) power2_nat_le_eq_le)
   moreover then have "(\<Sum>d \<in> popular_sum_set c A . (f_sum d A)^2) \<le> 
    (card (popular_sum_set c A)) * (card A)^2" 
    using sum_distrib_right by simp
    ultimately show ?thesis by linarith
  qed
  also have "...  \<le> ((card (popular_sum_set c A)) * (card A)^2) + (c * card A) * (card A)^2" 
  proof-
    have "(\<Sum>d \<in> (sumset A A - popular_sum_set c A) . (f_sum d A)) \<le>
      (\<Sum>d \<in> sumset A A . (f_sum d A))" using DiffD1 subsetI assms sum_mono2 
      finite_sumset zero_le by metis
    then have "(c * card A) * ((\<Sum>d \<in> (sumset A A - popular_sum_set c A). (f_sum d A))) 
      \<le> (c * card A) * (card A)^2" 
      using f_sum_card hc le0 mult_left_mono of_nat_0 of_nat_mono zero_le_mult_iff assms by metis
    then show ?thesis by linarith 
  qed
  finally have "(2 * c) * (card A)^3  \<le> ((card (popular_sum_set c A)) * (card A)^2) + 
    (c * card A) * (card A)^2" by linarith
  then have "(card (popular_sum_set c A)) \<ge>
    ((2 * c)* (card A)^3 - (c * card A) * (card A)^2)/((card A)^2)"
    using hA by (simp add: field_simps)
  moreover have "((2 * c)* (card A)^3 - (c * card A) * (card A)^2)/((card A)^2) = 2 * c * card A - c * card A" 
    using hA by (simp add: power2_eq_square power3_eq_cube)
  ultimately show ?thesis by linarith
next
  assume "\<not> card A \<noteq> 0"
  thus ?thesis by auto
qed


text\<open>The following is an analogous version of lemma @{term obtains_subsets_differenceset_card_bound}
(2.18 in Gowers's notes \cite{Gowersnotes}) but for a sumset instead of a difference set. It is not used anywhere in this 
development but we provide it for the sake of completeness. The proof is identical to that of 
lemma @{term obtains_subsets_differenceset_card_bound} with @{term f_diff} changed to @{term f_sum}, 
@{term popular_diff} changed to @{term popular_sum}, \oplus interchanged with \ominus, and instead of 
lemma @{term popular_differences_card} we apply its analogous version for popular sums, that is 
lemma @{term popular_sums_card}. \<close>

lemma obtains_subsets_sumset_card_bound: fixes A::"'a set" and c::real 
  assumes "finite A"  and "c>0"  and "A \<noteq> {}" and "A \<subseteq> G" and "additive_energy A = 2 * c"
  obtains B and A' where "B \<subseteq> A" and "B \<noteq> {}" and "card B \<ge> c^4 * card A / 16"
  and "A' \<subseteq> A" and "A' \<noteq> {}" and "card A' \<ge> c^2 * card A / 4"
  and "card (sumset A' B) \<le> 2^13 * card A / c^15"

proof-
  let ?X = "A \<times> {0:: nat}"
  let ?Y = "A \<times> {1:: nat}"
  let ?E = "mk_edge ` {(x, y)| x y. x \<in> ?X \<and> y \<in> ?Y \<and> (popular_sum (fst y \<oplus> fst x) c A)}"
  interpret H: fin_bipartite_graph "?X \<union> ?Y" ?E ?X ?Y
  proof (unfold_locales, auto simp add: partition_on_def assms(3) assms(1) disjoint_def)
    show "{} = A \<times> {0} \<Longrightarrow> False" using assms(3) by auto
  next
    show "{} = A \<times> {Suc 0} \<Longrightarrow> False" using assms(3) by auto
  next
    show "A \<times> {0} = A \<times> {Suc 0} \<Longrightarrow> False" using assms(3) by fastforce
  next
    fix x y assume "x \<in> A" and "y \<in> A" and "popular_sum (y \<oplus> x) c A"
    thus "{(x, 0), (y, Suc 0)} \<in> all_bi_edges (A \<times> {0}) (A \<times> {Suc 0})" 
      using all_bi_edges_def[of "A \<times> {0}" "A \<times> {Suc 0}"]
      by (simp add: in_mk_edge_img)
  qed
  have edges1: "\<forall> a \<in> A. \<forall> b \<in> A. ({(a, 0), (b, 1)} \<in> ?E \<longleftrightarrow> popular_sum (b \<oplus> a) c A)"
    by (auto simp add: in_mk_uedge_img_iff)
  have hXA: "card A = card ?X" by (simp add: card_cartesian_product)
  have hYA: "card A = card ?Y" by (simp add: card_cartesian_product) 
  have hA: "card A \<noteq> 0" using assms card_0_eq by blast
  have edge_density: "H.edge_density ?X ?Y \<ge> c^2"
  proof-
    define f:: "'a \<Rightarrow> ('a \<times> nat) edge set" where "f \<equiv> (\<lambda> x. {{(a, 0), (b, 1)} | a b. 
      a \<in> A \<and> b \<in> A \<and> b \<oplus> a = x})"
    have f_disj: "pairwise (\<lambda> s t. disjnt (f s) (f t)) (popular_sum_set c A)" 
    proof (intro pairwiseI)
      fix x y assume hx: "x \<in> popular_sum_set c A" and hy: "y \<in> popular_sum_set c A" 
        and hxy: "x \<noteq> y" 
      show "disjnt (f x) (f y)"
      proof-
        have "\<forall>a. \<not> (a \<in> f x \<and> a \<in> f y)"
        proof (intro allI notI)
          fix a assume "a \<in> f x \<and> a \<in> f y"
          then obtain z w where hazw: "a = {(z, 0), (w, 1)}" and hx: "{(z,0), (w, 1)} \<in> f x"
            and hy: "{(z, 0), (w, 1)} \<in> f y" using f_def by blast
          have "w \<oplus> z = x" using f_def hx by (simp add: doubleton_eq_iff)
          moreover have "w \<oplus> z = y" using f_def hy by (simp add: doubleton_eq_iff)
          ultimately show "False" using hxy by auto
        qed
        thus ?thesis using disjnt_iff by auto
      qed
    qed
    have f_sub_edges: "\<forall> d \<in> popular_sum_set c A. (f d) \<subseteq> ?E"
      using popular_sum_set_def f_def edges1 by auto
    have f_union_sub: "(\<Union> d \<in> popular_sum_set c A. (f d)) \<subseteq> ?E" using popular_sum_set_def 
      f_def edges1 by auto
    have f_disj2: "disjoint (f ` (popular_sum_set c A))" using f_disj 
      pairwise_image[of "disjnt" "f" "popular_sum_set c A"] by (simp add: pairwise_def) 
    have f_finite: "\<And>B. B \<in> f ` popular_sum_set c A \<Longrightarrow> finite B"
      using finite_subset f_sub_edges H.fin_edges by auto
    have card_eq_f_diff: "\<forall> d \<in> popular_sum_set c A. card (f d) = f_sum d A"
    proof
      fix d assume "d \<in> popular_sum_set c A"
      define g:: "('a \<times> 'a) \<Rightarrow> ('a \<times> nat) edge" where "g = (\<lambda> (a, b). {(b, 0), (a, 1)})"
      have g_inj: "inj_on g {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}"
      proof (intro inj_onI)
        fix x y assume "x \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}" and 
          "y \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}" and hg: "g x = g y"
        then obtain a1 a2 b1 b2  where hx: "x = (a1, a2)" and hy: "y = (b1, b2)"  by blast
        thus "x = y" using g_def hg hx hy by (simp add: doubleton_eq_iff)
      qed
      have g_image: "g ` {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d} = f d" using f_def g_def by auto
      show "card (f d) = f_sum d A" using card_image g_inj g_image f_sum_def by fastforce 
    qed
    have "c ^ 2 * (card A) ^ 2 = c * (card A) * (c * (card A))" using power2_eq_square
      by (metis of_nat_power power_mult_distrib)
    also have "... \<le> (card (popular_sum_set c A)) * (c * (card A))" 
      using assms  popular_sums_card hA by force
    also have "... \<le> (\<Sum> d \<in> popular_sum_set c A. f_sum d A)" using sum_mono popular_sum_set_def
      popular_sum_def by (smt (verit, ccfv_SIG) mem_Collect_eq of_nat_sum of_real_of_nat_eq 
      sum_constant)  
    also have "... = (\<Sum> d \<in> popular_sum_set c A. card (f d))"
      using card_eq_f_diff sum.cong by auto
    also have "... = sum card (f ` (popular_sum_set c A))"
      using f_disj sum_card_image[of "popular_sum_set c A" "f"] popular_sum_set_def 
        finite_sumset assms(1) finite_subset by auto
    also have "... = card (\<Union> d \<in> popular_sum_set c A. (f d))"
      using card_Union_disjoint[of "f ` (popular_sum_set c A)"] f_disj2 f_finite by auto
    also have "... \<le> card ?E" using card_mono f_union_sub H.fin_edges by auto
    finally have "c ^ 2 * (card A) ^ 2 \<le> card ?E" by linarith
    then have "c ^ 2 * (card A) ^ 2 \<le> card (H.all_edges_between ?X ?Y)"
      using H.card_edges_between_set by auto
    moreover have "H.edge_density ?X ?Y = card (H.all_edges_between ?X ?Y) / (card A) ^ 2" 
      using  H.edge_density_def power2_eq_square hXA hYA
      by (smt (verit, best))
    ultimately have "(c ^ 2 * (card A) ^ 2) / (card A) ^ 2 \<le> H.edge_density ?X ?Y" using hA 
      divide_le_cancel by (smt (verit, del_insts) H.edge_density_ge0 \<open>c\<^sup>2 * real ((card A)\<^sup>2) = 
        c * real (card A) * (c * real (card A))\<close> divide_divide_eq_right zero_le_divide_iff)
    thus ?thesis using hA assms(2) by auto
  qed
  obtain X' and Y' where X'sub: "X' \<subseteq> ?X" and Y'sub: "Y' \<subseteq> ?Y" and
    hX': "card X' \<ge> (H.edge_density ?X ?Y)^2 * (card ?X)/16" and
    hY': "card Y' \<ge> (H.edge_density ?X ?Y) * (card ?Y)/4" and
    hwalks: "\<forall>  x \<in> X'. \<forall> y \<in> Y'. card ({p. H.connecting_walk x y p \<and> H.walk_length p = 3}) \<ge> 
    (H.edge_density ?X ?Y)^6 * card ?X * card ?Y / 2^13"
    using H.walks_of_length_3_subsets_bipartite \<open>c>0\<close> by auto
  have "((c^2)^2) * (card A) \<le> (H.edge_density ?X ?Y)^2 * (card A)"
    using edge_density assms(2) hA power_mono zero_le_power2 mult_le_cancel_right
    by (smt (verit) of_nat_less_of_nat_power_cancel_iff of_nat_zero_less_power_iff 
      power2_less_eq_zero_iff power_0_left)
  then have cardX': "card X' \<ge> (c^4) * (card A)/16" using hX' divide_le_cancel hXA by fastforce
  have "c^2 * (card A) / 4 \<le> (H.edge_density ?X ?Y) * card ?Y / 4" using hYA hA edge_density 
      mult_le_cancel_right by simp
  then have cardY': "card Y' \<ge> c^2 * (card A)/4" using hY' by linarith
  have "(H.edge_density ?X ?Y)^6 * (card ?X * card ?Y)/ 2^13 \<ge> (c^2)^6 * ((card A)^2) / 2^13" using
  hXA hYA power2_eq_square edge_density divide_le_cancel mult_le_cancel_right hA
    by (smt (verit, ccfv_SIG) of_nat_power power2_less_0 power_less_imp_less_base zero_le_power)
  then have card_walks: "\<forall> x \<in> X'. \<forall> y \<in> Y'. 
    card ({p. H.connecting_walk x y p \<and> H.walk_length p = 3}) \<ge> (c^12) * ((card A)^2) / 2^13" 
    using hwalks by fastforce 
  (* ?X and ?Y are subsets of the vertex set, now project down to G, giving subsets ?B and ?C of A,
  respectively*)
  let ?B = "(\<lambda> (a, b). a) ` X'"
  let ?C = "(\<lambda> (a, b). a) ` Y'"
  have hBA: "?B \<subseteq> A" and hCA: "?C \<subseteq> A" using Y'sub X'sub by auto
  have inj_on_X': "inj_on (\<lambda> (a, b). a) X'" using X'sub by (intro inj_onI) (auto)
  have inj_on_Y': "inj_on (\<lambda> (a, b). a) Y'" using Y'sub by (intro inj_onI) (auto)
  have hBX': "card ?B = card X'" and hCY': "card ?C = card Y'"
    using card_image inj_on_X' inj_on_Y' by auto 
  then have cardB: "card ?B \<ge> (c^4) * (card A)/16" and cardC: "card ?C \<ge> c^2 * (card A)/4" 
    using cardX' cardY' by auto
  have card_ineq1: "\<And> x y. x \<in> ?B \<Longrightarrow> y \<in> ?C \<Longrightarrow> card ({(z, w) | z w. z \<in> A \<and> w \<in> A \<and> 
  popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}) \<ge> 
  (c^12) * ((card A)^2) / 2^13"
  proof-
    fix x y assume hx: "x \<in> ?B" and hy: "y \<in> ?C"
    have hxA: "x \<in> A" and hyA: "y \<in> A" using hx hy hBA hCA by auto
    define f:: "'a \<times> 'a \<Rightarrow> ('a \<times> nat) list" 
      where "f \<equiv> (\<lambda> (z, w). [(x, 0), (z, 1), (w, 0), (y, 1)])"
    have f_inj_on: "inj_on f {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and>
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}" using f_def by (intro inj_onI) (auto)
    have f_image: "f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and>
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} = 
      {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
    proof
      show "f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
        popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} \<subseteq> 
        {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
      proof
        fix p assume hp: "p \<in> f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and>
          popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}"
        then obtain z w where hz: "z \<in> A" and hw: "w \<in> A" and hzx: "popular_sum (z \<oplus> x) c A" and 
          hzw: "popular_sum (z \<oplus> w) c A" and hyw: "popular_sum (y \<oplus> w) c A" and 
          hp: "p = [(x, 0), (z, 1), (w, 0), (y, 1)]" using f_def hp by fast
        then have hcon: "H.connecting_walk (x, 0) (y, 1) p"
          unfolding H.connecting_walk_def H.is_walk_def 
          using hxA hyA H.vert_adj_def H.vert_adj_sym edges1 by simp
        thus "p \<in> {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}" 
            using hp H.walk_length_conv by auto
        qed
      next
        show "{p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3} \<subseteq> f ` {(z, w) |z w.
          z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> 
          popular_sum (y \<oplus> w) c A}"
        proof(intro subsetI)
          fix p assume hp: "p \<in> {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
          then have len: "length p = 4" using H.walk_length_conv by auto
          have hpsub: "set p \<subseteq> A \<times> {0} \<union> A \<times> {1}" using hp H.connecting_walk_def H.is_walk_def 
            by auto
          then have fst_sub: "fst ` set p \<subseteq> A" by auto
          have h1A: "fst (p!1) \<in> A" and h2A: "fst (p!2) \<in> A" using fst_sub len by auto
          have hpnum: "p = [p!0, p!1, p!2, p!3]"
          proof (auto simp add:  list_eq_iff_nth_eq len) 
            fix k assume "k < (4:: nat)"
            then have "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3" by auto
            thus "p ! k = [p ! 0, p ! Suc 0, p ! 2, p ! 3] ! k" by fastforce
          qed
          then have "set (H.walk_edges p) = {{p!0, p!1} , {p!1, p!2}, {p!2, p!3}}" using
            comp_sgraph.walk_edges.simps(2) comp_sgraph.walk_edges.simps(3) 
            by (metis empty_set list.simps(15))
          then have h1: "{p!0, p!1} \<in> ?E" and h2: "{p!2, p!1} \<in> ?E" and h3: "{p!2, p!3} \<in> ?E"
            using hp H.connecting_walk_def H.is_walk_def len by auto
          have hxp: "p!0 = (x, 0)" using hp len hd_conv_nth H.connecting_walk_def H.is_walk_def 
            by fastforce 
          have hyp: "p!3 = (y, 1)" using hp len last_conv_nth H.connecting_walk_def H.is_walk_def 
            by fastforce
          have h1p: "p!1 = (fst (p!1), 1)"
          proof-
            have "p!1 \<in> A \<times> {0} \<union> A \<times> {1}" using hpnum hpsub 
              by (metis (no_types, lifting) insertCI list.simps(15) subsetD)
            then have hsplit: "snd (p!1) = 0 \<or> snd (p!1) = 1" by auto
            then have "snd (p!1) = 1"
            proof(cases "snd (p!1) = 0")
              case True
              then have 1: "{(x, 0), (fst (p!1), 0)} \<in> ?E" using h1 hxp doubleton_eq_iff
                by (smt (verit, del_insts) surjective_pairing)
              have hY: "(fst (p!1), 0) \<notin> ?Y" and  hX: "(x, 0) \<in> ?X" using hxA by auto
              then have 2: "{(x, 0), (fst (p!1), 0)} \<notin> ?E" using H.X_vert_adj_Y H.vert_adj_def by meson
              then show ?thesis using 1 2 by blast
            next
              case False
              then show ?thesis using hsplit by auto
            qed
            thus "(p ! 1) = (fst (p ! 1), 1)" 
              by (metis (full_types) split_pairs)
          qed
          have h2p: "p!2 = (fst (p!2), 0)"
          proof-
            have "p!2 \<in> A \<times> {0} \<union> A \<times> {1}" using hpnum hpsub
              by (metis (no_types, lifting) insertCI list.simps(15) subsetD)
            then have hsplit: "snd (p!2) = 0 \<or> snd (p!2) = 1" by auto
            then have "snd (p!2) = 0" 
            proof(cases "snd (p!2) = 1")
              case True
              then have 1: "{(fst (p!2), 1), (y, 1)} \<in> ?E" using h3 hyp doubleton_eq_iff
                by (smt (verit, del_insts) surjective_pairing)
              have hY: "(y, 1) \<notin> ?X" and hX: "(fst (p!2), 1) \<in> ?Y" using hyA h2A by auto
              then have 2: "{(fst (p!2), 1), (y, 1)} \<notin> ?E" using H.Y_vert_adj_X H.vert_adj_def
                by meson
              then show ?thesis using 1 2 by blast
            next
              case False
              then show ?thesis using hsplit by auto
            qed
            thus "(p ! 2) = (fst (p ! 2), 0)" 
              by (metis (full_types) split_pairs)
          qed
          have hpop1: "popular_sum ((fst (p!1)) \<oplus> x) c A" using edges1 h1 hxp h1p hxA h1A
            by (smt (z3))
          have hpop2: "popular_sum((fst (p!1)) \<oplus> (fst (p!2))) c A" using edges1 h2 h1p h2p h1A h2A
            by (smt (z3))
          have hpop3: "popular_sum (y \<oplus> (fst (p!2))) c A" using edges1 h3 h2p hyp hyA h2A 
            by (smt (z3))
          thus "p \<in> f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and>
            popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}" using f_def hpnum hxp h1p h2p hyp
            h1A h2A hpop1 hpop2 hpop3 by force
        qed
      qed
      have hx1: "(x, 0) \<in> X'" and hy2: "(y, 1) \<in> Y'"  using hx X'sub hy Y'sub by auto
      have "card {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
        popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} = 
        card {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
        using card_image f_inj_on f_image by fastforce
      thus "card {(z, w) |z w. z \<in> A \<and> w \<in> A \<and>  popular_sum (z \<oplus> x) c A \<and> 
        popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} \<ge> c ^ 12 * ((card A)^2) / 2 ^ 13"
        using hx1 hy2 card_walks by auto
    qed
  have "\<And> x x2 y y2 z w . (x, x2) \<in> X'\<Longrightarrow> (y, y2) \<in> Y'\<Longrightarrow>  z \<in> A \<Longrightarrow> w \<in> A 
    \<Longrightarrow> popular_sum (z \<oplus> x) c A \<Longrightarrow> popular_sum (z \<oplus> w) c A \<Longrightarrow> popular_sum (y \<oplus> w) c A \<Longrightarrow> 
    c ^ 3 * real (card A) ^ 3 \<le>
    (card {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
    p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w})"
  proof -
    fix x x2 y y2 z w assume "(x, x2) \<in> X'" and "(y, y2) \<in> Y'" and "z \<in> A" and "w \<in> A" and
      1: "popular_sum (z \<oplus> x) c A" and 2: "popular_sum (z \<oplus> w) c A" and 
      3: "popular_sum (y \<oplus> w) c A"
    define f:: "'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> ('a \<times> 'a) \<times> ('a \<times> 'a) \<times> ('a \<times> 'a)" where
      "f \<equiv> (\<lambda> (p, q, r, s, t, u). ((p, q), (r, s), (t, u)))"
    (* Types ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) and  ('a \<times> 'a) \<times> ('a \<times> 'a) \<times> ('a \<times> 'a) are not
    definitionally equal, so we need to define a bijection between them *)
    have f_inj: "inj_on f {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
      t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}" using f_def 
      by (intro inj_onI) (auto) 
    have f_image: "f ` {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
      t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w} = 
      {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x} \<times> 
      {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> w} \<times> 
      {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = y \<oplus> w}" using f_def by force 
    (* warning: this proof takes a while *)
    have 4: "card {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
      t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus>  w \<and> t \<oplus> u = y \<oplus> w} = 
      card ({(p, q). p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x} \<times>
      {(p, q). p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> w} \<times> {(p, q). p \<in> A \<and> q \<in> A \<and> p \<oplus> q = y \<oplus> w})" 
      using card_image f_inj f_image by fastforce
    moreover have 5: "card ({(p, q). p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x} \<times>
      {(p, q). p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> w} \<times> {(p, q). p \<in> A \<and> q \<in> A \<and> p \<oplus> q = y \<oplus> w}) =
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x} *
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> w} * 
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = y \<oplus> w}"
      using card_cartesian_product3 by auto
    have "c * card A \<le> card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x}" 
      using 1 popular_sum_def f_sum_def by auto
    then have "(c * card A) * (c * card A) \<le> card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x} * 
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> w}" 
      using 2 popular_sum_def f_sum_def mult_mono assms(2) mult_nonneg_nonneg 
        of_nat_0_le_iff of_nat_mult by fastforce
    then have 6: "(c * card A) * (c * card A) * (c * card A) \<le> card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> x} * 
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = z \<oplus> w} * 
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<oplus> q = y \<oplus> w}"
      using 3 popular_sum_def f_sum_def mult_mono assms(2) mult_nonneg_nonneg of_nat_0_le_iff 
      of_nat_mult by fastforce
    have 7: "c ^ 3 * card A ^ 3 = (c * card A) * ((c * card A) * (c * card A))" 
      by (simp add: power3_eq_cube algebra_simps)
    show "c ^ 3 * real (card A) ^ 3 \<le>
      (card {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
      p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w})" using 4 5 6 7 by auto
  qed
  then have card_ineq2: "\<And> x y z w. x \<in> ?B \<Longrightarrow> y \<in> ?C \<Longrightarrow> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> 
    popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} \<Longrightarrow>
    card {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
    p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w} \<ge> c^3 * card A^3"
    by auto
  have card_ineq3: "\<And> x y.  x \<in> ?B \<Longrightarrow> y \<in> ?C \<Longrightarrow> card (\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> 
    popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) \<ge> 
    c ^ 15 * ((card A)^5) / 2 ^ 13"
  proof-
    fix x y assume hx: "x \<in> ?B" and hy: "y \<in> ?C"
    have hxG: "x \<in> G" and hyG: "y \<in> G" using hx hy hBA hCA assms(4) by auto
    let ?f = "(\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w})"
    have hpair_disj: "pairwise (\<lambda> a b. disjnt (?f a) (?f b)) 
      {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and>
      popular_sum (y \<oplus> w) c A}" 
      proof (intro pairwiseI)
      fix a b assume "a \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
       popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}" "b \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and>
       popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}" and 
       "a \<noteq> b" 
      then obtain a1 a2 b1 b2 where ha: "a = (a1, a2)" and hb: "b = (b1, b2)" and ha1: "a1 \<in> G" and 
        ha2: "a2 \<in> G" and hb1: "b1 \<in> G" and hb2: "b2 \<in> G" and hne: "(a1, a2) \<noteq> (b1, b2)" 
        using assms(4) by blast
      have "(\<forall>x. \<not> (x \<in> (?f a) \<and> x \<in> (?f b)))"
      proof(intro allI notI)
        fix d assume "d \<in> (?f a) \<and> d \<in> (?f b)"
        then obtain p q r s t u where "d = (p, q, r, s, t, u)" and hpq1: "p \<oplus> q = a1 \<oplus> x" and 
          htu1: "t \<oplus> u = y \<oplus> a2" and hpq2: "p \<oplus> q = b1 \<oplus> x" and htu2: "t \<oplus> u = y \<oplus> b2" 
          using ha hb by auto
        then have "y \<oplus> a2 = y \<oplus> b2" using htu1 htu2 by auto
        then have 2: "a2 = b2" using ha2 hb2 hyG by (metis invertible invertible_left_cancel)
        have 1: "a1 = b1" using hpq1 hpq2 ha1 hb1 hxG by simp
        show "False" using 1 2 hne by auto
      qed
      thus "disjnt (?f a) (?f b)" using disjnt_iff[of "(?f a)" "(?f b)"] by auto
    qed
    have hfinite_walks: "\<And> B. B \<in> ((\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) ` 
      {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and>
      popular_sum (y \<oplus> w) c A}) \<Longrightarrow> finite B"
    proof-
      fix B assume "B \<in> ((\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
        r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) ` 
        {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and>
        popular_sum (y \<oplus> w) c A})"
      then have "B \<subseteq> A \<times> A \<times> A \<times> A \<times> A \<times> A" by auto
      thus "finite B" using assms(1)
        by (auto simp add: finite_subset)
    qed
    have hdisj: "disjoint ((\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) ` 
      {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and>
      popular_sum (y \<oplus> w) c A})" using hpair_disj pairwise_image[of "disjnt" "(\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w})" 
      "{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and>
      popular_sum (y \<oplus> w) c A}"] by (simp add: pairwise_def)
    have "{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} \<subseteq> A \<times> A" by auto
    then have hwalks_finite: "finite {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}" using finite_subset assms(1) 
      by fastforce
    have f_ineq: "\<forall> a \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. c ^ 3 * (card A) ^ 3 \<le>
      card (?f a)" using card_ineq2 hx hy by auto
    have "c ^ 15 * ((card A)^5) / 2 ^ 13 = (c ^ 12 * (card A) ^ 2 / 2 ^ 13) *  (c ^ 3 * card A ^ 3)"
      by (simp add: algebra_simps)
      also have "... \<le> card {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A} * (c ^ 3 * (card A) ^ 3)" 
        using card_ineq1[of "x" "y"] hx hy mult_le_cancel_right hA by (smt (verit, best) assms(2) 
        mult_pos_pos of_nat_0_less_iff of_nat_le_0_iff zero_less_power)
    also have "...  = (\<Sum> a \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. (c ^ 3 * (card A) ^ 3))" by auto
    also have "... \<le> (\<Sum>a\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. card (?f a))"
      using sum_mono f_ineq by (smt (verit, del_insts) of_nat_sum) 
    also have "... = sum card (?f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and>
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A})"
      using sum_card_image[of "{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}" "?f"] hpair_disj hwalks_finite by auto
    also have "... = card (\<Union> (z, w)\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and>
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> 
      t \<oplus> u = y \<oplus> w})" using card_Union_disjoint hdisj hfinite_walks by (metis (no_types, lifting))
    finally show "c ^ 15 * real (card A ^ 5) / 2 ^ 13 \<le> real (card (\<Union>(z, w)\<in>{(z, w) |z w.
     z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> 
     popular_sum (y \<oplus> w) c A}. {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
     s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}))" by simp
  qed
  have pos: "0 < c ^ 15 * real (card A ^ 5) / 2 ^ 13" using hA \<open>c>0\<close> by auto
  have "(5:: nat) \<le> 6" by auto
  then have "(card A ^ 6 / card A ^ 5) = (card A) ^ (6 - 5)" 
    using hA power_diff by (metis of_nat_eq_0_iff of_nat_power)
  then have cardApow: "(card A ^ 6 / card A ^ 5) = card A" using power_one_right by simp
  have hdsub: "\<forall> d \<in> sumset ?C ?B. \<exists> y \<in> ?C. \<exists> x \<in> ?B.
    (\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
    popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) 
    \<subseteq> {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}"
  proof
    fix d assume "d \<in> sumset ?C ?B"
    then obtain y x where hy: "y \<in> ?C" and hx: "x \<in> ?B" and hxy: "d = y \<oplus> x" 
      using sumset_def minusset_def hBA hCA assms(4) subset_trans
      by (smt (verit, best) minusset.simps sumset.cases)
    have hxG: "x \<in> G" and hyG: "y \<in> G" using hx hy hBA hCA assms(4) by auto
    have "(\<Union>(z, w)\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w})
      \<subseteq> {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
      d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}"
    proof (rule Union_least)
      fix X assume "X \<in> (\<lambda>(z, w). {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> 
      t \<oplus> u = y \<oplus> w}) ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
      popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}"
      then obtain z w where hX: "X = {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> 
        s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}"
        and hz: "z \<in> A" and hw: "w \<in> A" by auto
      have hzG: "z \<in> G" and hwG: "w \<in> G" using hz hw assms(4) by auto
      have "{(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> 
        s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w} \<subseteq> 
        {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
        d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" 
      proof
        fix e assume "e \<in> {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
          t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}"
        then obtain p q r s t u where "p \<oplus> q = z \<oplus> x" and "r \<oplus> s = z \<oplus> w" and "t \<oplus> u = y \<oplus> w"
          and hp: "p \<in> A" and hq: "q \<in> A" and hr: "r \<in> A" and hs: "s \<in> A" and ht: "t \<in> A" 
          and hu: "u \<in> A" and he: "e = (p, q, r, s, t, u)" by blast
        then have "p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u = z \<oplus> x \<ominus> (z \<oplus> w) \<oplus> y \<oplus> w"
          by (smt (verit, ccfv_threshold) assms(4) associative composition_closed hwG hxG hyG hzG 
              inverse_closed subset_eq)
        also have "... = y \<oplus> x" using hxG hyG hzG hwG
          by (smt (verit) associative commutative composition_closed inverse_closed invertible
              invertible_right_inverse2)
        finally have "d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u" using hxy by simp
        thus "e \<in> {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> 
          u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" using he hp hq hr hs ht hu by auto
      qed
      thus "X \<subseteq> {(p, q, r, s, t, u) |p q r s t u.
               p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" 
        using hX by auto
    qed
    thus "\<exists>y\<in>(\<lambda>(a, b). a) ` Y'. \<exists>x\<in>(\<lambda>(a, b). a) ` X'. (\<Union>(z, w)\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> 
      popular_sum (z \<oplus> x) c A \<and> popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}.
      {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
      p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) \<subseteq> {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" 
      using hx hy by meson
  qed
  moreover have "\<forall> d \<in> sumset ?C ?B. card {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and>
    r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u} \<ge> c ^ 15 * (card A) ^ 5 / 2 ^13"
  proof
    fix d assume "d \<in> sumset ((\<lambda>(a, b). a) ` Y') ((\<lambda>(a, b). a) ` X')"
    then obtain x y where hy: "y \<in> ?C" and hx: "x \<in> ?B" and hsub: 
    "(\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
    popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w}) 
    \<subseteq> {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" using hdsub by meson
    have "{(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u} \<subseteq> A \<times> A \<times> A \<times> A \<times> A \<times> A" by auto
    then have fin: "finite {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
      s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" 
      using finite_subset assms(1) finite_cartesian_product by fastforce
    have "c ^ 15 * (card A) ^ 5 / 2 ^13 \<le> card (\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> popular_sum (z \<oplus> x) c A \<and> 
    popular_sum (z \<oplus> w) c A \<and> popular_sum (y \<oplus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<oplus> q = z \<oplus> x \<and> r \<oplus> s = z \<oplus> w \<and> t \<oplus> u = y \<oplus> w})" 
      using card_ineq3 hx hy by auto
    also have "... \<le> card {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" 
      using hsub card_mono fin by auto 
    finally show "c ^ 15 * (card A) ^ 5 / 2 ^13 \<le> card {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}" by linarith
  qed
  moreover have "pairwise (\<lambda> s t. disjnt ((\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and>  s \<in> A \<and>  t \<in> A \<and>  u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}) s) 
    ((\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and>  s \<in> A \<and>  t \<in> A \<and>  u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u}) t)) (sumset ?C ?B)" 
    unfolding disjnt_def by (intro pairwiseI) (auto)
  moreover have "\<forall> d \<in> sumset ?C ?B. ((\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and>  s \<in> A \<and>  t \<in> A \<and>  u \<in> A \<and> (d = p \<oplus> q \<oplus> r \<oplus>  s \<oplus>  t \<oplus> u)}) d) \<subseteq> A \<times> A \<times> A \<times> A \<times> A \<times> A"
    by blast
  ultimately have "card (sumset ?C ?B) \<le> ((card A) ^ 6) / (c^15 *(card A)^5 /2^13)" 
    using assms(1) hA finite_cartesian_product card_cartesian_product_6[of "A"]
    pos card_le_image_div[of "A \<times> A \<times> A \<times> A \<times> A \<times> A" "(\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<oplus> q \<ominus> (r \<oplus> s) \<oplus> t \<oplus> u})" "sumset ?C ?B" 
    "(c^15 * (card A)^5 /2^13)"] by auto
  also have "... = (card A ^ 6 / card A ^ 5) / (c^15 / 2^13)" 
    using hA assms(3) field_simps by simp
  also have "... = (card A) / (c ^ 15 / 2 ^ 13)"
    using cardApow by metis
  finally have final: "card (sumset ?C ?B) \<le> 2 ^ 13 * (1 / c ^ 15) * real (card A)"
    by argo
  have "0 < c ^ 4 * real (card A) / 16" and "0 < c ^ 2 * real (card A) / 4" using assms(2) hA by auto
  then have "?B \<noteq> {}" and "?C \<noteq> {}" using cardB cardC by auto
  then show ?thesis using hCA hBA cardC cardB final that by auto
qed


end
end