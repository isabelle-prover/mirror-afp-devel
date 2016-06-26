(*  Title:       Functor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Functor

theory Functor
imports Category DualCategory InitialTerminal
begin

  text{*
    One advantage of the ``object-free'' definition of category is that a functor
    from category @{text A} to category @{text B} is simply a function from the type
    of arrows of @{text A} to the type of arrows of @{text B} that satisfies certain
    conditions: namely, that arrows are mapped to arrows, non-arrows are mapped to
    @{text null}, and domains, codomains, and composition of arrows are preserved.
  *}

  locale "functor" =
    A: category A +
    B: category B
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_extensional [simp]: "\<not>A.arr f \<Longrightarrow> F f = B.null"
  and preserves_arr [simp]: "A.arr f \<Longrightarrow> B.arr (F f)"
  and preserves_dom [iff]: "A.arr f \<Longrightarrow> B.dom (F f) = F (A.dom f)"
  and preserves_cod [iff]: "A.arr f \<Longrightarrow> B.cod (F f) = F (A.cod f)"
  and preserves_comp [iff]: "\<lbrakk> A.arr f; g \<in> A.hom (A.cod f) (A.cod g) \<rbrakk>
                                                   \<Longrightarrow> F (A g f) = B (F g) (F f)"
  begin

    lemma preserves_hom [intro]:
    assumes "f \<in> A.hom a b"
    shows "F f \<in> B.hom (F a) (F b)"
      using assms preserves_dom preserves_cod by auto

    text{*
      The following, which is made possible through the presence of @{text null},
      allows us to infer that the subterm @{term f} denotes an arrow if the
      term @{term "F f"} denotes an arrow.  This is very useful, because otherwise
      doing anything with @{term f} would require a separate proof that it is an arrow
      by some other means.
    *}

    lemma reflects_arr:
    assumes "B.arr (F f)"
    shows "A.arr f"
      using assms is_extensional B.not_arr_null by metis

    lemma preserves_ide [simp]:
    assumes "A.ide a"
    shows "B.ide (F a)"
      using assms preserves_hom A.ideD(1) A.ideD(2) B.ideI_dom
      by (metis (mono_tags, lifting) mem_Collect_eq)

    lemma preserves_seq:
    assumes "A.seq g f"
    shows "B.seq (F g) (F f)"
      using assms preserves_hom by fastforce

    lemma preserves_iso [simp]:
    assumes "A.iso f"
    shows "B.iso (F f)"
    proof
      show "B.inverse_arrows (F f) (F (A.inv f))"
      proof
        show 1: "B.antipar (F f) (F (A.inv f))"
          using assms
          by (metis (full_types) A.inverse_arrowsD(1) A.isoE A.inverse_unique preserves_arr
              preserves_cod preserves_dom)
        show "B.ide (B (F f) (F (A.inv f)))"
        proof -
          have 2: "A.seq f (A.inv f)"
            using assms 1 A.inv_is_inverse by (metis A.inverse_arrowsD(1))
          hence "B (F f) (F (A.inv f)) = F (A f (A.inv f))"
            by simp
          also have "... = F (A.cod f)"
            using assms 1 2 A.inv_is_inverse A.ide_comp_simp
            by (metis A.inverse_arrowsD(3) preserves_cod preserves_dom)
          finally show ?thesis
            using assms by simp
        qed
        show "B.ide (B (F (A.inv f)) (F f))"
        proof -
          have 2: "A.seq (A.inv f) f"
            using assms 1 A.inv_is_inverse by (metis A.inverse_arrowsD(1))
          hence "B (F (A.inv f)) (F f) = F (A (A.inv f) f)"
            by simp
          also have "... = F (A.dom f)"
            using assms 1 2 A.inv_is_inverse
            by (simp add: A.ide_comp_simp A.inverse_arrowsD(2))
          finally show ?thesis
            using assms by simp
        qed
      qed
    qed

  end

  locale faithful_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_faithful: "\<lbrakk> A.par f f'; F f = F f' \<rbrakk> \<Longrightarrow> f = f'"
  begin

    lemma locally_reflects_ide:
    assumes "f \<in> A.hom a a" and "B.ide (F f)"
    shows "A.ide f"
    proof -
      have "A.par f (A.dom f)"
        using assms by auto
      moreover have "F f = F (A.dom f)"
        using assms by (metis B.ideD(1) B.ideD(2) preserves_dom reflects_arr)
      ultimately show ?thesis
        using assms is_faithful [of f "A.dom f"] by auto
    qed

  end

  locale full_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_full: "\<lbrakk> A.ide a; A.ide a'; g \<in> B.hom (F a') (F a) \<rbrakk>
                       \<Longrightarrow> \<exists>f. f \<in> A.hom a' a \<and> F f = g"

  locale fully_faithful_functor =
    faithful_functor A B F +
    full_functor A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  begin

    lemma reflects_iso:
    assumes "f \<in> A.hom a' a" and "B.iso (F f)"
    shows "A.iso f"
    proof -
      from assms obtain g' where g': "B.inverse_arrows (F f) g'" by blast
      have 1: "g' \<in> B.hom (F a) (F a')"
        using assms(1) g' by auto
      from this obtain g where g: "g \<in> A.hom a a' \<and> F g = g'"
        using assms(1) is_full by fastforce
      have "A.inverse_arrows f g"
      proof
        show 2: "A.antipar f g" using assms(1) 1 g by simp
        show "A.ide (A f g)"
        proof -
          have "B.ide (F (A f g))" using 2 g g' by auto
          hence "F (A f g) = B.dom (F (A f g))" by simp
          hence "F (A f g) = F (A.dom g)" using assms(1) g by auto
          thus ?thesis using 2 is_faithful [of "A f g" "A.dom g"] by simp
        qed
        show "A.ide (A g f)"
        proof -
          have "B.ide (F (A g f))" using 2 g g' by auto
          hence "F (A g f) = B.dom (F (A g f))" by simp
          hence "F (A g f) = F (A.dom f)" using assms(1) g by auto
          thus ?thesis using 2 is_faithful [of "A g f" "A.dom f"] by simp
        qed
      qed
      thus ?thesis by auto
    qed

  end

  locale embedding_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_embedding: "\<lbrakk> A.arr f; A.arr f'; F f = F f' \<rbrakk> \<Longrightarrow> f = f'"

  sublocale embedding_functor \<subseteq> faithful_functor
  proof
    fix f f'
    assume A: "A.par f f'"
    and B: "F f = F f'"
    show "f = f'" using A B is_embedding by blast
  qed

  context embedding_functor
  begin

    lemma reflects_ide:
    assumes "A.arr f" and "B.ide (F f)"
    shows "A.ide f"
      using assms is_embedding
      by (metis A.ide_dom B.ideD(2) A.ideD(1) preserves_dom)

  end

  locale full_embedding_functor =
    embedding_functor A B F +
    full_functor A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"

  locale constant_functor =
    A: category A +
    B: category B
  for A :: "'a comp"
  and B :: "'b comp"
  and b :: 'b +
  assumes value_is_ide: "B.ide b"
  begin

    definition map
    where "map f = (if A.arr f then b else B.null)"

    lemma map_simp [simp]:
    assumes "A.arr f"
    shows "map f = b"
      using assms map_def by auto

    lemma is_functor:
    shows "functor A B map"
      apply unfold_locales
      by (auto simp add: map_def value_is_ide)
      
  end

  sublocale constant_functor \<subseteq> "functor" A B map
    using is_functor by auto

  locale identity_functor =
    C: category C
    for C :: "'a comp"
  begin

    definition map :: "'a \<Rightarrow> 'a"
    where "map f = (if C.arr f then f else C.null)"

    lemma map_simp [simp]:
    assumes "C.arr f"
    shows "map f = f"
      using assms map_def by simp

    lemma is_functor:
    shows "functor C C map"
      apply (unfold_locales)
      by (auto simp add: map_def)

  end

  sublocale identity_functor \<subseteq> "functor" C C map
    using is_functor by auto

  text{*
    Composition of functors coincides with function composition, thanks to the
    magic of @{text null}.
  *}

  lemma functor_comp:
  assumes "functor A B F" and "functor B C G"
  shows "functor A C (G o F)"
  proof -
    interpret F: "functor" A B F using assms(1) by auto
    interpret G: "functor" B C G using assms(2) by auto
    show "functor A C (G o F)"
      apply unfold_locales
      (* 5 *) apply (metis F.reflects_arr G.is_extensional comp_apply)
      (* 4 *) by simp_all
  qed

  locale composite_functor =
    F: "functor" A B F +
    G: "functor" B C G
  for A :: "'a comp"
  and B :: "'b comp"
  and C :: "'c comp"
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'c"
  begin

    abbreviation map
    where "map \<equiv> G o F"

  end

  sublocale composite_functor \<subseteq> "functor" A C "G o F"
    using functor_comp F.functor_axioms G.functor_axioms by blast

  lemma comp_ide_dom [simp]:
  assumes "functor A B F"
  shows "F o identity_functor.map A = F"
  proof
    interpret "functor" A B F using assms by blast
    interpret I: identity_functor A ..
    show "\<And>x. (F o I.map) x = F x"
      using I.map_def by (simp add: A.not_arr_null)
  qed

  lemma comp_ide_cod [simp]:
  assumes "functor A B F"
  shows "identity_functor.map B o F = F"
  proof
    interpret "functor" A B F using assms by blast
    interpret I: identity_functor B ..
    show "\<And>x. (I.map o F) x = F x"
      using I.map_def by (metis comp_apply is_extensional preserves_arr)
  qed

  locale inverse_functors =
    A: category A +
    B: category B +
    F: "functor" A B F +
    G: "functor" B A G
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'a" +
  assumes inv: "G o F = identity_functor.map A"
  and inv': "F o G = identity_functor.map B"

  locale isomorphic_categories =
    A: category A +
    B: category B
  for A :: "'a comp"
  and B :: "'b comp" +
  assumes iso: "\<exists>F G. inverse_functors A B F G"

  sublocale inverse_functors \<subseteq> isomorphic_categories A B
  proof
    have "inverse_functors A B F G" ..
    thus "\<exists>F G. inverse_functors A B F G" by auto
  qed
  
  lemma inverse_functors_sym:
  assumes "inverse_functors A B F G"
  shows "inverse_functors B A G F"
  proof -
    interpret inverse_functors A B F G using assms by auto
    show ?thesis
      apply (unfold_locales) using inv inv' by auto
  qed
  
  locale invertible_functor =
    A: category A +
    B: category B +
    F: "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes invertible: "\<exists>G. inverse_functors A B F G"
  begin
  
    lemma preserves_terminal:
    assumes "A.terminal a"
    shows "B.terminal (F a)"
    proof
      show "B.ide (F a)" using assms F.preserves_ide A.terminal_def by blast
      fix b :: 'b
      assume b: "B.ide b"
      show "\<exists>!g. g \<in> B.hom b (F a)"
      proof
        let ?G = "SOME G. inverse_functors A B F G"
        from invertible have G: "inverse_functors A B F ?G"
          using someI_ex [of "\<lambda>G. inverse_functors A B F G"] by fast
        interpret inverse_functors A B F ?G using G by auto
        interpret IA: identity_functor A ..
        interpret IB: identity_functor B ..
        let ?P = "\<lambda>f. f \<in> A.hom (?G b) a"
        have 1: "\<exists>!f. ?P f" using assms b A.terminal_def G.preserves_ide by simp
        hence 2: "?P (THE f. ?P f)" by (metis (no_types, lifting) theI')
        thus "F (THE f. ?P f) \<in> B.hom b (F a)"
          using b inv' B.ideD(1) F.preserves_hom
          by (metis (mono_tags, lifting) IB.map_simp comp_def mem_Collect_eq)
        hence 3: "(THE f. ?P f) \<in> A.hom (?G b) a"
          using assms 2 b G by simp
        fix g :: 'b
        assume g: "g \<in> B.hom b (F a)"
        have "?G g \<in> A.hom (?G b) a"
        proof -
          have "A.arr a" using assms(1) A.ideD(1) A.terminal_def by blast
          moreover have "?G g \<in> A.hom (?G b) (?G (F a))"
            using g G.preserves_hom [of g b "F a"] by simp
          ultimately show ?thesis using g IA.map_simp
            by (metis (no_types, lifting) comp_apply inv mem_Collect_eq)
        qed
        hence "?G g = (THE f. ?P f)" using assms 1 3 A.terminal_def by blast
        thus "g = F (THE f. ?P f)"
          using inv' CollectD g IB.map_simp mem_Collect_eq
          by (metis (no_types, lifting) comp_apply)
      qed
    qed
  
  end

  locale dual_functor =
    F: "functor" A B F +
    Aop: dual_category A +
    Bop: dual_category B
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  begin

    definition map
    where "map \<equiv> F"

    lemma map_char [iff]:
    shows "map f = F f"
      by (simp add: map_def)

    lemma is_functor:
    shows "functor Aop.comp Bop.comp map"
      apply (unfold_locales) by auto

  end

  sublocale dual_functor \<subseteq> "functor" Aop.comp Bop.comp map
    using is_functor by auto

end

