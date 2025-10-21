(*  Title:       CategoryOfTransitions
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Categories of Transitions"

theory CategoryOfTransitions
imports Main Category3.EpiMonoIso CategoryWithBoundedPushouts
        ResiduatedTransitionSystem.ResiduatedTransitionSystem
begin

  text\<open>
    A category of transitions is a category with bounded pushouts in which every
    arrow is an epimorphism and the only isomorphisms are identities.
  \<close>

  locale category_of_transitions =
    category_with_bounded_pushouts +
  assumes arr_implies_epi: "arr t \<Longrightarrow> epi t"
  and iso_implies_ide: "iso t \<Longrightarrow> ide t"
  begin

    (* TODO: Move with rest of commutative_square facts (currently CategoryWithPullbacks). *)
    lemma commutative_square_sym:
    shows "commutative_square f g h k \<Longrightarrow> commutative_square g f k h"
      by auto

    text \<open>
      In this setting, pushouts are uniquely determined.
    \<close>

    sublocale elementary_category_with_bounded_pushouts C inj0 inj1
      using extends_to_elementary_category_with_bounded_pushouts by blast

    lemma pushouts_unique:
    assumes "pushout_square f g h k"
    shows "f = \<i>\<^sub>1[h, k]" and "g = \<i>\<^sub>0[h, k]"
    proof -
      obtain w where w: "w \<cdot> \<i>\<^sub>1[h, k] = f \<and> w \<cdot> \<i>\<^sub>0[h, k] = g"
        using assms pushout_universal pushout_square_def by meson
      obtain w' where w': "w' \<cdot> f = \<i>\<^sub>1[h, k] \<and> w' \<cdot> g = \<i>\<^sub>0[h, k]"
        using assms pushout_universal pushout_square_def pushout_commutes 
          bounded_spanI
        by meson
      have 1: "ide w"
      proof -
        have "commutative_square f g h k"
          using assms pushout_square_def by blast
        hence "ide (w \<cdot> w')"
          using assms w w' comp_cod_arr ide_char' comp_assoc
          apply (elim commutative_squareE)
          by (metis arr_implies_epi epi_cancel seqE)
        thus ?thesis
          by (metis ideD(1) ide_is_iso inv_comp_right(2) iso_iff_section_and_epi
              sectionI seqE arr_implies_epi iso_implies_ide)
      qed
      show "f = \<i>\<^sub>1[h, k]" and "g = \<i>\<^sub>0[h, k]"
        using 1 w w' by (metis comp_ide_arr ext null_is_zero(2))+
    qed

    lemma inj_sym:
    shows "\<i>\<^sub>0[k, h] = \<i>\<^sub>1[h, k]"
    proof -
      have "\<not> bounded_span h k \<Longrightarrow> ?thesis"
        using inj0_ext [of k h] inj1_ext [of h k] bounded_span_sym by metis
      moreover have "bounded_span h k \<Longrightarrow> ?thesis"
      proof -
        assume 1: "bounded_span h k"
        have "(\<exists>l. l \<cdot> \<i>\<^sub>1[h, k] = \<i>\<^sub>0[k, h]) \<and> (\<exists>l'. l' \<cdot> \<i>\<^sub>0[k, h] = \<i>\<^sub>1[h, k])"
          by (meson 1 bounded_span_sym commutative_square_sym
              pushout_commutes pushout_universal)
        moreover have "epi \<i>\<^sub>0[k, h] \<and> epi \<i>\<^sub>1[h, k]"
          by (meson 1 arr_implies_epi bounded_span_sym
              commutative_squareE pushout_commutes)
        ultimately show ?thesis
          by (metis arr_implies_epi iso_iff_section_and_epi comp_cod_arr
              comp_ide_arr epi_cancel epi_implies_arr ide_cod
              iso_implies_ide comp_assoc sectionI seqE)
      qed
      ultimately show ?thesis by auto
    qed

    lemma inj_arr_self:
    assumes "arr t"
    shows "\<i>\<^sub>0[t, t] = cod t" and "\<i>\<^sub>1[t, t] = cod t"
    proof -
      have 1: "pushout_square (cod t) (cod t) t t"
        using assms comp_arr_dom pushout_universal
        apply (intro pushout_squareI)
            apply auto[4]
        apply auto 
         apply (metis commutative_squareE inj_sym)
        by (metis ide_cod commutative_squareE comp_arr_ide)
      show "\<i>\<^sub>0[t, t] = cod t" and "\<i>\<^sub>1[t, t] = cod t"
        using 1 pushouts_unique by auto
    qed

    lemma inj_arr_dom:
    assumes "arr t"
    shows "\<i>\<^sub>0[t, dom t] = t" and "\<i>\<^sub>1[t, dom t] = cod t"
    proof -
      have 1: "pushout_square (cod t) t t (dom t)"
        using assms comp_arr_dom comp_cod_arr pushout_universal
        apply (intro pushout_squareI)
            apply auto[4]
        apply auto
         apply (metis cod_dom commutative_squareE)
        by (metis arr_implies_epi commutative_squareE epi_cancel)
      show "\<i>\<^sub>0[t, dom t] = t" and "\<i>\<^sub>1[t, dom t] = cod t"
        using 1 pushouts_unique by auto
    qed

    lemma eq_iff_ide_inj:
    assumes "span t u"
    shows "t = u \<longleftrightarrow> ide \<i>\<^sub>0[t, u] \<and> ide \<i>\<^sub>0[u, t]"
    proof
      show "t = u \<Longrightarrow> ide \<i>\<^sub>0[t, u] \<and> ide \<i>\<^sub>0[u, t]"
        using assms by (simp add: inj_arr_self(1))
      show "ide \<i>\<^sub>0[t, u] \<and> ide \<i>\<^sub>0[u, t] \<Longrightarrow> t = u"
        by (metis (no_types, lifting) comp_cod_arr commutative_squareE
            ide_char ide_def inj0_ext inj_sym pushout_commutes)
    qed

    lemma inj_comp:
    assumes "bounded_span t (v \<cdot> u)"
    shows "\<i>\<^sub>0[t, v \<cdot> u] = \<i>\<^sub>0[\<i>\<^sub>0[t, u], v]"
    and "\<i>\<^sub>0[v \<cdot> u, t] = \<i>\<^sub>0[v, \<i>\<^sub>0[t, u]] \<cdot> \<i>\<^sub>0[u, t]"
    proof -
      obtain w x where wx: "seq w t \<and> w \<cdot> t = x \<cdot> v \<cdot> u"
        using assms by blast
      have 1: "seq w t \<and> w \<cdot> t = (x \<cdot> v) \<cdot> u"
        using wx comp_assoc by auto
      have 2: "pushout_square \<i>\<^sub>0[u, t] \<i>\<^sub>0[t, u] t u"
        by (metis (full_types) 1 bounded_span_def cod_comp
            commutative_squareI dom_comp has_bounded_pushouts inj_sym seqE)
      have 3: "pushout_square \<i>\<^sub>0[v, \<i>\<^sub>0[t, u]] \<i>\<^sub>0[\<i>\<^sub>0[t, u], v] \<i>\<^sub>0[t, u] v"
      proof -
        have 4: "commutative_square w (x \<cdot> v) t u"
          using wx comp_assoc
          by (metis (mono_tags, lifting) cod_comp commutative_square_def
              dom_comp seqE)
        obtain l where l: "l \<cdot> \<i>\<^sub>0[u, t] = w \<and> l \<cdot> \<i>\<^sub>0[t, u] = x \<cdot> v"
          using 2 4 pushout_square_def [of "\<i>\<^sub>0[u, t]" "\<i>\<^sub>0[t, u]" t u] by blast
        have "bounded_span \<i>\<^sub>0[t, u] v"
          by (metis (full_types) 1 l bounded_spanI cod_comp
              commutative_squareI dom_comp seqE)
        thus ?thesis
          using assms has_bounded_pushouts inj_sym by auto
      qed
      show "\<i>\<^sub>0[t, v \<cdot> u] = \<i>\<^sub>0[\<i>\<^sub>0[t, u], v]"
        using assms 2 3 composition_of_pushouts pushouts_unique
        by (metis (full_types))
      show "\<i>\<^sub>0[v \<cdot> u, t] = \<i>\<^sub>0[v, \<i>\<^sub>0[t, u]] \<cdot> \<i>\<^sub>0[u, t]"
        using assms 2 3 composition_of_pushouts pushouts_unique inj_sym
        by metis
    qed

    lemma inj_prefix:
    assumes "arr (u \<cdot> t)"
    shows "\<i>\<^sub>0[u \<cdot> t, t] = u" and "\<i>\<^sub>0[t, u \<cdot> t] = cod u"
    proof -
      have 1: "bounded_span (u \<cdot> t) t"
        by (metis assms ideD(1) ide_cod inj1_ext inj_arr_self(1)
            inj_comp(2) inj_sym not_arr_null seqE)
      show "\<i>\<^sub>0[u \<cdot> t, t] = u"
        using assms 1
        by (metis bounded_span_sym seqE comp_arr_dom inj_arr_dom(1)
            inj_arr_self(1) inj_comp(2))
      show "\<i>\<^sub>0[t, u \<cdot> t] = cod u"
        using 1
        by (metis assms bounded_span_sym seqE inj_arr_dom(2) inj_arr_self(1)
            inj_comp(1) inj_sym)
    qed

  end

  lemma category_of_transitions_preserved_by_iso:
  assumes "isomorphic_categories A B"
  and "category_of_transitions A"
  shows "category_of_transitions B"
  proof -
    interpret A: category A
      using assms(1) isomorphic_categories.axioms(1) by blast
    interpret B: category B
      using assms(1) isomorphic_categories.axioms(2) by blast
    obtain F G where FG: "inverse_functors A B G F"
      using assms isomorphic_categories.iso by blast
    interpret FG: inverse_functors A B G F
      using FG by blast
    interpret A: category_of_transitions A
      using assms(2) by blast
    show ?thesis
    proof
      show "\<And>t. B.iso t \<Longrightarrow> B.ide t"
        by (metis FG.F.preserves_iso FG.G.preserves_ide FG.inv FG.iso assms(2)
            category.iso_is_arr category_of_transitions.iso_implies_ide comp_eq_dest_lhs
            identity_functor.map_simp identity_functor_def inverse_functors_def)
      show "\<And>t. B.arr t \<Longrightarrow> B.epi t"
      proof -
        fix t
        assume t: "B.arr t"
        hence "A.arr (G t)"
          by blast
        hence "A.epi (G t)"
          using A.arr_implies_epi by blast
        hence "B.epi (F (G t))"
        proof (intro B.epiI)
          show "A.epi (G t) \<Longrightarrow> B.arr (F (G t))"
            using \<open>A.arr (G t)\<close> by blast
          show "\<And>g g'. \<lbrakk>A.epi (G t); B.seq g (F (G t)); B.seq g' (F (G t));
                        B g (F (G t)) = B g' (F (G t))\<rbrakk> \<Longrightarrow> g = g'"
            by (metis A.arr_implies_epi A.category_axioms B.category_axioms B.is_faithful
                FG.F.preserves_arr FG.F.preserves_comp FG.inv category.cod_comp
                category.epi_cancel category.seqE o_apply)
        qed
        thus "B.epi t"
          by (metis B.map_simp FG.inv o_apply t)
      qed
      show "\<And>h k. B.bounded_span h k \<Longrightarrow> \<exists>f g. B.pushout_square f g h k"
      proof -
        fix h k
        assume hk: "B.bounded_span h k"
        have 1: "A.bounded_span (G h) (G k)"
        proof -
          obtain f g where fg: "B.commutative_square f g h k"
            using hk by blast
          have "A.commutative_square (G f) (G g) (G h) (G k)"
            by (metis (mono_tags, lifting) A.commutative_squareI B.commutative_squareE
                B.seqI FG.F.preserves_cod FG.F.preserves_comp FG.F.preserves_dom
                FG.F.preserves_reflects_arr fg)
          thus ?thesis by blast
        qed
        obtain Gf Gg where fg: "A.pushout_square Gf Gg (G h) (G k)"
          using 1 A.has_bounded_pushouts by blast
        have "B.pushout_square (F Gf) (F Gg) h k"
        proof
          show "B.span h k"
            using hk by auto
          show "B.cospan (F Gf) (F Gg)"
            using A.commutative_square_def A.pushout_square_def FG.G.preserves_arr
                  FG.G.preserves_cod fg
            by presburger
          show "B.dom (F Gf) = B.cod h"
            by (metis A.commutative_square_def A.pushout_square_def B.identity_functor_axioms
                FG.G.preserves_cod FG.G.preserves_dom FG.inv \<open>B.span h k\<close> fg
                identity_functor.map_def o_apply)
          show "B (F Gf) h = B (F Gg) k"
            by (metis (no_types, lifting) A.category_axioms A.pushout_square_def
                B.map_simp FG.G.preserves_comp FG.inv \<open>B.span h k\<close> category.commutative_squareE
                category.seqI fg o_apply)
          show "\<And>f' g'. B.commutative_square f' g' h k \<Longrightarrow> \<exists>!l. B l (F Gf) = f' \<and> B l (F Gg) = g'"
          proof -
            fix f' g'
            assume 1: "B.commutative_square f' g' h k"
            have 2: "A.commutative_square (G f') (G g') (G h) (G k)"
              by (metis (no_types, lifting) ext "1" A.commutative_squareI A.seqE
                  B.commutative_square_def B.comp_arr_dom B.seqI
                  FG.F.as_nat_trans.preserves_comp_2 FG.F.preserves_cod FG.F.preserves_seq
                  \<open>B.span h k\<close>)
            hence "\<exists>!Gl. A Gl Gf = G f' \<and> A Gl Gg = G g'"
              using A.pushout_square_def fg by presburger
            thus "\<exists>!l. B l (F Gf) = f' \<and> B l (F Gg) = g'"
              by (metis (full_types) "1" "2" A.category_axioms B.category_axioms
                  B.identity_functor_axioms FG.G.preserves_comp FG.inv
                  \<open>B.cospan (F Gf) (F Gg)\<close> \<open>\<And>t. B.arr t \<Longrightarrow> B.epi t\<close>
                  category.commutative_square_def category.epi_cancel
                  identity_functor.map_simp o_apply)
          qed
        qed
        thus "\<exists>f g. B.pushout_square f g h k" by blast
      qed
    qed
  qed

section "Extensional RTS's with Composites as Categories"

  text \<open>
    An extensional RTS with composites can be regarded as a category in an obvious way.
  \<close>

  locale extensional_rts_with_composites_as_category =
    A: extensional_rts_with_composites
  begin

    text \<open>
      Because we've defined RTS composition to take its arguments in diagram order,
      the ordering has to be reversed to match the way it is done for categories.
    \<close>

    abbreviation comp
    where "comp \<equiv> \<lambda>u t. t \<cdot> u"

    interpretation Category.partial_magma comp
      using A.comp_null by unfold_locales metis
    interpretation Category.partial_composition comp ..

    lemma null_char:
    shows "null = A.null"
      by (metis A.comp_null\<^sub>C\<^sub>C(1) null_is_zero(2))

    lemma ide_char:
    shows "ide a \<longleftrightarrow> A.ide a"
    proof
      assume a: "A.ide a"
      show "ide a"
      proof (unfold ide_def, intro conjI allI impI)
        show "a \<cdot> a \<noteq> null"
          using a null_char by auto
        show "\<And>t. t \<cdot> a \<noteq> null \<Longrightarrow> t \<cdot> a = t"
          using a
          by (metis A.comp_def A.comp_is_composite_of(2) A.composable_def
              A.composite_of_def A.cong_char null_char)
        show "\<And>t. a \<cdot> t \<noteq> null \<Longrightarrow> a \<cdot> t = t"
          using a
          by (metis A.arr_comp A.ide_iff_trg_self A.comp_src_arr null_char
              A.comp_def A.arr_compE\<^sub>E\<^sub>C)
      qed
      next
      assume a: "ide a"
      show "A.ide a"
        using a
        by (metis A.arr_comp A.comp_def A.comp_eqI A.cong_reflexive
            ide_def null_char)
    qed

    lemma src_in_domains:
    assumes "A.arr t"
    shows "A.src t \<in> domains t"
      unfolding domains_def
      using assms ide_char null_char by force

    lemma trg_in_codomains:
    assumes "A.arr t"
    shows "A.trg t \<in> codomains t"
      unfolding codomains_def
      using assms ide_char null_char by force

    lemma arr_char:
    shows "arr = A.arr"
    proof
      fix t
      show "arr t \<longleftrightarrow> A.arr t"
      proof
        show "A.arr t \<Longrightarrow> arr t"
          using src_in_domains trg_in_codomains arr_def by auto
        assume t: "arr t"
        have 1: "domains t \<noteq> {} \<or> codomains t \<noteq> {}"
          using t arr_def by simp
        show "A.arr t"
        proof (cases "domains t \<noteq> {}")
          case True
          obtain a where a: "a \<in> domains t"
            using True by auto
          show "A.arr t"
            using a t A.composable_iff_seq [of a t] A.comp_def domains_def
                  null_char
            by auto
          next
          case False
          obtain a where a: "a \<in> codomains t"
            using False 1 by auto
          show "A.arr t"
            using a t A.composable_iff_seq [of t a] A.comp_def codomains_def
                  null_char
            by auto
        qed
      qed
    qed

    lemma seq_char:
    shows "seq u t \<longleftrightarrow> A.seq t u"
      using arr_char by auto

    sublocale category comp
    proof
      show "\<And>g f. f \<cdot> g \<noteq> null \<Longrightarrow> seq g f"
        using A.composable_iff_comp_not_null null_char seq_char by auto
      show "\<And>f. (domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using arr_char arr_def src_in_domains trg_in_codomains empty_iff by metis
      fix f g h
      show 1: "f \<cdot> (g \<cdot> h) = (f \<cdot> g) \<cdot> h"
        using A.comp_assoc\<^sub>E\<^sub>C by blast
      show "\<lbrakk>seq h g; seq (g \<cdot> h) f\<rbrakk> \<Longrightarrow> seq g f"
        using A.comp_assoc\<^sub>E\<^sub>C seq_char by auto
      show "\<lbrakk>seq h (f \<cdot> g); seq g f\<rbrakk> \<Longrightarrow> seq h g"
        by (metis 1 A.arr_compE\<^sub>E\<^sub>C arr_char)
      show "\<lbrakk>seq g f; seq h g\<rbrakk> \<Longrightarrow> seq (g \<cdot> h) f"
        using seq_char by fastforce
    qed

    proposition is_category:
    shows "category comp"
      ..

    lemma cod_char:
    shows "cod = A.trg"
      unfolding A.trg_def
      by (metis arr_char cod_def cod_eqI' codomains_char null_char
          A.con_implies_arr(2) trg_in_codomains A.conI A.trg_def)

    lemma dom_char:
    shows "dom = A.src"
      unfolding A.src_def
      by (metis A.src_def arr_char arr_def dom_eqI' dom_def null_char
          src_in_domains)

    lemma arr_implies_epi:
    assumes "arr t"
    shows "epi t"
      using assms
      by (metis arr_char epiI A.comp_cancel_left)

    lemma iso_implies_ide:
    assumes "iso t"
    shows "ide t"
      by (metis A.ide_backward_stable A.src_ide arr_char arr_inv assms
          comp_inv_arr' dom_char dom_inv ide_char' iso_is_arr A.ide_src
          A.prfx_comp seqI)

  end

  locale composite_completion_as_category =
    R: rts +
    extensional_rts_with_composites_as_category \<open>composite_completion.resid resid\<close>

  section "Characterization"

  text \<open>
    The categories arising from extensional RTS's with composites are categories
    of transitions.
  \<close>

  context extensional_rts_with_composites_as_category
  begin

    lemma has_bounded_pushouts:
    assumes "bounded_span h k"
    shows "pushout_square (k \\ h) (h \\ k) h k"
    proof
      have con: "h \<frown> k"
        using assms
        by (metis A.bounded_imp_con\<^sub>E A.cong_reflexive arr_char
            bounded_span_def commutative_squareE seqI)
      show "cospan (k \\ h) (h \\ k)"
        by (simp add: con A.apex_sym A.con_sym arr_char cod_char)
      show "span h k"
        using assms by blast
      show "dom (k \\ h) = cod h"
        using A.join_expansion(2) con seq_char by blast
      show "h \<cdot> k \\ h = k \<cdot> h \\ k"
        using A.diamond_commutes by blast
      show "\<And>f g h k. commutative_square f g h k
                         \<Longrightarrow> \<exists>!l. k \\ h \<cdot> l = f \<and> h \\ k \<cdot> l = g"
      proof -
        fix f g h k
        assume 1: "commutative_square f g h k"
        hence 2: "h \<cdot> f = k \<cdot> g"
          using dom_char cod_char by auto
        hence 3: "h \<frown> k"
          by (metis "1" A.bounded_imp_con\<^sub>E A.prfx_reflexive arr_char
              commutative_squareE seqI)
        let ?l = "(h \<cdot> f) \\ (h \<squnion> k)"
        have 4: "(k \\ h) \<cdot> ?l = f"
        proof -
          have "A.joinable h k"
            using 3 by simp
          thus ?thesis
            by (metis 1 A.comp_assoc\<^sub>E\<^sub>C A.comp_resid_prfx A.induced_arrow(2)
                A.join_expansion(1) A.seq_implies_arr_comp commutative_squareE
                seqI seq_char)
        qed
        moreover have "(h \\ k) \<cdot> ?l = g"
          by (metis "1" A.comp_resid_prfx A.induced_arrow(2)
              A.seq_implies_arr_comp calculation commutative_squareE
              seqI seq_char)
        ultimately have "\<exists>l. (k \\ h) \<cdot> ?l = f \<and> (h \\ k) \<cdot> ?l = g"
          by simp
        moreover have "\<And>l'. (k \\ h) \<cdot> l' = f \<and> (h \\ k) \<cdot> l' = g \<Longrightarrow> l' = ?l"
          by (metis 1 4 A.comp_cancel_left arr_char commutative_square_def)
        ultimately show "\<exists>!l. (k \\ h) \<cdot> l = f \<and> (h \\ k) \<cdot> l = g" by auto
      qed
    qed

    sublocale category_of_transitions comp
      using has_bounded_pushouts arr_implies_epi iso_implies_ide
      by unfold_locales auto

    proposition is_category_of_transitions:
    shows "category_of_transitions comp"
      ..

  end

  text \<open>
    Every category of transitions is derived from an underlying extensional RTS,
    obtained by using pushouts to define residuation.
  \<close>

  locale underlying_rts =
    C: category_of_transitions
  begin

    abbreviation resid
    where "resid \<equiv> \<lambda>h k. \<i>\<^sub>0[h, k]"

    interpretation ResiduatedTransitionSystem.partial_magma resid
      using C.inj0_ext C.inj1_ext C.commutative_squareE C.not_arr_null C.pushout_commutes
      by unfold_locales metis

    lemma null_char:
    shows "null = C.null"
      using null_eqI C.inj0_ext C.not_arr_null C.pushout_commutes
      by (metis C.commutative_squareE)

    interpretation residuation resid
    proof
      show 0: "\<And>t u. \<i>\<^sub>0[t, u] \<noteq> null \<Longrightarrow> \<i>\<^sub>0[u, t] \<noteq> null"
        by (metis C.inj0_ext C.inj_sym C.not_arr_null C.pushout_commutes
            C.commutative_squareE null_char)
      show "\<And>t u. \<i>\<^sub>0[t, u] \<noteq> null \<Longrightarrow> \<i>\<^sub>0[\<i>\<^sub>0[t, u], \<i>\<^sub>0[t, u]] \<noteq> null"
        by (metis C.commutative_squareE C.eq_iff_ide_inj C.ideD(1) C.inj0_ext
            C.not_arr_null C.pushout_commutes null_char)
      have *: "\<And>t u v. \<lbrakk>\<i>\<^sub>0[t, u] \<noteq> null; \<i>\<^sub>0[t, v] \<noteq> null; \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<noteq> null\<rbrakk>
                          \<Longrightarrow> \<exists>w. \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] = w \<cdot> \<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]]"
      proof -
        fix t u v
        assume tu: "\<i>\<^sub>0[t, u] \<noteq> null" and tv: "\<i>\<^sub>0[t, v] \<noteq> null"
        and vt_ut: "\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<noteq> null"
        have 1: "(\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u]) \<cdot> u = (\<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v]) \<cdot> v"
        proof -
          have "(\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u]) \<cdot> u = \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u] \<cdot> u"
            using C.comp_assoc by simp
          also have "... =  \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[u, t] \<cdot> t"
            using tu C.pushout_commutes
            by (metis C.commutative_squareE C.inj0_ext C.inj_sym null_char)
          also have "... = (\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[u, t]) \<cdot> t"
            using C.comp_assoc by simp
          also have "... = (\<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[v, t]) \<cdot> t"
            using vt_ut C.pushout_commutes
            by (metis (no_types, lifting) C.commutative_squareE C.inj0_ext C.inj_sym null_char)
          also have "... = \<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[v, t] \<cdot> t"
            using C.comp_assoc by simp
          also have "... = \<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v] \<cdot> v"
            using tv C.pushout_commutes
            by (metis C.commutative_squareE C.inj0_ext C.inj_sym null_char)
          also have "... = (\<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v]) \<cdot> v"
            using C.comp_assoc by simp
          finally show ?thesis by blast
        qed
        have 2: "C.commutative_square (\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u])
                  (\<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v]) u v"
        proof -
          have "C.span u v"
            by (metis (mono_tags, opaque_lifting) C.commutative_square_def
                C.inj0_ext C.pushout_commutes null_char tu tv)
          moreover have "C.cospan (\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u])
                                  (\<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v])"
          proof (intro conjI)
            show 3: "C.seq \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<i>\<^sub>0[t, u]"
            proof
              show "\<guillemotleft>\<i>\<^sub>0[t, u] : C.cod u \<rightarrow> C.cod \<i>\<^sub>0[u, t]\<guillemotright>"
                using C.pushout_commutes [of t u]
                by (metis C.commutative_squareE C.in_homI C.inj0_ext C.inj_sym null_char tu)
              show "\<guillemotleft>\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] : C.cod \<i>\<^sub>0[u, t] \<rightarrow> C.cod \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]]\<guillemotright>"
                using C.pushout_commutes [of "\<i>\<^sub>0[v, t]" "\<i>\<^sub>0[u, t]"]
                      C.arr_iff_in_hom C.commutative_square_def C.inj0_ext null_char vt_ut
                by force
            qed
            show 4: "C.seq \<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<i>\<^sub>0[t, v]"
              by (metis 1 3 C.dom_inj(1) C.inj0_ext C.seqE C.seqI calculation
                  C.dom_comp null_char tu)
            show "C.cod (\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u]) =
                  C.cod (\<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v])"
              by (metis 3 4 C.cod_inj C.inj0_ext C.inj_sym C.cod_comp)
          qed
          moreover have "C.dom (\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u]) = C.cod u"
            by (metis C.dom_comp C.dom_inj(1) C.inj0_ext calculation(2)
                null_char tu)
          ultimately show ?thesis
            using 1 by blast
        qed
        hence "C.bounded_span u v"
          by blast
        obtain l where l: "l \<cdot> \<i>\<^sub>0[v, u] = \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<cdot> \<i>\<^sub>0[t, u] \<and>
                           l \<cdot> \<i>\<^sub>0[u, v] = \<i>\<^sub>0[\<i>\<^sub>0[u, t], \<i>\<^sub>0[v, t]] \<cdot> \<i>\<^sub>0[t, v]"
          using 2 C.pushout_universal by (metis C.inj_sym)
        have 3: "C.commutative_square \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] l \<i>\<^sub>0[t, u] \<i>\<^sub>0[v, u]"
          using tu tv vt_ut l 2
          by (metis (mono_tags, lifting) C.cod_comp C.commutative_square_def
              C.dom_comp C.seqE)
        obtain w where "\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] = w \<cdot> \<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]] \<and>
                        l = w \<cdot> \<i>\<^sub>0[\<i>\<^sub>0[t, u], \<i>\<^sub>0[v, u]]"
          using 3 C.pushout_universal by (metis C.inj_sym)
        thus "\<exists>w. \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] = w \<cdot> \<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]]" by auto
      qed
      show "\<And>t u v. \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<noteq> null
                       \<Longrightarrow> \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] = \<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]]"
      proof -
        fix t u v
        assume vt_ut: "\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] \<noteq> null"
        have tu: "\<i>\<^sub>0[t, u] \<noteq> null"
          using vt_ut
          by (metis \<open>\<And>u t. \<i>\<^sub>0[t, u] \<noteq> null \<Longrightarrow> \<i>\<^sub>0[u, t] \<noteq> null\<close> null_is_zero(2))
        have tv: "\<i>\<^sub>0[t, v] \<noteq> null"
          using vt_ut
          by (metis \<open>\<And>u t. \<i>\<^sub>0[t, u] \<noteq> null \<Longrightarrow> \<i>\<^sub>0[u, t] \<noteq> null\<close> null_is_zero(1))
        obtain w where w: "\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] = w \<cdot> \<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]]"
          using tu tv vt_ut * by blast
        have vu_tu: "\<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]] \<noteq> null"
          using w null_char vt_ut by fastforce
        obtain w' where w': "\<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]] = w' \<cdot> \<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]]"
          using 0 vu_tu * null_is_zero(2) by metis
        have "C.ide (w \<cdot> w')"
          using w w' vt_ut
          by (metis C.comp_cod_arr C.ext C.ide_cod C.inj_prefix(1-2) C.seqE
              null_char)
        hence "C.ide w"
          using w w'
          by (metis C.comp_arr_ide C.ide_compE C.inj_arr_dom(1) C.inj_prefix(2)
              C.seqE)
        thus "\<i>\<^sub>0[\<i>\<^sub>0[v, t], \<i>\<^sub>0[u, t]] = \<i>\<^sub>0[\<i>\<^sub>0[v, u], \<i>\<^sub>0[t, u]]"
          using w C.comp_ide_arr
          by (metis C.ext null_char vt_ut)
      qed
    qed

    lemma con_char:
    shows "con t u \<longleftrightarrow> C.bounded_span t u"
      by (metis C.commutative_squareE C.inj0_ext C.not_arr_null
          C.pushout_commutes con_def null_char)

    lemma arr_char:
    shows "arr t \<longleftrightarrow> C.arr t"
      by (metis C.arr_cod C.inj_arr_self(1) C.not_arr_null C.pushout_commutes
          arr_def C.commutative_squareE con_char con_def null_char)

    lemma ide_char:
    shows "ide a \<longleftrightarrow> C.ide a"
      by (metis C.ide_char C.ide_char' C.ide_def C.inj_arr_self(1) arr_char ide_def
          null_char con_def ide_implies_arr)

    interpretation rts \<open>\<lambda>h k. \<i>\<^sub>0[h, k]\<close>
    proof
      show "\<And>a t. \<lbrakk>ide a; con t a\<rbrakk> \<Longrightarrow> \<i>\<^sub>0[t, a] = t"
        using C.inj_arr_dom con_char ide_char by fastforce
      thus "\<And>a t. \<lbrakk>ide a; con a t\<rbrakk> \<Longrightarrow> ide \<i>\<^sub>0[a, t]"
        by (metis con_sym cube ide_def con_def)
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        by (metis arr_char C.eq_iff_ide_inj ide_char resid_arr_self)
      thus "\<And>t u. con t u \<Longrightarrow> \<exists>a. ide a \<and> con a t \<and> con a u"
        using con_char ide_char
        by (metis C.ide_dom C.inj_arr_dom(1) C.pushout_commutes
            C.commutative_squareE con_implies_arr(1) con_sym arr_resid_iff_con)
      show "\<And>t u v. \<lbrakk>ide \<i>\<^sub>0[t, u]; con u v\<rbrakk> \<Longrightarrow> con \<i>\<^sub>0[t, u] \<i>\<^sub>0[v, u]"
        by (metis (no_types, lifting) C.dom_inj(1) C.ideD(2) C.inj_arr_dom(1)
            arr_char con_char ide_char arr_resid_iff_con con_sym ide_implies_arr)
    qed

    interpretation extensional_rts resid
      by unfold_locales
         (metis C.ideD(2) C.inj_sym C.pushout_commutes prfx_implies_con
                C.commutative_squareE C.comp_cod_arr con_char ide_char)

    lemma src_char:
    assumes "arr t"
    shows "src t = C.dom t"
      by (metis C.ide_dom C.inj_arr_dom(1) arr_char arr_resid_iff_con assms
          con_imp_eq_src ide_char src_ide)

    lemma trg_char:
    assumes "arr t"
    shows "trg t = C.cod t"
      by (metis assms C.inj_arr_self(1) resid_arr_self arr_char)

    lemma seq_char:
    shows "seq t u \<longleftrightarrow> C.seq u t"
      using seq_def sources_char\<^sub>W\<^sub>E targets_char\<^sub>W\<^sub>E arr_char src_char trg_char
      by auto

    lemma comp_char:
    shows "comp t u = u \<cdot> t"
      by (metis C.cod_comp C.ext C.inj_arr_self(1) C.inj_prefix(1-2)
          arr_char composable_imp_seq cong_reflexive comp_def null_char
          prfx_decomp seq_char)

    sublocale extensional_rts_with_composites resid
      by unfold_locales
         (metis C.not_arr_null composable_iff_comp_not_null comp_char null_char
           seq_char)

    proposition is_extensional_rts_with_composites:
    shows "extensional_rts_with_composites resid"
      ..

  end

  context extensional_rts_with_composites_as_category
  begin

    interpretation R: underlying_rts comp ..

    lemma resid_char:
    shows "R.resid = resid"
    proof -
      have 1: "\<And>t u. R.con t u = (t \<frown> u)"
      proof -
        fix t u
        have "R.con t u \<longleftrightarrow> bounded_span t u"
          using R.con_char by blast
        also have "... \<longleftrightarrow> (\<exists>v w. seq v t \<and> comp v t = comp w u)"
          unfolding bounded_span_def
          by (metis (lifting) HOL.ext cod_comp commutative_square_def dom_comp seqE seqI)
        also have "... \<longleftrightarrow> (\<exists>v w. A.seq t v \<and> A.comp t v = A.comp u w)"
          using seq_char by simp
        also have "... \<longleftrightarrow> A.con t u"
          by (metis A.arr_def A.arr_resid_iff_con A.con_comp_iff\<^sub>E\<^sub>C(2) A.con_implies_arr(2)
              A.diamond_commutes A.has_joins A.join_expansion(2) A.seq_implies_arr_comp)
        finally show "R.con t u = (t \<frown> u)" by blast
      qed
      have "\<And>t u. R.resid t u = t \\ u"
        using 1
        by (metis A.con_def R.con_char has_bounded_pushouts inj0_ext null_char pushouts_unique(2))
      thus ?thesis by blast
    qed

  end

  locale pushout_preserving_functor =
    "functor" +
  assumes preserves_pushouts: "A.pushout_square f g h k
                                  \<Longrightarrow> B.pushout_square (F f) (F g) (F h) (F k)"

  lemma pushout_preserving_functor_identity:
  assumes "category A"
  shows "pushout_preserving_functor A A (identity_functor.map A)"
  proof -
    interpret A: category A
      using assms by blast
    interpret A: identity_functor A ..
    show ?thesis
    proof
      show "\<And>f g h k. A.pushout_square f g h k \<Longrightarrow>
                         A.pushout_square (A.map f) (A.map g) (A.map h) (A.map k)"
        by (simp add: A.commutative_square_def A.pushout_square_def)
    qed
  qed

  lemma pushout_preserving_functor_comp:
  assumes "pushout_preserving_functor A B F"
  and "pushout_preserving_functor B C G"
  shows "pushout_preserving_functor A C (G \<circ> F)"
  proof -
    interpret F: pushout_preserving_functor A B F
      using assms(1) by blast
    interpret G: pushout_preserving_functor B C G
      using assms(2) by blast
    interpret GoF: composite_functor A B C F G ..
    show ?thesis
      using F.preserves_pushouts G.preserves_pushouts
      by unfold_locales auto
  qed

  lemma pushout_preserving_functor_const:
  assumes "category A" and "category B"
  and "partial_composition.ide B b"
  shows "pushout_preserving_functor A B (constant_functor.map A B b)"
  proof -
    interpret A: category A
      using assms(1) by blast
    interpret B: category B
      using assms(2) by blast
    interpret F: constant_functor A B b
      using assms(3) by unfold_locales blast
    show ?thesis
    proof
      fix f g h k
      assume 1: "A.pushout_square f g h k"
      show "B.pushout_square (F.map f) (F.map g) (F.map h) (F.map k)"
      proof
        show 2: "B.cospan (F.map f) (F.map g)"
          using 1 A.pushout_square_def by auto
        show 3: "B.span (F.map h) (F.map k)"
          using 1 A.commutative_square_def A.pushout_square_def F.value_is_ide by force
        show "B.dom (F.map f) = B.cod (F.map h)"
          using 2 3 B.ide_char F.map_simp F.preserves_reflects_arr F.value_is_ide
          by metis
        show "B (F.map f) (F.map h) = B (F.map g) (F.map k)"
          using 2 3 by force
        fix f' g'
        assume 4: "B.commutative_square f' g' (F.map h) (F.map k)"
        show "\<exists>!l. B l (F.map f) = f' \<and> B l (F.map g) = g'"
          by (metis (lifting) ext 2 4 B.commutative_square_def B.comp_arr_dom B.ide_char
              B.seqE F.map_simp F.preserves_reflects_arr F.value_is_ide)
      qed
    qed
  qed

  lemma invertible_functor_is_pushout_preserving:
  assumes "invertible_functor A B F"
  shows "pushout_preserving_functor A B F"
  proof -
    interpret F: invertible_functor A B F
      using assms by blast
    obtain G where G: "inverse_functors A B G F"
      using F.has_unique_inverse by blast
    interpret FG: inverse_functors A B G F
      using G by blast
    show ?thesis
    proof
      fix f g h k
      assume 1: "F.A.pushout_square f g h k"
      show "F.B.pushout_square (F f) (F g) (F h) (F k)"
      proof
        show "F.B.cospan (F f) (F g)"
          using 1 F.A.commutative_square_def F.A.pushout_square_def by force
        show "F.B.span (F h) (F k)"
          using 1 F.A.pushout_square_def by auto
        show "F.B.dom (F f) = F.B.cod (F h)"
          using 1 F.A.pushout_square_def by auto
        show "B (F f) (F h) = B (F g) (F k)"
          by (metis 1 F.A.commutative_square_def F.A.pushout_square_def F.A.seqI
              F.G.preserves_comp)
        fix f' g'
        assume 2: "F.B.commutative_square f' g' (F h) (F k)"
        show "\<exists>!l'. B l' (F f) = f' \<and> B l' (F g) = g'"
        proof -
          have 3: "F.A.commutative_square (G f') (G g') h k"
          proof
            show "F.A.cospan (G f') (G g')"
              by (metis 2 F.B.commutative_square_def FG.F.preserves_arr FG.F.preserves_cod)
            show "F.A.span h k"
              using 1 F.A.pushout_square_def by blast
            show "F.A.dom (G f') = F.A.cod h"
              by (metis 2 F.A.map_simp F.B.commutative_square_def FG.F.preserves_cod
                  FG.F.preserves_dom FG.inv' \<open>F.A.span h k\<close> o_apply)
            show "A (G f') h = A (G g') k"
              by (metis 2 F.A.map_simp F.B.commutative_squareE FG.F.preserves_comp G
                  \<open>F.A.span h k\<close> F.B.seqI comp_eq_dest_lhs inverse_functors.inv')
          qed
          obtain l where l: "A l f = G f' \<and> A l g = G g'"
            using 1 3 by (meson F.A.pushout_square_def)
          have "B (F l) (F f) = f' \<and> B (F l) (F g) = g'"
            by (metis 2 F.B.commutative_square_def F.B.identity_functor_axioms
                F.G.preserves_comp FG.F.preserves_arr FG.inv identity_functor.map_simp
                l o_apply)
          moreover have "\<And>l'. \<lbrakk>B l' (F f) = f'; B l' (F g) = g'\<rbrakk> \<Longrightarrow> F l = l'"
          proof -
            fix l'
            assume 4: "B l' (F f) = f'" and 5: "B l' (F g) = g'"
            have "A (G l') f = G f' \<and> A (G l') g = G g'"
              by (metis 3 4 5 F.A.commutative_square_def F.A.map_simp
                  F.G.preserves_reflects_arr FG.F.as_nat_trans.preserves_comp_2
                  FG.F.preserves_reflects_arr FG.inv' \<open>F.B.cospan (F f) (F g)\<close> o_apply)
            hence "G l' = l"
              using 1 3 l F.A.pushout_square_def [of f g h k] by blast
            thus "F l = l'"
              by (metis 3 F.A.commutative_squareE F.A.null_is_zero(1)
                  F.A.partial_composition_axioms F.B.map_def FG.F.extensionality FG.inv
                  l o_apply partial_composition.not_arr_null)
          qed
          ultimately show "\<exists>!l'. B l' (F f) = f' \<and> B l' (F g) = g'" by blast
        qed
      qed
    qed
  qed

  locale simulation_as_functor =
    simulation +
    A: extensional_rts_with_composites A +
    B: extensional_rts_with_composites B
  begin

    sublocale A.as_category: extensional_rts_with_composites_as_category A ..
    sublocale B.as_category: extensional_rts_with_composites_as_category B ..

    sublocale "functor" A.as_category.comp B.as_category.comp F
    proof
      show "\<And>f. \<not> A.as_category.arr f \<Longrightarrow> F f = B.as_category.null"
        by (simp add: A.as_category.arr_char B.as_category.null_char extensionality)
      show "\<And>f. A.as_category.arr f \<Longrightarrow> B.as_category.arr (F f)"
        by (simp add: A.as_category.arr_char B.as_category.arr_char)
      show "\<And>f. A.as_category.arr f \<Longrightarrow> B.as_category.dom (F f) = F (A.as_category.dom f)"
        by (simp add: A.as_category.arr_char A.as_category.dom_char
            B.as_category.dom_char B.src_eqI)
      show "\<And>f. A.as_category.arr f \<Longrightarrow> B.as_category.cod (F f) = F (A.as_category.cod f)"
        by (simp add: A.as_category.arr_char A.as_category.cod_char
            B.as_category.cod_char)
      show "\<And>g f. A.as_category.seq g f \<Longrightarrow>
                     F (A.as_category.comp g f) = B.as_category.comp (F g) (F f)"
        by (metis A.as_category.seq_char A.comp_is_composite_of(1)
            A.rts_with_chosen_composites_axioms A.seq_implies_arr_comp
            B.extensional_rts_axioms rts_with_chosen_composites.composable_iff_arr_comp\<^sub>C\<^sub>C
            simulation_axioms simulation_to_extensional_rts.intro
            simulation_to_extensional_rts.preserves_comp)
    qed

    lemma is_functor:
    shows "functor A.as_category.comp B.as_category.comp F"
      ..

    sublocale pushout_preserving_functor A.as_category.comp B.as_category.comp F
    proof
      fix f g h k
      assume 1: "A.as_category.pushout_square f g h k"
      show "B.as_category.pushout_square (F f) (F g) (F h) (F k)"
      proof
        show "B.as_category.cospan (F f) (F g)"
          by (metis 1 A.as_category.commutative_square_def A.as_category.pushout_square_def
              preserves_arr preserves_cod)
        show "B.as_category.span (F h) (F k)"
          using 1 A.as_category.pushout_square_def by auto
        show "B.as_category.dom (F f) = B.as_category.cod (F h)"
          by (metis 1 A.as_category.commutative_squareE A.as_category.pushout_square_def
              preserves_cod preserves_dom)
        show "B.as_category.comp (F f) (F h) = B.as_category.comp (F g) (F k)"
          by (metis 1 A.as_category.arr_char A.as_category.cod_char
              A.as_category.commutative_square_def A.as_category.dom_char
              A.as_category.pushout_square_def as_nat_trans.preserves_comp_2
              extensional_rts_with_composites.arr_comp\<^sub>E\<^sub>C simulation_as_functor_axioms
              simulation_as_functor_def)
        show "\<And>f' g'. B.as_category.commutative_square f' g' (F h) (F k) \<Longrightarrow>
                         \<exists>!l. B.as_category.comp l (F f) = f' \<and> B.as_category.comp l (F g) = g'"
        proof -
          fix f' g'
          assume 2: "B.as_category.commutative_square f' g' (F h) (F k)"
          moreover have "B.as_category.pushout_square (F k \\\<^sub>B F h) (F h \\\<^sub>B F k) (F h) (F k)"
            using 2 B.as_category.has_bounded_pushouts by blast
          ultimately have "\<exists>!l. B.as_category.comp l (F k \\\<^sub>B F h) = f' \<and>
                                B.as_category.comp l (F h \\\<^sub>B F k) = g'"
            unfolding B.as_category.pushout_square_def by presburger
          moreover have "f = k \\\<^sub>A h \<and> g = h \\\<^sub>A k"
            by (metis 1 A.as_category.bounded_spanI A.as_category.has_bounded_pushouts
                A.as_category.pushout_square_def A.as_category.pushouts_unique(1-2))
          ultimately show "\<exists>!l. B.as_category.comp l (F f) = f' \<and> B.as_category.comp l (F g) = g'"
            unfolding B.as_category.pushout_square_def
            using A.arr_resid_iff_con A.as_category.arr_char \<open>B.as_category.cospan (F f) (F g)\<close>
            by auto
        qed
      qed
    qed

    lemma is_pushout_preserving_functor:
    shows "pushout_preserving_functor A.as_category.comp B.as_category.comp F"
      ..

  end

  lemma simulation_is_pushout_preserving_functor:
  assumes "extensional_rts_with_composites A"
  and "extensional_rts_with_composites B"
  and "simulation A B F"
  shows "pushout_preserving_functor
           (extensional_rts_with_composites_as_category.comp A)
           (extensional_rts_with_composites_as_category.comp B)
           F"
  proof -
    interpret A: extensional_rts_with_composites A
      using assms(1) by blast
    interpret B: extensional_rts_with_composites B
      using assms(2) by blast
    interpret F: simulation A B F
      using assms(3) by blast
    interpret F: simulation_as_functor A B F ..
    show ?thesis
      using F.pushout_preserving_functor_axioms by blast
  qed

  lemma pushout_preserving_functor_is_simulation:
  assumes "category_of_transitions A"
  and "category_of_transitions B"
  and "pushout_preserving_functor A B F"
  shows "simulation
           (category_with_bounded_pushouts.inj0 A)
           (category_with_bounded_pushouts.inj0 B)
           F"
  proof -
    interpret A: category_of_transitions A
      using assms(1) by blast
    interpret B: category_of_transitions B
      using assms(2) by blast
    interpret F: pushout_preserving_functor A B F
      using assms(3) by blast
    interpret A': underlying_rts A ..
    interpret B': underlying_rts B ..
    show ?thesis
    proof
      show "\<And>t. \<not> A'.arr t \<Longrightarrow> F t = B'.null"
        by (simp add: A'.arr_char B'.null_char F.extensionality)
      show "\<And>t u. A'.con t u \<Longrightarrow> B'.con (F t) (F u)"
      proof -
        fix t u
        assume con: "A'.con t u"
        obtain v w where vw: "A'.seq t v \<and> A'.comp t v = A'.comp u w"
          using con
          by (meson A'.diamond_commutes A'.has_joins A'.join_expansion(2))
        hence "F (A v t) = F (A w u)"
          by (simp add: A'.comp_char)
        hence "B (F v) (F t) = B (F w) (F u)"
          by (metis A'.comp_char A'.seq_char F.preserves_comp vw)
        thus "B'.con (F t) (F u)"
          by (metis A'.seq_char B'.bounded_imp_con\<^sub>E B'.comp_char B'.prfx_reflexive
              B'.seq_char B'.seq_implies_arr_comp F.preserves_seq vw)
      qed
      show "\<And>t u. A'.con t u \<Longrightarrow> F (A.inj0 t u) = B.inj0 (F t) (F u)"
        by (meson A'.con_char A.has_bounded_pushouts B.category_of_transitions_axioms
            F.preserves_pushouts category_of_transitions.pushouts_unique(2))
    qed
  qed

end
