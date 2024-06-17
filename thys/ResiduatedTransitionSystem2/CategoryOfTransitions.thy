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
    elementary_category_with_bounded_pushouts +
  assumes arr_implies_epi: "arr t \<Longrightarrow> epi t"
  and iso_implies_ide: "iso t \<Longrightarrow> ide t"
  begin

    (* TODO: Move with rest of commutative_square facts (currently CategoryWithPullbacks). *)
    lemma commutative_square_sym:
    shows "commutative_square f g h k \<Longrightarrow> commutative_square g f k h"
      by auto

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
              comp_ide_arr epiE epi_implies_arr ide_cod iso_implies_ide
              comp_assoc sectionI seqE)
      qed
      ultimately show ?thesis by auto
    qed

    text \<open>
      In this setting, pushouts are uniquely determined.
    \<close>

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
          by (metis arr_implies_epi epiE seqE)
        thus ?thesis
          by (metis ideD(1) ide_is_iso inv_comp_right(2) iso_iff_section_and_epi
              sectionI seqE arr_implies_epi iso_implies_ide)
      qed
      show "f = \<i>\<^sub>1[h, k]" and "g = \<i>\<^sub>0[h, k]"
        using 1 w w' by (metis comp_ide_arr ext null_is_zero(2))+
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
        by (metis arr_implies_epi commutative_squareE epiE)
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

    interpretation Category.partial_magma \<open>\<lambda>u t. t \<cdot> u\<close>
      using A.comp_null by unfold_locales metis
    interpretation Category.partial_composition \<open>\<lambda>u t. t \<cdot> u\<close> ..

    lemma null_char:
    shows "null = A.null"
      by (metis A.comp_null(1) null_is_zero(1))

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

    sublocale category \<open>\<lambda>u t. t \<cdot> u\<close>
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
    shows "category (\<lambda>u t. t \<cdot> u)"
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

  section "Characterization"

  text \<open>
    The categories arising from extensional RTS's with composites are categories
    of transitions.
  \<close>

  context extensional_rts_with_composites_as_category
  begin

    sublocale category_of_transitions \<open>\<lambda>u t. t \<cdot> u\<close> \<open>\<lambda>h k. h \ k\<close> \<open>\<lambda>h k. k \ h\<close>
    proof
      show 1: "\<And>h k. \<not> bounded_span h k \<Longrightarrow> k \\ h = null"
      proof -
        fix h k
        have "k \\ h \<noteq> null \<Longrightarrow> commutative_square (k \\ h) (h \\ k) h k"
          by (metis (no_types, lifting) A.apex_sym A.conI A.con_imp_eq_src
              A.diamond_commutes dom_char cod_char commutative_squareI
              A.join_expansion(2) null_char seqE seq_char)
        thus "\<not> bounded_span h k \<Longrightarrow> k \\ h = null"
          by auto
      qed
      show "\<And>h k. \<not> bounded_span h k \<Longrightarrow> h \\ k = null"
        using 1 bounded_span_sym by blast
      show "\<And>h k. bounded_span h k \<Longrightarrow> commutative_square (k \\ h) (h \\ k) h k"
      proof -
        fix h k
        assume 1: "bounded_span h k"
        hence con: "h \<frown> k"
          by (metis A.bounded_imp_con\<^sub>E A.cong_reflexive arr_char
              bounded_span_def commutative_squareE seqI)
        show "commutative_square (k \\ h) (h \\ k) h k"
        proof
          show "cospan (k \\ h) (h \\ k)"
            by (simp add: con A.apex_sym A.con_sym arr_char cod_char)
          show "span h k"
            using 1 by blast
          show "dom (k \\ h) = cod h"
            using A.join_expansion(2) con seq_char by blast
          show "h \<cdot> k \\ h = k \<cdot> h \\ k"
            using A.diamond_commutes by blast
        qed
      qed
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
          by (metis 1 3 A.comp_assoc\<^sub>E\<^sub>C A.comp_resid_prfx A.induced_arrow(2)
              A.join_expansion(1) A.seq_implies_arr_comp commutative_squareE
              seqI seq_char)
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
      show "\<And>t. arr t \<Longrightarrow> epi t"
        using arr_implies_epi by simp
      show "\<And>t. iso t \<Longrightarrow> ide t"
        using iso_implies_ide by simp
    qed

    proposition is_category_of_transitions:
    shows "category_of_transitions (\<lambda>u t. t \<cdot> u) (\<lambda>h k. h \\ k) (\<lambda>h k. k \\ h)"
      ..

  end

  text \<open>
    Every category of transitions is derived from an underlying extensional RTS,
    obtained by using pushouts to define residuation.
  \<close>

  locale underlying_rts =
    C: category_of_transitions
  begin

    interpretation ResiduatedTransitionSystem.partial_magma \<open>\<lambda>h k. \<i>\<^sub>0[h, k]\<close>
      by unfold_locales
         (metis C.inj1_ext C.inj_sym C.not_arr_null C.pushout_commutes
           C.commutative_squareE)

    lemma null_char:
    shows "null = C.null"
      using null_eqI C.inj0_ext C.not_arr_null C.pushout_commutes
      by (metis C.commutative_squareE)

    interpretation residuation \<open>\<lambda>h k. \<i>\<^sub>0[h, k]\<close>
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
          using tu tv vt_ut C.commutative_squareE C.comp_assoc C.inj0_ext
                C.inj_sym C.pushout_commutes null_char
          by metis (* 8 sec *)
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
              by (metis (mono_tags, opaque_lifting) C.commutative_square_def
                  C.ext C.inj0_ext C.inj_sym C.pushout_commutes C.seqI
                  null_char vt_ut)
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

    interpretation extensional_rts \<open>\<lambda>h k. \<i>\<^sub>0[h, k]\<close>
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
      using seq_def sources_char targets_char\<^sub>W\<^sub>E arr_char src_char trg_char
      by auto

    lemma comp_char:
    shows "comp t u = u \<cdot> t"
      by (metis C.cod_comp C.ext C.inj_arr_self(1) C.inj_prefix(1-2)
          arr_char composable_imp_seq cong_reflexive comp_def null_char
          prfx_decomp seq_char)

    sublocale extensional_rts_with_composites \<open>\<lambda>h k. \<i>\<^sub>0[h, k]\<close>
      by unfold_locales
         (metis C.not_arr_null composable_iff_comp_not_null comp_char null_char
           seq_char)

    proposition is_extensional_rts_with_composites:
    shows "extensional_rts_with_composites (\<lambda>h k. \<i>\<^sub>0[h, k])"
      ..

  end

end
