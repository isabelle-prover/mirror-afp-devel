(*  Title:       CartesianClosedMonoidalCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Cartesian Closed Monoidal Categories"

text\<open>
  A \emph{cartesian closed monoidal category} is a cartesian monoidal category that is a
  closed monoidal category with respect to a chosen product.  This is not quite the same
  thing as a cartesian closed category, because a cartesian monoidal category
  (being a monoidal category) has chosen structure (the tensor, associators, and unitors),
  whereas we have defined a cartesian closed category to be an abstract category satisfying
  certain properties that are expressed without assuming any chosen structure.

\<close>

theory CartesianClosedMonoidalCategory
imports Category3.CartesianClosedCategory MonoidalCategory.CartesianMonoidalCategory
        ClosedMonoidalCategory
begin

  locale cartesian_closed_monoidal_category =
    cartesian_monoidal_category +
    closed_monoidal_category

  locale elementary_cartesian_closed_monoidal_category =
    cartesian_monoidal_category +
    elementary_closed_monoidal_category
  begin

    lemmas prod_eq_tensor [simp]

  end

  text\<open>
    The following is the main purpose for the current theory: to show that a
    cartesian closed category with chosen structure determines a cartesian closed
    monoidal category.
  \<close>

  context elementary_cartesian_closed_category
  begin

    interpretation CMC: cartesian_monoidal_category C Prod \<alpha> \<iota>
      using extends_to_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>C by blast

    interpretation CMC: closed_monoidal_category C Prod \<alpha> \<iota>
      using CMC.T.is_extensional interchange left_adjoint_prod
      by unfold_locales
         (auto simp add: left_adjoint_functor.ex_terminal_arrow)

    lemma extends_to_closed_monoidal_category\<^sub>E\<^sub>C\<^sub>C\<^sub>C:
    shows "closed_monoidal_category C Prod \<alpha> \<iota>"
      ..

    lemma extends_to_cartesian_closed_monoidal_category\<^sub>E\<^sub>C\<^sub>C\<^sub>C:
    shows "cartesian_closed_monoidal_category C Prod \<alpha> \<iota>"
      ..

    interpretation CMC: elementary_monoidal_category
                          C CMC.tensor CMC.unity CMC.lunit CMC.runit CMC.assoc
      using CMC.induces_elementary_monoidal_category by blast

    interpretation CMC: elementary_closed_monoidal_category
                         C Prod \<alpha> \<iota> exp eval curry
      using eval_in_hom_ax curry_in_hom uncurry_curry_ax curry_uncurry_ax
      by unfold_locales auto

    lemma extends_to_elementary_closed_monoidal_category\<^sub>E\<^sub>C\<^sub>C\<^sub>C:
    shows "elementary_closed_monoidal_category C Prod \<alpha> \<iota> exp eval curry"
      ..

    lemma extends_to_elementary_cartesian_closed_monoidal_category\<^sub>E\<^sub>C\<^sub>C\<^sub>C:
    shows "elementary_cartesian_closed_monoidal_category C Prod \<alpha> \<iota> exp eval curry"
      ..

  end

  context elementary_cartesian_closed_monoidal_category
  begin

    interpretation elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by blast

    text \<open>
      The following fact is not used in the present article, but it is a natural
      and likely useful lemma for which I constructed a proof at one point.
      The proof requires cartesianness; I suspect this is essential, but I am not
      absolutely certain of it.
    \<close>

    lemma isomorphic_exp_prod:
    assumes "ide a" and "ide b" and "ide x"
    shows "\<guillemotleft>\<langle>Curry[exp x (a \<otimes> b), x, a] (\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b)),
             Curry[exp x (a \<otimes> b), x, b] (\<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b))\<rangle>
               : exp x (a \<otimes> b) \<rightarrow> exp x a \<otimes> exp x b\<guillemotright>"
        (is "\<guillemotleft>\<langle>?C, ?D\<rangle> : exp x (a \<otimes> b) \<rightarrow> exp x a \<otimes> exp x b\<guillemotright>")
    and "\<guillemotleft>Curry[exp x a \<otimes> exp x b, x, a \<otimes> b]
               \<langle>eval x a \<cdot> \<langle>\<pp>\<^sub>1[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                           \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>,
                eval x b \<cdot> \<langle>\<pp>\<^sub>0[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                           \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>\<rangle>
             : exp x a \<otimes> exp x b \<rightarrow> exp x (a \<otimes> b)\<guillemotright>"
        (is "\<guillemotleft>Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>
                : exp x a \<otimes> exp x b \<rightarrow> exp x (a \<otimes> b)\<guillemotright>")
    and "inverse_arrows
           (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b]
              \<langle>eval x a \<cdot> \<langle>\<pp>\<^sub>1[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                          \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>,
               eval x b \<cdot> \<langle>\<pp>\<^sub>0[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                          \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>\<rangle>)
           \<langle>Curry[exp x (a \<otimes> b), x, a] (\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b)),
            Curry[exp x (a \<otimes> b), x, b] (\<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b))\<rangle>"
    and "isomorphic (exp x (a \<otimes> b)) (exp x a \<otimes> exp x b)"
    proof -
      have A: "\<guillemotleft>?A : (exp x a \<otimes> exp x b) \<otimes> x \<rightarrow> a\<guillemotright>"
        using assms by auto
      have B: "\<guillemotleft>?B : (exp x a \<otimes> exp x b) \<otimes> x \<rightarrow> b\<guillemotright>"
        using assms by auto
      have AB: "\<guillemotleft>\<langle>?A, ?B\<rangle> : (exp x a \<otimes> exp x b) \<otimes> x \<rightarrow> a \<otimes> b\<guillemotright>"
        by (metis A B ECC.tuple_in_hom prod_eq_tensor)
      have C: "\<guillemotleft>?C : exp x (a \<otimes> b) \<rightarrow> exp x a\<guillemotright>"
        using assms by auto
      have D: "\<guillemotleft>?D : exp x (a \<otimes> b) \<rightarrow> exp x b\<guillemotright>"
        using assms by auto
      show CD: "\<guillemotleft>\<langle>?C, ?D\<rangle> : exp x (a \<otimes> b) \<rightarrow> exp x a \<otimes> exp x b\<guillemotright>"
        using C D by fastforce
      show 1: "\<guillemotleft>Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>
                  : (exp x a \<otimes> exp x b) \<rightarrow> exp x (a \<otimes> b)\<guillemotright>"
        by (simp add: AB assms(1-3) Curry_in_hom)
      show "inverse_arrows (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>) \<langle>?C, ?D\<rangle>"
      proof
        show "ide (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> \<cdot> \<langle>?C, ?D\<rangle>)"
        proof -
          have "Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> \<cdot> \<langle>?C, ?D\<rangle> =
                Curry[exp x (a \<otimes> b), x, a \<otimes> b] (\<langle>?A, ?B\<rangle> \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x))"
            using assms AB CD comp_Curry_arr by presburger
          also have "... = Curry[exp x (a \<otimes> b), x, a \<otimes> b]
                             \<langle>?A \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x), ?B \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x)\<rangle>"
          proof -
            have "span ?A ?B"
              using A B by fastforce
            moreover have "arr (\<langle>?C, ?D\<rangle> \<otimes> x)"
              using assms CD by auto
            moreover have "dom ?A = cod (\<langle>?C, ?D\<rangle> \<otimes> x)"
              by (metis A CD assms(3) cod_tensor ide_char in_homE)
            ultimately show ?thesis
              using assms ECC.comp_tuple_arr by metis
          qed
          also have "... = Curry[exp x (a \<otimes> b), x, a \<otimes> b]
                             \<langle>Uncurry[x, a] ?C, eval x b \<cdot> (?D \<otimes> x)\<rangle>"
          proof -
            have "?A \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x) = Uncurry[x, a] ?C"
            proof -
              have "?A \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x) =
                    eval x a \<cdot>
                      \<langle>\<pp>\<^sub>1[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x] \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x),
                       \<pp>\<^sub>0[exp x a \<otimes> exp x b, x] \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x)\<rangle>"
                using assms ECC.comp_tuple_arr comp_assoc by simp
              also have "... = eval x a \<cdot>
                                 \<langle>?C \<cdot> \<pp>\<^sub>1[exp x (a \<otimes> b), x], x \<cdot> \<pp>\<^sub>0[exp x (a \<otimes> b), x]\<rangle>"
                using assms ECC.pr_naturality(1-2) by auto
              also have "... = eval x a \<cdot> (?C \<otimes> x) \<cdot>
                                 \<langle>\<pp>\<^sub>1[exp x (a \<otimes> b), x], \<pp>\<^sub>0[exp x (a \<otimes> b), x]\<rangle>"
                using assms
                      ECC.prod_tuple
                        [of "\<pp>\<^sub>1[exp x (a \<otimes> b), x]" "\<pp>\<^sub>0[exp x (a \<otimes> b), x]" ?C x]
                by simp
              also have "... = Uncurry[x, a] ?C"
                using assms C ECC.tuple_pr comp_arr_ide comp_arr_dom by auto
              finally show ?thesis by blast
            qed
            moreover have "?B \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x) = Uncurry[x, b] ?D"
            proof -
              have "?B \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x) =
                    eval x b \<cdot>
                      \<langle>\<pp>\<^sub>0[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x] \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x),
                       \<pp>\<^sub>0[exp x a \<otimes> exp x b, x] \<cdot> (\<langle>?C, ?D\<rangle> \<otimes> x)\<rangle>"
                using assms ECC.comp_tuple_arr comp_assoc by simp
              also have "... = eval x b \<cdot>
                                 \<langle>?D \<cdot> \<pp>\<^sub>1[exp x (a \<otimes> b), x], x \<cdot> \<pp>\<^sub>0[exp x (a \<otimes> b), x]\<rangle>"
                using assms C ECC.pr_naturality(1-2) by auto
              also have "... = eval x b \<cdot> (?D \<otimes> x) \<cdot>
                                 \<langle>\<pp>\<^sub>1[exp x (a \<otimes> b), x], \<pp>\<^sub>0[exp x (a \<otimes> b), x]\<rangle>"
                using assms
                      ECC.prod_tuple
                        [of "\<pp>\<^sub>1[exp x (a \<otimes> b), x]" "\<pp>\<^sub>0[exp x (a \<otimes> b), x]" ?D x]
                by simp
              also have "... = Uncurry[x, b] ?D"
                using assms C ECC.tuple_pr comp_arr_ide comp_arr_dom by auto
              finally show ?thesis by blast
            qed
            ultimately show ?thesis by simp
          qed
          also have "... = Curry[exp x (a \<otimes> b), x, a \<otimes> b]
                             (\<langle>\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b), \<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b)\<rangle>)"
            using assms Uncurry_Curry by auto
          also have "... = Curry[exp x (a \<otimes> b), x, a \<otimes> b]
                             (\<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle> \<cdot> eval x (a \<otimes> b))"
            using assms ECC.comp_tuple_arr [of "\<pp>\<^sub>1[a, b]" "\<pp>\<^sub>0[a, b]" "eval x (a \<otimes> b)"]
            by simp
          also have "... = Curry[exp x (a \<otimes> b), x, a \<otimes> b] (eval x (a \<otimes> b))"
            using assms comp_cod_arr by simp
          also have "... = exp x (a \<otimes> b)"
            using assms Curry_Uncurry ide_exp ide_in_hom tensor_preserves_ide
                  Uncurry_exp
            by metis
          finally have "Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> \<cdot> \<langle>?C, ?D\<rangle> =
                        exp x (a \<otimes> b)"
            by blast
          thus ?thesis
            using assms ide_exp tensor_preserves_ide by presburger
        qed
        show "ide (\<langle>?C, ?D\<rangle> \<cdot> Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>)"
        proof -
          have 2: "span \<pp>\<^sub>1[exp x a \<otimes> exp x b, x] \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]"
            using assms by simp
          have 3: "seq x \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]"
            using assms by simp
          have "\<langle>?C, ?D\<rangle> \<cdot> Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> =
                \<langle>?C \<cdot> Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>,
                 ?D \<cdot> Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>\<rangle>"
            using assms C D 1 ECC.comp_tuple_arr by (metis in_homE)
          also have "... = \<langle>\<pp>\<^sub>1[exp x a, exp x b], \<pp>\<^sub>0[exp x a, exp x b]\<rangle>"
          proof -
            have "Curry[exp x (a \<otimes> b), x, a] (\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b)) \<cdot>
                    Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> =
                  \<pp>\<^sub>1[exp x a, exp x b]"
            proof -
              have "Curry[exp x (a \<otimes> b), x, a] (\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b)) \<cdot>
                      Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> =
                    Curry[exp x a \<otimes> exp x b, x, a]
                      ((\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b)) \<cdot>
                         (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> \<otimes> x))"
                using assms 1 comp_Curry_arr by auto
              also have "... = Curry[exp x a \<otimes> exp x b, x, a]
                                 (\<pp>\<^sub>1[a, b] \<cdot> eval x (a \<otimes> b) \<cdot>
                                    (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> \<otimes> x))"
                using comp_assoc by simp
              also have "... = Curry[exp x a \<otimes> exp x b, x, a] (\<pp>\<^sub>1[a, b] \<cdot> \<langle>?A, ?B\<rangle>)"
                using assms AB Uncurry_Curry ide_exp tensor_preserves_ide by simp
              also have "... = Curry[exp x a \<otimes> exp x b, x, a]
                                (eval x a \<cdot>
                                   \<langle>\<pp>\<^sub>1[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                                    \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>)"
                using assms A B ECC.pr_tuple(1) by fastforce
              also have "... = Curry[exp x a \<otimes> exp x b, x, a]
                                (eval x a \<cdot> (\<pp>\<^sub>1[exp x a, exp x b] \<otimes> x) \<cdot>
                                              \<langle>\<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                                               \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>)"
              proof -
                have "seq \<pp>\<^sub>1[exp x a, exp x b] \<pp>\<^sub>1[exp x a \<otimes> exp x b, x]"
                  using assms by auto
                thus ?thesis
                  using assms 2 3 prod_eq_tensor comp_ide_arr ECC.prod_tuple
                  by metis
              qed
              also have "... = Curry (exp x a \<otimes> exp x b) x a
                                 (eval x a \<cdot> (\<pp>\<^sub>1[exp x a, exp x b] \<otimes> x))"
                using assms comp_arr_dom by simp
              also have "... = \<pp>\<^sub>1[exp x a, exp x b]"
                using assms Curry_Uncurry by simp
              finally show ?thesis by blast
            qed
            moreover have "Curry[exp x (a \<otimes> b), x, b] (\<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b)) \<cdot>
                             Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> =
                           \<pp>\<^sub>0[exp x a, exp x b]"
            proof -
              have "Curry[exp x (a \<otimes> b), x, b] (\<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b)) \<cdot>
                      Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> =
                    Curry[exp x a \<otimes> exp x b, x, b]
                      ((\<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b)) \<cdot>
                         (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> \<otimes> x))"
              proof -
                have "\<guillemotleft>Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>
                         : exp x a \<otimes> exp x b \<rightarrow> exp x (a \<otimes> b)\<guillemotright>"
                  using 1 by blast
                moreover have "\<guillemotleft>\<pp>\<^sub>0[a, b] \<cdot> eval x (a \<otimes> b) : exp x (a \<otimes> b) \<otimes> x \<rightarrow> b\<guillemotright>"
                  using assms
                  by (metis (no_types, lifting) ECC.pr0_in_hom' ECC.pr_simps(2)
                      comp_in_homI eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C prod_eq_tensor tensor_preserves_ide)
                ultimately show ?thesis
                  using assms comp_Curry_arr by simp
              qed
              also have "... = Curry[exp x a \<otimes> exp x b, x, b]
                                 (\<pp>\<^sub>0[a, b] \<cdot>
                                    Uncurry[x, a \<otimes> b]
                                      (Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle>))"
                using comp_assoc by simp
              also have "... = Curry (exp x a \<otimes> exp x b) x b (\<pp>\<^sub>0[a, b] \<cdot> \<langle>?A, ?B\<rangle>)"
                using assms AB Uncurry_Curry ide_exp tensor_preserves_ide by simp
              also have "... = Curry[exp x a \<otimes> exp x b, x, b]
                                 (eval x b \<cdot>
                                   \<langle>\<pp>\<^sub>0[exp x a, exp x b] \<cdot> \<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                                    \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>)"
                using assms A B by fastforce
              also have "... = Curry[exp x a \<otimes> exp x b, x, b]
                                 (eval x b \<cdot> (\<pp>\<^sub>0[exp x a, exp x b] \<otimes> x) \<cdot>
                                              \<langle>\<pp>\<^sub>1[exp x a \<otimes> exp x b, x],
                                               \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle>)"
              proof -
                have "seq \<pp>\<^sub>0[exp x a, exp x b] \<pp>\<^sub>1[exp x a \<otimes> exp x b, x]"
                  using assms by auto
                thus ?thesis
                  using assms 2 3 prod_eq_tensor comp_ide_arr ECC.prod_tuple
                  by metis
              qed
              also have "... = Curry (exp x a \<otimes> exp x b) x b
                                 (Uncurry[x, b] \<pp>\<^sub>0[exp x a, exp x b])"
              proof -
                have "(\<pp>\<^sub>0[exp x a, exp x b] \<otimes> x) \<cdot>
                        \<langle>\<pp>\<^sub>1[exp x a \<otimes> exp x b, x], \<pp>\<^sub>0[exp x a \<otimes> exp x b, x]\<rangle> =
                      \<pp>\<^sub>0[exp x a, exp x b] \<otimes> x"
                  using assms comp_arr_ide ECC.tuple_pr by auto
                thus ?thesis by simp
              qed
              also have "... = \<pp>\<^sub>0[exp x a, exp x b]"
                using assms Curry_Uncurry by simp
              finally show ?thesis by blast
            qed
            ultimately show ?thesis by simp
          qed
          also have "... = exp x a \<otimes> exp x b"
            using assms ECC.tuple_pr by simp
          finally have "\<langle>?C, ?D\<rangle> \<cdot> Curry[exp x a \<otimes> exp x b, x, a \<otimes> b] \<langle>?A, ?B\<rangle> =
                        exp x a \<otimes> exp x b"
            by blast
          thus ?thesis
            using assms tensor_preserves_ide by simp
        qed
      qed
      thus "isomorphic (exp x (a \<otimes> b)) (exp x a \<otimes> exp x b)"
        unfolding isomorphic_def
        using CD by blast
    qed

  end

end
