(*  Title:       Yoneda
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Yoneda

theory Yoneda
imports DualCategory SetCat FunctorCategory
begin

  text{*
    This theory defines the notion of a ``hom-functor'' and gives a proof of the Yoneda Lemma.
    In traditional developments of category theory based on set theories such as ZFC,
    hom-functors are normally defined to be functors into the large category \textbf{Set}
    whose objects are of \emph{all} sets and whose arrows are functions between sets.
    However, in HOL there does not exist a single ``type of all sets'', so the notion of
    the category of \emph{all} sets and functions does not make sense.  To work around this,
    we consider a more general setting consisting of a category @{term C} together with
    a set category @{term S} and a function @{term "\<phi> :: 'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"} such that
    whenever @{term b} and @{term a} are objects of C then @{term "\<phi> (b, a)"} maps
    @{text "C.hom b a"} injectively to @{text "S.Univ"}.  We show that these data induce
    a binary functor @{text Hom} from @{text "Cop\<times>C"} to @{term S} in such a way that @{term \<phi>}
    is rendered natural in @{term "(b, a)"}.  The Yoneda lemma is then proved for the
    Yoneda functor determined by @{text Hom}.
  *}

  section "Hom-Functors"

  text{*
    A hom-functor for a category @{term C} allows us to regard the hom-sets of @{term C}
    as objects of a category @{term S} of sets and functions.  Any description of a
    hom-functor for @{term C} must therefore specify the category @{term S} and provide
    some sort of correspondence between arrows of @{term C} and elements of objects of @{term S}.
    If we are to think of each hom-set @{text "C.hom b a"} of @{text C} as corresponding
    to an object @{text "Hom (b, a)"} of @{term S} then at a minimum it ought to be the
    case that the correspondence between arrows and elements is bijective between
    @{text "C.hom b a"} and @{text "Hom (b, a)"}.  The @{text hom_functor} locale defined
    below captures this idea by assuming a set category @{term S} and a function @{term \<phi>}
    taking arrows of @{term C} to elements of @{text S.Univ}, such that @{term \<phi>} is injective
    on each set @{text "C.hom b a"}.  We show that these data induce a functor @{text Hom}
    from @{text "Cop\<times>C"} to @{text S} in such a way that @{term \<phi>} becomes a natural
    bijection between @{text "C.hom b a"} and @{text "Hom (b, a)"}.
  *}

  locale hom_functor =
    C: category C +
    Cop: dual_category C +
    CopxC: product_category Cop.comp C +
    S: set_category S
  for C :: "'c comp"
  and S :: "'s comp"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's" +
  assumes maps_arr_to_Univ: "C.arr f \<Longrightarrow> \<phi> (C.dom f, C.cod f) f \<in> S.Univ"
  and local_inj: "\<lbrakk> C.ide b; C.ide a \<rbrakk> \<Longrightarrow> inj_on (\<phi> (b, a)) (C.hom b a)"
  begin

    definition set
    where "set ba \<equiv> \<phi> (fst ba, snd ba) ` C.hom (fst ba) (snd ba)"

    lemma set_subset_Univ:
    assumes "C.ide b" and "C.ide a"
    shows "set (b, a) \<subseteq> S.Univ"
      using assms set_def maps_arr_to_Univ CopxC.ide_char by auto

    definition \<psi> :: "'c * 'c \<Rightarrow> 's \<Rightarrow> 'c"
    where "\<psi> ba = inv_into (C.hom (fst ba) (snd ba)) (\<phi> ba)"

    lemma \<phi>_mapsto:
    assumes "C.ide b" and "C.ide a"
    shows "\<phi> (b, a) \<in> C.hom b a \<rightarrow> set (b, a)"
      using assms set_def maps_arr_to_Univ by auto

    lemma \<psi>_mapsto:
    assumes "C.ide b" and "C.ide a"
    shows "\<psi> (b, a) \<in> set (b, a) \<rightarrow> C.hom b a"
      using assms set_def \<psi>_def local_inj by auto

    lemma \<psi>_\<phi> [simp]:
    assumes "f \<in> C.hom b a"
    shows "\<psi> (b, a) (\<phi> (b, a) f) = f"
      using assms local_inj \<psi>_def by auto

    lemma \<phi>_\<psi> [simp]:
    assumes "C.ide b" and "C.ide a"
    and "x \<in> set (b, a)"
    shows "\<phi> (b, a) (\<psi> (b, a) x) = x"
      using assms set_def local_inj \<psi>_def by auto

    lemma \<psi>_img_set:
    assumes "C.ide b" and "C.ide a"
    shows "\<psi> (b, a) ` set (b, a) = C.hom b a"
      using assms \<psi>_def set_def local_inj by auto

    text{*
      A hom-functor maps each arrow @{term "(g, f)"} of @{term "CopxC"}
      to the arrow of the set category @{term S} corresponding to the function that takes
      an arrow @{term h} of @{term C} to the arrow @{term "C f (C h g)"} of @{term C}
      obtained by precomposing with @{term g} and postcomposing with @{term f}.
    *}

    definition map
    where "map gf =
             (if CopxC.arr gf then
                S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf))
                        (\<phi> (CopxC.cod gf) o (\<lambda>h. C (snd gf) (C h (fst gf))) o \<psi> (CopxC.dom gf))
              else S.null)"

    lemma arr_map:
    assumes "CopxC.arr gf"
    shows "S.arr (map gf)"
    proof -
      have "\<phi> (CopxC.cod gf) o (\<lambda>h. C (snd gf) (C h (fst gf))) o \<psi> (CopxC.dom gf)
              \<in> set (CopxC.dom gf) \<rightarrow> set (CopxC.cod gf)"
        using assms set_def map_def [of gf] \<phi>_mapsto \<psi>_mapsto by fastforce
      thus ?thesis
        using assms map_def set_subset_Univ by auto
    qed

    lemma map_ide [simp]:
    assumes "C.ide b" and "C.ide a"
    shows "map (b, a) = S.mkIde (set (b, a))"
    proof -
      have "map (b, a) = S.mkArr (set (b, a)) (set (b, a))
                                 (\<phi> (b, a) o (\<lambda>h. C a (C h b)) o \<psi> (b, a))"
        using assms map_def by simp
      also have "... = S.mkArr (set (b, a)) (set (b, a)) (\<lambda>h. h)"
      proof -
        have "S.mkArr (set (b, a)) (set (b, a)) (\<lambda>h. h) = ..."
        proof (intro S.mkArr_eqI')
          show "S.arr (S.mkArr (set (b, a)) (set (b, a)) (\<lambda>h. h))"
            using assms S.arr_mkArr set_subset_Univ by simp
          show "\<And>x. x \<in> set (b, a) \<Longrightarrow> x = (\<phi> (b, a) o (\<lambda>h. C a (C h b)) o \<psi> (b, a)) x"
            using assms set_def \<psi>_mapsto [of b a] by auto
        qed
        thus ?thesis by auto
      qed
       also have "... = S.mkIde (set (b, a))"
        using assms S.mkIde_as_mkArr [of "set (b, a)"] set_subset_Univ by simp
      finally show ?thesis by auto
    qed

    lemma set_map:
    assumes "C.ide a" and "C.ide b"
    shows "S.set (map (b, a)) = set (b, a)"
      using assms map_ide S.set_mkIde set_subset_Univ by simp

    text{*
      The definition does in fact yield a functor.
    *}

    interpretation "functor" CopxC.comp S map
    proof
      fix gf
      assume "\<not>CopxC.arr gf"
      thus "map gf = S.null" using map_def by auto
      next
      fix gf
      assume gf: "CopxC.arr gf"
      thus arr: "S.arr (map gf)" using gf arr_map by blast
      show "S.dom (map gf) = map (CopxC.dom gf)"
      proof -
        have "S.dom (map gf) = S.mkArr (set (CopxC.dom gf)) (set (CopxC.dom gf)) (\<lambda>x. x)"
          using gf arr_map [of gf] map_def [of gf] by simp
        also have "... = S.mkArr (set (CopxC.dom gf)) (set (CopxC.dom gf))
                                 (\<phi> (CopxC.dom gf) o (\<lambda>h. C (snd (CopxC.dom gf))
                                                            (C h (fst (CopxC.dom gf))))
                                                   o \<psi> (CopxC.dom gf))"
          apply (intro S.mkArr_eqI')
          using gf set_subset_Univ \<psi>_mapsto [of "fst (CopxC.dom gf)" "snd (CopxC.dom gf)"]
                map_def set_def
          by auto
        also have "... = map (CopxC.dom gf)" using gf map_def by simp
        finally show ?thesis by auto
      qed
      show "S.cod (map gf) = map (CopxC.cod gf)"
      proof -
        have "S.cod (map gf) = S.mkArr (set (CopxC.cod gf)) (set (CopxC.cod gf)) (\<lambda>x. x)"
          using gf map_def [of gf] arr_map [of gf] by simp
        also have "... = S.mkArr (set (CopxC.cod gf)) (set (CopxC.cod gf))
                                 (\<phi> (CopxC.cod gf) o (\<lambda>h. C (snd (CopxC.cod gf))
                                                            (C h (fst (CopxC.cod gf))))
                                                   o \<psi> (CopxC.cod gf))"
          apply (intro S.mkArr_eqI')
          using gf S.arr_mkArr set_subset_Univ set_def
                \<psi>_mapsto [of "fst (CopxC.cod gf)" "snd (CopxC.cod gf)"]
          by auto
        also have "... = map (CopxC.cod gf)" using gf map_def by simp
        finally show ?thesis by auto
      qed
      fix gf'
      assume gf': "gf' \<in> CopxC.hom (CopxC.cod gf) (CopxC.cod gf')"
      hence S: "CopxC.cod gf = CopxC.dom gf'" by auto
      have 0: "S.arr (map (CopxC.comp gf' gf))"
        using gf gf' S arr_map by simp
      have 1: "map (CopxC.comp gf' gf) =
                    S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf'))
                            (\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd (CopxC.comp gf' gf))
                                                        (C h (fst (CopxC.comp gf' gf))))
                                               o \<psi> (CopxC.dom gf))"
        using gf gf' map_def by auto
      also have "... = S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf'))
                               ((\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd gf') (C h (fst gf')))
                                                   o \<psi> (CopxC.dom gf'))
                                 o (\<phi> (CopxC.cod gf) o (\<lambda>h. C (snd gf) (C h (fst gf)))
                                                     o \<psi> (CopxC.dom gf)))"
      proof (intro S.mkArr_eqI')
        show "S.arr (S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf'))
                             (\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd (CopxC.comp gf' gf))
                                                         (C h (fst (CopxC.comp gf' gf))))
                                                 o \<psi> (CopxC.dom gf)))"
          using 0 1 by simp
        show "\<And>x. x \<in> set (CopxC.dom gf) \<Longrightarrow>
                     (\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd (CopxC.comp gf' gf))
                                                 (C h (fst (CopxC.comp gf' gf))))
                                        o \<psi> (CopxC.dom gf)) x
                      = ((\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd gf') (C h (fst gf')))
                                            o \<psi> (CopxC.dom gf'))
                                 o (\<phi> (CopxC.cod gf) o (\<lambda>h. C (snd gf) (C h (fst gf)))
                                                     o \<psi> (CopxC.dom gf))) x"
        proof -
          fix x
          assume x: "x \<in> set (CopxC.dom gf)"
          show "(\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd (CopxC.comp gf' gf))
                                            (C h (fst (CopxC.comp gf' gf))))
                                   o \<psi> (CopxC.dom gf)) x
                      = ((\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd gf') (C h (fst gf')))
                                            o \<psi> (CopxC.dom gf'))
                                 o (\<phi> (CopxC.cod gf) o (\<lambda>h. C (snd gf) (C h (fst gf)))
                                                     o \<psi> (CopxC.dom gf))) x"
          proof -
            have "(\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd (CopxC.comp gf' gf))
                                              (C h (fst (CopxC.comp gf' gf))))
                                     o \<psi> (CopxC.dom gf)) x =
                  \<phi> (CopxC.cod gf')
                    (C (snd (CopxC.comp gf' gf))
                       (C (\<psi> (CopxC.dom gf) x) (fst (CopxC.comp gf' gf))))"
              by simp
            also have "... = \<phi> (CopxC.cod gf')
                               ((((\<lambda>h. C (snd gf') (C h (fst gf'))) o \<psi> (CopxC.dom gf'))
                                 o (\<phi> (CopxC.dom gf') o (\<lambda>h. C (snd gf) (C h (fst gf)))))
                                (\<psi> (CopxC.dom gf) x))"
              using x gf gf' S arr_map set_def by auto
            also have "... = ((\<phi> (CopxC.cod gf') o (\<lambda>h. C (snd gf') (C h (fst gf')))
                                                 o \<psi> (CopxC.dom gf'))
                                 o (\<phi> (CopxC.dom gf') o (\<lambda>h. C (snd gf) (C h (fst gf)))
                                                      o \<psi> (CopxC.dom gf))) x"
              by auto
            finally show ?thesis using S by auto
          qed
        qed
      qed
      also have "... = S (map gf') (map gf)"
        using S gf gf' map_def [of gf] map_def [of gf'] arr_map [of gf] arr_map [of gf']
              S.comp_mkArr
        by simp
      finally show "map (CopxC.comp gf' gf) = S (map gf') (map gf)"
        using S gf gf' by auto
    qed

    interpretation binary_functor Cop.comp C S map ..

    lemma is_binary_functor:
    shows "binary_functor Cop.comp C S map" ..

  end

  sublocale hom_functor \<subseteq> binary_functor Cop.comp C S map
    using is_binary_functor by auto

  context hom_functor
  begin

    text{*
      The map @{term \<phi>} determines a bijection between @{term "C.hom b a"} and
      @{term "set (b, a)"} which is natural in @{term "(b, a)"}.
    *}

    lemma \<phi>_local_bij:
    assumes "C.ide b" and "C.ide a"
    shows "bij_betw (\<phi> (b, a)) (C.hom b a) (set (b, a))"
      using assms local_inj inj_on_imp_bij_betw set_def by auto

    lemma \<phi>_natural:
    assumes "C.arr g" and "C.arr f" and "h \<in> C.hom (C.cod g) (C.dom f)"
    shows "\<phi> (C.dom g, C.cod f) (C f (C h g)) = S.Fun (map (g, f)) (\<phi> (C.cod g, C.dom f) h)"
    proof -
      let ?\<phi>h = "\<phi> (C.cod g, C.dom f) h"
      have \<phi>h: "?\<phi>h \<in> set (C.cod g, C.dom f)"
        using assms \<phi>_mapsto set_def by simp
      have gf: "CopxC.arr (g, f)" using assms by simp
      hence "map (g, f) =
               S.mkArr (set (C.cod g, C.dom f)) (set (C.dom g, C.cod f))
                       (\<phi> (C.dom g, C.cod f) \<circ> (\<lambda>h. C f (C h g)) \<circ> \<psi> (C.cod g, C.dom f))"
        using map_def [of "(g, f)"] by simp
      moreover have "S.arr (map (g, f))" using gf by simp
      ultimately have
          "S.Fun (map (g, f)) =
               restrict (\<phi> (C.dom g, C.cod f) \<circ> (\<lambda>h. C f (C h g)) \<circ> \<psi> (C.cod g, C.dom f))
                        (set (C.cod g, C.dom f))"
        using S.Fun_mkArr by simp
      hence "S.Fun (map (g, f)) ?\<phi>h =
                (\<phi> (C.dom g, C.cod f) \<circ> (\<lambda>h. C f (C h g)) \<circ> \<psi> (C.cod g, C.dom f)) ?\<phi>h"
        using \<phi>h by simp
      also have "... = \<phi> (C.dom g, C.cod f) (C f (C h g))"
        using assms(3) by simp
      finally show ?thesis by auto
    qed

    lemma Dom_map:
    assumes "C.arr g" and "C.arr f"
    shows "S.Dom (map (g, f)) = set (C.cod g, C.dom f)"
      using assms map_def preserves_arr by auto

    lemma Cod_map:
    assumes "C.arr g" and "C.arr f"
    shows "S.Cod (map (g, f)) = set (C.dom g, C.cod f)"
      using assms map_def preserves_arr by auto

    lemma Fun_map:
    assumes "C.arr g" and "C.arr f"
    shows "S.Fun (map (g, f)) =
             restrict (\<phi> (C.dom g, C.cod f) o (\<lambda>h. C f (C h g)) o \<psi> (C.cod g, C.dom f))
                      (set (C.cod g, C.dom f))"
    proof
      fix x
      have "x \<notin> set (C.cod g, C.dom f) \<Longrightarrow>
              S.Fun (map (g, f)) x =
                restrict (\<phi> (C.dom g, C.cod f) o (\<lambda>h. C f (C h g)) o \<psi> (C.cod g, C.dom f))
                         (set (C.cod g, C.dom f)) x"
      proof -
        have "S.arr (map (g, f))"
          using assms preserves_arr by fastforce
        thus ?thesis
          using assms map_def [of "(g, f)"] S.Fun_mapsto [of "map (g, f)"]
                extensional_arb [of "S.Fun (map (g, f))" "S.Dom (map (g, f))"]
          by force
      qed
      moreover have "x \<in> set (C.cod g, C.dom f) \<Longrightarrow>
              S.Fun (map (g, f)) x =
                restrict (\<phi> (C.dom g, C.cod f) o (\<lambda>h. C f (C h g)) o \<psi> (C.cod g, C.dom f))
                         (set (C.cod g, C.dom f)) x"
        using assms preserves_arr map_def \<psi>_mapsto [of "C.cod g" "C.dom f"]
              \<phi>_natural [of f g "\<psi> (C.cod g, C.dom f) x"]
        by force
      ultimately show
          "S.Fun (map (g, f)) x =
                restrict (\<phi> (C.dom g, C.cod f) o (\<lambda>h. C f (C h g)) o \<psi> (C.cod g, C.dom f))
                         (set (C.cod g, C.dom f)) x"
        by auto
    qed

    lemma map_simp_1:
    assumes "C.arr g" and "C.ide a"
    shows "map (g, a) = S.mkArr (set (C.cod g, a)) (set (C.dom g, a))
                                (\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a))"
    proof -
      have 1: "map (g, a) = S.mkArr (set (C.cod g, a)) (set (C.dom g, a))
                                    (\<phi> (C.dom g, a) o (\<lambda>h. C a (C h g)) o \<psi> (C.cod g, a))"
        using assms map_def by force
      also have "... = S.mkArr (set (C.cod g, a)) (set (C.dom g, a))
                               (\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a))"
        using assms 1 preserves_arr [of "(g, a)"] \<psi>_mapsto [of "C.cod g" a] by force
      finally show ?thesis by auto
    qed

    lemma map_simp_2:
    assumes "C.ide b" and "C.arr f"
    shows "map (b, f) = S.mkArr (set (b, C.dom f)) (set (b, C.cod f))
                                (\<phi> (b, C.cod f) o C f o \<psi> (b, C.dom f))"
    proof -
      have 1: "map (b, f) = S.mkArr (set (b, C.dom f)) (set (b, C.cod f))
                                    (\<phi> (b, C.cod f) o (\<lambda>h. C f (C h b)) o \<psi> (b, C.dom f))"
        using assms map_def by force
      also have "... = S.mkArr (set (b, C.dom f)) (set (b, C.cod f))
                               (\<phi> (b, C.cod f) o C f o \<psi> (b, C.dom f))"
        using assms 1 preserves_arr [of "(b, f)"] \<psi>_mapsto [of b "C.dom f"] by force
      finally show ?thesis by auto
    qed

  end

  text{*
    Every category @{term C} has a hom-functor: take @{term S} to be the set category
    @{text SetCat} generated by the set of arrows of @{term C} and take @{term "\<phi> (b, a)"}
    to be the map @{text "UP :: 'c \<Rightarrow> 'c SetCat.arr"}.
  *}

  context category
  begin

    interpretation Cop: dual_category C ..
    interpretation CopxC: product_category Cop.comp C ..
    interpretation S: set_category "SetCat.comp :: 'a SetCat.arr comp"
      using SetCat.is_set_category by auto
    interpretation Hom: hom_functor C "SetCat.comp :: 'a SetCat.arr comp" "\<lambda>_. UP"
      apply unfold_locales
      (* 2 *) using UP_mapsto apply auto[1]
      (* 1 *) using inj_UP by (metis (no_types, lifting) injD inj_onI)

    lemma has_hom_functor:
    shows "hom_functor C (SetCat.comp :: 'a SetCat.arr comp) (\<lambda>_. UP)" ..

  end

  text{*
    The locales @{text set_valued_functor} and @{text set_valued_transformation} provide some
    abbreviations that are convenient when working with functors and natural transformations
    into a set category.
  *}

  locale set_valued_functor =
    C: category C +
    S: set_category S +
    "functor" C S F
    for C :: "'c comp"
    and S :: "'s comp"
    and F :: "'c \<Rightarrow> 's"
  begin

    abbreviation SET :: "'c \<Rightarrow> 's set"
    where "SET a \<equiv> S.set (F a)"
    
    abbreviation DOM :: "'c \<Rightarrow> 's set"
    where "DOM f \<equiv> S.Dom (F f)"
    
    abbreviation COD :: "'c \<Rightarrow> 's set"
    where "COD f \<equiv> S.Cod (F f)"

    abbreviation FUN :: "'c \<Rightarrow> 's \<Rightarrow> 's"
    where "FUN f \<equiv> S.Fun (F f)"

  end

  locale set_valued_transformation =
    C: category C +
    S: set_category S +
    F: set_valued_functor C S F +
    G: set_valued_functor C S G +
    natural_transformation C S F G \<tau>
  for C :: "'c comp"
  and S :: "'s comp"
  and F :: "'c \<Rightarrow> 's"
  and G :: "'c \<Rightarrow> 's"
  and \<tau> :: "'c \<Rightarrow> 's"
  begin
  
    abbreviation DOM :: "'c \<Rightarrow> 's set"
    where "DOM f \<equiv> S.Dom (\<tau> f)"
    
    abbreviation COD :: "'c \<Rightarrow> 's set"
    where "COD f \<equiv> S.Cod (\<tau> f)"

    abbreviation FUN :: "'c \<Rightarrow> 's \<Rightarrow> 's"
    where "FUN f \<equiv> S.Fun (\<tau> f)"

  end

  section "Yoneda Functors"
    
  text{*
    A Yoneda functor is the functor from @{term C} to @{text "[Cop, S]"} obtained by ``currying''
    a hom-functor in its first argument.
  *}

  locale yoneda_functor =
    C: category C +
    Cop: dual_category C +
    CopxC: product_category Cop.comp C +
    S: set_category S + 
    Hom: hom_functor C S \<phi> +
    Cop_S: functor_category Cop.comp S +
    curried_functor' Cop.comp C S Hom.map
  for C :: "'c comp"
  and S :: "'s comp"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  begin

    abbreviation \<psi>
    where "\<psi> \<equiv> Hom.\<psi>"

    text{*
      An arrow of the functor category @{text "[Cop, S]"} consists of a natural transformation
      bundled together with its domain and codomain functors.  However, when considering
      a Yoneda functor from @{term C} to @{text "[Cop, S]"} we generally are only interested
      in the mapping @{term Y} that takes each arrow @{term f} of @{term C} to the corresponding
      natural transformation @{term "Y f"}.  The domain and codomain functors are then the identity
      transformations @{term "Y (C.dom f)"} and @{term "Y (C.cod f)"}.
    *}

    definition Y
    where "Y f \<equiv> Cop_S.Fun (map f)"

    lemma Y_simp [simp]:
    assumes "C.arr f"
    shows "Y f = (\<lambda>g. Hom.map (g, f))"
      using assms preserves_hom Y_def [of f] by auto

    lemma Y_ide_is_functor:
    assumes "C.ide a"
    shows "functor Cop.comp S (Y a)"
      using assms Y_def by (simp add: Hom.fixing_ide_gives_functor_2)

    lemma Y_arr_is_transformation:
    assumes "C.arr f"
    shows "natural_transformation Cop.comp S (Y (C.dom f)) (Y (C.cod f)) (Y f)"
      using assms Y_def [of f] map_def Hom.fixing_arr_gives_natural_transformation_2
            preserves_dom preserves_cod by simp

    lemma Y_ide_arr [simp]:
    assumes a: "C.ide a" and "g \<in> C.hom b' b"
    shows "Y a g \<in> S.hom (Hom.map (b, a)) (Hom.map (b', a))"
    and "Y a g = S.mkArr (Hom.set (b, a)) (Hom.set (b', a)) (\<phi> (b', a) o Cop.comp g o \<psi> (b, a))"
      using assms apply simp
      using assms Hom.map_simp_1 [of g a] by simp

    lemma Y_arr_ide [simp]:
    assumes "C.ide b" and "f \<in> C.hom a a'"
    shows "Y f b \<in> S.hom (Hom.map (b, a)) (Hom.map (b, a'))"
    and "Y f b = S.mkArr (Hom.set (b, a)) (Hom.set (b, a')) (\<phi> (b, a') o C f o \<psi> (b, a))"
      using assms apply simp
      using assms Hom.map_simp_2 [of b f] by simp

  end

  locale yoneda_functor_fixed_object =
    yoneda_functor C S \<phi>
  for C :: "'c comp"
  and S :: "'s comp"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and a :: 'c +
  assumes ide_a: "C.ide a"
  
  sublocale yoneda_functor_fixed_object \<subseteq> "functor" Cop.comp S "Y a"
    using ide_a Y_ide_is_functor by auto
  sublocale yoneda_functor_fixed_object \<subseteq> set_valued_functor Cop.comp S "Y a" ..

  text{*
    The Yoneda lemma states that, given a category @{term C} and a functor @{term F}
    from @{term Cop} to a set category @{term S}, for each object @{term a} of @{term C},
    the set of natural transformations from the contravariant functor @{term "Y a"}
    to @{term F} is in bijective correspondence with the set @{text "F.SET a"}
    of elements of @{term "F a"}.

    Explicitly, if @{term e} is an arbitrary element of the set @{text "F.SET a"},
    then the functions @{text "\<lambda>x. F.FUN (\<psi> (b, a) x) e"} are the components of a
    natural transformation from @{term "Y a"} to @{term F}.
    Conversely, if @{term \<tau>} is a natural transformation from @{term "Y a"} to @{term F},
    then the component @{term "\<tau> b"} of @{term \<tau>} at an arbitrary object @{term b}
    is completely determined by the single arrow @{text "\<tau>.FUN a (\<phi> (a, a) a)))"},
    which is the the element of @{text "F.SET a"} that corresponds to the image of the
    identity @{term a} under the function @{text "\<tau>.FUN a"}.
    Then @{term "\<tau> b"} is the arrow from @{term "Y a b"} to @{term "F b"} corresponding
    to the function @{text "\<lambda>x. (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a (\<phi> (a, a) a)))"}
    from @{text "S.set (Y a b)"} to @{text "F.SET b"}.
   
    The above expressions look somewhat more complicated than the usual versions due to the
    need to account for the coercions @{term \<phi>} and @{term \<psi>}.
  *}

  locale yoneda_lemma =
    C: category C +
    Cop: dual_category C +
    S: set_category S +
    F: set_valued_functor Cop.comp S F +
    yoneda_functor_fixed_object C S \<phi> a
    for C :: "'c comp"
    and S :: "'s comp"
    and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and F :: "'c \<Rightarrow> 's"
    and a :: 'c
  begin

    text{*
      The mapping that evaluates the component @{term "\<tau> a"} at @{term a} of a
      natural transformation @{term \<tau>} from @{term Y} to @{term F} on the element
      @{term "\<phi> (a, a) a"} of @{term "SET a"}, yielding an element of @{term "F.SET a"}.
    *}

    definition \<E> :: "('c \<Rightarrow> 's) \<Rightarrow> 's"
    where "\<E> \<tau> = S.Fun (\<tau> a) (\<phi> (a, a) a)"

    text{*
      The mapping that takes an element @{term e} of @{term "F.SET a"} and produces
      a map on objects of @{term C} whose value at @{term b} is the arrow of @{term S}
      corresponding to the function
      @{term "(\<lambda>x. F.FUN (\<psi> (b, a) x) e) \<in> Hom.set (b, a) \<rightarrow> F.SET b"}.
    *}

    definition \<T>o :: "'s \<Rightarrow> 'c \<Rightarrow> 's"
    where "\<T>o e b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. F.FUN (\<psi> (b, a) x) e)"

    lemma \<T>o_e_ide:
    assumes e: "e \<in> S.set (F a)" and b: "C.ide b"
    shows "\<T>o e b \<in> S.hom (Y a b) (F b)"
    and "\<T>o e b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. F.FUN (\<psi> (b, a) x) e)"
    proof -
      show "\<T>o e b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. F.FUN (\<psi> (b, a) x) e)"
        using \<T>o_def by auto
      moreover have "(\<lambda>x. F.FUN (\<psi> (b, a) x) e) \<in> Hom.set (b, a) \<rightarrow> F.SET b"
      proof
        fix x
        assume x: "x \<in> Hom.set (b, a)"
        hence "\<psi> (b, a) x \<in> C.hom b a" using assms ide_a Hom.\<psi>_mapsto [of b a] by auto
        hence "F (\<psi> (b, a) x) \<in> S.hom (F a) (F b)" by simp
        hence "F.FUN (\<psi> (b, a) x) \<in> F.SET a \<rightarrow> F.SET b"
          using S.Fun_mapsto [of "F (\<psi> (b, a) x)"] by simp
        thus "F.FUN (\<psi> (b, a) x) e \<in> F.SET b" using e by auto
      qed
      ultimately show "\<T>o e b \<in> S.hom (Y a b) (F b)"
        using ide_a b S.mkArr_in_hom Hom.set_subset_Univ by simp
    qed

    text{*
      For each @{term "e \<in> F.SET a"}, the mapping @{term "\<T>o e"} gives the components
      of a natural transformation @{term \<T>} from @{term "Y a"} to @{term F}.
    *}

    lemma \<T>o_e_induces_transformation:
    assumes e: "e \<in> S.set (F a)"
    shows "transformation_by_components Cop.comp S (Y a) F (\<T>o e)"
    proof
      fix b :: 'c
      assume b: "Cop.ide b"
      show "\<T>o e b \<in> S.hom (Y a b) (F b)" using ide_a b e \<T>o_e_ide by blast
      next
      fix g :: 'c
      assume g: "Cop.arr g"
      let ?b = "Cop.dom g"
      let ?b' = "Cop.cod g"
      show "S (\<T>o e ?b') (Y a g) = S (F g) (\<T>o e ?b)"
      proof -
        have 1: "S (\<T>o e ?b') (Y a g)
                   = S.mkArr (Hom.set (?b, a)) (F.SET ?b')
                             ((\<lambda>x. F.FUN (\<psi> (?b', a) x) e)
                                o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a)))"
          using S.comp_mkArr [of "Hom.set (?b, a)" "Hom.set (?b', a)"
                                 "\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a)"
                                 "F.SET ?b'" "\<lambda>x. F.FUN (\<psi> (?b', a) x) e"]
                Y_ide_arr [of a g ?b' ?b] \<T>o_e_ide [of e ?b'] ide_a e g
        proof -
          have "S.arr (S.mkArr (Hom.set (Cop.cod g, a)) (F.SET (Cop.cod g))
                      (\<lambda>s. F.FUN (\<psi> (Cop.cod g, a) s) e)) \<and>
                S.dom (S.mkArr (Hom.set (Cop.cod g, a)) (F.SET (Cop.cod g))
                      (\<lambda>s. F.FUN (\<psi> (Cop.cod g, a) s) e)) = Y a (Cop.cod g) \<and>
                S.cod (S.mkArr (Hom.set (Cop.cod g, a)) (F.SET (Cop.cod g))
                      (\<lambda>s. F.FUN (\<psi> (Cop.cod g, a) s) e)) = F (Cop.cod g)"
            using Cop.cod_char \<T>o_e_ide [of e ?b'] \<T>o_e_ide [of e ?b'] e g
            by force
          moreover have "Y a g = S.mkArr (Hom.set (Cop.dom g, a)) (Hom.set (Cop.cod g, a))
                                         (\<phi> (Cop.cod g, a) \<circ> Cop.comp g \<circ> \<psi> (Cop.dom g, a))"
            using Y_ide_arr [of a g ?b' ?b] ide_a g by simp
          ultimately show ?thesis
            using ide_a e g Y_ide_arr [of a g] Cop.cod_char
                  S.comp_mkArr [of "Hom.set (?b, a)" "Hom.set (?b', a)"
                                   "\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a)"
                                   "F.SET ?b'" "\<lambda>x. F.FUN (\<psi> (?b', a) x) e"]
                  \<T>o_e_ide [of e ?b']
            by simp
        qed
        also have "... = S.mkArr (Hom.set (?b, a)) (F.SET ?b')
                                 (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e))"
        proof (intro S.mkArr_eqI')
          have "(\<lambda>x. F.FUN (\<psi> (?b', a) x) e)
                   o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a)) \<in> Hom.set (?b, a) \<rightarrow> F.SET ?b'"
          proof -
            have "S.arr (S (\<T>o e ?b') (Y a g))"
              using ide_a e g \<T>o_e_ide [of e ?b'] by simp
            thus ?thesis using 1 by simp
          qed
          thus "S.arr (S.mkArr (Hom.set (?b, a)) (F.SET ?b')
                               ((\<lambda>x. F.FUN (\<psi> (?b', a) x) e)
                                  o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))))"
            using ide_a e g Hom.set_subset_Univ by simp
          show "\<And>x. x \<in> Hom.set (?b, a) \<Longrightarrow>
                        ((\<lambda>x. F.FUN (\<psi> (?b', a) x) e) o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))) x
                        = (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)) x"
          proof -
            fix x
            assume x: "x \<in> Hom.set (?b, a)"
            have "((\<lambda>x. (F.FUN o \<psi> (?b', a)) x e)
                       o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))) x
                    = F.FUN (\<psi> (?b', a) (\<phi> (?b', a) (C (\<psi> (?b, a) x) g))) e"
              by simp
            also have "... = (F.FUN g o (F.FUN o \<psi> (?b, a)) x) e"
            proof -
              have "\<psi> (?b, a) x \<in> C.hom ?b a"
                using ide_a x g Hom.\<psi>_mapsto [of ?b a] by auto
              thus ?thesis
                using assms ide_a x g F.preserves_comp by simp
            qed
            also have "... = (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)) x" by fastforce
            finally show "((\<lambda>x. F.FUN (\<psi> (?b', a) x) e)
                             o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))) x
                            = (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)) x"
              by simp
          qed
        qed
        also have "... = S (F g) (\<T>o e ?b)"
        proof -
          have "S.arr (F g) \<and> F g = S.mkArr (F.SET ?b) (F.SET ?b') (F.FUN g)"
            using g S.mkArr_Fun [of "F g"] by simp
          moreover have "S.arr (\<T>o e ?b) \<and>
                         \<T>o e ?b = S.mkArr (Hom.set (?b, a)) (F.SET ?b) (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)"
            using e g \<T>o_e_ide by simp
          ultimately show ?thesis
            using S.comp_mkArr [of "Hom.set (?b, a)" "F.SET ?b" "\<lambda>x. F.FUN (\<psi> (?b, a) x) e"
                                     "F.SET ?b'" "F.FUN g"]
            by metis
        qed
        finally show ?thesis by blast
      qed
    qed

    abbreviation \<T> :: "'s \<Rightarrow> 'c \<Rightarrow> 's"
    where "\<T> e \<equiv> transformation_by_components.map Cop.comp S (Y a) (\<T>o e)"

  end

  locale yoneda_lemma_fixed_e =
    yoneda_lemma C S \<phi> F a
    for C :: "'c comp"
    and S :: "'s comp"
    and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and F :: "'c \<Rightarrow> 's"
    and a :: 'c
    and e :: 's +
    assumes E: "e \<in> F.SET a"
  begin

    interpretation \<T>e: transformation_by_components Cop.comp S "Y a" F "\<T>o e"
      using E \<T>o_e_induces_transformation by auto

    lemma natural_transformation_\<T>e:
    shows "natural_transformation Cop.comp S (Y a) F (\<T> e)" ..

    lemma \<T>e_ide:
    assumes "Cop.ide b"
    shows "S.arr (\<T> e b)"
    and "\<T> e b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. F.FUN (\<psi> (b, a) x) e)"
      using assms E \<T>o_e_ide \<T>e.map_simp_ide \<T>o_def by auto

  end

  locale yoneda_lemma_fixed_\<tau> =
    yoneda_lemma C S \<phi> F a +
    \<tau>: set_valued_transformation Cop.comp S "Y a" F \<tau>
    for C :: "'c comp"
    and S :: "'s comp"
    and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and F :: "'c \<Rightarrow> 's"
    and a :: 'c
    and \<tau> :: "'c \<Rightarrow> 's"
  begin

    text{*
      The key lemma: The component @{term "\<tau> b"} of @{term \<tau>} at an arbitrary object @{term b}
      is completely determined by the single element @{term "\<tau>.FUN a (\<phi> (a, a) a) \<in> F.SET a"}.
    *}

    lemma \<tau>_ide:
    assumes b: "Cop.ide b"
    shows "\<tau> b = S.mkArr (Hom.set (b, a)) (F.SET b)
                         (\<lambda>x. (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a (\<phi> (a, a) a))))"
    proof -
      let ?\<phi>a = "\<phi> (a, a) a"
      have \<phi>a: "\<phi> (a, a) a \<in> Hom.set (a, a)" using ide_a Hom.\<phi>_mapsto [of a a] by auto
      have 1: "\<tau> b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<tau>.FUN b)"
        using ide_a b S.mkArr_Fun [of "\<tau> b"] Hom.set_map by simp
      also have "... = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a ?\<phi>a)))"
      proof (intro S.mkArr_eqI')
        show "S.arr (S.mkArr (Hom.set (b, a)) (F.SET b) (\<tau>.FUN b))"
          using ide_a b S.mkArr_Fun [of "\<tau> b"] Hom.set_map by simp
        show "\<And>x. x \<in> Hom.set (b, a) \<Longrightarrow> \<tau>.FUN b x = (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a ?\<phi>a))"
        proof -
          fix x
          assume x: "x \<in> Hom.set (b, a)"
          let ?\<psi>x = "\<psi> (b, a) x"
          have \<psi>x: "?\<psi>x \<in> C.hom b a" using ide_a b x Hom.\<psi>_mapsto [of b a] by auto
          show "\<tau>.FUN b x = (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a ?\<phi>a))"
          proof -
            have "\<tau>.FUN b x = S.Fun (S (\<tau> b) (Y a ?\<psi>x)) ?\<phi>a"
            proof -
              have "\<tau>.FUN b x = \<tau>.FUN b ((\<phi> (b, a) o Cop.comp ?\<psi>x) a)"
                using ide_a b x \<psi>x by force
              also have "... = S.Fun (S (\<tau> b) (Y a ?\<psi>x)) ?\<phi>a"
              proof -
                have "\<tau>.FUN b ((\<phi> (b, a) o Cop.comp ?\<psi>x) a)
                        = (\<tau>.FUN b o (\<phi> (b, a) o Cop.comp ?\<psi>x o \<psi> (a, a))) ?\<phi>a"
                  using ide_a b by simp
                also have "... = S.Fun (S (\<tau> b) (Y a ?\<psi>x)) ?\<phi>a"
                proof -
                  have "S.arr (Y a ?\<psi>x)"
                    using ide_a \<psi>x preserves_arr by blast
                  hence "S.arr (Y a ?\<psi>x) \<and>
                         Y a ?\<psi>x = S.mkArr (Hom.set (a, a)) (SET b)
                                           (\<phi> (b, a) \<circ> Cop.comp ?\<psi>x \<circ> \<psi> (a, a))"
                    using ide_a b \<psi>x preserves_hom [of ?\<psi>x a b] Y_ide_arr [of a ?\<psi>x b a]
                    by auto
                  moreover have "S.arr (\<tau> b) \<and> \<tau> b = S.mkArr (SET b) (F.SET b) (\<tau>.FUN b)"
                    using ide_a b S.mkArr_Fun [of "\<tau> b"] by simp
                  ultimately have "S.arr (S (\<tau> b) (Y a ?\<psi>x)) \<and>
                        S (\<tau> b) (Y a ?\<psi>x) =
                           S.mkArr (Hom.set (a, a)) (F.SET b)
                                   (\<tau>.FUN b o (\<phi> (b, a) \<circ> Cop.comp ?\<psi>x \<circ> \<psi> (a, a)))"
                    using 1 S.comp_mkArr [of "Hom.set (a, a)" "SET b"
                                             "\<phi> (b, a) \<circ> Cop.comp ?\<psi>x \<circ> \<psi> (a, a)"
                                             "F.SET b" "\<tau>.FUN b"]
                    by (metis S.arr_comp S.cod_mkArr S.dom_mkArr)
                  thus ?thesis
                    using ide_a b x Hom.\<phi>_mapsto [of a a]
                          S.Fun_mkArr [of "Hom.set (a, a)" "F.SET b"
                                         "\<tau>.FUN b o (\<phi> (b, a) \<circ> Cop.comp ?\<psi>x \<circ> \<psi> (a, a))"]
                    by auto
                qed
                finally show ?thesis by auto
              qed
              finally show ?thesis by simp
            qed
            also have "... = S.Fun (S (F ?\<psi>x) (\<tau> a)) ?\<phi>a"
              using ide_a b \<psi>x \<tau>.is_natural_1 [of ?\<psi>x] \<tau>.is_natural_2 [of ?\<psi>x] by force
            also have "... = F.FUN ?\<psi>x (\<tau>.FUN a ?\<phi>a)"
            proof -
              have "restrict (S.Fun (S (F ?\<psi>x) (\<tau> a))) (Hom.set (a, a))
                               = restrict (F.FUN (\<psi> (b, a) x) o \<tau>.FUN a) (Hom.set (a, a))"
              proof -
                have "S.arr (S (F ?\<psi>x) (\<tau> a))
                      \<and> S (F ?\<psi>x) (\<tau> a) = S.mkArr (Hom.set (a, a)) (F.SET b) (F.FUN ?\<psi>x o \<tau>.FUN a)"
                proof
                  have 1: "S.seq (F ?\<psi>x) (\<tau> a)"
                    using \<psi>x ide_a \<tau>.preserves_cod F.preserves_dom by auto
                  thus "S.arr (S (F ?\<psi>x) (\<tau> a))" by auto
                  have "\<tau> a = S.mkArr (Hom.set (a, a)) (F.SET a) (\<tau>.FUN a)"
                    using ide_a 1 S.mkArr_Fun [of "\<tau> a"] Hom.set_map by simp
                  moreover have "F ?\<psi>x = S.mkArr (F.SET a) (F.SET b) (F.FUN ?\<psi>x)"
                    using x \<psi>x 1 S.mkArr_Fun [of "F ?\<psi>x"] by simp
                  ultimately show "S (F ?\<psi>x) (\<tau> a) =
                                     S.mkArr (Hom.set (a, a)) (F.SET b) (F.FUN ?\<psi>x o \<tau>.FUN a)"
                    using 1 S.comp_mkArr [of "Hom.set (a, a)" "F.SET a" "\<tau>.FUN a"
                                             "F.SET b" "F.FUN ?\<psi>x"]
                    by simp
                qed
                thus ?thesis by force
              qed
              thus "S.Fun (S (F (\<psi> (b, a) x)) (\<tau> a)) ?\<phi>a = F.FUN ?\<psi>x (\<tau>.FUN a ?\<phi>a)"
                 using ide_a \<phi>a restr_eqE [of "S.Fun (S (F ?\<psi>x) (\<tau> a))"
                                           "Hom.set (a, a)" "F.FUN ?\<psi>x o \<tau>.FUN a"]
                 by simp
            qed
            finally show ?thesis by simp
          qed
        qed
      qed
      finally show ?thesis by auto
    qed

    text{*
      Consequently, if @{term \<tau>'} is any natural transformation from @{term "Y a"} to @{term F}
      that agrees with @{term \<tau>} at @{term a}, then @{term "\<tau>' = \<tau>"}.
    *}

    lemma eqI:
    assumes "natural_transformation Cop.comp S (Y a) F \<tau>'" and "\<tau>' a = \<tau> a"
    shows "\<tau>' = \<tau>"
    proof (intro NaturalTransformation.eqI)
      interpret \<tau>': natural_transformation Cop.comp S "Y a" F \<tau>' using assms by auto
      interpret T': yoneda_lemma_fixed_\<tau> C S \<phi> F a \<tau>' ..
      show "natural_transformation Cop.comp S (Y a) F \<tau>" ..
      show "natural_transformation Cop.comp S (Y a) F \<tau>'" ..
      show "\<And>b. Cop.ide b \<Longrightarrow> \<tau>' b = \<tau> b"
        using assms(2) \<tau>_ide T'.\<tau>_ide by simp
    qed

  end

  context yoneda_lemma
  begin

    text{*
      One half of the Yoneda lemma:
      The mapping @{term \<T>} is an injection, with left inverse @{term \<E>},
      from the set @{term "F.SET a"} to the set of natural transformations from
      @{term "Y a"} to @{term F}.
    *}

    lemma \<T>_is_injection:
    assumes "e \<in> F.SET a"
    shows "natural_transformation Cop.comp S (Y a) F (\<T> e)" and "\<E> (\<T> e) = e"
    proof -
      interpret yoneda_lemma_fixed_e C S \<phi> F a e
        apply (unfold_locales) using assms apply auto done
      interpret \<T>e: natural_transformation Cop.comp S "Y a" F "\<T> e"
        using natural_transformation_\<T>e by auto
      show "natural_transformation Cop.comp S (Y a) F (\<T> e)" ..
      show "\<E> (\<T> e) = e"
        using assms \<E>_def ide_a \<T>e_ide S.Fun_mkArr Hom.\<phi>_mapsto Hom.\<psi>_\<phi> ide_a
              F.preserves_ide [of a] S.Fun_ide [of "F a"] restrict_apply
        by fastforce 
    qed

    lemma \<E>\<tau>_in_Fa:
    assumes "natural_transformation Cop.comp S (Y a) F \<tau>"
    shows "\<E> \<tau> \<in> F.SET a"
    proof -
      interpret \<tau>: natural_transformation Cop.comp S "Y a" F \<tau> using assms by auto
      interpret yoneda_lemma_fixed_\<tau> C S \<phi> F a \<tau> ..
      show ?thesis
      proof (unfold \<E>_def)
        have "S.arr (\<tau> a) \<and> S.Dom (\<tau> a) = Hom.set (a, a) \<and> S.Cod (\<tau> a) = F.SET a"
          using ide_a Hom.set_map by simp
        hence "\<tau>.FUN a \<in> Hom.set (a, a) \<rightarrow> F.SET a"
          using S.Fun_mapsto by auto
        thus "\<tau>.FUN a (\<phi> (a, a) a) \<in> F.SET a"
          using ide_a Hom.\<phi>_mapsto [of a a] by auto
      qed
    qed

    text{*
      The other half of the Yoneda lemma:
      The mapping @{term \<T>} is a surjection, with right inverse @{term \<E>},
      taking natural transformations from @{term "Y a"} to @{term F}
      to elements of @{term "F.SET a"}.
    *}

    lemma \<T>_is_surjection:
    assumes "natural_transformation Cop.comp S (Y a) F \<tau>"
    shows "\<E> \<tau> \<in> F.SET a" and "\<T> (\<E> \<tau>) = \<tau>"
    proof -
      interpret natural_transformation Cop.comp S "Y a" F \<tau> using assms by auto
      interpret yoneda_lemma_fixed_\<tau> C S \<phi> F a \<tau> ..
      show 1: "\<E> \<tau> \<in> F.SET a" using assms \<E>\<tau>_in_Fa by auto
      interpret yoneda_lemma_fixed_e C S \<phi> F a "\<E> \<tau>"
        apply (unfold_locales) using 1 by auto
      interpret \<T>e: natural_transformation Cop.comp S "Y a" F "\<T> (\<E> \<tau>)"
        using natural_transformation_\<T>e by auto
      show "\<T> (\<E> \<tau>) = \<tau>"
      proof (intro eqI)
        show "natural_transformation Cop.comp S (Y a) F (\<T> (\<E> \<tau>))" ..
        show "\<T> (\<E> \<tau>) a = \<tau> a"
          using ide_a \<tau>_ide [of a] \<T>e_ide \<E>_def by simp
      qed
    qed
     
    text{*
      The main result.
    *}

    theorem yoneda_lemma:
    shows "bij_betw \<T> (F.SET a) (Collect (natural_transformation Cop.comp S (Y a) F))"
      using \<T>_is_injection \<T>_is_surjection apply (intro bij_betwI) by auto

  end

  text{*
    We now consider the special case in which @{term F} is the contravariant
    functor @{term "Y a'"}.  Then for any @{term e} in @{text "Hom.set (a, a')"}
    we have @{term "\<T> e = Y (\<psi> (a, a') e)"}, and @{term \<T>} is a bijection from
    @{text "Hom.set (a, a')"} to the set of natural transformations from @{term "Y a"}
    to @{term "Y a'"}.  It then follows that that the Yoneda functor @{term Y}
    is a fully faithful functor from @{term C} to the functor category @{text "[Cop, S]"}.
  *}

  locale yoneda_lemma_for_hom =
    C: category C +
    Cop: dual_category C +
    S: set_category S +
    yoneda_functor_fixed_object C S \<phi> a +
    Ya': yoneda_functor_fixed_object C S \<phi> a' +
    yoneda_lemma C S \<phi> "Y a'" a
    for C :: "'c comp"
    and S :: "'s comp"
    and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and F :: "'c \<Rightarrow> 's"
    and a :: 'c
    and a' :: 'c +
    assumes ide_a': "C.ide a'"
  begin

    text{*
      In case @{term F} is the functor @{term "Y a'"}, for any @{term "e \<in> Hom.set (a, a')"}
      the induced natural transformation @{term "\<T> e"} from @{term "Y a"} to @{term "Y a'"}
      is just @{term "Y (\<psi> (a, a') e)"}.
    *}

    lemma \<T>_equals_Yo\<psi>:
    assumes e: "e \<in> Hom.set (a, a')"
    shows "\<T> e = Y (\<psi> (a, a') e)"
    proof -
      let ?\<psi>e = "\<psi> (a, a') e"
      have \<psi>e: "?\<psi>e \<in> C.hom a a'" using ide_a ide_a' e Hom.\<psi>_mapsto [of a a'] by auto
      have 1: "C.dom ?\<psi>e = a \<and> C.cod ?\<psi>e = a'" using \<psi>e by auto
      interpret Ye: natural_transformation Cop.comp S "Y a" "Y a'" "Y ?\<psi>e"
        using Y_arr_is_transformation [of ?\<psi>e] \<psi>e 1 by simp
      interpret yoneda_lemma_fixed_e C S \<phi> "Y a'" a e
        apply (unfold_locales)
        using ide_a ide_a' e S.set_mkIde [of "Hom.set (a, a')"] Hom.set_map by simp
      interpret \<T>e: natural_transformation Cop.comp S "Y a" "Y a'" "\<T> e"
        using natural_transformation_\<T>e by auto
      interpret yoneda_lemma_fixed_\<tau> C S \<phi> "Y a'" a "\<T> e" ..
      have "natural_transformation Cop.comp S (Y a) (Y a') (Y ?\<psi>e)" ..
      moreover have "natural_transformation Cop.comp S (Y a) (Y a') (\<T> e)" ..
      moreover have "\<T> e a = Y ?\<psi>e a"
      proof -
        have 1: "S.arr (\<T> e a)"
          using ide_a E \<T>e.preserves_arr by simp
        have 2: "\<T> e a = S.mkArr (Hom.set (a, a)) (Ya'.SET a) (\<lambda>x. Ya'.FUN (\<psi> (a, a) x) e)"
          using ide_a \<T>o_def [of e a] \<T>e_ide [of a] by simp
        also have "... = S.mkArr (Hom.set (a, a)) (Hom.set (a, a')) (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a))"
        proof (intro S.mkArr_eqI)
          show "S.arr (S.mkArr (Hom.set (a, a)) (Ya'.SET a) (\<lambda>x. Ya'.FUN (\<psi> (a, a) x) e))"
            using ide_a E 1 2 by simp
          show "Hom.set (a, a) = Hom.set (a, a)" ..
          show 3: "Ya'.SET a = Hom.set (a, a')"
            using ide_a ide_a' Y_simp Hom.set_map by simp
          show "\<And>x. x \<in> Hom.set (a, a) \<Longrightarrow>
                      Ya'.FUN (\<psi> (a, a) x) e = (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a)) x"
          proof -
            fix x
            assume x: "x \<in> Hom.set (a, a)"
            have \<psi>x: "\<psi> (a, a) x \<in> C.hom a a" using ide_a x Hom.\<psi>_mapsto [of a a] by auto
            have "S.arr (Y a' (\<psi> (a, a) x)) \<and>
                  Y a' (\<psi> (a, a) x) = S.mkArr (Hom.set (a, a')) (Hom.set (a, a'))
                                              (\<phi> (a, a') \<circ> Cop.comp (\<psi> (a, a) x) \<circ> \<psi> (a, a'))"
              using Y_ide_arr [of a' "\<psi> (a, a) x" a a] ide_a ide_a' \<psi>x by blast
            hence "Ya'.FUN (\<psi> (a, a) x) e = (\<phi> (a, a') \<circ> Cop.comp (\<psi> (a, a) x) \<circ> \<psi> (a, a')) e"
              using E 3 S.Fun_mkArr [of "Hom.set (a, a')" "Hom.set (a, a')"
                                       "\<phi> (a, a') \<circ> Cop.comp (\<psi> (a, a) x) \<circ> \<psi> (a, a')"]
              by auto
            also have "... = (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a)) x" by simp
            finally show "Ya'.FUN (\<psi> (a, a) x) e = (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a)) x" by auto
          qed
        qed
        also have "... = Y ?\<psi>e a"
          using ide_a ide_a' \<psi>e Y_arr_ide [of a ?\<psi>e a a'] by auto
        finally show "\<T> e a = Y ?\<psi>e a" by auto
      qed
      ultimately show ?thesis using eqI by auto
    qed

    lemma Y_injective_on_homs:
    assumes "f \<in> C.hom a a'" and "f' \<in> C.hom a a'" and "map f = map f'"
    shows "f = f'"
    proof -
      have "f = \<psi> (a, a') (\<phi> (a, a') f)"
        using assms ide_a Hom.\<psi>_\<phi> [of a a'] by simp
      also have "... = \<psi> (a, a') (\<E> (\<T> (\<phi> (a, a') f)))"
        using ide_a assms(1) \<T>_is_injection Hom.\<phi>_mapsto [of a a'] Hom.set_map by fastforce
      also have "... = \<psi> (a, a') (\<E> (Y (\<psi> (a, a') (\<phi> (a, a') f))))"
        using assms Hom.\<phi>_mapsto [of a a'] \<T>_equals_Yo\<psi> [of "\<phi> (a, a') f"] by force
      also have "... = \<psi> (a, a') (\<E> (\<T> (\<phi> (a, a') f')))"
        using assms Hom.\<phi>_mapsto [of a a'] ide_a Hom.\<psi>_\<phi> [of a a'] Y_def
              \<T>_equals_Yo\<psi> [of "\<phi> (a, a') f'"]
        by fastforce
      also have "... = \<psi> (a, a') (\<phi> (a, a') f')"
        using ide_a assms(2) \<T>_is_injection Hom.\<phi>_mapsto [of a a'] Hom.set_map by fastforce
      also have "... = f'"
        using assms ide_a Hom.\<psi>_\<phi> [of a a'] by simp
      finally show "f = f'" by auto
    qed

    lemma Y_surjective_on_homs:
    assumes \<tau>: "natural_transformation Cop.comp S (Y a) (Y a') \<tau>"
    shows "Y (\<psi> (a, a') (\<E> \<tau>)) = \<tau>"
      using ide_a ide_a' \<tau> \<T>_is_surjection \<T>_equals_Yo\<psi> \<E>\<tau>_in_Fa Hom.set_map by simp

  end

  context yoneda_functor
  begin

    lemma is_faithful_functor:
    shows "faithful_functor C Cop_S.comp map"
    proof
      fix f :: 'c and f' :: 'c
      assume par: "C.par f f'" and ff': "map f = map f'"
      show "f = f'"
      proof -
        interpret Ya': yoneda_functor_fixed_object C S \<phi> "C.cod f"
          apply (unfold_locales) using par by auto
        interpret yoneda_lemma_for_hom C S \<phi> "Y (C.cod f)" "C.dom f" "C.cod f"
          apply (unfold_locales) using par by auto
        show "f = f'" using par ff' Y_injective_on_homs [of f f'] by simp
      qed
    qed

    lemma is_full_functor:
    shows "full_functor C Cop_S.comp map"
    proof
      fix a :: 'c and a' :: 'c and t
      assume a: "C.ide a" and a': "C.ide a'"
      assume t: "t \<in> Cop_S.hom (map a) (map a')"
      show "\<exists>e. e \<in> C.hom a a' \<and> (map e) = t"
      proof
        interpret Ya': yoneda_functor_fixed_object C S \<phi> a'
          apply (unfold_locales) using a' by auto
        interpret yoneda_lemma_for_hom C S \<phi> "Y a'" a a'
          apply (unfold_locales) using a a' by auto
        have NT: "natural_transformation Cop.comp S (Y a) (Y a') (Cop_S.Fun t)"
        proof -
          have "Cop_S.Dom t = Y a"
            using t Y_def Cop_S.Fun_dom mem_Collect_eq Cop_S.dom_simp by fastforce
          moreover have "Cop_S.Cod t = Y a'"
            using t a' Y_def Cop_S.Fun_cod mem_Collect_eq Cop_S.cod_simp by fastforce
          ultimately show ?thesis
            using t Cop_S.arr_char by auto
        qed
        hence 1: "\<E> (Cop_S.Fun t) \<in> Hom.set (a, a')"
          using \<E>\<tau>_in_Fa ide_a ide_a' Hom.set_map by simp
        moreover have "map (\<psi> (a, a') (\<E> (Cop_S.Fun t))) = t"
        proof (intro Cop_S.arr_eqI)
          have 2: "map (\<psi> (a, a') (\<E> (Cop_S.Fun t))) \<in> Cop_S.hom (map a) (map a')"
            (*
             * There is an odd namespace behavior here that makes it impossible to name the
             * "top-level" preserves_hom fact by writing "preserves_hom" or "local.preserves_hom".
             * Instead, I get local.\<tau>.preserves_hom, which refers to an eponymous fact in
             * natural_transformation.  So I obtained the desired fact through inference by the
             * "garden path" below.
             *
             * It seems to be that the preserves_hom fact inherited by yoneda_functor from
             * the super-locale curried_functor_2 becomes hidden by the preserves_hom fact
             * for \<tau> in yoneda_lemma_fixed_\<tau>.  It might be useful to try to extract a minimal
             * situation that exercises this.
             *)
            using 1 functor.preserves_hom [of C Cop_S.comp map] is_functor Hom.\<psi>_mapsto [of a a']
                  ide_a ide_a'
            by blast
          show "Cop_S.arr t" using t by blast
          show "Cop_S.arr (map (\<psi> (a, a') (\<E> (Cop_S.Fun t))))" using 2 by blast
          show 3: "Cop_S.Fun (map (\<psi> (a, a') (\<E> (Cop_S.Fun t)))) = Cop_S.Fun t"
            using NT Y_surjective_on_homs Y_def by simp
          show 4: "Cop_S.Dom (map (\<psi> (a, a') (\<E> (Cop_S.Fun t)))) = Cop_S.Dom t"
            using 2 natural_transformation_axioms
            by (metis (mono_tags, lifting) Cop_S.Fun_dom mem_Collect_eq t)
          show "Cop_S.Cod (map (\<psi> (a, a') (\<E> (Cop_S.Fun t)))) = Cop_S.Cod t"
            using 2 3 4 t
            by (metis (mono_tags, lifting) Cop_S.Fun_cod mem_Collect_eq)
        qed
        ultimately show "\<psi> (a, a') (\<E> (Cop_S.Fun t)) \<in> C.hom a a' \<and>
                         map (\<psi> (a, a') (\<E> (Cop_S.Fun t))) = t"
          using ide_a ide_a' Hom.\<psi>_mapsto [of a a'] by auto
      qed
    qed

  end

  sublocale yoneda_functor \<subseteq> faithful_functor C Cop_S.comp map
    using is_faithful_functor by auto
  sublocale yoneda_functor \<subseteq> full_functor C Cop_S.comp map using is_full_functor by auto
  sublocale yoneda_functor \<subseteq> fully_faithful_functor C Cop_S.comp map ..

end

