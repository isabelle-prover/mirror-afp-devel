(*  Title:       Yoneda
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Yoneda

theory Yoneda
imports DualCategory SetCat FunctorCategory
begin

  text\<open>
    This theory defines the notion of a ``hom-functor'' and gives a proof of the Yoneda Lemma.
    In traditional developments of category theory based on set theories such as ZFC,
    hom-functors are normally defined to be functors into the large category \textbf{Set}
    whose objects are of \emph{all} sets and whose arrows are functions between sets.
    However, in HOL there does not exist a single ``type of all sets'', so the notion of
    the category of \emph{all} sets and functions does not make sense.  To work around this,
    we consider a more general setting consisting of a category @{term C} together with
    a set category @{term S} and a function @{term "\<phi> :: 'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"} such that
    whenever @{term b} and @{term a} are objects of C then @{term "\<phi> (b, a)"} maps
    \<open>C.hom b a\<close> injectively to \<open>S.Univ\<close>.  We show that these data induce
    a binary functor \<open>Hom\<close> from \<open>Cop\<times>C\<close> to @{term S} in such a way that @{term \<phi>}
    is rendered natural in @{term "(b, a)"}.  The Yoneda lemma is then proved for the
    Yoneda functor determined by \<open>Hom\<close>.
\<close>

  section "Hom-Functors"

  text\<open>
    A hom-functor for a category @{term C} allows us to regard the hom-sets of @{term C}
    as objects of a category @{term S} of sets and functions.  Any description of a
    hom-functor for @{term C} must therefore specify the category @{term S} and provide
    some sort of correspondence between arrows of @{term C} and elements of objects of @{term S}.
    If we are to think of each hom-set \<open>C.hom b a\<close> of \<open>C\<close> as corresponding
    to an object \<open>Hom (b, a)\<close> of @{term S} then at a minimum it ought to be the
    case that the correspondence between arrows and elements is bijective between
    \<open>C.hom b a\<close> and \<open>Hom (b, a)\<close>.  The \<open>hom_functor\<close> locale defined
    below captures this idea by assuming a set category @{term S} and a function @{term \<phi>}
    taking arrows of @{term C} to elements of \<open>S.Univ\<close>, such that @{term \<phi>} is injective
    on each set \<open>C.hom b a\<close>.  We show that these data induce a functor \<open>Hom\<close>
    from \<open>Cop\<times>C\<close> to \<open>S\<close> in such a way that @{term \<phi>} becomes a natural
    bijection between \<open>C.hom b a\<close> and \<open>Hom (b, a)\<close>.
\<close>

  locale hom_functor =
    C: category C +
    S: set_category S setp
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and setp :: "'s set \<Rightarrow> bool"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's" +
  assumes maps_arr_to_Univ: "C.arr f \<Longrightarrow> \<phi> (C.dom f, C.cod f) f \<in> S.Univ"
  and local_inj: "\<lbrakk> C.ide b; C.ide a \<rbrakk> \<Longrightarrow> inj_on (\<phi> (b, a)) (C.hom b a)"
  and small_homs: "\<lbrakk> C.ide b; C.ide a \<rbrakk> \<Longrightarrow> setp (\<phi> (b, a) ` C.hom b a)"
  begin

    sublocale Cop: dual_category C ..
    sublocale CopxC: product_category Cop.comp C ..

    notation S.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>S _\<guillemotright>")
    notation CopxC.comp   (infixr "\<odot>" 55)
    notation CopxC.in_hom ("\<guillemotleft>_ : _ \<rightleftharpoons> _\<guillemotright>")

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
    assumes "\<guillemotleft>f : b \<rightarrow> a\<guillemotright>"
    shows "\<psi> (b, a) (\<phi> (b, a) f) = f"
      using assms local_inj [of b a] \<psi>_def by fastforce

    lemma \<phi>_\<psi> [simp]:
    assumes "C.ide b" and "C.ide a"
    and "x \<in> set (b, a)"
    shows "\<phi> (b, a) (\<psi> (b, a) x) = x"
      using assms set_def local_inj \<psi>_def by auto

    lemma \<psi>_img_set:
    assumes "C.ide b" and "C.ide a"
    shows "\<psi> (b, a) ` set (b, a) = C.hom b a"
      using assms \<psi>_def set_def local_inj by auto

    text\<open>
      A hom-functor maps each arrow @{term "(g, f)"} of @{term "CopxC"}
      to the arrow of the set category @{term[source=true] S} corresponding to the function
      that takes an arrow @{term h} of @{term C} to the arrow @{term "C f (C h g)"} of @{term C}
      obtained by precomposing with @{term g} and postcomposing with @{term f}.
\<close>

    definition map
    where "map gf =
             (if CopxC.arr gf then
                S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf))
                        (\<phi> (CopxC.cod gf) o (\<lambda>h. snd gf \<cdot> h \<cdot> fst gf) o \<psi> (CopxC.dom gf))
              else S.null)"

    lemma arr_map:
    assumes "CopxC.arr gf"
    shows "S.arr (map gf)"
    proof -
      have "\<phi> (CopxC.cod gf) o (\<lambda>h. snd gf \<cdot> h \<cdot> fst gf) o \<psi> (CopxC.dom gf)
              \<in> set (CopxC.dom gf) \<rightarrow> set (CopxC.cod gf)"
        using assms \<phi>_mapsto [of "fst (CopxC.cod gf)" "snd (CopxC.cod gf)"]
              \<psi>_mapsto [of "fst (CopxC.dom gf)" "snd (CopxC.dom gf)"]
        by fastforce
      thus ?thesis
        using assms map_def set_subset_Univ small_homs
        by (simp add: set_def)
    qed

    lemma map_ide [simp]:
    assumes "C.ide b" and "C.ide a"
    shows "map (b, a) = S.mkIde (set (b, a))"
    proof -
      have "map (b, a) = S.mkArr (set (b, a)) (set (b, a))
                                 (\<phi> (b, a) o (\<lambda>h. a \<cdot> h \<cdot> b) o \<psi> (b, a))"
        using assms map_def by auto
      also have "... = S.mkArr (set (b, a)) (set (b, a)) (\<lambda>h. h)"
      proof -
        have "S.mkArr (set (b, a)) (set (b, a)) (\<lambda>h. h) = ..."
          using assms set_subset_Univ set_def C.comp_arr_dom C.comp_cod_arr
                S.arr_mkIde small_homs
          by (intro S.mkArr_eqI', simp, fastforce)
        thus ?thesis by auto
      qed
      also have "... = S.mkIde (set (b, a))"
        using assms S.mkIde_as_mkArr set_subset_Univ small_homs set_def by simp
      finally show ?thesis by blast
    qed

    lemma set_map:
    assumes "C.ide a" and "C.ide b"
    shows "S.set (map (b, a)) = set (b, a)"
      using assms map_ide set_subset_Univ small_homs set_def by simp

    text\<open>
      The definition does in fact yield a functor.
\<close>

    sublocale "functor" CopxC.comp S map
    proof
      show "\<And>gf. \<not> CopxC.arr gf \<Longrightarrow> map gf = S.null"
        using map_def by auto
      fix gf
      assume gf: "CopxC.arr gf"
      thus arr: "S.arr (map gf)" using gf arr_map by blast
      show "S.dom (map gf) = map (CopxC.dom gf)"
        using arr gf local.map_def map_ide by auto
      show "S.cod (map gf) = map (CopxC.cod gf)"
        using gf set_subset_Univ \<psi>_mapsto map_def set_def S.arr_mkIde arr map_ide by auto
      next
      fix gf gf'
      assume gf': "CopxC.seq gf' gf"
      hence seq: "C.arr (fst gf) \<and> C.arr (snd gf) \<and> C.dom (snd gf') = C.cod (snd gf) \<and>
                  C.arr (fst gf') \<and> C.arr (snd gf') \<and> C.dom (fst gf) = C.cod (fst gf')"
        by (elim CopxC.seqE C.seqE, auto)
      have 0: "S.arr (map (CopxC.comp gf' gf))"
        using gf' arr_map by blast
      have 1: "map (gf' \<odot> gf) =
                    S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf'))
                            (\<phi> (CopxC.cod gf') o (\<lambda>h. snd (gf' \<odot> gf) \<cdot> h \<cdot> fst (gf' \<odot> gf))
                                               o \<psi> (CopxC.dom gf))"
        using gf' map_def using CopxC.cod_comp CopxC.dom_comp by auto
      also have "... = S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf'))
                               (\<phi> (CopxC.cod gf') \<circ> (\<lambda>h. snd gf' \<cdot> h \<cdot> fst gf') \<circ> \<psi> (CopxC.dom gf')
                                \<circ>
                               (\<phi> (CopxC.cod gf) \<circ> (\<lambda>h. snd gf \<cdot> h \<cdot> fst gf) \<circ> \<psi> (CopxC.dom gf)))"
      proof (intro S.mkArr_eqI')
        show "S.arr (S.mkArr (set (CopxC.dom gf)) (set (CopxC.cod gf'))
                             (\<phi> (CopxC.cod gf') \<circ> (\<lambda>h. snd (gf' \<odot> gf) \<cdot> h \<cdot> fst (gf' \<odot> gf))
                                                \<circ> \<psi> (CopxC.dom gf)))"
          using 0 1 by simp
        show "\<And>x. x \<in> set (CopxC.dom gf) \<Longrightarrow>
                     (\<phi> (CopxC.cod gf') \<circ> (\<lambda>h. snd (gf' \<odot> gf) \<cdot> h \<cdot> fst (gf' \<odot> gf)) \<circ>
                      \<psi> (CopxC.dom gf)) x =
                     (\<phi> (CopxC.cod gf') \<circ> (\<lambda>h. snd gf' \<cdot> h \<cdot> fst gf') \<circ> \<psi> (CopxC.dom gf') \<circ>
                      (\<phi> (CopxC.cod gf) \<circ> (\<lambda>h. snd gf \<cdot> h \<cdot> fst gf) \<circ> \<psi> (CopxC.dom gf))) x"
          using gf' \<psi>_mapsto set_def \<psi>_\<phi> C.comp_assoc by fastforce
      qed
      also have "... = map gf' \<cdot>\<^sub>S map gf"
        using seq gf' map_def arr_map [of gf] arr_map [of gf'] S.comp_mkArr by auto
      finally show "map (gf' \<odot> gf) = map gf' \<cdot>\<^sub>S map gf"
        using seq gf' by auto
    qed

    lemma is_functor:
    shows "functor CopxC.comp S map" ..

    sublocale binary_functor Cop.comp C S map ..

    lemma is_binary_functor:
    shows "binary_functor Cop.comp C S map" ..

    text\<open>
      The map @{term \<phi>} determines a bijection between @{term "C.hom b a"} and
      @{term "set (b, a)"} which is natural in @{term "(b, a)"}.
\<close>

    lemma \<phi>_local_bij:
    assumes "C.ide b" and "C.ide a"
    shows "bij_betw (\<phi> (b, a)) (C.hom b a) (set (b, a))"
      using assms local_inj inj_on_imp_bij_betw set_def by auto

    lemma \<phi>_natural:
    assumes "C.arr g" and "C.arr f" and "h \<in> C.hom (C.cod g) (C.dom f)"
    shows "\<phi> (C.dom g, C.cod f) (f \<cdot> h \<cdot> g) = S.Fun (map (g, f)) (\<phi> (C.cod g, C.dom f) h)"
    proof -
      let ?\<phi>h = "\<phi> (C.cod g, C.dom f) h"
      have \<phi>h: "?\<phi>h \<in> set (C.cod g, C.dom f)"
        using assms \<phi>_mapsto set_def by simp
      have gf: "CopxC.arr (g, f)" using assms by simp
      have "S.Fun (map (g, f)) ?\<phi>h =
                (\<phi> (C.dom g, C.cod f) \<circ> (\<lambda>h. f \<cdot> h \<cdot> g) \<circ> \<psi> (C.cod g, C.dom f)) ?\<phi>h"
      proof -
        have "S.Fun (map (g, f)) =
                 restrict (\<phi> (C.dom g, C.cod f) \<circ> (\<lambda>h. f \<cdot> h \<cdot> g) \<circ> \<psi> (C.cod g, C.dom f))
                          (set (C.cod g, C.dom f))"
        proof -
          have "map (g, f) =
                   S.mkArr (set (C.cod g, C.dom f)) (set (C.dom g, C.cod f))
                           (\<phi> (C.dom g, C.cod f) \<circ> (\<lambda>h. f \<cdot> h \<cdot> g) \<circ> \<psi> (C.cod g, C.dom f))"
            using assms map_def by simp
          moreover have "S.arr (map (g, f))" using gf by simp
          ultimately show ?thesis
            using S.Fun_mkArr by simp
        qed
        thus ?thesis
          using \<phi>h by simp
      qed
      also have "... = \<phi> (C.dom g, C.cod f) (f \<cdot> h \<cdot> g)"
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
             restrict (\<phi> (C.dom g, C.cod f) o (\<lambda>h. f \<cdot> h \<cdot> g) o \<psi> (C.cod g, C.dom f))
                      (set (C.cod g, C.dom f))"
      using assms map_def preserves_arr by force

    lemma map_simp_1:
    assumes "C.arr g" and "C.ide a"
    shows "map (g, a) = S.mkArr (set (C.cod g, a)) (set (C.dom g, a))
                                (\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a))"
    proof -
      have 1: "map (g, a) = S.mkArr (set (C.cod g, a)) (set (C.dom g, a))
                                    (\<phi> (C.dom g, a) o (\<lambda>h. a \<cdot> h \<cdot> g) o \<psi> (C.cod g, a))"
        using assms map_def by force
      also have "... = S.mkArr (set (C.cod g, a)) (set (C.dom g, a))
                               (\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a))"
        using assms 1 preserves_arr [of "(g, a)"] set_def C.in_homI C.comp_cod_arr
        by (intro S.mkArr_eqI) auto
     finally show ?thesis by blast
    qed

    lemma map_simp_2:
    assumes "C.ide b" and "C.arr f"
    shows "map (b, f) = S.mkArr (set (b, C.dom f)) (set (b, C.cod f))
                                (\<phi> (b, C.cod f) o C f o \<psi> (b, C.dom f))"
    proof -
      have 1: "map (b, f) = S.mkArr (set (b, C.dom f)) (set (b, C.cod f))
                                    (\<phi> (b, C.cod f) o (\<lambda>h. f \<cdot> h \<cdot> b) o \<psi> (b, C.dom f))"
        using assms map_def by force
      also have "... = S.mkArr (set (b, C.dom f)) (set (b, C.cod f))
                               (\<phi> (b, C.cod f) o C f o \<psi> (b, C.dom f))"
        using assms 1 preserves_arr [of "(b, f)"] set_def C.in_homI C.comp_arr_dom
        by (intro S.mkArr_eqI) auto
      finally show ?thesis by blast
    qed

  end

  text\<open>
    Every category @{term C} has a hom-functor: take @{term S} to be the replete set category
    generated by the arrow type \<open>'a\<close> of @{term C} and take @{term "\<phi> (b, a)"} to be the map
    \<open>S.UP :: 'a \<Rightarrow> 'a SC.arr\<close>.
\<close>

  context category
  begin

    interpretation S: replete_setcat \<open>TYPE('a)\<close> .

    lemma has_hom_functor:
    shows "hom_functor C S.comp S.setp (\<lambda>_. S.UP)"
      using S.UP_mapsto S.inj_UP injD inj_onI
      by unfold_locales (auto simp add: inj_def inj_onI)

  end

  text\<open>
    The locales \<open>set_valued_functor\<close> and \<open>set_valued_transformation\<close> provide some
    abbreviations that are convenient when working with functors and natural transformations
    into a set category.
\<close>

  locale set_valued_functor =
    C: category C +
    S: set_category S setp +
    "functor" C S F
    for C :: "'c comp"
    and S :: "'s comp"
    and setp :: "'s set \<Rightarrow> bool"
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
    S: set_category S setp +
    F: set_valued_functor C S setp F +
    G: set_valued_functor C S setp G +
    natural_transformation C S F G \<tau>
  for C :: "'c comp"
  and S :: "'s comp"
  and setp :: "'s set \<Rightarrow> bool"
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
    
  text\<open>
    A Yoneda functor is the functor from @{term C} to \<open>[Cop, S]\<close> obtained by ``currying''
    a hom-functor in its first argument.
\<close>

  locale yoneda_functor =
    C: category C +
    Cop: dual_category C +
    CopxC: product_category Cop.comp C +
    S: set_category S setp +
    Hom: hom_functor C S setp \<phi>
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and setp :: "'s set \<Rightarrow> bool"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  begin

    sublocale Cop_S: functor_category Cop.comp S ..
    sublocale curried_functor' Cop.comp C S Hom.map ..

    notation Cop_S.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>C\<^sub>o\<^sub>p\<^sub>,\<^sub>S\<^sub>] _\<guillemotright>")

    abbreviation \<psi>
    where "\<psi> \<equiv> Hom.\<psi>"

    text\<open>
      An arrow of the functor category \<open>[Cop, S]\<close> consists of a natural transformation
      bundled together with its domain and codomain functors.  However, when considering
      a Yoneda functor from @{term[source=true] C} to \<open>[Cop, S]\<close> we generally are only
      interested in the mapping @{term Y} that takes each arrow @{term f} of @{term[source=true] C}
      to the corresponding natural transformation @{term "Y f"}.  The domain and codomain functors
      are then the identity transformations @{term "Y (C.dom f)"} and @{term "Y (C.cod f)"}.
\<close>

    definition Y
    where "Y f \<equiv> Cop_S.Map (map f)"

    lemma Y_simp [simp]:
    assumes "C.arr f"
    shows "Y f = (\<lambda>g. Hom.map (g, f))"
      using assms preserves_arr Y_def by simp

    lemma Y_ide_is_functor:
    assumes "C.ide a"
    shows "functor Cop.comp S (Y a)"
      using assms Y_def Hom.fixing_ide_gives_functor_2 by force

    lemma Y_arr_is_transformation:
    assumes "C.arr f"
    shows "natural_transformation Cop.comp S (Y (C.dom f)) (Y (C.cod f)) (Y f)"
      using assms Y_def [of f] map_def Hom.fixing_arr_gives_natural_transformation_2
            preserves_dom preserves_cod by fastforce

    lemma Y_ide_arr [simp]:
    assumes a: "C.ide a" and "\<guillemotleft>g : b' \<rightarrow> b\<guillemotright>"
    shows "\<guillemotleft>Y a g : Hom.map (b, a) \<rightarrow>\<^sub>S Hom.map (b', a)\<guillemotright>"
    and "Y a g = S.mkArr (Hom.set (b, a)) (Hom.set (b', a)) (\<phi> (b', a) o Cop.comp g o \<psi> (b, a))"
      using assms Hom.map_simp_1 by (fastforce, auto)

    lemma Y_arr_ide [simp]:
    assumes "C.ide b" and "\<guillemotleft>f : a \<rightarrow> a'\<guillemotright>"
    shows "\<guillemotleft>Y f b : Hom.map (b, a) \<rightarrow>\<^sub>S Hom.map (b, a')\<guillemotright>"
    and "Y f b = S.mkArr (Hom.set (b, a)) (Hom.set (b, a')) (\<phi> (b, a') o C f o \<psi> (b, a))"
      using assms apply fastforce
      using assms Hom.map_simp_2 by auto

  end

  locale yoneda_functor_fixed_object =
    yoneda_functor +
  fixes a
  assumes ide_a: "C.ide a"
  begin
  
    sublocale "functor" Cop.comp S \<open>Y a\<close>
      using ide_a Y_ide_is_functor by auto
    sublocale set_valued_functor Cop.comp S setp \<open>Y a\<close> ..

  end

  text\<open>
    The Yoneda lemma states that, given a category @{term C} and a functor @{term F}
    from @{term Cop} to a set category @{term S}, for each object @{term a} of @{term C},
    the set of natural transformations from the contravariant functor @{term "Y a"}
    to @{term F} is in bijective correspondence with the set \<open>F.SET a\<close>
    of elements of @{term "F a"}.

    Explicitly, if @{term e} is an arbitrary element of the set \<open>F.SET a\<close>,
    then the functions \<open>\<lambda>x. F.FUN (\<psi> (b, a) x) e\<close> are the components of a
    natural transformation from @{term "Y a"} to @{term F}.
    Conversely, if @{term \<tau>} is a natural transformation from @{term "Y a"} to @{term F},
    then the component @{term "\<tau> b"} of @{term \<tau>} at an arbitrary object @{term b}
    is completely determined by the single arrow \<open>\<tau>.FUN a (\<phi> (a, a) a)))\<close>,
    which is the the element of \<open>F.SET a\<close> that corresponds to the image of the
    identity @{term a} under the function \<open>\<tau>.FUN a\<close>.
    Then @{term "\<tau> b"} is the arrow from @{term "Y a b"} to @{term "F b"} corresponding
    to the function \<open>\<lambda>x. (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a (\<phi> (a, a) a)))\<close>
    from \<open>S.set (Y a b)\<close> to \<open>F.SET b\<close>.
   
    The above expressions look somewhat more complicated than the usual versions due to the
    need to account for the coercions @{term \<phi>} and @{term \<psi>}.
\<close>

  locale yoneda_lemma =
    yoneda_functor_fixed_object C S setp \<phi> a +
    F: set_valued_functor Cop.comp S setp F
  for C :: "'c comp" (infixr "\<cdot>" 55)
  and S :: "'s comp" (infixr "\<cdot>\<^sub>S" 55)
  and setp :: "'s set \<Rightarrow> bool"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and F :: "'c \<Rightarrow> 's"
  and a :: 'c
  begin

    text\<open>
      The mapping that evaluates the component @{term "\<tau> a"} at @{term a} of a
      natural transformation @{term \<tau>} from @{term Y} to @{term F} on the element
      @{term "\<phi> (a, a) a"} of @{term "SET a"}, yielding an element of @{term "F.SET a"}.
\<close>

    definition \<E> :: "('c \<Rightarrow> 's) \<Rightarrow> 's"
    where "\<E> \<tau> = S.Fun (\<tau> a) (\<phi> (a, a) a)"

    text\<open>
      The mapping that takes an element @{term e} of @{term "F.SET a"} and produces
      a map on objects of @{term[source=true] C} whose value at @{term b} is the arrow of
      @{term[source=true] S} corresponding to the function
      @{term "(\<lambda>x. F.FUN (\<psi> (b, a) x) e) \<in> Hom.set (b, a) \<rightarrow> F.SET b"}.
\<close>

    definition \<T>\<^sub>o :: "'s \<Rightarrow> 'c \<Rightarrow> 's"
    where "\<T>\<^sub>o e b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. F.FUN (\<psi> (b, a) x) e)"

    lemma \<T>\<^sub>o_in_hom:
    assumes e: "e \<in> S.set (F a)" and b: "C.ide b"
    shows "\<guillemotleft>\<T>\<^sub>o e b : Y a b \<rightarrow>\<^sub>S F b\<guillemotright>"
    proof -
      have "(\<lambda>x. F.FUN (\<psi> (b, a) x) e) \<in> Hom.set (b, a) \<rightarrow> F.SET b"
      proof
        fix x
        assume x: "x \<in> Hom.set (b, a)"
        thus "F.FUN (\<psi> (b, a) x) e \<in> F.SET b"
          using assms e ide_a Hom.\<psi>_mapsto S.Fun_mapsto [of "F (\<psi> (b, a) x)"] by force
      qed
      thus ?thesis
        using ide_a b S.mkArr_in_hom Hom.set_subset_Univ S.mkIde_set \<T>\<^sub>o_def
        by (metis C.ideD(1) Cop.ide_char F.preserves_ide Hom.set_map S.setp_set_ide
            preserves_ide Y_simp)
    qed

    text\<open>
      For each @{term "e \<in> F.SET a"}, the mapping @{term "\<T>\<^sub>o e"} gives the components
      of a natural transformation @{term \<T>} from @{term "Y a"} to @{term F}.
\<close>

    lemma \<T>\<^sub>o_induces_transformation:
    assumes e: "e \<in> S.set (F a)"
    shows "transformation_by_components Cop.comp S (Y a) F (\<T>\<^sub>o e)"
    proof
      show "\<And>b. Cop.ide b \<Longrightarrow> \<guillemotleft>\<T>\<^sub>o e b : Y a b \<rightarrow>\<^sub>S F b\<guillemotright>"
        using ide_a e \<T>\<^sub>o_in_hom by simp
      fix g :: 'c
      assume g: "Cop.arr g"
      let ?b = "Cop.dom g"
      let ?b' = "Cop.cod g"
      show "\<T>\<^sub>o e (Cop.cod g) \<cdot>\<^sub>S Y a g = F g \<cdot>\<^sub>S \<T>\<^sub>o e (Cop.dom g)"
      proof -
        have 1: "\<T>\<^sub>o e (Cop.cod g) \<cdot>\<^sub>S Y a g =
                 S.mkArr (Hom.set (?b, a)) (F.SET ?b')
                         ((\<lambda>x. F.FUN (\<psi> (?b', a) x) e) o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a)))"
        proof -
          have "S.arr (S.mkArr (Hom.set (?b', a)) (F.SET ?b') (\<lambda>s. F.FUN (\<psi> (?b', a) s) e)) \<and>
                S.dom (S.mkArr (Hom.set (?b', a)) (F.SET ?b') (\<lambda>s. F.FUN (\<psi> (?b', a) s) e))
                   = Y a ?b' \<and>
                S.cod (S.mkArr (Hom.set (?b', a)) (F.SET ?b') (\<lambda>s. F.FUN (\<psi> (?b', a) s) e))
                   = F ?b'"
            using Cop.cod_char \<T>\<^sub>o_def \<T>\<^sub>o_in_hom e g
            by (metis Cop.ide_char Cop.ide_cod S.in_homE)
          moreover have "Y a g = S.mkArr (Hom.set (?b, a)) (Hom.set (?b', a))
                                         (\<phi> (?b', a) \<circ> Cop.comp g \<circ> \<psi> (?b, a))"
            using Y_ide_arr [of a g ?b' ?b] ide_a g by auto
          ultimately show ?thesis
            using ide_a e g Y_ide_arr Cop.cod_char \<T>\<^sub>o_def S.comp_mkArr preserves_arr
            by metis
        qed
        also have "... = S.mkArr (Hom.set (?b, a)) (F.SET ?b')
                                 (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e))"
        proof (intro S.mkArr_eqI')
          show "S.arr (S.mkArr (Hom.set (?b, a)) (F.SET ?b')
                               ((\<lambda>x. F.FUN (\<psi> (?b', a) x) e)
                                  o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))))"
          proof (intro S.arr_mkArrI)
            show "setp (Hom.set (Cop.dom g, a))"
              by (metis C.ideD(1) Cop.arr_dom Cop.ide_char CopxC.arrI\<^sub>P\<^sub>C Hom.arr_map
                  S.arr_mkIde Cop.ide_dom g Hom.map_ide ide_a)
            show "setp (F.SET (Cop.cod g))"
              using g by force
            show "(\<lambda>x. F.FUN (\<psi> (?b', a) x) e) o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))
                      \<in> Hom.set (?b, a) \<rightarrow> F.SET ?b'"
            proof -
              have "S.arr (S (\<T>\<^sub>o e ?b') (Y a g))"
                using ide_a e g \<T>\<^sub>o_in_hom Y_ide_arr(1) Cop.ide_char Cop.ide_cod by blast
              thus ?thesis using 1 by simp
            qed
          qed
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
              have "\<guillemotleft>\<psi> (?b, a) x : ?b \<rightarrow> a\<guillemotright>"
                using ide_a x g Hom.\<psi>_mapsto [of ?b a] by auto
              thus ?thesis
                using assms g Hom.\<psi>_\<phi> F.preserves_comp by fastforce
            qed
            also have "... = (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)) x" by fastforce
            finally show "((\<lambda>x. F.FUN (\<psi> (?b', a) x) e) o (\<phi> (?b', a) o Cop.comp g o \<psi> (?b, a))) x
                            = (F.FUN g o (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)) x"
              by simp
          qed
        qed
        also have "... = F g \<cdot>\<^sub>S \<T>\<^sub>o e ?b"
        proof -
          have "S.arr (F g) \<and> F g = S.mkArr (F.SET ?b) (F.SET ?b') (F.FUN g)"
            using g S.mkArr_Fun [of "F g"] by simp
          moreover have
              "S.arr (\<T>\<^sub>o e ?b) \<and>
               \<T>\<^sub>o e ?b = S.mkArr (Hom.set (?b, a)) (F.SET ?b) (\<lambda>x. F.FUN (\<psi> (?b, a) x) e)"
            using e g \<T>\<^sub>o_def \<T>\<^sub>o_in_hom
            by (metis C.ide_cod Cop.arr_char Cop.dom_char S.in_homE)
          ultimately show ?thesis
            using S.comp_mkArr by metis
        qed
        finally show ?thesis by blast
      qed
    qed

    definition \<T> :: "'s \<Rightarrow> 'c \<Rightarrow> 's"
    where "\<T> e \<equiv> transformation_by_components.map Cop.comp S (Y a) (\<T>\<^sub>o e)"

  end

  locale yoneda_lemma_fixed_e =
    yoneda_lemma +
  fixes e
  assumes E: "e \<in> F.SET a"
  begin

    interpretation \<T>e: transformation_by_components Cop.comp S \<open>Y a\<close> F \<open>\<T>\<^sub>o e\<close>
      using E \<T>\<^sub>o_induces_transformation by auto
    sublocale \<T>e: natural_transformation Cop.comp S \<open>Y a\<close> F \<open>\<T> e\<close>
      unfolding \<T>_def ..

    lemma natural_transformation_\<T>e:
    shows "natural_transformation Cop.comp S (Y a) F (\<T> e)" ..

    lemma \<T>e_ide:
    assumes "Cop.ide b"
    shows "S.arr (\<T> e b)"
    and "\<T> e b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. F.FUN (\<psi> (b, a) x) e)"
      using assms apply auto[1]
      using assms \<T>\<^sub>o_def \<T>_def by auto

  end

  locale yoneda_lemma_fixed_\<tau> =
    yoneda_lemma +
    \<tau>: natural_transformation Cop.comp S \<open>Y a\<close> F \<tau>
  for \<tau>
  begin

    sublocale \<tau>: set_valued_transformation Cop.comp S setp \<open>Y a\<close> F \<tau> ..

    text\<open>
      The key lemma: The component @{term "\<tau> b"} of @{term \<tau>} at an arbitrary object @{term b}
      is completely determined by the single element @{term "\<tau>.FUN a (\<phi> (a, a) a) \<in> F.SET a"}.
\<close>

    lemma \<tau>_ide:
    assumes b: "Cop.ide b"
    shows "\<tau> b = S.mkArr (Hom.set (b, a)) (F.SET b)
                         (\<lambda>x. (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a (\<phi> (a, a) a))))"
    proof -
      let ?\<phi>a = "\<phi> (a, a) a"
      have \<phi>a: "\<phi> (a, a) a \<in> Hom.set (a, a)" using ide_a Hom.\<phi>_mapsto by fastforce
      have 1: "\<tau> b = S.mkArr (Hom.set (b, a)) (F.SET b) (\<tau>.FUN b)"
        using ide_a b S.mkArr_Fun [of "\<tau> b"] Hom.set_map by auto
      also have
          "... = S.mkArr (Hom.set (b, a)) (F.SET b) (\<lambda>x. (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a ?\<phi>a)))"
      proof (intro S.mkArr_eqI')
        show 2: "S.arr (S.mkArr (Hom.set (b, a)) (F.SET b) (\<tau>.FUN b))"
          using ide_a b 1 S.mkArr_Fun [of "\<tau> b"] Hom.set_map by auto
        show "\<And>x. x \<in> Hom.set (b, a) \<Longrightarrow> \<tau>.FUN b x = (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a ?\<phi>a))"
        proof -
          fix x
          assume x: "x \<in> Hom.set (b, a)"
          let ?\<psi>x = "\<psi> (b, a) x"
          have \<psi>x: "\<guillemotleft>?\<psi>x : b \<rightarrow> a\<guillemotright>"
            using ide_a b x Hom.\<psi>_mapsto [of b a] by auto
          show "\<tau>.FUN b x = (F.FUN (\<psi> (b, a) x) (\<tau>.FUN a ?\<phi>a))"
          proof -
            have "\<tau>.FUN b x = S.Fun (\<tau> b \<cdot>\<^sub>S Y a ?\<psi>x) ?\<phi>a"
            proof -
              have "\<tau>.FUN b x = \<tau>.FUN b ((\<phi> (b, a) o Cop.comp ?\<psi>x) a)"
                using ide_a b x \<psi>x Hom.\<phi>_\<psi>
                by (metis C.comp_cod_arr C.in_homE C.ide_dom Cop.comp_def comp_apply)
              also have "... = (\<tau>.FUN b o (\<phi> (b, a) o Cop.comp ?\<psi>x o \<psi> (a, a))) ?\<phi>a"
                using ide_a b C.ide_in_hom by simp
              also have "... = S.Fun (\<tau> b \<cdot>\<^sub>S Y a ?\<psi>x) ?\<phi>a"
              proof -
                have "S.seq (\<tau> b) (Y a ?\<psi>x) \<and>
                      \<tau> b \<cdot>\<^sub>S Y a ?\<psi>x =
                         S.mkArr (Hom.set (a, a)) (F.SET b)
                                 (\<tau>.FUN b o (\<phi> (b, a) \<circ> Cop.comp ?\<psi>x \<circ> \<psi> (a, a)))"
                proof
                  show "S.seq (\<tau> b) (Y a ?\<psi>x)"
                    using \<psi>x \<tau>.is_natural_2 by fastforce
                  show "\<tau> b \<cdot>\<^sub>S Y a ?\<psi>x =
                           S.mkArr (Hom.set (a, a)) (F.SET b)
                                   (\<tau>.FUN b o (\<phi> (b, a) \<circ> Cop.comp ?\<psi>x \<circ> \<psi> (a, a)))"
                    by (metis 1 2 Cop.arrI Cop.hom_char S.comp_mkArr Y_ide_arr(2)
                        \<psi>x ide_a preserves_arr)
                qed
                thus ?thesis
                  using ide_a b x Hom.\<phi>_mapsto S.Fun_mkArr by force
              qed
              finally show ?thesis by auto
            qed
            also have "... = S.Fun (F ?\<psi>x \<cdot>\<^sub>S \<tau> a) ?\<phi>a"
              using ide_a b \<psi>x \<tau>.naturality by force
            also have "... = F.FUN ?\<psi>x (\<tau>.FUN a ?\<phi>a)"
            proof -
              have "restrict (S.Fun (F ?\<psi>x \<cdot>\<^sub>S \<tau> a)) (Hom.set (a, a))
                               = restrict (F.FUN (\<psi> (b, a) x) o \<tau>.FUN a) (Hom.set (a, a))"
              proof -
                have "S.arr (F ?\<psi>x \<cdot>\<^sub>S \<tau> a) \<and>
                      F ?\<psi>x \<cdot>\<^sub>S \<tau> a = S.mkArr (Hom.set (a, a)) (F.SET b) (F.FUN ?\<psi>x o \<tau>.FUN a)"
                proof
                  show 1: "S.seq (F ?\<psi>x) (\<tau> a)"
                    using \<psi>x ide_a \<tau>.preserves_cod F.preserves_dom
                    by (elim C.in_homE, auto)
                  show "F ?\<psi>x \<cdot>\<^sub>S \<tau> a = S.mkArr (Hom.set (a, a)) (F.SET b) (F.FUN ?\<psi>x o \<tau>.FUN a)"
                  proof -
                    have "\<tau> a = S.mkArr (Hom.set (a, a)) (F.SET a) (\<tau>.FUN a)"
                      using ide_a 1 S.mkArr_Fun [of "\<tau> a"] Hom.set_map by auto
                    moreover have "F ?\<psi>x = S.mkArr (F.SET a) (F.SET b) (F.FUN ?\<psi>x)"
                      using x \<psi>x 1 S.mkArr_Fun [of "F ?\<psi>x"] by fastforce
                    ultimately show ?thesis
                      using 1 S.comp_mkArr [of "Hom.set (a, a)" "F.SET a" "\<tau>.FUN a"
                                               "F.SET b" "F.FUN ?\<psi>x"]
                      by (elim S.seqE, auto)
                  qed
                qed
                thus ?thesis by force
              qed
              thus "S.Fun (F (\<psi> (b, a) x) \<cdot>\<^sub>S \<tau> a) ?\<phi>a = F.FUN ?\<psi>x (\<tau>.FUN a ?\<phi>a)"
                 using ide_a \<phi>a restr_eqE [of "S.Fun (F ?\<psi>x \<cdot>\<^sub>S \<tau> a)"
                                              "Hom.set (a, a)" "F.FUN ?\<psi>x o \<tau>.FUN a"]
                 by simp
            qed
            finally show ?thesis by simp
          qed
        qed
      qed
      finally show ?thesis by auto
    qed

    text\<open>
      Consequently, if @{term \<tau>'} is any natural transformation from @{term "Y a"} to @{term F}
      that agrees with @{term \<tau>} at @{term a}, then @{term "\<tau>' = \<tau>"}.
\<close>

    lemma eqI:
    assumes "natural_transformation Cop.comp S (Y a) F \<tau>'" and "\<tau>' a = \<tau> a"
    shows "\<tau>' = \<tau>"
    proof (intro NaturalTransformation.eqI)
      interpret \<tau>': natural_transformation Cop.comp S \<open>Y a\<close> F \<tau>' using assms by auto
      interpret T': yoneda_lemma_fixed_\<tau> C S setp \<phi> F a \<tau>' ..
      show "natural_transformation Cop.comp S (Y a) F \<tau>" ..
      show "natural_transformation Cop.comp S (Y a) F \<tau>'" ..
      show "\<And>b. Cop.ide b \<Longrightarrow> \<tau>' b = \<tau> b"
        using assms(2) \<tau>_ide T'.\<tau>_ide by simp
    qed

  end

  context yoneda_lemma
  begin

    text\<open>
      One half of the Yoneda lemma:
      The mapping @{term \<T>} is an injection, with left inverse @{term \<E>},
      from the set @{term "F.SET a"} to the set of natural transformations from
      @{term "Y a"} to @{term F}.
\<close>

    lemma \<T>_is_injection:
    assumes "e \<in> F.SET a"
    shows "natural_transformation Cop.comp S (Y a) F (\<T> e)" and "\<E> (\<T> e) = e"
    proof -
      interpret yoneda_lemma_fixed_e C S setp \<phi> F a e
        using assms by (unfold_locales, auto)
      show "natural_transformation Cop.comp S (Y a) F (\<T> e)" ..
      show "\<E> (\<T> e) = e"
        unfolding \<E>_def
        using assms \<T>e_ide S.Fun_mkArr Hom.\<phi>_mapsto Hom.\<psi>_\<phi> ide_a
              F.preserves_ide S.Fun_ide restrict_apply C.ide_in_hom
        by (auto simp add: Pi_iff)
    qed

    lemma \<E>\<tau>_mapsto:
    assumes "natural_transformation Cop.comp S (Y a) F \<tau>"
    shows "\<E> \<tau> \<in> F.SET a"
    proof -
      interpret \<tau>: natural_transformation Cop.comp S \<open>Y a\<close> F \<tau>
        using assms by auto
      interpret yoneda_lemma_fixed_\<tau> C S setp \<phi> F a \<tau> ..
      show ?thesis
      proof (unfold \<E>_def)
        have "\<tau>.FUN a \<in> Hom.set (a, a) \<rightarrow> F.SET a"
        proof -
          have "S.arr (\<tau> a) \<and> S.Dom (\<tau> a) = Hom.set (a, a) \<and> S.Cod (\<tau> a) = F.SET a"
            using ide_a Hom.set_map by auto
          thus ?thesis
            using S.Fun_mapsto by blast
        qed
        thus "\<tau>.FUN a (\<phi> (a, a) a) \<in> F.SET a"
          using ide_a Hom.\<phi>_mapsto by fastforce
      qed
    qed

    text\<open>
      The other half of the Yoneda lemma:
      The mapping @{term \<T>} is a surjection, with right inverse @{term \<E>},
      taking natural transformations from @{term "Y a"} to @{term F}
      to elements of @{term "F.SET a"}.
\<close>

    lemma \<T>_is_surjection:
    assumes "natural_transformation Cop.comp S (Y a) F \<tau>"
    shows "\<T> (\<E> \<tau>) = \<tau>"
    proof -
      interpret natural_transformation Cop.comp S \<open>Y a\<close> F \<tau>
        using assms by auto
      interpret yoneda_lemma_fixed_\<tau> C S setp \<phi> F a \<tau> ..
      interpret yoneda_lemma_fixed_e C S setp \<phi> F a \<open>\<E> \<tau>\<close>
        using assms \<E>\<tau>_mapsto by unfold_locales auto
      show "\<T> (\<E> \<tau>) = \<tau>"
        using ide_a \<tau>_ide [of a] \<T>e_ide \<E>_def natural_transformation_\<T>e
        by (intro eqI) auto
    qed
     
    text\<open>
      The main result.
\<close>

    theorem yoneda_lemma:
    shows "bij_betw \<T> (F.SET a) {\<tau>. natural_transformation Cop.comp S (Y a) F \<tau>}"
      using \<E>\<tau>_mapsto \<T>_is_injection \<T>_is_surjection
      by (intro bij_betwI) auto

  end

  text\<open>
    We now consider the special case in which @{term F} is the contravariant
    functor @{term "Y a'"}.  Then for any @{term e} in \<open>Hom.set (a, a')\<close>
    we have @{term "\<T> e = Y (\<psi> (a, a') e)"}, and @{term \<T>} is a bijection from
    \<open>Hom.set (a, a')\<close> to the set of natural transformations from @{term "Y a"}
    to @{term "Y a'"}.  It then follows that that the Yoneda functor @{term Y}
    is a fully faithful functor from @{term C} to the functor category \<open>[Cop, S]\<close>.
\<close>

  locale yoneda_lemma_for_hom =
    yoneda_functor_fixed_object C S setp \<phi> a +
    Ya': yoneda_functor_fixed_object C S setp \<phi> a' +
    yoneda_lemma C S setp \<phi> "Y a'" a
  for C :: "'c comp" (infixr "\<cdot>" 55)
  and S :: "'s comp" (infixr "\<cdot>\<^sub>S" 55)
  and setp :: "'s set \<Rightarrow> bool"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and a :: 'c
  and a' :: 'c +
  assumes ide_a': "C.ide a'"
  begin

    text\<open>
      In case @{term F} is the functor @{term "Y a'"}, for any @{term "e \<in> Hom.set (a, a')"}
      the induced natural transformation @{term "\<T> e"} from @{term "Y a"} to @{term "Y a'"}
      is just @{term "Y (\<psi> (a, a') e)"}.
\<close>

    lemma app_\<T>_equals:
    assumes e: "e \<in> Hom.set (a, a')"
    shows "\<T> e = Y (\<psi> (a, a') e)"
    proof -
      let ?\<psi>e = "\<psi> (a, a') e"
      have \<psi>e: "\<guillemotleft>?\<psi>e : a \<rightarrow> a'\<guillemotright>" using ide_a ide_a' e Hom.\<psi>_mapsto by auto
      interpret Ye: natural_transformation Cop.comp S \<open>Y a\<close> \<open>Y a'\<close> \<open>Y ?\<psi>e\<close>
        using Y_arr_is_transformation [of ?\<psi>e] \<psi>e by (elim C.in_homE, auto)
      interpret yoneda_lemma_fixed_e C S setp \<phi> \<open>Y a'\<close> a e
        using ide_a ide_a' e Hom.set_map
        by (unfold_locales, simp_all)
      interpret yoneda_lemma_fixed_\<tau> C S setp \<phi> \<open>Y a'\<close> a \<open>\<T> e\<close> ..
      have "natural_transformation Cop.comp S (Y a) (Y a') (Y ?\<psi>e)" ..
      moreover have "natural_transformation Cop.comp S (Y a) (Y a') (\<T> e)" ..
      moreover have "\<T> e a = Y ?\<psi>e a"
      proof -
        have 1: "\<T> e a = S.mkArr (Hom.set (a, a)) (Ya'.SET a) (\<lambda>x. Ya'.FUN (\<psi> (a, a) x) e)"
          using ide_a \<T>\<^sub>o_def \<T>e_ide by simp
        also have
            "... = S.mkArr (Hom.set (a, a)) (Hom.set (a, a')) (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a))"
        proof (intro S.mkArr_eqI)
          show "S.arr (S.mkArr (Hom.set (a, a)) (Ya'.SET a) (\<lambda>x. Ya'.FUN (\<psi> (a, a) x) e))"
            using ide_a e 1 \<T>e.preserves_reflects_arr
            by (metis Cop.ide_char \<T>e_ide(1))
          show "Hom.set (a, a) = Hom.set (a, a)" ..
          show 2: "Ya'.SET a = Hom.set (a, a')"
            using ide_a ide_a' Y_simp Hom.set_map by simp
          show "\<And>x. x \<in> Hom.set (a, a) \<Longrightarrow>
                      Ya'.FUN (\<psi> (a, a) x) e = (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a)) x"
          proof -
            fix x
            assume x: "x \<in> Hom.set (a, a)"
            have \<psi>x: "\<guillemotleft>\<psi> (a, a) x : a \<rightarrow> a\<guillemotright>"
              using ide_a x Hom.\<psi>_mapsto [of a a] by auto
            have "S.arr (Y a' (\<psi> (a, a) x)) \<and>
                  Y a' (\<psi> (a, a) x) = S.mkArr (Hom.set (a, a')) (Hom.set (a, a'))
                                              (\<phi> (a, a') \<circ> Cop.comp (\<psi> (a, a) x) \<circ> \<psi> (a, a'))"
              using Y_ide_arr ide_a ide_a' \<psi>x by blast
            hence "Ya'.FUN (\<psi> (a, a) x) e = (\<phi> (a, a') \<circ> Cop.comp (\<psi> (a, a) x) \<circ> \<psi> (a, a')) e"
              using e 2 S.Fun_mkArr Ya'.preserves_reflects_arr [of "\<psi> (a, a) x"] by simp
            also have "... = (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a)) x" by simp
            finally show "Ya'.FUN (\<psi> (a, a) x) e = (\<phi> (a, a') o C ?\<psi>e o \<psi> (a, a)) x" by auto
          qed
        qed
        also have "... = Y ?\<psi>e a"
          using ide_a ide_a' Y_arr_ide \<psi>e by simp
        finally show "\<T> e a = Y ?\<psi>e a" by auto
      qed
      ultimately show ?thesis using eqI by auto
    qed

    lemma is_injective_on_homs:
    shows "inj_on map (C.hom a a')"
    proof (intro inj_onI)
      fix f f'
      assume f: "f \<in> C.hom a a'" and f': "f' \<in> C.hom a a'"
      assume eq: "map f = map f'"
      show "f = f'"
      proof -
        have "f = \<psi> (a, a') (\<E> (Y (\<psi> (a, a') (\<phi> (a, a') f))))"
          by (metis (no_types, lifting) C.comp_arr_dom C.ide_in_hom Hom.\<phi>_natural
              Hom.\<psi>_\<phi> \<E>_def category.in_homE f ide_a mem_Collect_eq
              Y_simp yoneda_functor_axioms yoneda_functor_def)
        also have "... = \<psi> (a, a') (\<E> (\<T> (\<phi> (a, a') f')))"
          using f f' eq Hom.\<phi>_mapsto [of a a'] ide_a Hom.\<psi>_\<phi> Y_def
                app_\<T>_equals [of "\<phi> (a, a') f'"]
          by fastforce
        also have "... = f'"
          by (metis C.ideD(1) Hom.\<phi>_mapsto Hom.\<psi>_\<phi> Hom.set_map PiE Y_simp
              \<T>_is_injection(2) f' ide_a ide_a' mem_Collect_eq)
        finally show ?thesis by auto
      qed
    qed

  end

  context yoneda_functor
  begin

    sublocale faithful_functor C Cop_S.comp map
    proof
      fix f :: 'c and f' :: 'c
      assume par: "C.par f f'" and ff': "map f = map f'"
      show "f = f'"
      proof -
        interpret Ya': yoneda_functor_fixed_object C S setp \<phi> \<open>C.cod f\<close>
          using par by (unfold_locales, auto)
        interpret yoneda_lemma_for_hom C S setp \<phi> \<open>C.dom f\<close> \<open>C.cod f\<close>
          using par by (unfold_locales, auto)
        show "f = f'"
          using par ff' is_injective_on_homs inj_on_def [of map "C.hom (C.dom f) (C.cod f)"]
          by force
      qed
    qed

    lemma is_faithful_functor:
    shows "faithful_functor C Cop_S.comp map"
      ..

    sublocale full_functor C Cop_S.comp map
    proof
      fix a :: 'c and a' :: 'c and t
      assume a: "C.ide a" and a': "C.ide a'"
      assume t: "\<guillemotleft>t : map a \<rightarrow>\<^sub>[\<^sub>C\<^sub>o\<^sub>p\<^sub>,\<^sub>S\<^sub>] map a'\<guillemotright>"
      show "\<exists>e. \<guillemotleft>e : a \<rightarrow> a'\<guillemotright> \<and> map e = t"
      proof
        interpret Ya': yoneda_functor_fixed_object C S setp \<phi> a'
          using a' by (unfold_locales, auto)
        interpret yoneda_lemma_for_hom C S setp \<phi> a a'
          using a a' by (unfold_locales, auto)
        have NT: "natural_transformation Cop.comp S (Y a) (Y a') (Cop_S.Map t)"
          using t a' Y_def Cop_S.Map_dom Cop_S.Map_cod Cop_S.dom_char Cop_S.cod_char
                Cop_S.in_homE Cop_S.arrE
          by metis
        hence 1: "\<E> (Cop_S.Map t) \<in> Hom.set (a, a')"
          using \<E>\<tau>_mapsto ide_a ide_a' Hom.set_map by simp
        moreover have "map (\<psi> (a, a') (\<E> (Cop_S.Map t))) = t"
        proof (intro Cop_S.arr_eqI)
          have 2: "\<guillemotleft>map (\<psi> (a, a') (\<E> (Cop_S.Map t))) : map a \<rightarrow>\<^sub>[\<^sub>C\<^sub>o\<^sub>p\<^sub>,\<^sub>S\<^sub>] map a'\<guillemotright>"
            using 1 ide_a ide_a' Hom.\<psi>_mapsto [of a a'] by blast
          show "Cop_S.arr t" using t by blast
          show "Cop_S.arr (map (\<psi> (a, a') (\<E> (Cop_S.Map t))))" using 2 by blast
          show 3: "Cop_S.Map (map (\<psi> (a, a') (\<E> (Cop_S.Map t)))) = Cop_S.Map t"
            using NT 1 Y_def \<T>_is_surjection app_\<T>_equals \<E>\<tau>_mapsto by metis
          show 4: "Cop_S.Dom (map (\<psi> (a, a') (\<E> (Cop_S.Map t)))) = Cop_S.Dom t"
            using t 2 functor_axioms Cop_S.Map_dom by (metis Cop_S.in_homE)
          show "Cop_S.Cod (map (\<psi> (a, a') (\<E> (Cop_S.Map t)))) = Cop_S.Cod t"
            using 2 3 4 t Cop_S.Map_cod by (metis Cop_S.in_homE)
        qed
        ultimately show "\<guillemotleft>\<psi> (a, a') (\<E> (Cop_S.Map t)) : a \<rightarrow> a'\<guillemotright> \<and>
                         map (\<psi> (a, a') (\<E> (Cop_S.Map t))) = t"
          using ide_a ide_a' Hom.\<psi>_mapsto by auto
      qed
    qed

    lemma is_full_functor:
    shows "full_functor C Cop_S.comp map"
      ..

    sublocale fully_faithful_functor C Cop_S.comp map ..

  end

end

