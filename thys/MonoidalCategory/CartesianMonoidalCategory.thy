(*  Title:       CartesianMonoidalCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Cartesian Monoidal Category"

theory CartesianMonoidalCategory
imports MonoidalCategory Category3.CartesianCategory
begin

section "Symmetric Monoidal Category"

  locale symmetric_monoidal_category =
    monoidal_category C T \<alpha> \<iota> +
    S: symmetry_functor C C +
    ToS: composite_functor CC.comp CC.comp C S.map T +
    \<sigma>: natural_isomorphism CC.comp C T ToS.map \<sigma>
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  and \<sigma> :: "'a * 'a \<Rightarrow> 'a" +
  assumes sym_inverse: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> inverse_arrows (\<sigma> (a, b)) (\<sigma> (b, a))"
  and unitor_coherence: "ide a \<Longrightarrow> \<l>[a] \<cdot> \<sigma> (a, \<I>) = \<r>[a]"
  and assoc_coherence: "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow>
                          \<alpha> (b, c, a) \<cdot> \<sigma> (a, b \<otimes> c) \<cdot> \<alpha> (a, b, c)
                             = (b \<otimes> \<sigma> (a, c)) \<cdot> \<alpha> (b, a, c) \<cdot> (\<sigma> (a, b) \<otimes> c)"
  begin

    abbreviation sym                  ("\<s>[_, _]")
    where "sym a b \<equiv> \<sigma> (a, b)"

  end

  locale elementary_symmetric_monoidal_category =
    elementary_monoidal_category C tensor unity lunit runit assoc
  for C :: "'a comp"                  (infixr "\<cdot>" 55)
  and tensor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<otimes>" 53)
  and unity :: 'a                      ("\<I>")
  and lunit :: "'a \<Rightarrow> 'a"              ("\<l>[_]")
  and runit :: "'a \<Rightarrow> 'a"              ("\<r>[_]")
  and assoc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]")
  and sym :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"          ("\<s>[_, _]") +
  assumes sym_in_hom: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> \<guillemotleft>\<s>[a, b] : a \<otimes> b \<rightarrow> b \<otimes> a\<guillemotright>"
  and sym_naturality: "\<lbrakk> arr f; arr g \<rbrakk> \<Longrightarrow> \<s>[cod f, cod g] \<cdot> (f \<otimes> g) = (g \<otimes> f) \<cdot> \<s>[dom f, dom g]"
  and sym_inverse: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> inverse_arrows \<s>[a, b] \<s>[b, a]"
  and unitor_coherence: "ide a \<Longrightarrow> \<l>[a] \<cdot> \<s>[a, \<I>] = \<r>[a]"
  and assoc_coherence: "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow>
                          \<a>[b, c, a] \<cdot> \<s>[a, b \<otimes> c] \<cdot> \<a>[a, b, c]
                             = (b \<otimes> \<s>[a, c]) \<cdot> \<a>[b, a, c] \<cdot> (\<s>[a, b] \<otimes> c)"
  begin

    lemma sym_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr \<s>[a, b]"
    and "dom \<s>[a, b] = a \<otimes> b"
    and "cod \<s>[a, b] = b \<otimes> a"
      using assms sym_in_hom by auto

    interpretation CC: product_category C C ..
    sublocale MC: monoidal_category C T \<alpha> \<iota>
      using induces_monoidal_category by simp

    interpretation S: symmetry_functor C C ..
    interpretation ToS: composite_functor CC.comp CC.comp C S.map T ..

    definition \<sigma> :: "'a * 'a \<Rightarrow> 'a"
    where "\<sigma> f \<equiv> if CC.arr f then \<s>[cod (fst f), cod (snd f)] \<cdot> (fst f \<otimes> snd f) else null"

    interpretation \<sigma>: natural_isomorphism CC.comp C T ToS.map \<sigma>
    proof -
      interpret \<sigma>: transformation_by_components CC.comp C T ToS.map "\<lambda>a. \<s>[fst a, snd a]"
        using sym_in_hom sym_naturality
        by unfold_locales auto
      interpret \<sigma>: natural_isomorphism CC.comp C T ToS.map \<sigma>.map
        using sym_inverse \<sigma>.map_simp_ide
        by unfold_locales auto
      have "\<sigma> = \<sigma>.map"
        using \<sigma>_def \<sigma>.map_def sym_naturality by fastforce
      thus "natural_isomorphism CC.comp C T ToS.map \<sigma>"
        using \<sigma>.natural_isomorphism_axioms by presburger
    qed

    interpretation symmetric_monoidal_category C T \<alpha> \<iota> \<sigma>
    proof
      show "\<And>a b. \<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> inverse_arrows (\<sigma> (a, b)) (\<sigma> (b, a))"
        using sym_inverse comp_arr_dom \<sigma>_def by auto
      show "\<And>a. ide a \<Longrightarrow> MC.lunit a \<cdot> \<sigma> (a, MC.unity) = MC.runit a"
        using lunit_agreement \<I>_agreement sym_in_hom comp_arr_dom
              unitor_coherence runit_agreement \<sigma>_def
         by simp
      show "\<And>a b c. \<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow>
                      MC.assoc b c a \<cdot> \<sigma> (a, MC.tensor b c) \<cdot> MC.assoc a b c =
                      MC.tensor b (\<sigma> (a, c)) \<cdot> MC.assoc b a c \<cdot> MC.tensor (\<sigma> (a, b)) c"
        using sym_in_hom tensor_preserves_ide \<sigma>_def assoc_coherence
              comp_arr_dom comp_cod_arr
        by simp
    qed

    lemma induces_symmetric_monoidal_category\<^sub>C\<^sub>M\<^sub>C:
    shows "symmetric_monoidal_category C T \<alpha> \<iota> \<sigma>"
      ..

  end

  context symmetric_monoidal_category
  begin

    interpretation EMC: elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by auto

    lemma induces_elementary_symmetric_monoidal_category\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_symmetric_monoidal_category
             C tensor unity lunit runit assoc (\<lambda>a b. \<sigma> (a, b))"
      using \<sigma>.naturality unitor_coherence assoc_coherence sym_inverse
      by unfold_locales auto

  end

section "Cartesian Monoidal Category"

  text \<open>
    Here we define ``cartesian monoidal category'' by imposing additional properties,
    but not additional structure, on top of ``monoidal category''.  The additional properties
    are that the unit is a terminal object and that the tensor is a categorical product,
    with projections defined in terms of unitors, terminators, and tensor.  It then follows
    that the associators are induced by the product structure.
  \<close>

  locale cartesian_monoidal_category =
    monoidal_category C T \<alpha> \<iota>
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a +
  assumes terminal_unity: "terminal \<I>"
  and tensor_is_product:
        "\<lbrakk>ide a; ide b; \<guillemotleft>t\<^sub>a : a \<rightarrow> \<I>\<guillemotright>; \<guillemotleft>t\<^sub>b : b \<rightarrow> \<I>\<guillemotright>\<rbrakk> \<Longrightarrow>
            has_as_binary_product a b (\<r>[a] \<cdot> (a \<otimes> t\<^sub>b)) (\<l>[b] \<cdot> (t\<^sub>a \<otimes> b))"
  begin

    sublocale category_with_terminal_object
      using terminal_unity by unfold_locales blast

    lemma is_category_with_terminal_object:
    shows "category_with_terminal_object C"
      ..

    definition the_trm  ("\<t>[_]")
    where "the_trm \<equiv> \<lambda>f. THE t. \<guillemotleft>t : dom f \<rightarrow> \<I>\<guillemotright>"

    lemma trm_in_hom [intro]:
    assumes "ide a"
    shows "\<guillemotleft>\<t>[a] : a \<rightarrow> \<I>\<guillemotright>"
      unfolding the_trm_def
      using assms theI [of "\<lambda>t. \<guillemotleft>t : dom a \<rightarrow> \<I>\<guillemotright>"] terminal_unity terminal_arr_unique
      by (metis ideD(2) terminalE)

    lemma trm_simps [simp]:
    assumes "ide a"
    shows "arr \<t>[a]" and "dom \<t>[a] = a" and "cod \<t>[a] = \<I>"
      using assms trm_in_hom by auto

    interpretation elementary_category_with_terminal_object C \<I> the_trm
    proof
      show "ide \<I>"
        using ide_unity by blast
      fix a
      show "ide a \<Longrightarrow> \<guillemotleft>the_trm a : a \<rightarrow> \<I>\<guillemotright>"
        using the_trm_def theI [of "\<lambda>t. \<guillemotleft>t : dom a \<rightarrow> \<I>\<guillemotright>"] terminalE terminal_unity by auto
      thus "\<And>f. \<lbrakk>ide a; \<guillemotleft>f : a \<rightarrow> \<I>\<guillemotright>\<rbrakk> \<Longrightarrow> f = the_trm a"
        using theI [of "\<lambda>t. \<guillemotleft>t : dom a \<rightarrow> \<I>\<guillemotright>"]
        by (metis terminalE terminal_unity)
    qed

    lemma extends_to_elementary_category_with_terminal_object\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_category_with_terminal_object C \<I> the_trm"
      ..

    definition pr\<^sub>0  ("\<pp>\<^sub>0[_, _]")
    where "pr\<^sub>0 a b \<equiv> \<l>[b] \<cdot> (\<t>[a] \<otimes> b)"

    definition pr\<^sub>1  ("\<pp>\<^sub>1[_, _]")
    where "pr\<^sub>1 a b \<equiv> \<r>[a] \<cdot> (a \<otimes> \<t>[b])"

    (* TODO: Must use qualified name to avoid clash between definitions of assoc. *)
    sublocale ECC: elementary_category_with_binary_products C pr\<^sub>0 pr\<^sub>1
    proof
      fix f g
      assume fg: "span f g"
      have "has_as_binary_product (cod f) (cod g) \<pp>\<^sub>1[cod f, cod g] \<pp>\<^sub>0[cod f, cod g]"
        using fg tensor_is_product pr\<^sub>0_def pr\<^sub>1_def by auto
      thus "\<exists>!l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g"
        using fg
        by (elim has_as_binary_productE) blast
    qed (unfold pr\<^sub>0_def pr\<^sub>1_def, auto)

    lemma induces_elementary_category_with_binary_products\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_category_with_binary_products C pr\<^sub>0 pr\<^sub>1"
      ..

    lemma is_category_with_binary_products:
    shows "category_with_binary_products C"
      using ECC.is_category_with_binary_products by blast

    sublocale category_with_binary_products C
      using is_category_with_binary_products by blast

    (* TODO: Here the clash is on lunit and runit. *)
    sublocale ECC: elementary_cartesian_category C pr\<^sub>0 pr\<^sub>1 \<I> the_trm ..

    lemma extends_to_elementary_cartesian_category\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_cartesian_category C pr\<^sub>0 pr\<^sub>1 \<I> the_trm"
      ..

    lemma is_cartesian_category:
    shows "cartesian_category C"
      using ECC.is_cartesian_category by simp

    sublocale cartesian_category C
      using is_cartesian_category by blast

    abbreviation dup  ("\<d>[_]")
    where "dup \<equiv> ECC.dup"

    abbreviation tuple  ("\<langle>_, _\<rangle>")
    where "\<langle>f, g\<rangle> \<equiv> ECC.tuple f g"

    lemma prod_eq_tensor:
    shows "ECC.prod = tensor"
    proof -
      have "\<And>f g. ECC.prod f g = f \<otimes> g"
      proof -
        fix f g
        show "ECC.prod f g = f \<otimes> g"
        proof (cases "arr f \<and> arr g")
          show "\<not> (arr f \<and> arr g) \<Longrightarrow> ?thesis"
            by (metis CC.arrE ECC.prod_def ECC.tuple_ext T.is_extensional fst_conv seqE snd_conv)
          assume 0: "arr f \<and> arr g"
          have 1: "span (f \<cdot> \<pp>\<^sub>1[dom f, dom g]) (g \<cdot> \<pp>\<^sub>0[dom f, dom g])"
            using 0 by simp
          have "\<pp>\<^sub>1[cod f, cod g] \<cdot> ECC.prod f g = \<pp>\<^sub>1[cod f, cod g] \<cdot> (f \<otimes> g)"
          proof -
            have "\<pp>\<^sub>1[cod f, cod g] \<cdot> ECC.prod f g =
                  \<pp>\<^sub>1[cod f, cod g] \<cdot> \<langle>f \<cdot> \<pp>\<^sub>1[dom f, dom g], g \<cdot> \<pp>\<^sub>0[dom f, dom g]\<rangle>"
              unfolding ECC.prod_def by simp
            also have "... = f \<cdot> \<pp>\<^sub>1[dom f, dom g]"
              using 0 1 ECC.pr_tuple(1) by fastforce
            also have "... = (f \<cdot> \<r>[dom f]) \<cdot> (dom f \<otimes> \<t>[dom g])"
              unfolding pr\<^sub>1_def
              using comp_assoc by simp
            also have "... = (\<r>[cod f] \<cdot> (f \<otimes> \<I>)) \<cdot> (dom f \<otimes> \<t>[dom g])"
              using 0 runit_naturality by auto
            also have "... = \<r>[cod f] \<cdot> (f \<otimes> \<I>) \<cdot> (dom f \<otimes> \<t>[dom g])"
              using comp_assoc by simp
            also have "... = \<r>[cod f] \<cdot> (cod f \<otimes> \<t>[cod g]) \<cdot> (f \<otimes> g)"
              using 0 interchange comp_arr_dom comp_cod_arr trm_naturality trm_simps(1)
              by force
            also have "... = (\<r>[cod f] \<cdot> (cod f \<otimes> \<t>[cod g])) \<cdot> (f \<otimes> g)"
              using comp_assoc by simp
            also have "... = \<pp>\<^sub>1[cod f, cod g] \<cdot> (f \<otimes> g)"
              unfolding pr\<^sub>1_def by simp
            finally show ?thesis by blast
          qed
          moreover have "\<pp>\<^sub>0[cod f, cod g] \<cdot> ECC.prod f g = \<pp>\<^sub>0[cod f, cod g] \<cdot> (f \<otimes> g)"
          proof -
            have "\<pp>\<^sub>0[cod f, cod g] \<cdot> ECC.prod f g =
                  \<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f \<cdot> \<pp>\<^sub>1[dom f, dom g], g \<cdot> \<pp>\<^sub>0[dom f, dom g]\<rangle>"
              unfolding ECC.prod_def by simp
            also have "... = g \<cdot> \<pp>\<^sub>0[dom f, dom g]"
              using 0 1 ECC.pr_tuple by fastforce
            also have "... = (g \<cdot> \<l>[dom g]) \<cdot> (\<t>[dom f] \<otimes> dom g)"
              unfolding pr\<^sub>0_def
              using comp_assoc by simp
            also have "... = (\<l>[cod g] \<cdot> (\<I> \<otimes> g)) \<cdot> (\<t>[dom f] \<otimes> dom g)"
              using 0 lunit_naturality by auto
            also have "... = \<l>[cod g] \<cdot> (\<I> \<otimes> g) \<cdot> (\<t>[dom f] \<otimes> dom g)"
              using comp_assoc by simp
            also have "... = \<l>[cod g] \<cdot> (\<t>[cod f] \<otimes> cod g) \<cdot> (f \<otimes> g)"
              using 0 interchange comp_arr_dom comp_cod_arr trm_naturality trm_simps(1)
              by force
            also have "... = (\<l>[cod g] \<cdot> (\<t>[cod f] \<otimes> cod g)) \<cdot> (f \<otimes> g)"
              using comp_assoc by simp
            also have "... = \<pp>\<^sub>0[cod f, cod g] \<cdot> (f \<otimes> g)"
              unfolding pr\<^sub>0_def by simp
            finally show ?thesis by blast
          qed
          ultimately show ?thesis
            by (metis 0 1 ECC.pr_naturality(1-2) ECC.tuple_pr_arr ide_cod)
        qed
      qed
      thus ?thesis by blast
    qed

    lemma Prod_eq_T:
    shows "ECC.Prod = T"
    proof
      fix fg
      show "ECC.Prod fg = T fg"
        using prod_eq_tensor
        by (cases "CC.arr fg") auto
    qed

  text \<open>
     It is somewhat amazing that once the tensor product has been assumed to be a
     categorical product with the indicated projections, then the associators are
     forced to be those induced by the categorical product.
  \<close>

    lemma pr_assoc:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = \<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]"
    and "\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = \<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]"
    and "\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = \<pp>\<^sub>0[a \<otimes> b, c]"
    proof -
      show "\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = \<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]"
      proof -
        have "\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = (\<r>[a] \<cdot> (a \<otimes> \<iota> \<cdot> (\<t>[b] \<otimes> \<t>[c]))) \<cdot> \<a>[a, b, c]"
          by (metis ECC.trm_tensor ECC.unit_eq_trm arr_cod_iff_arr assms(2-3) comp_cod_arr
              dom_lunit ide_unity pr\<^sub>1_def prod_eq_tensor trm_naturality trm_one trm_simps(1)
              unitor_coincidence(1))
        also have "... = (\<r>[a] \<cdot> (a \<otimes> \<iota>) \<cdot> (a \<otimes> \<t>[b] \<otimes> \<t>[c])) \<cdot> \<a>[a, b, c]"
          using assms interchange unit_in_hom_ax by auto
        also have "... = \<r>[a] \<cdot> (a \<otimes> \<iota>) \<cdot> (a \<otimes> \<t>[b] \<otimes> \<t>[c]) \<cdot> \<a>[a, b, c]"
          using comp_assoc by simp
        also have "... = \<r>[a] \<cdot> (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>] \<cdot> ((a \<otimes> \<t>[b]) \<otimes> \<t>[c])"
          using assms assoc_naturality [of a "\<t>[b]" "\<t>[c]"] by force
        also have "... = \<r>[a] \<cdot> (\<r>[a] \<otimes> \<I>) \<cdot> ((a \<otimes> \<t>[b]) \<otimes> \<t>[c])"
          using assms runit_char comp_assoc by simp
        also have "... = \<r>[a] \<cdot> (\<pp>\<^sub>1[a, b] \<otimes> \<t>[c])"
          using assms comp_arr_dom comp_cod_arr interchange [of "\<r>[a]" "a \<otimes> \<t>[b]" \<I> "\<t>[c]"]
          by (metis ECC.pr_simps(4) pr\<^sub>1_def trm_simps(1) trm_simps(3))
        also have "... = \<r>[a] \<cdot> (\<pp>\<^sub>1[a, b] \<cdot> (a \<otimes> b) \<otimes> \<I> \<cdot> \<t>[c])"
          using assms comp_arr_dom comp_cod_arr
          by (metis (no_types, lifting) ECC.pr_simps(4-5) prod_eq_tensor trm_simps(1,3))
        also have "... = \<r>[a] \<cdot> (\<pp>\<^sub>1[a, b] \<otimes> \<I>) \<cdot> ((a \<otimes> b) \<otimes> \<t>[c])"
          using assms interchange [of "\<pp>\<^sub>1[a, b]" "a \<otimes> b" \<I> " \<t>[c]"]
          by (metis (no_types, lifting) ECC.pr_simps(4-5) Prod_eq_T comp_arr_dom comp_cod_arr
              fst_conv snd_conv trm_simps(1,3))
        also have "... = (\<r>[a] \<cdot> (\<pp>\<^sub>1[a, b] \<otimes> \<I>)) \<cdot> ((a \<otimes> b) \<otimes> \<t>[c])"
          using comp_assoc by simp
        also have "... = (\<pp>\<^sub>1[a, b] \<cdot> \<r>[a \<otimes> b]) \<cdot> ((a \<otimes> b) \<otimes> \<t>[c])"
          using assms runit_naturality
          by (metis (no_types, lifting) ECC.cod_pr1 ECC.pr_simps(4,5) prod_eq_tensor)
        also have "... = \<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]"
          using pr\<^sub>1_def comp_assoc by simp
        finally show ?thesis by blast
      qed
      show "\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = \<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]"
      proof -
        have "\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c] =
              \<r>[b] \<cdot> (b \<otimes> \<t>[c]) \<cdot> \<l>[b \<otimes> c] \<cdot> \<a>[\<I>, b, c] \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms pr\<^sub>0_def pr\<^sub>1_def assoc_naturality [of "\<t>[a]" b c] comp_assoc by auto
        also have "... = \<r>[b] \<cdot> ((b \<otimes> \<t>[c]) \<cdot> \<l>[b \<otimes> c]) \<cdot> \<a>[\<I>, b, c] \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using comp_assoc by simp
        also have "... = \<r>[b] \<cdot> (\<l>[b \<otimes> \<I>] \<cdot> (\<I> \<otimes> b \<otimes> \<t>[c])) \<cdot> \<a>[\<I>, b, c] \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms lunit_naturality [of "b \<otimes> \<t>[c]"] by auto
        also have "... = \<r>[b] \<cdot> \<l>[b \<otimes> \<I>] \<cdot> ((\<I> \<otimes> b \<otimes> \<t>[c]) \<cdot> \<a>[\<I>, b, c]) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using comp_assoc by simp
        also have "... = \<r>[b] \<cdot> \<l>[b \<otimes> \<I>] \<cdot> (\<a>[\<I>, b, \<I>] \<cdot> ((\<I> \<otimes> b) \<otimes> \<t>[c])) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms assoc_naturality [of \<I> b "\<t>[c]"] by auto
        also have "... = \<r>[b] \<cdot> (\<l>[b] \<otimes> \<I>) \<cdot> ((\<I> \<otimes> b) \<otimes> \<t>[c]) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms lunit_tensor [of b \<I>] comp_assoc
          by (metis ide_unity lunit_tensor')
        also have "... = \<r>[b] \<cdot> (\<l>[b] \<otimes> \<I>) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> \<I>) \<cdot> ((a \<otimes> b) \<otimes> \<t>[c])"
          using assms comp_arr_dom comp_cod_arr interchange by simp
        also have "... = (\<r>[b] \<cdot> (\<pp>\<^sub>0[a, b] \<otimes> \<I>)) \<cdot> ((a \<otimes> b) \<otimes> \<t>[c])"
          using assms pr\<^sub>0_def ECC.pr_simps(1) R.preserves_comp comp_assoc by simp
        also have "... = (\<pp>\<^sub>0[a, b] \<cdot> \<r>[a \<otimes> b]) \<cdot> ((a \<otimes> b) \<otimes> \<t>[c])"
          using assms pr\<^sub>0_def runit_naturality [of "\<pp>\<^sub>0[a, b]"] comp_assoc by simp
        also have "... = \<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]"
          using pr\<^sub>0_def pr\<^sub>1_def comp_assoc by simp
        finally show ?thesis by blast
      qed
      show "\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = \<pp>\<^sub>0[a \<otimes> b, c]"
      proof -
        have "\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c] =
              \<l>[c] \<cdot> (\<t>[b] \<otimes> c) \<cdot> \<l>[b \<otimes> c] \<cdot> (\<t>[a] \<otimes> b \<otimes> c) \<cdot> \<a>[a, b, c]"
          using pr\<^sub>0_def comp_assoc by simp
        also have "... = \<l>[c] \<cdot> ((\<t>[b] \<otimes> c) \<cdot> \<l>[b \<otimes> c]) \<cdot> \<a>[\<I>, b, c] \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms assoc_naturality [of "\<t>[a]" b c] comp_assoc by simp
        also have "... = \<l>[c] \<cdot> (\<l>[\<I> \<otimes> c] \<cdot> (\<I> \<otimes> \<t>[b] \<otimes> c)) \<cdot> \<a>[\<I>, b, c] \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms lunit_naturality [of "\<t>[b] \<otimes> c"] by simp
        also have "... = \<l>[c] \<cdot> \<l>[\<I> \<otimes> c] \<cdot> (\<a>[\<I>, \<I>, c] \<cdot> ((\<I> \<otimes> \<t>[b]) \<otimes> c)) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms assoc_naturality [of \<I> "\<t>[b]" c] comp_assoc by simp
        also have "... = \<l>[c] \<cdot> (\<l>[\<I> \<otimes> c] \<cdot> \<a>[\<I>, \<I>, c]) \<cdot> ((\<I> \<otimes> \<t>[b]) \<otimes> c) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using comp_assoc by simp
        also have "... = \<l>[c] \<cdot> (\<iota> \<otimes> c) \<cdot> ((\<I> \<otimes> \<t>[b]) \<otimes> c) \<cdot> ((\<t>[a] \<otimes> b) \<otimes> c)"
          using assms lunit_tensor' unitor_coincidence(1) by simp
        also have "... = \<l>[c] \<cdot> (\<iota> \<otimes> c) \<cdot> ((\<I> \<otimes> \<t>[b]) \<cdot> (\<t>[a] \<otimes> b) \<otimes> c)"
          using assms comp_arr_dom comp_cod_arr
          by (metis arr_tensor ide_char interchange trm_simps(1-3))
        also have "... = \<l>[c] \<cdot> (\<iota> \<otimes> c) \<cdot> ((\<t>[a] \<otimes> \<t>[b]) \<otimes> c)"
          using assms comp_arr_dom comp_cod_arr interchange by simp
        also have "... = \<l>[c] \<cdot> (\<iota> \<cdot> (\<t>[a] \<otimes> \<t>[b]) \<otimes> c)"
          using assms interchange unit_in_hom_ax by auto
        also have "... = \<pp>\<^sub>0[a \<otimes> b, c]"
          using assms pr\<^sub>0_def ECC.trm_tensor category.comp_arr_dom category_axioms prod_eq_tensor
                trm_one unit_in_hom_ax unitor_coincidence(1)
          by fastforce
        finally show ?thesis by blast
      qed
    qed

    lemma assoc_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "ECC.assoc a b c = \<a>[a, b, c]"
    proof -
      have "\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> ECC.assoc a b c = \<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<a>[a, b, c]"
        using assms ECC.pr_assoc(3) pr_assoc(1) prod_eq_tensor by force
      moreover have "\<pp>\<^sub>0[a, b \<otimes> c] \<cdot> ECC.assoc a b c = \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c]"
      proof -
        have "\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> ECC.assoc a b c = \<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c]"
          using assms ECC.pr_assoc(2) pr_assoc(2) prod_eq_tensor by force
        moreover have "\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> ECC.assoc a b c =
                       \<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c]"
          using assms prod_eq_tensor ECC.pr_assoc(1) pr_assoc(3) by force
        ultimately show ?thesis
          using assms prod_eq_tensor
                ECC.pr_joint_monic
                  [of b c "\<pp>\<^sub>0[a, b \<otimes> c] \<cdot> ECC.assoc a b c " "\<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<a>[a, b, c]"]
          by fastforce
      qed
      ultimately show ?thesis
        using assms prod_eq_tensor
              ECC.pr_joint_monic [of a "b \<otimes> c" "ECC.assoc a b c" "\<a>[a, b, c]"]
        by fastforce
    qed

    lemma lunit_eq:
    assumes "ide a"
    shows "\<pp>\<^sub>0[\<I>, a] = \<l>[a]"
      by (simp add: assms comp_arr_dom pr\<^sub>0_def trm_one)

    lemma runit_eq:
    assumes "ide a"
    shows "\<pp>\<^sub>1[a, \<I>] = \<r>[a]"
      by (simp add: assms comp_arr_dom pr\<^sub>1_def trm_one)

    interpretation S: symmetry_functor C C ..
    interpretation ToS: composite_functor CC.comp CC.comp C S.map T ..

    interpretation \<sigma>: natural_transformation CC.comp C T ToS.map ECC.\<sigma>
    proof -
      have "ECC.Prod' = ToS.map"
      proof
        fix fg
        show "ECC.Prod' fg = ToS.map fg"
          using prod_eq_tensor
          by (metis CC.arr_char ECC.prod_def ECC.tuple_ext S.map_def ToS.is_extensional o_apply seqE)
      qed
      thus "natural_transformation CC.comp C T ToS.map ECC.\<sigma>"
        using Prod_eq_T ECC.\<sigma>_is_natural_transformation by simp
    qed

    interpretation \<sigma>: natural_isomorphism CC.comp C T ToS.map ECC.\<sigma>
      using ECC.sym_inverse_arrows comp_arr_dom
      by unfold_locales auto

    sublocale SMC: symmetric_monoidal_category C T \<alpha> \<iota> ECC.\<sigma>
    proof
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> inverse_arrows (ECC.\<sigma> (a, b)) (ECC.\<sigma> (b, a))"
        using comp_arr_dom by auto
      show "\<And>a. ide a \<Longrightarrow> \<l>[a] \<cdot> ECC.\<sigma> (a, \<I>) = \<r>[a]"
        using \<sigma>.naturality prod_eq_tensor
        by (metis (no_types, lifting) CC.arr_char ECC.prj_sym(1) R.preserves_ide
            \<ll>_ide_simp \<rho>_ide_simp \<sigma>.preserves_reflects_arr comp_arr_ide fst_conv
            ideD(1) ideD(3) ide_unity lunit_naturality pr\<^sub>0_def pr\<^sub>1_def runit_naturality
            snd_conv trm_one)
      show "\<And>a b c. \<lbrakk>ide a; ide b; ide c\<rbrakk> \<Longrightarrow>
                       \<a>[b, c, a] \<cdot> ECC.\<sigma> (a, b \<otimes> c) \<cdot> \<a>[a, b, c] =
                       (b \<otimes> ECC.\<sigma> (a, c)) \<cdot> \<a>[b, a, c] \<cdot> (ECC.\<sigma> (a, b) \<otimes> c)"
      proof -
        fix a b c
        assume a: "ide a" and b: "ide b" and c: "ide c"
        show "\<a>[b, c, a] \<cdot> ECC.\<sigma> (a, b \<otimes> c) \<cdot> \<a>[a, b, c] =
              (b \<otimes> ECC.\<sigma> (a, c)) \<cdot> \<a>[b, a, c] \<cdot> (ECC.\<sigma> (a, b) \<otimes> c)"
          using a b c prod_eq_tensor assoc_agreement comp_arr_dom ECC.sym_assoc_coherence [of a b c]
          by simp
        qed
      qed

  end

section "Elementary Cartesian Monoidal Category"

  locale elementary_cartesian_monoidal_category =
    elementary_monoidal_category C tensor unity lunit runit assoc
  for C :: "'a comp"                   (infixr "\<cdot>" 55)
  and tensor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<otimes>" 53)
  and unity :: 'a                      ("\<I>")
  and lunit :: "'a \<Rightarrow> 'a"              ("\<l>[_]")
  and runit :: "'a \<Rightarrow> 'a"              ("\<r>[_]")
  and assoc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]")
  and trm :: "'a \<Rightarrow> 'a"                ("\<t>[_]")
  and dup :: "'a \<Rightarrow> 'a"                ("\<d>[_]") +
  assumes trm_in_hom: "ide a \<Longrightarrow> \<guillemotleft>\<t>[a] : a \<rightarrow> \<I>\<guillemotright>"
  and trm_unity: "\<t>[\<I>] = \<I>"
  and trm_naturality: "arr f \<Longrightarrow> \<t>[cod f] \<cdot> f = \<t>[dom f]"
  and dup_in_hom [intro]: "ide a \<Longrightarrow> \<guillemotleft>\<d>[a] : a \<rightarrow> a \<otimes> a\<guillemotright>"
  and dup_naturality: "arr f \<Longrightarrow> \<d>[cod f] \<cdot> f = (f \<otimes> f) \<cdot> \<d>[dom f]"
  and prj0_dup: "ide a \<Longrightarrow> \<r>[a] \<cdot> (a \<otimes> \<t>[a]) \<cdot> \<d>[a] = a"
  and prj1_dup: "ide a \<Longrightarrow> \<l>[a] \<cdot> (\<t>[a] \<otimes> a) \<cdot> \<d>[a] = a"
  and tuple_prj: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> (\<r>[a] \<cdot> (a \<otimes> \<t>[b]) \<otimes> \<l>[b] \<cdot> (\<t>[a] \<otimes> b)) \<cdot> \<d>[a \<otimes> b] = a \<otimes> b"

  context cartesian_monoidal_category
  begin

    interpretation elementary_category_with_terminal_object C \<I> the_trm
      using extends_to_elementary_category_with_terminal_object\<^sub>C\<^sub>M\<^sub>C by blast

    interpretation elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by simp

    interpretation elementary_cartesian_monoidal_category C
                     tensor unity lunit runit assoc the_trm dup
      using ECC.trm_one ECC.trm_naturality ECC.tuple_in_hom' prod_eq_tensor ECC.dup_naturality in_homI
            ECC.comp_runit_term_dup runit_eq ECC.comp_lunit_term_dup lunit_eq ECC.tuple_expansion
            comp_cod_arr
      apply unfold_locales
             apply auto
    proof -
      fix a b
      assume a: "ide a" and b: "ide b"
      show "(\<r>[a] \<cdot> (a \<otimes> \<t>[b]) \<otimes> \<l>[b] \<cdot> (\<t>[a] \<otimes> b)) \<cdot> \<d>[a \<otimes> b] = a \<otimes> b"
        using a b ECC.tuple_pr pr\<^sub>0_def pr\<^sub>1_def prod_eq_tensor
        by (metis ECC.pr_simps(5) ECC.span_pr ECC.tuple_expansion)
    qed

    lemma induces_elementary_cartesian_monoidal_category\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_cartesian_monoidal_category C tensor \<I> lunit runit assoc the_trm dup"
      ..

  end

  context elementary_cartesian_monoidal_category
  begin

    lemma trm_simps [simp]:
    assumes "ide a"
    shows "arr \<t>[a]" and "dom \<t>[a] = a" and "cod \<t>[a] = \<I>"
      using assms trm_in_hom by auto

    lemma dup_simps [simp]:
    assumes "ide a"
    shows "arr \<d>[a]" and "dom \<d>[a] = a" and "cod \<d>[a] = a \<otimes> a"
      using assms dup_in_hom by auto

    interpretation elementary_category_with_terminal_object C \<I> trm
      apply unfold_locales
        apply auto
      by (metis comp_cod_arr in_homE trm_naturality trm_unity)

    lemma is_elementary_category_with_terminal_object:
    shows "elementary_category_with_terminal_object C \<I> trm"
      ..

    (* Must use a qualified name here because locale parameters shadow lunit, runit, etc. *)
    interpretation MC: monoidal_category C T \<alpha> \<iota>
      using induces_monoidal_category by auto

    interpretation ECBP: elementary_category_with_binary_products C
                           \<open>\<lambda>a b. \<l>[b] \<cdot> (\<t>[a] \<otimes> b)\<close> \<open>\<lambda>a b. \<r>[a] \<cdot> (a \<otimes> \<t>[b])\<close>
    proof -
      let ?pr\<^sub>0 = "\<lambda>a b. \<l>[b] \<cdot> (\<t>[a] \<otimes> b)"
      let ?pr\<^sub>1 = "\<lambda>a b. \<r>[a] \<cdot> (a \<otimes> \<t>[b])"
      show "elementary_category_with_binary_products C ?pr\<^sub>0 ?pr\<^sub>1"
      proof
        fix a b
        assume a: "ide a" and b: "ide b"
        show 0: "cod (?pr\<^sub>0 a b) = b"
          by (metis a arr_tensor b cod_comp cod_tensor ide_char in_homE lunit_in_hom
              seqI trm_simps(1,3))
        show 1: "cod (?pr\<^sub>1 a b) = a"
          by (metis a arr_tensor b cod_comp cod_tensor ideD(1,3) in_homE runit_in_hom
              seqI trm_simps(1,3))
        show "span (?pr\<^sub>1 a b) (?pr\<^sub>0 a b)"
          by (metis 0 1 a arr_cod_iff_arr b dom_cod dom_comp dom_tensor ideD(1) trm_simps(1-2))
        next
        fix f g
        assume fg: "span f g"
        show "\<exists>!l. ?pr\<^sub>1 (cod f) (cod g) \<cdot> l = f \<and> ?pr\<^sub>0 (cod f) (cod g) \<cdot> l = g"
        proof
          show 1: "?pr\<^sub>1 (cod f) (cod g) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f] = f \<and>
                   ?pr\<^sub>0 (cod f) (cod g) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f] = g"
          proof
            show "?pr\<^sub>1 (cod f) (cod g) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f] = f"
            proof -
              have "?pr\<^sub>1 (cod f) (cod g) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f] =
                    MC.runit (cod f) \<cdot> (MC.tensor (cod f) \<t>[cod g] \<cdot> (f \<otimes> g)) \<cdot> \<d>[dom f]"
                by (simp add: fg comp_assoc runit_agreement)
              also have "... = MC.runit (cod f) \<cdot> (MC.tensor f \<I> \<cdot> (dom f \<otimes> \<t>[dom g])) \<cdot> \<d>[dom f]"
                using fg
                by (simp add: comp_arr_dom comp_cod_arr interchange trm_naturality)
              also have "... = (MC.runit (cod f) \<cdot> MC.tensor f \<I> ) \<cdot> (dom f \<otimes> \<t>[dom g]) \<cdot> \<d>[dom f]"
                using comp_assoc by simp
              also have "... = f \<cdot> ?pr\<^sub>1 (dom f) (dom g) \<cdot> \<d>[dom f]"
                using MC.runit_naturality \<I>_agreement fg comp_assoc runit_agreement by force
              also have "... = f"
                using fg comp_arr_dom comp_assoc prj0_dup runit_agreement by fastforce
              finally show ?thesis by blast
            qed
            show "?pr\<^sub>0 (cod f) (cod g) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f] = g"
            proof -
              have "?pr\<^sub>0 (cod f) (cod g) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f] =
                    MC.lunit (cod g) \<cdot> (MC.tensor \<t>[cod f] (cod g) \<cdot> (f \<otimes> g)) \<cdot> \<d>[dom f]"
                by (simp add: fg comp_assoc lunit_agreement)
              also have "... = MC.lunit (cod g) \<cdot> (MC.tensor \<I> g \<cdot> (\<t>[dom f] \<otimes> dom g)) \<cdot> \<d>[dom f]"
                using fg
                by (simp add: comp_arr_dom comp_cod_arr interchange trm_naturality)
              also have "... = (MC.lunit (cod g) \<cdot> MC.tensor \<I> g) \<cdot> (\<t>[dom f] \<otimes> dom g) \<cdot> \<d>[dom f]"
                using comp_assoc by simp
              also have "... = g \<cdot> ?pr\<^sub>0 (dom f) (dom g) \<cdot> \<d>[dom f]"
                using MC.lunit_naturality \<I>_agreement fg comp_assoc lunit_agreement by force
              also have "... = g"
                using fg comp_arr_dom comp_assoc prj1_dup lunit_agreement by fastforce
              finally show ?thesis by blast
            qed
          qed
          fix l
          assume l: "?pr\<^sub>1 (cod f) (cod g) \<cdot> l = f \<and> ?pr\<^sub>0 (cod f) (cod g) \<cdot> l = g"
          show "l = (f \<otimes> g) \<cdot> \<d>[dom f]"
          proof -
            have 2: "\<guillemotleft>l : dom f \<rightarrow> cod f \<otimes> cod g\<guillemotright>"
              by (metis 1 arr_iff_in_hom cod_comp cod_tensor dom_comp fg l seqE)
            have "l = ((?pr\<^sub>1 (cod f) (cod g) \<otimes> ?pr\<^sub>0 (cod f) (cod g)) \<cdot> \<d>[cod f \<otimes> cod g]) \<cdot> l"
              using fg 2 tuple_prj [of "cod f" "cod g"] lunit_agreement runit_agreement comp_cod_arr
              by auto
            also have "... = (?pr\<^sub>1 (cod f) (cod g) \<otimes> ?pr\<^sub>0 (cod f) (cod g)) \<cdot> \<d>[cod f \<otimes> cod g] \<cdot> l"
              using comp_assoc by simp
            also have "... = ((?pr\<^sub>1 (cod f) (cod g) \<otimes> ?pr\<^sub>0 (cod f) (cod g)) \<cdot> (l \<otimes> l)) \<cdot> \<d>[dom f]"
              using 2 dup_naturality [of l] comp_assoc by auto
            also have "... = (f \<otimes> g) \<cdot> \<d>[dom f]"
              using fg l interchange [of "?pr\<^sub>1 (cod f) (cod g)" l "?pr\<^sub>0 (cod f) (cod g)" l] by simp
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma induces_elementary_category_with_binary_products\<^sub>E\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_category_with_binary_products C
             (\<lambda>a b. \<l>[b] \<cdot> (\<t>[a] \<otimes> b)) (\<lambda>a b. \<r>[a] \<cdot> (a \<otimes> \<t>[b]))"
      ..

    sublocale cartesian_monoidal_category C T \<alpha> \<iota>
    proof
      show "terminal MC.unity"
        by (simp add: \<I>_agreement terminal_one)
      show "\<And>a b t\<^sub>a t\<^sub>b. \<lbrakk>ide a; ide b; \<guillemotleft>t\<^sub>a : a \<rightarrow> MC.unity\<guillemotright>; \<guillemotleft>t\<^sub>b : b \<rightarrow> MC.unity\<guillemotright>\<rbrakk> \<Longrightarrow>
                           has_as_binary_product a b
                             (MC.runit a \<cdot> MC.tensor a t\<^sub>b) (MC.lunit b \<cdot> MC.tensor t\<^sub>a b)"
        by (metis ECBP.has_as_binary_product T_simp \<I>_agreement arrI ideD(1)
            lunit_agreement runit_agreement trm_eqI)
    qed

    lemma induces_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>M\<^sub>C:
    shows "cartesian_monoidal_category C T \<alpha> \<iota>"
      ..

  end

  (* TODO: This definition of "diagonal_functor" conflicts with the one in Category3.Limit. *)
  locale diagonal_functor =
    C: category C +
    CC: product_category C C
  for C :: "'a comp"
  begin

    abbreviation map
    where "map f \<equiv> if C.arr f then (f, f) else CC.null"

    lemma is_functor:
    shows "functor C CC.comp map"
      using map_def by unfold_locales auto

    sublocale "functor" C CC.comp map
      using is_functor by simp

  end

  context cartesian_monoidal_category
  begin

    sublocale \<Delta>: diagonal_functor C ..
    interpretation To\<Delta>: composite_functor C CC.comp C \<Delta>.map T ..

    sublocale \<delta>: natural_transformation C C map \<open>T o \<Delta>.map\<close> dup
    proof
      show "\<And>f. \<not> arr f \<Longrightarrow> \<d>[f] = null"
        using ECC.tuple_ext by blast
      show "\<And>f. arr f \<Longrightarrow> dom \<d>[f] = map (dom f)"
        using dup_def by simp
      show "\<And>f. arr f \<Longrightarrow> cod \<d>[f] = To\<Delta>.map (cod f)"
        by (simp add: prod_eq_tensor)
      show "\<And>f. arr f \<Longrightarrow> To\<Delta>.map f \<cdot> \<d>[dom f] = \<d>[f]"
        using ECC.tuple_expansion prod_eq_tensor by force
      show "\<And>f. arr f \<Longrightarrow> \<d>[cod f] \<cdot> map f = \<d>[f]"
        by (simp add: comp_cod_arr dup_def)
    qed

  end

section "Cartesian Monoidal Category from Cartesian Category"

  text \<open>
    A cartesian category extends to a cartesian monoidal category by using the product
    structure to obtain the various canonical maps.
  \<close>

  context elementary_cartesian_category
  begin

    interpretation CC: product_category C C ..
    interpretation CCC: product_category C CC.comp ..
    interpretation T: binary_functor C C C Prod
      using binary_functor_Prod by simp
    interpretation T: binary_endofunctor C Prod ..
    interpretation ToTC: "functor" CCC.comp C T.ToTC
      using T.functor_ToTC by auto
    interpretation ToCT: "functor" CCC.comp C T.ToCT
      using T.functor_ToCT by auto

    interpretation \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>
      using \<alpha>_is_natural_isomorphism by blast

    interpretation L: "functor" C C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close>
      using unit_is_terminal_arr T.fixing_ide_gives_functor_1 by simp
    interpretation L: endofunctor C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close> ..
    interpretation \<l>: transformation_by_components C C
                        \<open>\<lambda>f. Prod (cod \<iota>, f)\<close> map \<open>\<lambda>a. pr0 (cod \<iota>) a\<close>
      using unit_is_terminal_arr
      by unfold_locales auto
    interpretation \<l>: natural_isomorphism C C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close> map \<l>.map
      using \<l>.map_simp_ide inverse_arrows_lunit ide_one
      by unfold_locales auto
    interpretation L: equivalence_functor C C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close>
      using \<l>.natural_isomorphism_axioms naturally_isomorphic_def
            L.isomorphic_to_identity_is_equivalence
      by blast

    interpretation R: "functor" C C \<open>\<lambda>f. Prod (f, cod \<iota>)\<close>
      using unit_is_terminal_arr T.fixing_ide_gives_functor_2 by simp
    interpretation R: endofunctor C\<open>\<lambda>f. Prod (f, cod \<iota>)\<close> ..
    interpretation \<rho>: transformation_by_components C C
                        \<open>\<lambda>f. Prod (f, cod \<iota>)\<close> map \<open>\<lambda>a. \<pp>\<^sub>1[a, cod \<iota>]\<close>
      using unit_is_terminal_arr
      by unfold_locales auto
    interpretation \<rho>: natural_isomorphism C C \<open>\<lambda>f. Prod (f, cod \<iota>)\<close> map \<rho>.map
      using \<rho>.map_simp_ide inverse_arrows_runit ide_one
      by unfold_locales auto
    interpretation R: equivalence_functor C C \<open>\<lambda>f. Prod (f, cod \<iota>)\<close>
      using \<rho>.natural_isomorphism_axioms naturally_isomorphic_def
            R.isomorphic_to_identity_is_equivalence
      by blast

    interpretation MC: monoidal_category C Prod \<alpha> \<iota>
      using ide_one \<iota>_is_iso pentagon comp_assoc \<alpha>_simp_ide comp_cod_arr
      by unfold_locales auto

    lemma induces_monoidal_category\<^sub>E\<^sub>C\<^sub>C:
    shows "monoidal_category C Prod \<alpha> \<iota>"
      ..

    lemma unity_agreement:
    shows "MC.unity = \<one>"
      using ide_one by simp

    lemma assoc_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "MC.assoc a b c = \<a>[a, b, c]"
      using assms assoc_def \<alpha>_simp_ide by auto

    lemma assoc'_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "MC.assoc' a b c = \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms inverse_arrows_assoc inverse_unique \<alpha>_simp_ide by auto

    lemma runit_char_eqn:
    assumes "ide a"
    shows "\<r>[a] \<otimes> \<one> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<one>, \<one>]"
      using assms ide_one assoc_def comp_assoc prod_tuple comp_cod_arr
      by (intro pr_joint_monic [of a "\<one>" "\<r>[a] \<otimes> \<one>" "(a \<otimes> \<iota>) \<cdot> \<a>[a, \<one>, \<one>]"]) auto

    lemma runit_agreement:
    assumes "ide a"
    shows "MC.runit a = \<r>[a]"
      using assms unity_agreement assoc_agreement MC.runit_char(2) runit_char_eqn ide_one
      by (metis (no_types, lifting) MC.runit_eqI fst_conv runit_in_hom snd_conv)

    lemma lunit_char_eqn:
    assumes "ide a"
    shows "\<one> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> \<a>\<^sup>-\<^sup>1[\<one>, \<one>, a]"
    proof (intro pr_joint_monic [of "\<one>" a "\<one> \<otimes> \<l>[a]" "(\<iota> \<otimes> a) \<cdot> \<a>\<^sup>-\<^sup>1[\<one>, \<one>, a]"])
      show "ide a" by fact
      show "ide \<one>"
        using ide_one by simp
      show "seq \<l>[a] (\<one> \<otimes> \<l>[a])"
        using assms ide_one by simp
      show "\<l>[a] \<cdot> (\<one> \<otimes> \<l>[a]) = \<l>[a] \<cdot> (\<iota> \<otimes> a) \<cdot> \<a>\<^sup>-\<^sup>1[\<one>, \<one>, a]"
        using assms ide_one assoc'_def comp_assoc prod_tuple comp_cod_arr by simp
      show "\<pp>\<^sub>1[\<one>, a] \<cdot> prod \<one> (lunit a) = \<pp>\<^sub>1[\<one>, a] \<cdot> prod \<iota> a \<cdot> assoc' \<one> \<one> a"
        using assms ide_one assoc'_def comp_cod_arr prod_tuple pr_naturality
        apply simp
        by (metis (full_types) cod_pr0 cod_pr1 elementary_category_with_binary_products.ide_prod
            elementary_category_with_binary_products_axioms pr_simps(1-2,4-5) trm_naturality
            trm_one)
    qed

    lemma lunit_agreement:
    assumes "ide a"
    shows "MC.lunit a = \<l>[a]"
      by (metis (no_types, lifting) MC.lunit_eqI assms assoc'_agreement fst_conv ide_one
          lunit_char_eqn lunit_in_hom snd_conv unity_agreement)

    interpretation CMC: cartesian_monoidal_category C Prod \<alpha> \<iota>
    proof
      show "terminal MC.unity"
        by (simp add: terminal_one unity_agreement)
      fix a b t\<^sub>a t\<^sub>b
      assume a: "ide a" and b: "ide b"
      and t\<^sub>a: "\<guillemotleft>t\<^sub>a : a \<rightarrow> MC.unity\<guillemotright>" and t\<^sub>b: "\<guillemotleft>t\<^sub>b : b \<rightarrow> MC.unity\<guillemotright>"
      have 0: "\<pp>\<^sub>0[a, b] = MC.lunit b \<cdot> MC.tensor \<t>[a] b"
        by (metis (no_types, lifting) a b ide_char cod_pr0 comp_cod_arr lunit_agreement
            pr_naturality(1) pr_simps(1) prod.sel(1-2) trm_simps(1-3))
      have 1: "\<pp>\<^sub>1[a, b] = MC.runit a \<cdot> MC.tensor a \<t>[b]"
        by (metis (no_types, lifting) a b cod_pr1 comp_cod_arr ide_char pr_naturality(2)
            pr_simps(4) prod.sel(1-2) runit_agreement trm_simps(1-3))
      have 2: "\<t>[a] = t\<^sub>a \<and> \<t>[b] = t\<^sub>b"
        using a b t\<^sub>a t\<^sub>b terminal_arr_unique trm_eqI unity_agreement by metis
      show "has_as_binary_product a b (MC.runit a \<cdot> MC.tensor a t\<^sub>b) (MC.lunit b \<cdot> MC.tensor t\<^sub>a b)"
        using a b 0 1 2 has_as_binary_product by force
    qed

    lemma extends_to_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>C:
    shows "cartesian_monoidal_category C Prod \<alpha> \<iota>"
      ..

    lemma trm_agreement:
    assumes "ide a"
    shows "CMC.the_trm a = \<t>[a]"
      by (metis assms CMC.extends_to_elementary_category_with_terminal_object\<^sub>C\<^sub>M\<^sub>C
          elementary_category_with_terminal_object.trm_eqI trm_in_hom unity_agreement)

    lemma pr_agreement:
    assumes "ide a" and "ide b"
    shows "CMC.pr\<^sub>0 a b = \<pp>\<^sub>0[a, b]" and "CMC.pr\<^sub>1 a b = \<pp>\<^sub>1[a, b]"
    proof -
      show "CMC.pr\<^sub>0 a b = \<pp>\<^sub>0[a, b]"
        unfolding CMC.pr\<^sub>0_def
        using assms(1-2) lunit_agreement pr_expansion(1) trm_agreement by auto
      show "CMC.pr\<^sub>1 a b = \<pp>\<^sub>1[a, b]"
        unfolding CMC.pr\<^sub>1_def
        using assms(1-2) pr_expansion(2) runit_agreement trm_agreement by force
    qed

    lemma dup_agreement:
    assumes "ide a"
    shows "CMC.dup a = \<d>[a]"
      by (metis (no_types, lifting) CMC.ECC.tuple_eqI assms ideD(1) pr_agreement(1-2) pr_dup(1-2))

  end

section "Cartesian Monoidal Category from Elementary Cartesian Category"

  context elementary_cartesian_category
  begin

    interpretation MC: monoidal_category C Prod \<alpha> \<iota>
      using induces_monoidal_category\<^sub>E\<^sub>C\<^sub>C by blast

    (*
     * TODO: There are a number of facts from the monoidal_category locale that it
     * would be useful to re-interpret in the present context.  The following is one
     * for which we have an immediate use, but some systematic plan is needed here.
     *)

    lemma triangle:
    assumes "ide a" and "ide b"
    shows "(a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<one>, b] = \<r>[a] \<otimes> b"
      using assms MC.triangle [of a b] assoc_agreement ide_one lunit_agreement
            runit_agreement unity_agreement fst_conv snd_conv
      by (metis (no_types, lifting))

    lemma induces_elementary_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>C:
    shows "elementary_cartesian_monoidal_category (\<cdot>) prod \<one> lunit runit assoc trm dup"
      using ide_one inverse_arrows_lunit inverse_arrows_runit inverse_arrows_assoc
            interchange lunit_naturality runit_naturality assoc_naturality
            triangle pentagon comp_assoc trm_one trm_naturality
            in_homI prod_tuple isoI arr_dom MC.tensor_in_homI comp_arr_dom comp_cod_arr
      apply unfold_locales
                          apply simp_all
           apply blast
          apply blast
         by meson

  end

  context cartesian_category
  begin

    interpretation ECC: elementary_cartesian_category C
                          some_pr0 some_pr1 some_terminal some_terminator
      using extends_to_elementary_cartesian_category by simp

    lemma extends_to_cartesian_monoidal_category\<^sub>C\<^sub>C:
    shows "cartesian_monoidal_category C ECC.Prod ECC.\<alpha> ECC.\<iota>"
      using ECC.extends_to_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>C by blast

  end

  (*
   * TODO: I would like to have coherence theorems for symmetric monoidal and cartesian
   * monoidal categories here, but I haven't yet figured out a suitably economical way
   * to extend the existing result.
   *)

end

