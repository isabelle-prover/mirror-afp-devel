(*  Title:       Universe
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2026
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Universe"

theory Universe
imports Smallness
begin

  text\<open>
    This section defines a ``universe'' to be a set \<open>univ\<close> that admits embeddings of
    various other sets, typically the result of constructions on \<open>univ\<close> itself.
    These embeddings allow us to perform constructions on \<open>univ\<close> that result in sets
    at higher types, and then to encode the results of these constructions back down
    into \<open>univ\<close>.  An example application is showing that a category admits products:
    given objects \<open>a\<close> and \<open>b\<close> in a category whose arrows form a universe \<open>univ\<close>,
    for each object \<open>x\<close> we may form the cartesian product \<open>hom x a \<times> hom x b \<subseteq> univ \<times> univ\<close>
    and then use an embedding of \<open>univ \<times> univ\<close> in \<open>univ\<close> (\textit{i.e.}~a pairing function)
    to map the result back into \<open>univ\<close>.  Assuming we can show that the resulting set
    has the proper structure to be the set of arrows of an object of the category,
    we obtain an object \<open>a \<times> b\<close> with \<open>hom x (a \<times> b) \<cong> hom x a \<times> hom x b\<close>,
    as required for a product object in a category.
  \<close>

  section "Embeddings"

  text\<open>
    Here we define some basic notions pertaining to injections into a set \<open>univ\<close>.
  \<close>

  locale embedding =
  fixes univ :: "'U set"
  begin

    abbreviation is_embedding_of
    where "is_embedding_of \<iota> X \<equiv> inj_on \<iota> X \<and> \<iota> ` X \<subseteq> univ"

    definition some_embedding_of
    where "some_embedding_of X \<equiv> SOME \<iota>. is_embedding_of \<iota> X"

    abbreviation embeds
    where "embeds X \<equiv> \<exists>\<iota>. is_embedding_of \<iota> X"

    lemma is_embedding_of_some_embedding_of:
    assumes "embeds X"
    shows "is_embedding_of (some_embedding_of X) X"
      unfolding some_embedding_of_def
      using assms someI_ex [of "\<lambda>\<iota>. is_embedding_of \<iota> X"] by force

    lemma embeds_subset:
    assumes "embeds X" and "Y \<subseteq> X"
    shows "embeds Y"
      using assms
      by (meson dual_order.trans image_mono inj_on_subset)

  end

  section "Lifting"

  text\<open>
    The locale \<open>lifting\<close> axiomatizes a set \<open>univ\<close> that embeds itself, together with
    an additional element.  This is equivalent to \<open>univ\<close> being infinite.
  \<close>

  locale lifting =
    embedding univ
  for univ :: "'U set" +
  assumes embeds_lift: "embeds ({None} \<union> Some ` univ)"
  begin

    definition some_lifting :: "'U option \<Rightarrow> 'U"
    where "some_lifting \<equiv> some_embedding_of ({None} \<union> Some ` univ)"

    lemma some_lifting_is_embedding:
    shows "is_embedding_of some_lifting ({None} \<union> Some ` univ)"
      unfolding some_lifting_def
      using is_embedding_of_some_embedding_of embeds_lift by blast

    lemma some_lifting_in_univ [intro, simp]:
    shows "some_lifting None \<in> univ"
    and "x \<in> univ \<Longrightarrow> some_lifting (Some x) \<in> univ"
      using some_lifting_is_embedding by auto

    lemma some_lifting_cancel:
    shows "\<lbrakk>x \<in> univ; some_lifting (Some x) = some_lifting None\<rbrakk> \<Longrightarrow> False"
    and "\<lbrakk>x \<in> univ; x' \<in> univ; some_lifting (Some x) = some_lifting (Some x')\<rbrakk> \<Longrightarrow> x = x'"
      using some_lifting_is_embedding
       apply (meson Un_iff imageI inj_on_contraD insertI1 option.simps(3))
      using some_lifting_is_embedding
      by (meson UnI2 imageI inj_on_contraD option.inject)

    lemma infinite_univ:
    shows "infinite univ"
      by (metis None_notin_image_Some card_image card_inj_on_le card_insert_disjoint
          embeds_lift finite_imageI inj_Some insert_is_Un le_imp_less_Suc linorder_neq_iff)

    lemma embeds_bool:
    shows "embeds (UNIV :: bool set)"
      by (metis comp_inj_on ex_inj image_comp image_mono infinite_univ
          infinite_iff_countable_subset inj_on_subset subset_trans top_greatest)

    lemma embeds_nat:
    shows "embeds (UNIV :: nat set)"
      by (metis infinite_univ infinite_iff_countable_subset)

  end

  section "Pairing"

  text\<open>
    The locale \<open>pairing\<close> axiomatizes a set \<open>univ\<close> that embeds \<open>univ \<times> univ\<close>.
  \<close>

  locale pairing =
    embedding univ
  for univ :: "'U set" +
  assumes embeds_pairs: "embeds (univ \<times> univ)"
  begin

    definition some_pairing :: "'U * 'U \<Rightarrow> 'U"
    where "some_pairing \<equiv> some_embedding_of (univ \<times> univ)"

    lemma some_pairing_is_embedding:
    shows "is_embedding_of some_pairing (univ \<times> univ)"
      unfolding some_pairing_def
      using embeds_pairs is_embedding_of_some_embedding_of by blast

    abbreviation pair
    where "pair x y \<equiv> some_pairing (x, y)"

    abbreviation is_pair :: "'U \<Rightarrow> bool"
    where "is_pair x \<equiv> x \<in> some_pairing ` (univ \<times> univ)"

    definition first :: "'U \<Rightarrow> 'U"
    where "first x \<equiv> fst (inv_into (univ \<times> univ) some_pairing x)"

    definition second :: "'U \<Rightarrow> 'U"
    where "second x = snd (inv_into (univ \<times> univ) some_pairing x)"

    lemma first_conv:
    assumes "x \<in> univ" and "y \<in> univ"
    shows "first (pair x y) = x"
      using assms first_def some_pairing_is_embedding
      by (metis (mono_tags, lifting) fst_eqD inv_into_f_f mem_Times_iff snd_eqD)

    lemma second_conv:
    assumes "x \<in> univ" and "y \<in> univ"
    shows "second (pair x y) = y"
      using assms second_def some_pairing_is_embedding
      by (metis (mono_tags, lifting) fst_eqD inv_into_f_f mem_Times_iff snd_eqD)

    lemma pair_conv:
    assumes "is_pair x"
    shows "pair (first x) (second x) = x"
      using assms first_def second_def embeds_pairs is_embedding_of_some_embedding_of
      by (simp add: f_inv_into_f)

    lemma some_pairing_in_univ [intro, simp]:
    shows "\<lbrakk>x \<in> univ; y \<in> univ\<rbrakk> \<Longrightarrow> pair x y \<in> univ"
      using some_pairing_is_embedding by blast

    lemma some_pairing_cancel:
    shows "\<lbrakk>x \<in> univ; x' \<in> univ; y \<in> univ; y' \<in> univ; pair x y = pair x' y'\<rbrakk>
              \<Longrightarrow> x = x' \<and> y = y'"
      using embeds_pairs
      by (metis first_conv second_conv)

  end

  section "Powering"

  text\<open>
    The \<open>powering\<close> locale axiomatizes a universe that embeds the set of all its ``small'' subsets.
    Obviously, some condition on the subsets is required because (by Cantor's Theorem) it is
    not possible for a set to embed the set of \emph{all} its subsets.
    The concept of ``smallness'' used here is not fixed, but rather is taken as a parameter.
  \<close>

  locale powering =
    embedding univ +
    smallness sml
  for sml :: "'V set \<Rightarrow> bool"
  and univ :: "'U set" +
  assumes embeds_small_sets: "embeds {X. X \<subseteq> univ \<and> small X}"
  begin

    abbreviation some_embedding_of_small_sets :: "('U set) \<Rightarrow> 'U"
    where "some_embedding_of_small_sets \<equiv> some_embedding_of {X. X \<subseteq> univ \<and> small X}"

    definition emb_set :: "('U set) \<Rightarrow> 'U"
    where "emb_set \<equiv> some_embedding_of_small_sets"

    lemma emb_set_is_embedding:
    shows "is_embedding_of emb_set {X. X \<subseteq> univ \<and> small X}"
      unfolding emb_set_def
      using embeds_small_sets is_embedding_of_some_embedding_of by blast

    lemma emb_set_in_univ [intro, simp]:
    shows "\<lbrakk>X \<subseteq> univ; small X\<rbrakk> \<Longrightarrow> emb_set X \<in> univ"
      using emb_set_is_embedding by blast

    lemma emb_set_cancel:
    shows "\<lbrakk>X \<subseteq> univ; small X; X' \<subseteq> univ; small X'; emb_set X = emb_set X'\<rbrakk> \<Longrightarrow> X = X'"
      using emb_set_is_embedding
      by (metis (mono_tags, lifting) inj_onD mem_Collect_eq)

    text\<open>
      If \<open>univ\<close> embeds the collection of all its small subsets, then \<open>univ\<close> itself
      must be large.
    \<close>

    lemma large_univ:
    shows "\<not> small univ"
    proof -
      have "small univ \<Longrightarrow> False"
      proof -
        assume small: "small univ"
        have "embeds (Pow univ)"
          using small smaller_than_small embeds_small_sets
          by (metis (no_types, lifting) CollectI PowD embeds_subset subsetI)
        thus False
          using Cantors_theorem
          by (metis Pow_not_empty inj_on_iff_surj)
      qed
      thus ?thesis by blast
    qed

  end

  section "Tupling"

  text\<open>
    The \<open>tupling\<close> locale axiomatizes a set \<open>univ\<close> that embeds the set of all
    ``small extensional functions'' on its elements.  Here, the notion of
    ``extensional function'' is parametrized by the default value \<open>null\<close> produced
    by such a function when it is applied to an argument outside of \<open>univ\<close>.
    The default value \<open>null\<close> is neither assumed to be in \<open>univ\<close> nor outside of it.
  \<close>

  locale tupling =
    lifting univ +
    pairing univ +
    powering sml univ +
    small_funcset sml
  for sml :: "'V set \<Rightarrow> bool"
  and univ :: "'U set"
  and null :: "'U"
  begin

    text\<open>
      \<open>EF\<close> is the set of extensional functions on \<open>univ\<close>.  These map \<open>univ\<close> to
      \<open>univ \<union> {null}\<close> and map values outside of \<open>univ\<close> to \<open>null\<close>.  The default
      value \<open>null\<close> might or might not be an element of \<open>univ\<close>.
      The set \<open>SEF\<close> is the subset of \<open>EF\<close> consisting of those functions that
      are ``small functions''.
    \<close>

    definition EF
    where "EF \<equiv> {f. f ` univ \<subseteq> univ \<union> {null} \<and> (\<forall>x. x \<notin> univ \<longrightarrow> f x = null)}"

    abbreviation SEF
    where "SEF \<equiv> Collect small_function \<inter> EF"

    lemma EF_apply:
    assumes "F \<in> EF"
    shows "x \<in> univ \<Longrightarrow> F x \<in> univ \<union> {null}"
    and "x \<notin> univ \<Longrightarrow> F x = null"
      using assms
      unfolding EF_def by auto

    text\<open>
      Since \<open>univ\<close> is large, the set of all values at type \<open>'U\<close> must also be large.
      This implies that every small extensional function having type \<open>'U\<close> as its domain
      type must have a popular value.
    \<close>

    lemma SEFs_have_popular_value:
    assumes "F \<in> SEF"
    shows "\<exists>v. popular_value F v"
      using assms ex_popular_value_iff large_UNIV
      by (metis Int_iff large_univ mem_Collect_eq smaller_than_small top_greatest)

    text\<open>
      The following technical lemma uses powering to obtain an encoding of small
      extensional functions as elements of \<open>univ\<close>.  The idea is that a small extensional
      function \<open>F\<close> mapping \<open>univ\<close> to \<open>univ \<union> {null}\<close> can be canonically described
      by a small subset of \<open>univ \<times> (univ \<union> {null})\<close> consisting of all pairs
      \<open>(x, F x) \<subseteq> univ \<times> (univ \<union> {null})\<close> for which \<open>F x\<close> is not a popular value,
      together with the single popular value of \<open>F\<close> taken at other arguments \<open>x\<close>
      not represented by such pairs.
    \<close>

    lemma embeds_SEF:
    shows "embeds SEF"
    proof (intro exI conjI)
      have range_F: "\<And>F. F \<in> SEF \<Longrightarrow> range F \<subseteq> univ \<union> {null}"
        unfolding EF_def by blast
      let ?lift = "some_embedding_of (univ \<union> {null})"
      have lift: "is_embedding_of ?lift (univ \<union> {null})"
        using embeds_lift is_embedding_of_some_embedding_of
        by (metis bij_betw_imp_surj_on infinite_univ infinite_imp_bij_betw2
            inj_on_iff_surj insert_not_empty sup_bot.neutr_eq_iff)
      have lift_cancel [simp]: "\<And>x y. \<lbrakk>x \<in> univ \<union> {null}; y \<in> univ \<union> {null}; ?lift x = ?lift y\<rbrakk>
                                          \<Longrightarrow> x = y"
        using lift by (meson UnI1 inj_on_eq_iff)
      have 0: "\<And>F. F \<in> SEF \<Longrightarrow> ?lift (some_popular_value F) \<in> univ"
        using range_F popular_value_in_range popular_value_some_popular_value
          SEFs_have_popular_value
        by (metis image_subset_iff lift subset_eq)
      have 1: "\<And>F. F \<in> SEF \<Longrightarrow> small {x \<in> univ. \<not> popular_value F (F x)}"
        by (metis (no_types) CollectD Collect_conj_eq IntE inf_le2 small_SF_Dom
            smaller_than_small)
      have 2: "\<And>F. F \<in> SEF \<Longrightarrow>
                     (\<lambda>a. pair a (?lift (F a))) ` {x \<in> univ. \<not> popular_value F (F x)} \<subseteq> univ"
        apply auto[1]
        by (metis (no_types, lifting) CollectD EF_def Un_commute image_subset_iff insert_is_Un
            lift some_pairing_in_univ)
      have 3: "\<And>F. F \<in> SEF \<Longrightarrow>
                     emb_set ((\<lambda>a. pair a (?lift (F a))) ` {x \<in> univ. \<not> popular_value F (F x)})
                       \<in> univ"
        using 1 2 by blast
      (*
       * A small function may be encoded as an element of univ by pairing an encoding of
       * its graph, which is small, with its popular value.
       *)
      let ?e = "\<lambda>F. pair (?lift (some_popular_value F))
                         (emb_set ((\<lambda>a. pair a (?lift (F a))) `
                                      {x \<in> univ. \<not> popular_value F (F x)}))"
      show "?e ` SEF \<subseteq> univ"
        using 0 3 some_pairing_in_univ by blast
      show "inj_on ?e SEF"
      proof (intro inj_onI)
        fix F F' :: "'U \<Rightarrow> 'U"
        assume F: "F \<in> SEF"
        assume F': "F' \<in> SEF"
        assume eq: "?e F = ?e F'"
        have *: "\<And>x. x \<in> univ \<Longrightarrow>
                       first (pair x (?lift (F x))) = x \<and>
                       second (pair x (?lift (F x))) = ?lift (F x) \<and>
                       first (pair x (?lift (F' x))) = x \<and>
                       second (pair x (?lift (F' x))) = ?lift (F' x)"
          by (meson F F' first_conv image_subset_iff lift range_F range_subsetD second_conv)
        have 4: "?lift (some_popular_value F) = ?lift (some_popular_value F') \<and>
                 emb_set ((\<lambda>a. pair a (?lift (F a))) ` {x \<in> univ. \<not> popular_value F (F x)}) =
                 emb_set ((\<lambda>a. pair a (?lift (F' a))) ` {x \<in> univ. \<not> popular_value F' (F' x)})"
          using F F' 0 3 eq some_pairing_cancel by meson
        have 5: "(\<lambda>a. pair a (?lift (F a))) ` {x \<in> univ. \<not> popular_value F (F x)} =
                 (\<lambda>a. pair a (?lift (F' a))) ` {x \<in> univ. \<not> popular_value F' (F' x)}"
          using F F' 1 2 4 small_preimage_unpopular smaller_than_small
            emb_set_cancel
              [of "(\<lambda>a. pair a (?lift (F a))) ` {x \<in> univ. \<not> popular_value F (F x)}"
                  "(\<lambda>a. pair a (?lift (F' a))) ` {x \<in> univ. \<not> popular_value F' (F' x)}"]
          by blast
        have 6: "{x \<in> univ. \<not> popular_value F (F x)} = {x \<in> univ. \<not> popular_value F' (F' x)}"
        proof -
          have "(\<lambda>a. first (pair a (?lift (F a)))) ` {x \<in> univ. \<not> popular_value F (F x)} =
                (\<lambda>a. first (pair a (?lift (F' a)))) ` {x \<in> univ. \<not> popular_value F' (F' x)} \<and>
                (\<lambda>a. second (pair a (?lift (F a)))) ` {x \<in> univ. \<not> popular_value F (F x)} =
                (\<lambda>a. second (pair a (?lift (F' a)))) ` {x \<in> univ. \<not> popular_value F' (F' x)}"
            using 5 by (metis image_image)
          thus ?thesis
            using * embeds_pairs is_embedding_of_some_embedding_of by auto
        qed
        have 7: "\<And>x. x \<in> univ \<and> \<not> popular_value F (F x) \<Longrightarrow> F x = F' x"
        proof -
          fix x
          assume x: "x \<in> univ \<and> \<not> popular_value F (F x)"
          have "?lift (F x) = ?lift (F' x)"
          proof -
            have "\<And>y. ((x, y) \<in> (\<lambda>x. (x, ?lift (F x))) ` {x \<in> univ. \<not> popular_value F (F x)}
                          \<longleftrightarrow> y = ?lift (F x)) \<and>
                       ((x, y) \<in> (\<lambda>x. (x, ?lift (F' x))) ` {x \<in> univ. \<not> popular_value F (F x)}
                          \<longleftrightarrow> y = ?lift (F' x))"
              using x by blast
            moreover have "(\<lambda>x. (x, ?lift (F x))) ` {x \<in> univ. \<not> popular_value F (F x)} =
                           (\<lambda>x. (x, ?lift (F' x))) ` {x \<in> univ. \<not> popular_value F (F x)}"
            proof -
              have "(\<lambda>x. (x, ?lift (F x))) ` {x \<in> univ. \<not> popular_value F (F x)} =
                    (\<lambda>x. (x, ?lift (F' x))) ` {x \<in> univ. \<not> popular_value F' (F' x)}"
              proof -
                have "(\<lambda>x. (first (pair x (?lift (F x))), second (pair x (?lift (F x)))))
                                   ` {x \<in> univ. \<not> popular_value F (F x)} =
                      (\<lambda>x. (first (pair x (?lift (F' x))), second (pair x (?lift (F' x)))))
                                   ` {x \<in> univ. \<not> popular_value F' (F' x)}"
                proof -
                  have "(\<lambda>x. (first x, second x)) ` (\<lambda>a. pair a (?lift (F a)))
                           ` {x \<in> univ. \<not> popular_value F (F x)} =
                        (\<lambda>x. (first x, second x)) ` (\<lambda>a. pair a (?lift (F' a)))
                           ` {x \<in> univ. \<not> popular_value F' (F' x)}"
                    using 5 by argo
                  thus ?thesis by blast
                qed
                thus ?thesis
                  using * some_pairing_cancel by auto
              qed
              thus ?thesis
                using 6 by blast
            qed
            ultimately show ?thesis by fastforce
          qed
          thus "F x = F' x"
            by (metis EF_apply(1) F F' Int_iff lift_cancel x)
        qed
        show "F = F'"
        proof
          fix x
          show "F x = F' x"
          proof (cases "x \<in> univ")
            case False
            show ?thesis
              using F F' False EF_def
              by (metis EF_apply(2) IntE)
            next
            assume x: "x \<in> univ"
            show ?thesis
            proof (cases "popular_value F (F x)")
              case False
              show ?thesis
                using 7 False x by blast
              next
              case True
              show ?thesis
              proof -
                have "F x = some_popular_value F"
                  by (metis (mono_tags, lifting) CollectD Collect_mono F IntE True
                      small_preimage_unpopular smallness.smaller_than_small smallness_axioms)
                moreover have "F' x = some_popular_value F'"
                proof -
                  have "popular_value F' (F' x)"
                    using True x 6 by blast
                  thus ?thesis
                    by (metis (mono_tags, lifting) CollectD Collect_mono F' IntE
                        small_preimage_unpopular smallness.smaller_than_small smallness_axioms)
                qed
                moreover have "some_popular_value F = some_popular_value F'"
                  using F F' 4 calculation lift_cancel range_F range_subsetD
                  by (metis (no_types, opaque_lifting))
                ultimately show ?thesis by auto
              qed
            qed
          qed
        qed
      qed
    qed

    definition some_embedding_of_small_functions :: "('U \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "some_embedding_of_small_functions \<equiv> some_embedding_of SEF"

    lemma some_embedding_of_small_functions_is_embedding:
    shows "is_embedding_of some_embedding_of_small_functions SEF"
      unfolding some_embedding_of_small_functions_def
      using embeds_SEF is_embedding_of_some_embedding_of by blast

    lemma some_embedding_of_small_functions_in_univ [intro, simp]:
    assumes "F \<in> SEF"
    shows "some_embedding_of_small_functions F \<in> univ"
      using assms some_embedding_of_small_functions_is_embedding by blast

    lemma some_embedding_of_small_functions_cancel:
    assumes "F \<in> SEF" and "F' \<in> SEF"
    and "some_embedding_of_small_functions F = some_embedding_of_small_functions F'"
    shows "F = F'"
      using assms some_embedding_of_small_functions_is_embedding
      by (meson inj_onD)

  end

  section "Universe"

  text\<open>
    The \<open>universe\<close> locale axiomatizes a set that is equipped with an embedding of its
    own small extensional function space, and in addition the set of natural numbers
    is required to be small (\textit{i.e.}~there is a small infinite set).
  \<close>

  locale universe =
    tupling sml univ null +
    small_nat sml
  for sml :: "'V set \<Rightarrow> bool"
  and univ :: "'U set"
  and null :: "'U"
  begin

    text\<open>
      For a fixed notion of smallness, the property of being a universe is respected
      by equipollence; thus it is a property of the set itself, rather than something
      that depends on the ambient type.
    \<close>

    lemma is_respected_by_equipollence:
    assumes "eqpoll univ univ'"
    shows "universe sml univ'"
    proof
      obtain \<gamma> where \<gamma>: "bij_betw \<gamma> univ univ'"
        using assms eqpoll_def by blast
      show "\<exists>\<iota>. inj_on \<iota> ({None} \<union> Some ` univ') \<and> \<iota> ` ({None} \<union> Some ` univ') \<subseteq> univ'"
      proof -
        let ?\<iota> = "\<lambda> None \<Rightarrow> \<gamma> (some_lifting None)
                  | Some x \<Rightarrow> \<gamma> (some_lifting (Some (inv_into univ \<gamma> x)))"
        have "?\<iota> ` ({None} \<union> Some ` univ') \<subseteq> univ'"
          using \<gamma> is_embedding_of_some_embedding_of bij_betw_apply
          apply auto[1]
           apply fastforce
          by (simp add: bij_betw_imp_surj_on inv_into_into)
        moreover have "inj_on ?\<iota> ({None} \<union> Some ` univ')"
        proof
          fix x y
          assume x: "x \<in> {None} \<union> Some ` univ'"
          assume y: "y \<in> {None} \<union> Some ` univ'"
          assume eq: "?\<iota> x = ?\<iota> y"
          show "x = y"
            using x y eq \<gamma> some_lifting_cancel
            apply auto[1]
            by (metis bij_betw_def inv_into_f_eq inv_into_into inv_into_injective
                inv_into_into some_lifting_in_univ(1,2))+
        qed
        ultimately show ?thesis by blast
      qed
      show "\<exists>\<iota>. inj_on \<iota> (univ' \<times> univ') \<and> \<iota> ` (univ' \<times> univ') \<subseteq> univ'"
      proof -
        let ?\<iota> = "\<lambda>x. \<gamma> (some_pairing (inv_into univ \<gamma> (fst x), inv_into univ \<gamma> (snd x)))"
        have "?\<iota> ` (univ' \<times> univ') \<subseteq> univ'"
        proof -
          have "\<And>x. x \<in> univ' \<times> univ' \<Longrightarrow> ?\<iota> x \<in> univ'"
            by (metis \<gamma> bij_betw_def imageI inv_into_into mem_Times_iff some_pairing_in_univ)
          thus ?thesis by blast
        qed
        moreover have "inj_on ?\<iota> (univ' \<times> univ')"
        proof
          fix x y
          assume x: "x \<in> univ' \<times> univ'" and y: "y \<in> univ' \<times> univ'"
          assume eq: "?\<iota> x = ?\<iota> y"
          show "x = y"
          proof -
            have "pair (inv_into univ \<gamma> (fst x)) (inv_into univ \<gamma> (snd x)) =
                  pair (inv_into univ \<gamma> (fst y)) (inv_into univ \<gamma> (snd y))"
            proof -
              have "inv_into univ \<gamma> (fst x) \<in> univ \<and> inv_into univ \<gamma> (snd x) \<in> univ \<and>
                    inv_into univ \<gamma> (fst y) \<in> univ \<and> inv_into univ \<gamma> (snd y) \<in> univ"
                by (metis \<gamma> bij_betw_imp_surj_on inv_into_into mem_Times_iff x y)
              thus ?thesis
                by (metis \<gamma> bij_betw_inv_into_left eq some_pairing_in_univ)
            qed
            hence "inv_into univ \<gamma> (fst x) = inv_into univ \<gamma> (fst y) \<and>
                   inv_into univ \<gamma> (snd x) = inv_into univ \<gamma> (snd y)"
              using x y eq \<gamma>
              by (metis bij_betw_imp_surj_on first_conv inv_into_into mem_Times_iff second_conv)
            hence "fst x = fst y \<and> snd x = snd y"
              by (metis (full_types) \<gamma> bij_betw_inv_into_right mem_Times_iff x y)
            thus "x = y"
              by (simp add: prod_eq_iff)
          qed
        qed
        ultimately show ?thesis by blast
      qed
      show "\<exists>\<iota>. inj_on \<iota> {X. X \<subseteq> univ' \<and> small X} \<and> \<iota> ` {X. X \<subseteq> univ' \<and> small X} \<subseteq> univ'"
      proof -
        let ?\<iota> = "\<lambda>X. \<gamma> (emb_set (inv_into univ \<gamma> ` X))"
        have "?\<iota> ` {X. X \<subseteq> univ' \<and> small X} \<subseteq> univ'"
        proof
          fix X'
          assume X': "X' \<in> ?\<iota> ` {X. X \<subseteq> univ' \<and> small X}"
          obtain X where X: "X \<subseteq> univ' \<and> small X \<and> ?\<iota> X = X'"
            using X' by blast
          have "?\<iota> X \<in> univ'"
            by (metis X \<gamma> bij_betw_def bij_betw_inv_into imageI image_mono emb_set_in_univ
                small_image)
          thus "X' \<in> univ'"
            using X by blast
        qed
        moreover have "inj_on ?\<iota> {X. X \<subseteq> univ' \<and> small X}"
        proof
          fix X X'
          assume X: "X \<in> {X. X \<subseteq> univ' \<and> small X}"
          assume X': "X' \<in> {X. X \<subseteq> univ' \<and> small X}"
          assume eq: "?\<iota> X = ?\<iota> X'"
          show "X = X'"
          proof -
             have "emb_set (inv_into univ \<gamma> ` X) = emb_set (inv_into univ \<gamma> ` X')"
             proof -
               have "emb_set (inv_into univ \<gamma> ` X) \<in> univ \<and> emb_set (inv_into univ \<gamma> ` X') \<in> univ"
                 by (metis (no_types, lifting) Int_Collect Int_iff X X' \<gamma> bij_betw_def
                     bij_betw_inv_into powering.emb_set_in_univ powering_axioms small_image
                     subset_image_iff)
               thus ?thesis
                 by (metis \<gamma> bij_betw_inv_into_left eq)
             qed
             hence "inv_into univ \<gamma> ` X = inv_into univ \<gamma> ` X'"
               by (metis (no_types, lifting) Int_Collect Int_iff X X' \<gamma> bij_betw_def
                   bij_betw_inv_into powering.emb_set_cancel powering_axioms small_image
                   subset_image_iff)
             thus ?thesis
               by (metis X X' \<gamma> bij_betw_imp_surj_on image_inv_into_cancel mem_Collect_eq)
           qed
        qed
        ultimately show ?thesis by blast
      qed
    qed

    text\<open>
      A universe admits an embedding of all lists formed from its elements.
    \<close>

    sublocale small_funcset_and_nat ..

    fun some_embedding_of_lists :: "'U list \<Rightarrow> 'U"
    where "some_embedding_of_lists [] = some_lifting None"
        | "some_embedding_of_lists (x # l) =
           some_lifting (Some (some_pairing (x, some_embedding_of_lists l)))"

    lemma embeds_lists:
    shows "embeds {l. List.set l \<subseteq> univ}"
    and "is_embedding_of some_embedding_of_lists {l. List.set l \<subseteq> univ}"
    proof -
      show "is_embedding_of some_embedding_of_lists {l. List.set l \<subseteq> univ}"
      proof
        show *: "some_embedding_of_lists ` {l. list.set l \<subseteq> univ} \<subseteq> univ"
        proof -
          have "\<And>l. List.set l \<subseteq> univ \<Longrightarrow> some_embedding_of_lists l \<in> univ"
          proof -
            fix l
            show "List.set l \<subseteq> univ \<Longrightarrow> some_embedding_of_lists l \<in> univ"
              by (induct l) auto
          qed
          thus ?thesis by blast
        qed
        show "inj_on some_embedding_of_lists {l. list.set l \<subseteq> univ}"
        proof -
          have "\<And>n l m. \<lbrakk>l \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> n};
                         m \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> n};
                         some_embedding_of_lists l = some_embedding_of_lists m\<rbrakk>
                           \<Longrightarrow> l = m"
          proof -
            fix n l m
            show "\<lbrakk>l \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> n};
                   m \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> n};
                   some_embedding_of_lists l = some_embedding_of_lists m\<rbrakk>
                     \<Longrightarrow> l = m"
            proof (induct n arbitrary: l m)
              show "\<And>l m. \<lbrakk>l \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> 0};
                           m \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> 0};
                           some_embedding_of_lists l = some_embedding_of_lists m\<rbrakk>
                             \<Longrightarrow> l = m"
                by auto
              fix n l m
              assume ind: "\<And>l m. \<lbrakk>l \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> n};
                                  m \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> n};
                                  some_embedding_of_lists l = some_embedding_of_lists m\<rbrakk>
                                    \<Longrightarrow> l = m"
              assume l: "l \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> Suc n}"
              assume m: "m \<in> {l. list.set l \<subseteq> univ \<and> length l \<le> Suc n}"
              assume eq: "some_embedding_of_lists l = some_embedding_of_lists m"
              show "l = m"
              proof (cases l; cases m)
                show "\<lbrakk>l = []; m = []\<rbrakk> \<Longrightarrow> l = m" by simp
                show "\<And>a m'. \<lbrakk>l = []; m = a # m'\<rbrakk> \<Longrightarrow> l = m"
                  by (metis (no_types, lifting) "*" eq image_subset_iff insert_subset
                      list.simps(15) m mem_Collect_eq some_pairing_in_univ
                      some_embedding_of_lists.simps(1,2) some_lifting_cancel(1))
                show "\<And>a l'. \<lbrakk>l = a # l'; m = []\<rbrakk> \<Longrightarrow> l = m"
                  by (metis (lifting) "*" eq image_subset_iff l some_lifting_cancel(1)
                      list.set_intros(1) mem_Collect_eq some_pairing_in_univ set_subset_Cons
                      some_embedding_of_lists.simps(1,2) subset_code(1))
                show "\<And>a b l' m'. \<lbrakk>l = a # l'; m = b # m'\<rbrakk> \<Longrightarrow> l = m"
                proof -
                  fix a b l' m'
                  assume al': "l = a # l'" and bm': "m = b # m'"
                  have "some_pairing (a, some_embedding_of_lists l') =
                        some_pairing (b, some_embedding_of_lists m')"
                    using l m al' bm' eq some_lifting_is_embedding embeds_pairs
                    apply simp
                    by (metis (no_types, lifting) "*" image_subset_iff mem_Collect_eq
                        some_lifting_cancel(2) some_pairing_in_univ)
                  hence "a = b \<and> some_embedding_of_lists l' = some_embedding_of_lists m'"
                    using l m al' bm' embeds_pairs
                    by (metis (lifting) "*" image_subset_iff insert_subset list.simps(15)
                        mem_Collect_eq first_conv second_conv)
                  hence "a = b \<and> l' = m'"
                    using l m al' bm' ind by auto
                  thus "l = m"
                    using al' bm' by auto
                qed
              qed
            qed
          qed
          thus ?thesis
            using inj_on_def [of some_embedding_of_lists "{l. list.set l \<subseteq> univ}"]
            by (metis (lifting) linorder_le_cases mem_Collect_eq)
        qed
      qed
      thus "embeds {l. List.set l \<subseteq> univ}" by blast
    qed

    text\<open>
      A universe also admits an embedding of all small sets of lists formed from its elements.
    \<close>

    lemma embeds_small_sets_of_lists:
    shows "is_embedding_of (\<lambda>X. some_embedding_of_small_sets (some_embedding_of_lists ` X))
              {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}"
    and "embeds {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}"
    proof -
      show "is_embedding_of (\<lambda>X. some_embedding_of_small_sets (some_embedding_of_lists ` X))
              {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}"
      proof
        show "inj_on (\<lambda>X. some_embedding_of_small_sets (some_embedding_of_lists ` X))
                {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}"
        proof
          fix X Y :: "'U list set"
          assume X: "X \<in> {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}"
          and Y: "Y \<in> {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}"
          assume eq: "some_embedding_of_small_sets (some_embedding_of_lists ` X) =
                      some_embedding_of_small_sets (some_embedding_of_lists ` Y)"
          have "some_embedding_of_lists ` X = some_embedding_of_lists ` Y"
            by (metis (mono_tags, lifting) CollectD X Y emb_set_cancel emb_set_def
                embeds_lists(2) eq image_mono small_image subset_trans)
          thus "X = Y"
            using X Y embeds_lists inj_on_image_eq_iff by fastforce
        qed
        show "(\<lambda>X. some_embedding_of_small_sets (some_embedding_of_lists ` X)) `
                 {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X} \<subseteq> univ"
        proof
          fix X'
          assume X': "X' \<in> (\<lambda>X. some_embedding_of {X. X \<subseteq> univ \<and> small X}
                                (some_embedding_of_lists ` X))
                              ` {X. X \<subseteq> {l. set l \<subseteq> univ} \<and> small X}"
          obtain X where X: "X \<subseteq> {l. set l \<subseteq> univ} \<and> small X \<and>
                             (\<lambda>X. some_embedding_of {X. X \<subseteq> univ \<and> small X}
                                (some_embedding_of_lists ` X)) X = X'"
            using X' by blast
          have "some_embedding_of_lists ` X \<subseteq> univ \<and> small (some_embedding_of_lists ` X)"
            using X embeds_lists small_image by blast
          hence "(\<lambda>X. some_embedding_of {X. X \<subseteq> univ \<and> small X}
                   (some_embedding_of_lists ` X)) X \<in> univ"
            by (metis emb_set_def emb_set_in_univ)
          thus "X' \<in> univ"
            using X by blast
        qed
      qed
      thus "embeds {X. X \<subseteq> {l. list.set l \<subseteq> univ} \<and> small X}" by blast
    qed

  end

end

