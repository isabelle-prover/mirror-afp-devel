(*  Title:       Smallness
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2026
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Smallness"

theory Smallness
imports "HOL-Library.Equipollence"
begin

  text \<open>
    The purpose of this theory is to axiomatize, using locales, a notion of ``small set'' that
    is polymorphic over types and that is preserved by certain set-theoretic constructions
    in the way we would usually expect.  We first observe that we cannot simply define
    such a notion within normal HOL, because HOL does not permit us to quantify over types,
    nor does it permit us to show the existence of a single type ``large enough'' to admit
    sets of all cardinalities that would result, say, by iterating the application of the
    powerset operator starting with some infinite set.  So any way of defining ``smallness''
    is going to require extending HOL in some way.  Note that this is exactly what is already
    done in the article \<^cite>\<open>"ZFC_in_HOL-AFP"\<close>, which axiomatizes a particular type \<open>V\<close>
    and then defines a polymorphic function \<open>small\<close> using the properties of that type.
    However, we would prefer to have a notion of smallness that is not tied to one particular
    type or construction.

    Ideally, what we would like to do is to define a locale \<open>smallness\<close>, whose assumptions
    express closure properties that we would like to hold for a function
    \<open>small :: 'a set \<Rightarrow> bool\<close>.  This does not quite work, though, because the types involved
    in locale assumptions are essentially fixed, so that the function \<open>small\<close> could not
    be applied polymorphically.  A workaround is to have the locale assumption express
    closure properties of a function \<open>sml :: 'b \<Rightarrow> bool\<close>, where type \<open>'b\<close> is essentially
    fixed, and then to define within the locale context the actually polymorphic function
    \<open>small :: 'a \<Rightarrow> bool\<close>, which extends \<open>sml\<close> by equipollence to an arbitrary type \<open>'a\<close>.
    This is essentially what is done in \<^cite>\<open>"ZFC_in_HOL-AFP"\<close>, except rather than basing the definition
    on a notion of smallness derived from a particular type \<open>V\<close> we are defining a locale
    that takes the type and associated basic notion of smallness as a parameter.

    In the development here we have defined a basic \<open>smallness\<close> locale, along with several
    extensions that express various collections of closure properties.  It is not yet clear
    how useful this level of generality might turn out to be in practice, however at the
    very least, this allows us to segregate the property ``the set of natural number is
    small'' from the others.  This allows us to consider two interpretations for
    ``category of small sets and functions''; one of which only has objects corresponding
    to finite sets and the other of which also has objects corresponding to infinite sets.
  \<close>

  section "Basic Notions"

  text \<open>
    Here we define the base locale \<open>smallness\<close>, which takes as a parameter a function
    \<open>sml :: 'a set \<Rightarrow> bool\<close> that defines a basic notion of smallness at some fixed type,
    and extends this basic notion by equipollence to arbitrary types.  We assume that
    the basic notion of smallness \<open>sml\<close> given as a parameter already respects
    equipollence, so that \<open>small\<close> and \<open>sml\<close> coincide at type \<open>'a\<close>.
  \<close>

  locale smallness =
  fixes sml :: "'V set \<Rightarrow> bool"
  assumes lepoll_small_ax: "\<lbrakk>sml X; lepoll Y X\<rbrakk> \<Longrightarrow> sml Y"
  begin

    definition small :: "'a set \<Rightarrow> bool"
    where "small X \<equiv> \<exists>X\<^sub>0. sml X\<^sub>0 \<and> X \<approx> X\<^sub>0"

    lemma smallI:
    assumes "sml X\<^sub>0" and "X \<approx> X\<^sub>0"
    shows "small X"
      using assms small_def by auto

    lemma smallE:
    assumes "small X"
    and "\<And>X\<^sub>0. \<lbrakk>sml X\<^sub>0; X \<approx> X\<^sub>0\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms small_def by blast

    lemma small_iff_sml:
    shows "small X \<longleftrightarrow> sml X"
      using eqpoll_imp_lepoll small_def lepoll_small_ax by blast

    lemma lepoll_small:
    assumes "small X" and "lepoll Y X"
    shows "small Y"
      by (metis assms(1,2) eqpoll_sym image_lepoll inj_on_image_eqpoll_self
          lepoll_def' lepoll_small_ax lepoll_trans lepoll_trans2 small_def)

    lemma smaller_than_small:
    assumes "small X" and "Y \<subseteq> X"
    shows "small Y"
      using assms lepoll_small subset_imp_lepoll by blast

    lemma small_image [intro, simp]:
    assumes "small X"
    shows "small (f ` X)"
      using assms small_def image_lepoll lepoll_small by blast

    lemma small_image_iff [simp]: "inj_on f A \<Longrightarrow> small (f ` A) \<longleftrightarrow> small A"
      by (metis small_image the_inv_into_onto)

    lemma small_Collect [simp]: "small X \<Longrightarrow> small {x \<in> X. P x}"
      by (simp add: smaller_than_small subset_imp_lepoll)

  end

  section "Smallness of Finite Sets"

  text \<open>
    The locale \<open>small_finite\<close> is satisfied by notions of smallness that admit small
    sets of arbitrary finite cardinality.
  \<close>

  locale small_finite =
    smallness +
  assumes small_finite_ax: "\<exists>Y. sml Y \<and> eqpoll {1..n :: nat} Y"
  begin

    lemma small_finite:
    shows "finite X \<Longrightarrow> small X"
      using small_finite_ax
      by (meson eqpoll_def eqpoll_sym eqpoll_trans ex_bij_betw_nat_finite_1 small_def)

    lemma small_insert:
    assumes "small X"
    shows "small (insert a X)"
      by (meson assms eqpoll_imp_lepoll finite.insertI infinite_insert_eqpoll
        small_finite lepoll_small)

    lemma small_insert_iff [iff]: "small (insert a X) \<longleftrightarrow> small X"
      by (meson small_insert smaller_than_small subset_imp_lepoll subset_insertI)

  end

  section "Smallness of Binary Products"

  text \<open>
    The locale \<open>small_product\<close> is satisfied by notions of smallness that are preserved
    under cartesian product.
  \<close>

  locale small_product =
    smallness +
  assumes small_product_ax: "\<lbrakk>sml X; sml Y\<rbrakk> \<Longrightarrow> \<exists>Z. sml Z \<and> eqpoll (X \<times> Y) Z"
  begin

    lemma small_product [simp]:
    assumes "small X" "small Y" shows "small (X \<times> Y)"
      by (metis assms(1,2) eqpoll_trans small_def small_product_ax times_eqpoll_cong)

  end

  section "Smallness of Sums"

  text \<open>
    The locale \<open>small_sum\<close> is satisfied by notions of smallness that are preserved
    under the formation of small-indexed unions.
  \<close>

  locale small_sum =
    small_finite +
  assumes small_sum_ax: "\<lbrakk>sml X; \<And>x. x \<in> X \<Longrightarrow> sml (F x)\<rbrakk>
                            \<Longrightarrow> \<exists>U. sml U \<and> eqpoll (Sigma X F) U"
  begin

    lemma small_binary_sum:
    assumes "small X" and "small Y"
    shows "small (({False} \<times> X) \<union> ({True} \<times> Y))"
    proof -
      obtain X\<^sub>0 \<rho> where X\<^sub>0: "sml X\<^sub>0 \<and> bij_betw \<rho> X X\<^sub>0"
        using assms(1) small_def eqpoll_def by blast
      obtain Y\<^sub>0 \<sigma> where Y\<^sub>0: "sml Y\<^sub>0 \<and> bij_betw \<sigma> Y Y\<^sub>0"
        using assms(2) small_def eqpoll_def by blast
      obtain B\<^sub>0 \<beta> where B\<^sub>0: "sml B\<^sub>0 \<and>
                             bij_betw \<beta> {None, Some ({} :: 'b set)} B\<^sub>0"
        by (metis eqpoll_def finite.emptyI smallE small_finite.small_finite
          small_finite.small_insert_iff small_finite_axioms)
      let ?False = "\<beta> None" and ?True = "\<beta> (Some {})"
      have ne: "?False \<noteq> ?True"
        by (metis B\<^sub>0 bij_betw_inv_into_left insertCI option.discI)
      let ?\<iota> = "\<lambda>z. if fst z = False then (?False, \<rho> (snd z)) else (?True, \<sigma> (snd z))"
      have "small (({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0))"
      proof -
        have "Sigma B\<^sub>0 (\<lambda>x. if x = ?False then X\<^sub>0 else Y\<^sub>0) =
              ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0)"
        proof
          show "Sigma B\<^sub>0 (\<lambda>x. if x = ?False then X\<^sub>0 else Y\<^sub>0) \<subseteq>
                ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0)"
          proof
            fix bx
            assume bx: "bx \<in> Sigma B\<^sub>0 (\<lambda>x. if x = ?False then X\<^sub>0 else Y\<^sub>0)"
            have "fst bx = ?False \<or> fst bx = ?True"
              using B\<^sub>0 bij_betw_imp_surj_on bx by fastforce
            moreover have "fst bx = ?False \<Longrightarrow> snd bx \<in> X\<^sub>0"
              using bx by force
            moreover have "fst bx \<noteq> ?False \<Longrightarrow> snd bx \<in> Y\<^sub>0"
              using bx by force
            ultimately show "bx \<in> ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0)"
              by (metis Un_iff insertCI mem_Times_iff)
          qed
          show "({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0) \<subseteq>
                Sigma B\<^sub>0 (\<lambda>x. if x = ?False then X\<^sub>0 else Y\<^sub>0)"
            using B\<^sub>0 bij_betw_apply ne by fastforce
        qed
        moreover have "small (Sigma B\<^sub>0 (\<lambda>x. if x = ?False then X\<^sub>0 else Y\<^sub>0))"
          using X\<^sub>0 Y\<^sub>0 B\<^sub>0 small_sum_ax small_def by force
        ultimately show ?thesis by auto
      qed
      moreover have "bij_betw ?\<iota>
                       (({False} \<times> X) \<union> ({True} \<times> Y))
                       (({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0))"
      proof (intro bij_betwI)
        let ?\<iota>' = "\<lambda>z. if fst z = ?False then (False, inv_into X \<rho> (snd z))
                       else (True, inv_into Y \<sigma> (snd z))"
        show "?\<iota> \<in> ({False} \<times> X) \<union> ({True} \<times> Y) \<rightarrow> ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0)"
          using X\<^sub>0 Y\<^sub>0 bij_betw_def
          by (auto simp add: bij_betw_apply)
        show "?\<iota>' \<in> ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0) \<rightarrow> ({False} \<times> X) \<union> ({True} \<times> Y)"
        proof
          fix z
          assume z: "z \<in> ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0)"
          show "?\<iota>' z \<in> ({False} \<times> X) \<union> ({True} \<times> Y)"
            using z
            by (metis Un_iff X\<^sub>0 Y\<^sub>0 bij_betw_def inv_into_into mem_Sigma_iff ne prod.collapse
                singleton_iff)
        qed
        show "\<And>x. x \<in> {False} \<times> X \<union> {True} \<times> Y \<Longrightarrow> ?\<iota>' (?\<iota> x) = x"
        proof -
          fix x
          assume x: "x \<in> {False} \<times> X \<union> {True} \<times> Y"
          have "?\<iota> x \<in> ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0)"
            using X\<^sub>0 Y\<^sub>0 bij_betwE fst_conv mem_Times_iff x by fastforce
          thus "?\<iota>' (?\<iota> x) = x"
            using x X\<^sub>0 Y\<^sub>0 bij_betw_inv_into_left ne
            by auto[1] fastforce+
        qed
        show "\<And>y. y \<in> ({?False} \<times> X\<^sub>0) \<union> ({?True} \<times> Y\<^sub>0) \<Longrightarrow> ?\<iota> (?\<iota>' y) = y"
          using X\<^sub>0 Y\<^sub>0 bij_betw_inv_into_right ne by fastforce
      qed
      ultimately show ?thesis
        by (meson eqpoll_def eqpoll_trans small_def)
    qed

    lemma small_union:
    assumes X: "small X" and Y: "small Y"
    shows "small (X \<union> Y)"
    proof -
      have "lepoll (X \<union> Y) (({False} \<times> X) \<union> ({True} \<times> Y))"
      proof -
        let ?\<iota> = "\<lambda>z. if z \<in> X then (False, z) else (True, z)"
        have "?\<iota> \<in> X \<union> Y \<rightarrow> ({False} \<times> X) \<union> ({True} \<times> Y) \<and> inj_on ?\<iota> (X \<union> Y)"
          by (simp add: inj_on_def)
        thus ?thesis
          using lepoll_def' by blast
      qed
      moreover have "small (({False} \<times> X) \<union> ({True} \<times> Y))"
        using assms small_binary_sum by blast
      ultimately show ?thesis
        using lepoll_small by blast
    qed

    lemma small_Union_spc:
    assumes A\<^sub>0: "sml A\<^sub>0" and B: "\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> small (B x)"
    shows "small (\<Union>x\<in>A\<^sub>0. B x)"
    proof -
      have 1: "\<exists>B\<^sub>0. \<forall>x. x \<in> A\<^sub>0 \<longrightarrow> sml (B\<^sub>0 x) \<and> eqpoll (B x) (B\<^sub>0 x)"
        using A\<^sub>0 B small_def by meson
      obtain B\<^sub>0 where B\<^sub>0: "\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> sml (B\<^sub>0 x) \<and> eqpoll (B\<^sub>0 x) (B x)"
        using assms 1 eqpoll_sym by blast
      have 2: "\<exists>\<sigma>. \<forall>x. x \<in> A\<^sub>0 \<longrightarrow> bij_betw (\<sigma> x) (B\<^sub>0 x) (B x)"
        using B\<^sub>0 eqpoll_def
        by (meson \<open>\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> sml (B\<^sub>0 x) \<and> B\<^sub>0 x \<approx> B x\<close> eqpoll_def)
      obtain \<sigma> where \<sigma>: "\<And>x. x \<in> A\<^sub>0 \<Longrightarrow> bij_betw (\<sigma> x) (B\<^sub>0 x) (B x)"
        using 2 by blast
      have "small (Sigma A\<^sub>0 B\<^sub>0)"
        using assms small_sum_ax [of A\<^sub>0 B\<^sub>0] B\<^sub>0 small_def by blast
      moreover have "lepoll (\<Union>x\<in>A\<^sub>0. B x) (Sigma A\<^sub>0 B\<^sub>0)"
      proof -
        have "(\<lambda>z. \<sigma> (fst z) (snd z)) ` Sigma A\<^sub>0 B\<^sub>0 = (\<Union>x\<in>A\<^sub>0. B x)"
        proof
          show "(\<lambda>z. \<sigma> (fst z) (snd z)) ` Sigma A\<^sub>0 B\<^sub>0 \<subseteq> \<Union> (B ` A\<^sub>0)"
            unfolding Sigma_def
            using \<sigma> bij_betwE by fastforce
          show "\<Union> (B ` A\<^sub>0) \<subseteq> (\<lambda>z. \<sigma> (fst z) (snd z)) ` Sigma A\<^sub>0 B\<^sub>0"
          proof
            fix z
            assume z: "z \<in> (\<Union> (B ` A\<^sub>0))"
            obtain x where x: "x \<in> A\<^sub>0 \<and> z \<in> B x"
              using z by blast
            have "(x, inv_into (B\<^sub>0 x) (\<sigma> x) z) \<in> Sigma A\<^sub>0 B\<^sub>0"
              by (metis SigmaI \<sigma> bij_betw_def inv_into_into x)
            moreover have "(\<lambda>z. \<sigma> (fst z) (snd z)) (x, inv_into (B\<^sub>0 x) (\<sigma> x) z) = z"
              using \<sigma> bij_betw_inv_into_right x by fastforce
            ultimately show "z \<in> (\<lambda>z. \<sigma> (fst z) (snd z)) ` Sigma A\<^sub>0 B\<^sub>0"
              by force
          qed
        qed
        thus ?thesis
          by (metis image_lepoll)
      qed
      ultimately show ?thesis
        using lepoll_small by blast
    qed

    lemma small_Union [simp, intro]:
    assumes A: "small A" and B: "\<And>x. x \<in> A \<Longrightarrow> small (B x)"
    shows "small (\<Union>x\<in>A. B x)"
    proof -
      obtain A\<^sub>0 \<rho> where A\<^sub>0: "sml A\<^sub>0 \<and> bij_betw \<rho> A\<^sub>0 A"
        using assms(1) small_def eqpoll_def eqpoll_sym by blast
      have "eqpoll (\<Union>x\<in>A. B x) (\<Union>x\<in>A\<^sub>0. (B \<circ> \<rho>) x)"
        by (metis A\<^sub>0 bij_betw_def eqpoll_refl image_comp)
      moreover have "small (\<Union>x\<in>A\<^sub>0. (B \<circ> \<rho>) x)"
        by (metis A\<^sub>0 B bij_betwE comp_apply small_Union_spc)
      ultimately show ?thesis
        using eqpoll_imp_lepoll lepoll_small by blast
    qed

    text\<open>
      The @{locale small_sum} locale subsumes the @{locale small_product} locale,
      in the sense that any notion of smallness that satisfies @{locale small_sum}
      also satisfies @{locale small_product}.
    \<close>

    sublocale small_product
    proof
      show "\<And>X Y. \<lbrakk>sml X; sml Y\<rbrakk> \<Longrightarrow> \<exists>Z. sml Z \<and> X \<times> Y \<approx> Z"
        by (simp add: small_sum_ax)
    qed

  end

  section "Smallness of Powersets"

  text \<open>
    The locale \<open>small_powerset\<close> is satisfied by notions of smallness for which the set of
    all subsets of a small set is again small.
  \<close>

  locale small_powerset =
    smallness +
  assumes small_powerset_ax: "sml X \<Longrightarrow> \<exists>PX. sml PX \<and> eqpoll (Pow X) PX"
  begin

    lemma small_powerset:
    assumes "small X"
    shows "small (Pow X)"
      using assms small_powerset_ax
      by (meson bij_betw_Pow eqpoll_def eqpoll_trans small_def)

    lemma large_UNIV:
    shows "\<not> small (UNIV :: 'a set)"
      using small_powerset_ax Cantors_theorem
      by (metis Pow_UNIV UNIV_I eqpoll_iff_bijections small_iff_sml surjI)

  end

  section "Smallness of the Set of Natural Numbers"

  text \<open>
    The locale \<open>small_nat\<close> is satisfied by notions of smallness for which the set of
    natural numbers is small.
  \<close>

  locale small_nat =
    smallness +
  assumes small_nat_ax: "\<exists>X. sml X \<and> eqpoll X (UNIV :: nat set)"
  begin

    lemma small_nat:
    shows "small (UNIV :: nat set)"
      using small_nat_ax small_def eqpoll_sym by auto

  end

  section "Smallness of Function Spaces"

  text \<open>
    The objective of this section is to define a locale that is satisfied by notions of
    smallness for which ``the set of functions between two small sets is small.''
    This is complicated in HOL by the requirement that all functions be total,
    which forces us to define the value of a function at points outside of what we
    would consider to be its domain.  If we don't impose some restriction on the values
    taken on by a function outside of its domain, then the set of functions between
    a domain and codomain set could be large, even if the domain and codomain sets
    themselves are small.  We could limit the possible variation by restricting our
    consideration to ``extensional'' functions; \textit{i.e.}~those that take on a
    particular default value outside of their domain, but it becomes awkward if we
    have to make an \textit{a priori} choice of what this value should be.

    The approach we take here is to define the notion of a ``popular value'' of a function.
    This will be a value, in the function's range, whose preimage is a large set.
    The idea here is that the default values of extensional functions will typically
    have their default values as popular values (though this is not necessarily the
    case, as a function whose domain type is small will not have any popular values
    according to this definition).  We then define a ``small function'' to be a function
    whose range is a small set and which has at most one popular value.
    The ``essential domain'' of small function is the set of arguments on which the
    value of the function is not a popular value.  Then we can consistently require of
    a smallness notion that, if \<open>A\<close> and \<open>B\<close> are small sets, that the set of functions
    whose essential domains are contained in \<open>A\<close> and whose ranges are contained in \<open>B\<close>,
    is again small.
  \<close>

  subsection "Small Functions"

  context smallness
  begin

    abbreviation popular_value :: "('b \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool"
    where "popular_value F y \<equiv> \<not> small {x. F x = y}"

    definition some_popular_value :: "('b \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "some_popular_value F \<equiv> SOME y. popular_value F y"

    lemma popular_value_some_popular_value:
    assumes "\<exists>y. popular_value F y"
    shows "popular_value F (some_popular_value F)"
      using assms someI_ex [of "\<lambda>y. popular_value F y"] some_popular_value_def by metis

    abbreviation at_most_one_popular_value
    where "at_most_one_popular_value F \<equiv> \<exists>\<^sub>\<le>\<^sub>1 y. popular_value F y"

    definition small_function
    where "small_function F \<equiv> small (range F) \<and> at_most_one_popular_value F"

    lemma small_functionI [intro]:
    assumes "small (range f)" and "at_most_one_popular_value f"
    shows "small_function f"
      using assms small_function_def by blast

    lemma small_functionD [dest]:
    assumes "small_function f"
    shows "small (range f)" and "at_most_one_popular_value f"
      using assms small_function_def by auto

  end

  text\<open>
    If there are small sets of arbitrarily large finite cardinality, then the preimage
    of a popular value of a function must be an infinite set (in particular, it must be
    nonempty, since the empty set must be small).  We can derive various useful consequences
    of this fairly lax assumption.
  \<close>

  context small_finite
  begin

    lemma popular_value_in_range:
    assumes "popular_value F v"
    shows "v \<in> range F"
      using assms not_finite_existsD small_finite by auto

    lemma small_function_const:
    shows "small_function (\<lambda>x. y)"
      by (auto simp add: Uniq_def small_finite)

    definition inv_into\<^sub>E
    where "inv_into\<^sub>E X f \<equiv> \<lambda>y. if y \<in> f ` X then inv_into X f y
                               else SOME x. popular_value f (f x)"

    lemma small_function_inv_into\<^sub>E:
    assumes "small_function f" and "inj_on f X"
    shows "small_function (inv_into\<^sub>E X f)"
    proof
      show "small (range (inv_into\<^sub>E X f))"
      proof -
        have "small X"
          by (meson assms(1,2) small_functionD(1) small_image_iff smaller_than_small
              subset_UNIV subset_image_iff)
        moreover have "range (inv_into\<^sub>E X f) \<subseteq> X \<union> {SOME x. popular_value f (f x)}"
          unfolding inv_into\<^sub>E_def
          using assms(2) inf_sup_aci(5) by auto
        ultimately show ?thesis
          using smaller_than_small by auto
      qed
      show "at_most_one_popular_value (inv_into\<^sub>E X f)"
      proof -
        have "\<And>x. popular_value (inv_into\<^sub>E X f) x \<Longrightarrow> x = (SOME x. popular_value f (f x))"
        proof -
          fix x
          assume x: "popular_value (inv_into\<^sub>E X f) x"
          have "f x \<in> {y. y \<in> f ` X \<and> x = inv_into X f y} \<or> x = (SOME x. popular_value f (f x))"
            using assms x
            unfolding inv_into\<^sub>E_def
            using not_finite_existsD small_finite  by fastforce
          moreover have "x \<noteq> (SOME x. popular_value f (f x)) \<Longrightarrow>
                           f x \<notin> {y. y \<in> f ` X \<and> x = inv_into X f y}"
          proof -
            assume 1: "x \<noteq> (SOME x. popular_value f (f x))"
            have "small {y. y \<in> f ` X \<and> x = inv_into X f y}"
              using assms
              by (metis (no_types, lifting) image_subset_iff mem_Collect_eq rangeI
                  small_functionD(1) smaller_than_small subsetI)
            thus ?thesis
              using x 1
              unfolding inv_into\<^sub>E_def
              by (simp add: Collect_mono smallness.smaller_than_small smallness_axioms)
          qed
          ultimately show "x = (SOME x. popular_value f (f x))" by blast
        qed
        thus ?thesis
          using Uniq_def by blast
      qed
    qed

  end

  context small_sum
  begin

    lemma small_function_comp:
    assumes "small_function f" and "small_function g"
    shows "small_function (g \<circ> f)"
    proof
      show "small (range (g \<circ> f))"
        by (metis assms(1) fun.set_map small_image small_functionD(1))
      show "at_most_one_popular_value (g \<circ> f)"
      proof -
        have *: "\<And>z. popular_value (g \<circ> f) z \<Longrightarrow> \<exists>y. popular_value f y \<and> g y = z"
        proof -
          fix z
          assume z: "popular_value (g \<circ> f) z"
          have "\<not> small {x. g (f x) = z}"
            using z by auto
          moreover have "{x. g (f x) = z} = (\<Union>y\<in>range f \<inter> {y. g y = z}. {x. f x = y})"
            by auto
          moreover have "small (range f \<inter> {y. g y = z})"
            using assms(1) small_functionD(1) smaller_than_small by force
          ultimately have "\<exists>y. y \<in> range f \<inter> {y. g y = z} \<and> popular_value f y"
            by auto
          thus "\<exists>y. popular_value f y \<and> g y = z" by blast
        qed
        show ?thesis
        proof
          fix y y'
          assume y: "popular_value (g \<circ> f) y" and y': "popular_value (g \<circ> f) y'"
          have "\<exists>x. popular_value f x \<and> g x = y"
            using y * by blast
          moreover have "\<exists>x. popular_value f x \<and> g x = y'"
            using y' * by blast
          ultimately show "y = y'"
            using assms(2)
            by (metis (mono_tags, lifting) assms(1) small_functionD(2) the1_equality')
        qed
      qed
    qed

    text\<open>
      In the present context, a small function has a popular value if and only if its domain
      type is large.  This simplifies special cases that concern whether or not a function
      happens to have any popular value at all.
    \<close>

    lemma ex_popular_value_iff:
    assumes "small_function (F :: 'b \<Rightarrow> 'c)"
    shows "(\<exists>v. popular_value F v) \<longleftrightarrow> \<not> small (UNIV :: 'b set)"
    proof
      show "\<exists>v. popular_value F v \<Longrightarrow> \<not> small (UNIV :: 'b set)"
        using smaller_than_small by blast
      have "\<not> (\<exists>v. popular_value F v) \<Longrightarrow> small (UNIV :: 'b set)"
      proof -
        assume "\<not> (\<exists>y. popular_value F y)"
        hence "\<And>y. small {x. F x = y}"
          by blast
        moreover have "UNIV = (\<Union>y\<in>range F. {x. F x = y})"
          by auto
        ultimately show "small (UNIV :: 'b set)"
          using assms(1) small_function_def by (metis small_Union)
      qed
      thus "\<not> small (UNIV :: 'b set) \<Longrightarrow> \<exists>v. popular_value F v"
        by blast
    qed

    text\<open>
      A consequence is that the preimage of the set of all unpopular values of a function
      is small.
    \<close>

    lemma small_preimage_unpopular:
    fixes F :: "'b \<Rightarrow> 'c"
    assumes "small_function F"
    shows "small {x. F x \<noteq> some_popular_value F}"
    proof (cases "\<exists>y. popular_value F y")
      assume 1: "\<not> (\<exists>y. popular_value F y)"
      thus ?thesis
        using assms ex_popular_value_iff smaller_than_small by blast
      next
      assume 1: "\<exists>y. popular_value F y"
      have "popular_value F (some_popular_value F)"
        using 1 popular_value_some_popular_value by metis
      hence 2: "\<And>y. y \<noteq> some_popular_value F \<Longrightarrow> small {x. F x = y}"
        using assms
        unfolding small_function_def
        by (meson Uniq_D)
      moreover have "{x. F x \<noteq> some_popular_value F} =
                     (\<Union>y\<in>{y. y \<in> range F \<and> y \<noteq> some_popular_value F}. {x. F x = y})"
        by auto
      ultimately show ?thesis
        using assms
        unfolding small_function_def
        by auto
    qed

    text\<open>
      Here we are working toward showing that a small function has a ``small encoding'',
      which consists of its graph for arguments that map to non-popular values,
      paired with the single popular value it has on all other arguments.
    \<close>

    abbreviation SF_Dom
    where "SF_Dom f \<equiv> {x. \<not> popular_value f (f x)}"

    abbreviation SF_Rng
    where "SF_Rng f \<equiv> f ` SF_Dom f"

    abbreviation SF_Grph
    where "SF_Grph f \<equiv> (\<lambda>x. (x, f x)) ` SF_Dom f"

    abbreviation the_PV
    where "the_PV f \<equiv> THE y. popular_value f y"

    lemma small_SF_Dom:
    assumes "small_function f"
    shows "small (SF_Dom f)"
    proof -
      let ?F = "\<lambda>y. {x. f x = y}"
      have "SF_Dom f = (\<Union>y \<in> SF_Rng f. ?F y)"
      proof
        show "SF_Dom f \<subseteq> (\<Union>y \<in> SF_Rng f. ?F y)"
           by blast
       show "(\<Union>y \<in> SF_Rng f. ?F y) \<subseteq> SF_Dom f"
        proof
          fix x
          assume x: "x \<in> (\<Union>y \<in> SF_Rng f. ?F y)"
          obtain S y where S: "x \<in> S \<and> y \<in> SF_Rng f \<and> S = {x. f x = y}"
            using x by force
          show "x \<in> SF_Dom f"
            using S by fastforce
        qed
      qed
      moreover have "\<And>y. y \<in> SF_Rng f \<Longrightarrow> small (?F y)"
        using assms by blast
      ultimately show ?thesis
        using small_Union [of "SF_Rng f" ?F]
        by (metis assms image_mono small_functionD(1) smaller_than_small subset_UNIV)
    qed

    lemma small_SF_Rng:
    assumes "small_function f"
    shows "small (SF_Rng f)"
      using assms small_SF_Dom by blast

    lemma small_SF_Grph:
    assumes "small_function f"
    shows "small (SF_Grph f)"
      using assms small_SF_Dom by blast

    lemma small_function_expansion:
    assumes "small_function f"
    shows "f = (\<lambda>x. if x \<in> fst ` SF_Grph f then (THE y. (x, y) \<in> SF_Grph f) else the_PV f)"
    proof
      fix x
      show "f x = (if x \<in> fst ` SF_Grph f then (THE y. (x, y) \<in> SF_Grph f) else the_PV f)"
      proof (cases "x \<in> SF_Dom f")
        show "x \<notin> SF_Dom f \<Longrightarrow> ?thesis"
        proof -
          assume "x \<notin> SF_Dom f"
          hence "f x = the_PV f"
            using assms the1_equality' by fastforce
          thus ?thesis
            by (simp add: image_iff)
        qed
        show "x \<in> SF_Dom f \<Longrightarrow> ?thesis"
          by (simp add: image_iff)
      qed
    qed

  end

  subsection "Small Funcsets"

  locale small_funcset =
    small_sum +
    small_powerset
  begin

    text\<open>
      For a suitable definition of ``between'', the set of small functions between
      small sets is small.
    \<close>
  
    lemma small_funcset:
    assumes "small X" and "small Y"
    shows "small {f. small_function f \<and> SF_Dom f \<subseteq> X \<and> range f \<subseteq> Y}"
    proof -
      let ?Rep = "\<lambda>f. (SF_Grph f, Collect (popular_value f))"
      let ?SF = "{f. small_function f \<and> SF_Dom f \<subseteq> X \<and> range f \<subseteq> Y}"
      have *: "\<And>f x. \<lbrakk>f \<in> ?SF; x \<notin> SF_Dom f\<rbrakk> \<Longrightarrow> {f x} = Collect (popular_value f)"
      proof -
        fix f x
        assume f: "f \<in> ?SF" and x: "x \<notin> SF_Dom f"
        show "{f x} = Collect (popular_value f)"
        proof -
          have 1: "popular_value f (f x)"
            using x by blast
          have "\<exists>!y. popular_value f y"
          proof -
            have "\<exists>y. popular_value f y"
              using 1 by blast
            moreover have "\<And>y y'. \<lbrakk>popular_value f y; popular_value f y'\<rbrakk> \<Longrightarrow> y = y'"
              using f Uniq_def small_functionD(2)
              by (metis (mono_tags, lifting) mem_Collect_eq)
            ultimately show ?thesis by blast
          qed
          thus ?thesis
            using f 1 by blast
        qed
      qed
      have "small (?Rep ` ?SF)"
      proof -
        have "?Rep \<in> ?SF \<rightarrow> Pow (X \<times> Y) \<times> Pow Y"
          using popular_value_in_range by fastforce
        moreover have "small (Pow (X \<times> Y) \<times> Pow Y)"
          using assms by (simp add: small_powerset)
        ultimately show ?thesis
          by (simp add: image_subset_iff_funcset smaller_than_small)
      qed
      moreover have "inj_on ?Rep ?SF"
      proof
        fix f g :: "'b \<Rightarrow> 'c"
        assume f: "f \<in> ?SF" and g: "g \<in> ?SF"
        assume eq: "?Rep f = ?Rep g"
        show "f = g"
        proof
          fix x
          show "f x = g x"
          proof (cases "x \<in> SF_Dom f")
            show "x \<notin> SF_Dom f \<Longrightarrow> ?thesis"
            proof -
              assume x: "x \<notin> SF_Dom f"
              have "{f x} = Collect (popular_value f)"
                using f x * by blast
              also have "... = Collect (popular_value g)"
                using eq by force
              also have "... = {g x}"
                using g x eq * [of g x] by blast
              finally show "f x = g x" by blast
            qed
            show "x \<in> SF_Dom f \<Longrightarrow> ?thesis"
              using f g eq small_function_expansion by blast
          qed
        qed
      qed
      ultimately show ?thesis
        using small_image_iff by blast
    qed
  
  end

  section "Smallness of Sets of Lists"

  text\<open>
    A notion of smallness that is preserved under sum and powerset, and in addition declares
    the set of natural numbers to be small, is sufficiently inclusive as to include any
    set whose existence is provable in ZFC.  So it is not a surprise that we can show,
    for example, that the set of lists with elements in a given small set is again small.
    We do not use this particular fact in the present development, but we will have a use for
    it in a subsequent article.
  \<close>

  locale small_funcset_and_nat =
    small_funcset +
    small_nat
  begin

    definition list_as_fn :: "'b list \<Rightarrow> nat \<Rightarrow> 'b option"
    where "list_as_fn l n = (if n \<ge> length l then None else Some (l ! n))"
  
    lemma inj_list_as_fn:
    shows "inj list_as_fn"
    proof
      fix x y :: "'b list"
      have 1: "\<And>l :: 'b list. list_as_fn l (length l) = None"
        unfolding list_as_fn_def by simp
      assume eq: "list_as_fn x = list_as_fn y"
      have "length x = length y"
        using eq 1
        by (metis (no_types, lifting) list_as_fn_def nle_le not_Some_eq)
      moreover have "\<And>n. n < length x \<Longrightarrow> x ! n = y ! n"
        using eq list_as_fn_def
        by (metis calculation leD option.inject)
      ultimately show "x = y"
        using nth_equalityI by blast
    qed

    lemma small_function_list_as_fn:
    shows "small_function (list_as_fn l)"
      using Uniq_def small_function_def small_nat smaller_than_small by fastforce
  
    lemma small_listset:
    assumes "small Y"
    shows "small {l. List.set l \<subseteq> Y}"
    proof -
      let ?SF = "\<lambda>f. small_function f \<and> SF_Dom f \<subseteq> (UNIV :: nat set) \<and>
                     range f \<subseteq> Some ` Y \<union> {None}"
      have "list_as_fn ` {l. List.set l \<subseteq> Y} \<subseteq> Collect ?SF"
      proof
        fix f
        assume f: "f \<in> list_as_fn ` {l. List.set l \<subseteq> Y}"
        show "f \<in> Collect ?SF"
          using f small_function_list_as_fn
          unfolding list_as_fn_def
          apply auto
          by fastforce
      qed
      moreover have "small (Collect ?SF)"
        using assms small_nat small_funcset [of "UNIV :: nat set" "Some ` Y \<union> {None}"]
        by auto
      ultimately show ?thesis
        using small_image_iff [of list_as_fn "{l. list.set l \<subseteq> Y}"] inj_list_as_fn
          smaller_than_small
        by (metis (mono_tags, lifting) injD inj_onI)
    qed

  end

end
