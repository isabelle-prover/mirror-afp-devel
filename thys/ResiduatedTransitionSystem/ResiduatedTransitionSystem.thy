chapter "Residuated Transition Systems"

theory ResiduatedTransitionSystem
imports Main
begin

  section "Basic Definitions and Properties"

  subsection "Partial Magmas"

  text \<open>
    A \emph{partial magma} consists simply of a partial binary operation.
    We represent the partiality by assuming the existence of a unique value \<open>null\<close>
    that behaves as a zero for the operation.
  \<close>

  (*
   * TODO: This is currently identical with Category3.partial_magma.
   * This may get to be a problem for future theories that develop category-theoretic
   * properties of residuated transitions, but for now I don't want this theory
   * to depend on the Category3 session just because of this.
   *)
  locale partial_magma =
  fixes OP :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ex_un_null: "\<exists>!n. \<forall>t. OP n t = n \<and> OP t n = n"
  begin

    definition null :: 'a
    where "null = (THE n. \<forall>t. OP n t = n \<and> OP t n = n)"

    lemma null_eqI:
    assumes "\<And>t. OP n t = n \<and> OP t n = n"
    shows "n = null"
      using assms null_def ex_un_null the1_equality [of "\<lambda>n. \<forall>t. OP n t = n \<and> OP t n = n"]
      by auto
    
    lemma null_is_zero [simp]:
    shows "OP null t = null" and "OP t null = null"
      using null_def ex_un_null theI' [of "\<lambda>n. \<forall>t. OP n t = n \<and> OP t n = n"]
      by auto

  end

  subsection "Residuation"

    text \<open>
      A \emph{residuation} is a partial binary operation subject to three axioms.
      The first, \<open>con_sym_ax\<close>, states that the domain of a residuation is symmetric.
      The second, \<open>con_imp_arr_resid\<close>, constrains the results of residuation either to be \<open>null\<close>,
      which indicates inconsistency, or something that is self-consistent, which we will
      define below to be an ``arrow''.
      The ``cube axiom'', \<open>cube_ax\<close>, states that if \<open>v\<close> can be transported by residuation
      around one side of the ``commuting square'' formed by \<open>t\<close> and \<open>u \ t\<close>, then it can also
      be transported around the other side, formed by \<open>u\<close> and \<open>t \ u\<close>, with the same result.
    \<close>

  type_synonym 'a resid = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  locale residuation = partial_magma resid
  for resid :: "'a resid" (infix "\\" 70) +
  assumes con_sym_ax: "t \\ u \<noteq> null \<Longrightarrow> u \\ t \<noteq> null"
  and con_imp_arr_resid: "t \\ u \<noteq> null \<Longrightarrow> (t \\ u) \\ (t \\ u) \<noteq> null"
  and cube_ax: "(v \\ t) \\ (u \\ t) \<noteq> null \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
  begin

    text \<open>
      The axiom \<open>cube_ax\<close> is equivalent to the following unconditional form.
      The locale assumptions use the weaker form to avoid having to treat
      the case \<open>(v \ t) \ (u \ t) = null\<close> specially for every interpretation.
    \<close>

    lemma cube:
    shows "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      using cube_ax by metis

    text \<open>
      We regard \<open>t\<close> and \<open>u\<close> as \emph{consistent} if the residuation \<open>t \ u\<close> is defined.
      It is convenient to make this a definition, with associated notation.
    \<close>

    definition con  (infix "\<frown>" 50)
    where "t \<frown> u \<equiv> t \\ u \<noteq> null"

    lemma conI [intro]:
    assumes "t \\ u \<noteq> null"
    shows "t \<frown> u"
      using assms con_def by blast

    lemma conE [elim]:
    assumes "t \<frown> u"
    and "t \\ u \<noteq> null \<Longrightarrow> T"
    shows T
      using assms con_def by simp

    lemma con_sym:
    assumes "t \<frown> u"
    shows "u \<frown> t"
      using assms con_def con_sym_ax by blast

    text \<open>
      We call \<open>t\<close> an \emph{arrow} if it is self-consistent.
    \<close>

    definition arr
    where "arr t \<equiv> t \<frown> t"

    lemma arrI [intro]:
    assumes "t \<frown> t"
    shows "arr t"
      using assms arr_def by simp

    lemma arrE [elim]:
    assumes "arr t"
    and "t \<frown> t \<Longrightarrow> T"
    shows T
      using assms arr_def by simp

    lemma not_arr_null [simp]:
    shows "\<not> arr null"
      by (auto simp add: con_def)

    lemma con_implies_arr:
    assumes "t \<frown> u"
    shows "arr t" and "arr u"
      using assms
      by (metis arrI con_def con_imp_arr_resid cube null_is_zero(2))+

    lemma arr_resid [simp]:
    assumes "t \<frown> u"
    shows "arr (t \\ u)"
      using assms con_imp_arr_resid by blast

    lemma arr_resid_iff_con:
    shows "arr (t \\ u) \<longleftrightarrow> t \<frown> u"
      by auto

    lemma con_arr_self [simp]:
    assumes "arr f"
    shows "f \<frown> f"
      using assms arrE by auto

    lemma not_con_null [simp]:
    shows "con null t = False" and "con t null = False"
      by auto

    text \<open>
      The residuation of an arrow along itself is the \emph{canonical target} of the arrow.
    \<close>

    definition trg
    where "trg t \<equiv> t \\ t"

    lemma resid_arr_self:
    shows "t \\ t = trg t"
      using trg_def by auto

    text \<open>
      An \emph{identity} is an arrow that is its own target.
    \<close>

    definition ide
    where "ide a \<equiv> a \<frown> a \<and> a \\ a = a"

    lemma ideI [intro]:
    assumes "a \<frown> a" and "a \\ a = a"
    shows "ide a"
      using assms ide_def by auto

    lemma ideE [elim]:
    assumes "ide a"
    and "\<lbrakk>a \<frown> a; a \\ a = a\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms ide_def by blast

    lemma ide_implies_arr [simp]:
    assumes "ide a"
    shows "arr a"
      using assms by blast

    lemma not_ide_null [simp]:
    shows "ide null = False"
      by auto

  end

  subsection "Residuated Transition System"

  text \<open>
    A \emph{residuated transition system} consists of a residuation subject to
    additional axioms that concern the relationship between identities and residuation.
    These axioms make it possible to sensibly associate with each arrow certain nonempty
    sets of identities called the \emph{sources} and \emph{targets} of the arrow.
    Axiom \<open>ide_trg\<close> states that the canonical target \<open>trg t\<close> of an arrow \<open>t\<close> is an identity.
    Axiom \<open>resid_arr_ide\<close> states that identities are right units for residuation,
    when it is defined.
    Axiom \<open>resid_ide_arr\<close> states that the residuation of an identity along an arrow is
    again an identity, assuming that the residuation is defined.
    Axiom \<open>con_imp_coinitial_ax\<close> states that if arrows \<open>t\<close> and \<open>u\<close> are consistent,
    then there is an identity that is consistent with both of them (\emph{i.e.}~they
    have a common source).
    Axiom \<open>con_target\<close> states that an identity of the form \<open>t \ u\<close>
    (which may be regarded as a ``target'' of \<open>u\<close>) is consistent with any other
    arrow \<open>v \ u\<close> obtained by residuation along \<open>u\<close>.
    We note that replacing the premise \<open>ide (t \ u)\<close> in this axiom by either \<open>arr (t \ u)\<close>
    or \<open>t \<frown> u\<close> would result in a strictly stronger statement.
  \<close>

  locale rts = residuation +
  assumes ide_trg [simp]: "arr t \<Longrightarrow> ide (trg t)"
  and resid_arr_ide: "\<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
  and resid_ide_arr [simp]: "\<lbrakk>ide a; a \<frown> t\<rbrakk> \<Longrightarrow> ide (a \\ t)"
  and con_imp_coinitial_ax: "t \<frown> u \<Longrightarrow> \<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
  and con_target: "\<lbrakk>ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
  begin

    text \<open>
      We define the \emph{sources} of an arrow \<open>t\<close> to be the identities that
      are consistent with \<open>t\<close>.
    \<close>

    definition sources
    where "sources t = {a. ide a \<and> t \<frown> a}"

    text \<open>
      We define the \emph{targets} of an arrow \<open>t\<close> to be the identities that
      are consistent with the canonical target \<open>trg t\<close>.
    \<close>

    definition targets
    where "targets t = {b. ide b \<and> trg t \<frown> b}"

    lemma in_sourcesI [intro, simp]:
    assumes "ide a" and "t \<frown> a"
    shows "a \<in> sources t"
      using assms sources_def by simp

    lemma in_sourcesE [elim]:
    assumes "a \<in> sources t"
    and "\<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms sources_def by auto

    lemma in_targetsI [intro, simp]:
    assumes "ide b" and "trg t \<frown> b"
    shows "b \<in> targets t"
      using assms targets_def resid_arr_self by simp

    lemma in_targetsE [elim]:
    assumes "b \<in> targets t"
    and "\<lbrakk>ide b; trg t \<frown> b\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms targets_def resid_arr_self by force

    lemma trg_in_targets:
    assumes "arr t"
    shows "trg t \<in> targets t"
      using assms
      by (meson ideE ide_trg in_targetsI)

    lemma source_is_ide:
    assumes "a \<in> sources t"
    shows "ide a"
      using assms by blast

    lemma target_is_ide:
    assumes "a \<in> targets t"
    shows "ide a"
      using assms by blast

    text \<open>
      Consistent arrows have a common source.
    \<close>

    lemma con_imp_common_source:
    assumes "t \<frown> u"
    shows "sources t \<inter> sources u \<noteq> {}"
      using assms
      by (meson disjoint_iff in_sourcesI con_imp_coinitial_ax con_sym)

    text \<open>
       Arrows are characterized by the property of having a nonempty set of sources,
       or equivalently, by that of having a nonempty set of targets.
    \<close>

    lemma arr_iff_has_source:
    shows "arr t \<longleftrightarrow> sources t \<noteq> {}"
      using con_imp_common_source con_implies_arr(1) sources_def by blast

    lemma arr_iff_has_target:
    shows "arr t \<longleftrightarrow> targets t \<noteq> {}"
      using trg_def trg_in_targets by fastforce

    text \<open>
      The residuation of a source of an arrow along that arrow gives a target
      of the same arrow.
      However, it is \emph{not} true that every target of an arrow \<open>t\<close> is of the
      form \<open>u \ t\<close> for some \<open>u\<close> with \<open>t \<frown> u\<close>.
    \<close>

    lemma resid_source_in_targets:
    assumes "a \<in> sources t"
    shows "a \\ t \<in> targets t"
      by (metis arr_resid assms con_target con_sym resid_arr_ide ide_trg
          in_sourcesE resid_ide_arr in_targetsI resid_arr_self)

    text \<open>
      Residuation along an identity reflects identities.
    \<close>

    lemma ide_backward_stable:
    assumes "ide a" and "ide (t \\ a)"
    shows "ide t"
      by (metis assms ideE resid_arr_ide arr_resid_iff_con)

    lemma resid_reflects_con:
    assumes "t \<frown> v" and "u \<frown> v" and "t \\ v \<frown> u \\ v"
    shows "t \<frown> u"
      using assms cube
      by (elim conE) auto

    lemma con_transitive_on_ide:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<lbrakk>a \<frown> b; b \<frown> c\<rbrakk> \<Longrightarrow> a \<frown> c"
      using assms
      by (metis resid_arr_ide con_target con_sym)

    lemma sources_are_con:
    assumes "a \<in> sources t" and "a' \<in> sources t"
    shows "a \<frown> a'"
      using assms
      by (metis (no_types, lifting) CollectD con_target con_sym resid_ide_arr
          sources_def resid_reflects_con)
 
    lemma sources_con_closed:
    assumes "a \<in> sources t" and "ide a'" and "a \<frown> a'"
    shows "a' \<in> sources t"
      using assms
      by (metis (no_types, lifting) con_target con_sym resid_arr_ide
          mem_Collect_eq sources_def)

    lemma sources_eqI:
    assumes "sources t \<inter> sources t' \<noteq> {}"
    shows "sources t = sources t'"
      using assms sources_def sources_are_con sources_con_closed by blast (* 3 sec *)

    lemma targets_are_con:
    assumes "b \<in> targets t" and "b' \<in> targets t"
    shows "b \<frown> b'"
      using assms sources_are_con sources_def targets_def by blast

    lemma targets_con_closed:
    assumes "b \<in> targets t" and "ide b'" and "b \<frown> b'"
    shows "b' \<in> targets t"
      using assms sources_con_closed sources_def targets_def by blast

    lemma targets_eqI:
    assumes "targets t \<inter> targets t' \<noteq> {}"
    shows "targets t = targets t'"
      using assms targets_def targets_are_con targets_con_closed by blast (* 2 sec *)

    text \<open>
      Arrows are \emph{coinitial} if they have a common source, and \emph{coterminal}
      if they have a common target.
    \<close>

    definition coinitial
    where "coinitial t u \<equiv> sources t \<inter> sources u \<noteq> {}"

    definition coterminal
    where "coterminal t u \<equiv> targets t \<inter> targets u \<noteq> {}"

    lemma coinitialI [intro]:
    assumes "arr t" and "sources t = sources u"
    shows "coinitial t u"
      using assms coinitial_def arr_iff_has_source by simp

    lemma coinitialE [elim]:
    assumes "coinitial t u"
    and "\<lbrakk>arr t; arr u; sources t = sources u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms coinitial_def sources_eqI arr_iff_has_source by auto

    lemma con_imp_coinitial:
    assumes "t \<frown> u"
    shows "coinitial t u"
      using assms
      by (simp add: coinitial_def con_imp_common_source)

    lemma coinitial_iff:
    shows "coinitial t t' \<longleftrightarrow> arr t \<and> arr t' \<and> sources t = sources t'"
      by (metis arr_iff_has_source coinitial_def inf_idem sources_eqI)

    lemma coterminal_iff:
    shows "coterminal t t' \<longleftrightarrow> arr t \<and> arr t' \<and> targets t = targets t'"
      by (metis arr_iff_has_target coterminal_def inf_idem targets_eqI)

    lemma coterminal_iff_con_trg:
    shows "coterminal t u \<longleftrightarrow> trg t \<frown> trg u"
      by (metis coinitial_iff con_imp_coinitial coterminal_iff in_targetsE trg_in_targets
          resid_arr_self arr_resid_iff_con sources_def targets_def)

    lemma coterminalI [intro]:
    assumes "arr t" and "targets t = targets u"
    shows "coterminal t u"
      using assms coterminal_iff arr_iff_has_target by auto

    lemma coterminalE [elim]:
    assumes "coterminal t u"
    and "\<lbrakk>arr t; arr u; targets t = targets u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms coterminal_iff by auto

    lemma sources_resid [simp]:
    assumes "t \<frown> u"
    shows "sources (t \\ u) = targets u"
      unfolding targets_def trg_def
      using assms conI conE
      by (metis con_imp_arr_resid assms coinitial_iff con_imp_coinitial
          cube ex_un_null sources_def)

    lemma targets_resid_sym:
    assumes "t \<frown> u"
    shows "targets (t \\ u) = targets (u \\ t)"
      using assms
      apply (intro targets_eqI)
      by (metis (no_types, opaque_lifting) assms cube inf_idem arr_iff_has_target arr_def
          arr_resid_iff_con sources_resid)

    text \<open>
      Arrows \<open>t\<close> and \<open>u\<close> are \emph{sequential} if the set of targets of \<open>t\<close> equals
      the set of sources of \<open>u\<close>.
    \<close>

    definition seq
    where "seq t u \<equiv> arr t \<and> arr u \<and> targets t = sources u"

    lemma seqI [intro]:
    shows "\<lbrakk>arr t; targets t = sources u\<rbrakk> \<Longrightarrow> seq t u"
    and "\<lbrakk>arr u; targets t = sources u\<rbrakk> \<Longrightarrow> seq t u"
      using seq_def arr_iff_has_source arr_iff_has_target by metis+

    lemma seqE [elim]:
    assumes "seq t u"
    and "\<lbrakk>arr t; arr u; targets t = sources u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms seq_def by blast

    subsubsection "Congruence of Transitions"

    text \<open>
      Residuation induces a preorder \<open>\<lesssim>\<close> on transitions, defined by \<open>t \<lesssim> u\<close> if and only if
      \<open>t \ u\<close> is an identity.
    \<close>

    abbreviation prfx  (infix "\<lesssim>" 50)
    where "t \<lesssim> u \<equiv> ide (t \\ u)"

    lemma prfxE:
    assumes "t \<lesssim> u"
    and "ide (t \\ u) \<Longrightarrow> T"
    shows T
      using assms by fastforce

    lemma prfx_implies_con:
    assumes "t \<lesssim> u"
    shows "t \<frown> u"
      using assms arr_resid_iff_con by blast

    lemma prfx_reflexive:
    assumes "arr t"
    shows "t \<lesssim> t"
      by (simp add: assms resid_arr_self)

    lemma prfx_transitive [trans]:
    assumes "t \<lesssim> u" and "u \<lesssim> v"
    shows "t \<lesssim> v"
      using assms con_target resid_ide_arr ide_backward_stable cube conI
      by metis

    lemma source_is_prfx:
    assumes "a \<in> sources t"
    shows "a \<lesssim> t"
      using assms resid_source_in_targets by blast

    text \<open>
      The equivalence \<open>\<sim>\<close> associated with \<open>\<lesssim>\<close> is substitutive with respect to residuation.
    \<close>

    abbreviation cong  (infix "\<sim>" 50)
    where "t \<sim> u \<equiv> t \<lesssim> u \<and> u \<lesssim> t"

    lemma congE:
    assumes "t \<sim> u "
    and "\<lbrakk>t \<frown> u; ide (t \\ u); ide (u \\ t)\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms prfx_implies_con by blast

    lemma cong_reflexive:
    assumes "arr t"
    shows "t \<sim> t"
      using assms prfx_reflexive by simp

    lemma cong_symmetric:
    assumes "t \<sim> u"
    shows "u \<sim> t"
      using assms by simp

    lemma cong_transitive [trans]:
    assumes "t \<sim> u" and "u \<sim> v"
    shows "t \<sim> v"
      using assms prfx_transitive by auto

    lemma cong_subst_left:
    assumes "t \<sim> t'" and "t \<frown> u"
    shows "t' \<frown> u" and "t \\ u \<sim> t' \\ u"
      apply (meson assms con_sym con_target prfx_implies_con resid_reflects_con)
      by (metis assms con_sym con_target cube prfx_implies_con resid_ide_arr resid_reflects_con)

    lemma cong_subst_right:
    assumes "u \<sim> u'" and "t \<frown> u"
    shows "t \<frown> u'" and "t \\ u \<sim> t \\ u'"
    proof -
      have 1: "t \<frown> u' \<and> t \\ u' \<frown> u \\ u' \<and>
                (t \\ u) \\ (u' \\ u) = (t \\ u') \\ (u \\ u')"
        using assms cube con_sym con_target cong_subst_left(1) by meson
      show "t \<frown> u'"
        using 1 by simp
      show "t \\ u \<sim> t \\ u'"
        by (metis 1 arr_resid_iff_con assms(1) cong_reflexive resid_arr_ide)
    qed

    lemma cong_implies_coinitial:
    assumes "u \<sim> u'"
    shows "coinitial u u'"
      using assms con_imp_coinitial prfx_implies_con by simp

    lemma cong_implies_coterminal:
    assumes "u \<sim> u'"
    shows "coterminal u u'"
      using assms
      by (metis con_implies_arr(1) coterminalI ideE prfx_implies_con sources_resid
          targets_resid_sym)

    lemma ide_imp_con_iff_cong:
    assumes "ide t" and "ide u"
    shows "t \<frown> u \<longleftrightarrow> t \<sim> u"
      using assms
      by (metis con_sym resid_ide_arr prfx_implies_con)

    lemma sources_are_cong:
    assumes "a \<in> sources t" and "a' \<in> sources t"
    shows "a \<sim> a'"
      using assms sources_are_con
      by (metis CollectD ide_imp_con_iff_cong sources_def)

    lemma sources_cong_closed:
    assumes "a \<in> sources t" and "a \<sim> a'"
    shows "a' \<in> sources t"
      using assms sources_def
      by (meson in_sourcesE in_sourcesI cong_subst_right(1) ide_backward_stable)

    lemma targets_are_cong:
    assumes "b \<in> targets t" and "b' \<in> targets t"
    shows "b \<sim> b'"
      using assms(1-2) sources_are_cong sources_def targets_def by blast

    lemma targets_cong_closed:
    assumes "b \<in> targets t" and "b \<sim> b'"
    shows "b' \<in> targets t"
      using assms targets_def sources_cong_closed sources_def by blast

    lemma targets_char:
    shows "targets t = {b. arr t \<and> t \\ t \<sim> b}"
      unfolding targets_def
      by (metis (no_types, lifting) con_def con_implies_arr(2) con_sym cong_reflexive
          ide_def resid_arr_ide trg_def)

    lemma coinitial_ide_are_cong:
    assumes "ide a" and "ide a'" and "coinitial a a'"
    shows "a \<sim> a'"
      using assms coinitial_def
      by (metis ideE in_sourcesI coinitialE sources_are_cong)

    lemma cong_respects_seq:
    assumes "seq t u" and "cong t t'" and "cong u u'"
    shows "seq t' u'"
      by (metis assms coterminalE rts.coinitialE rts.cong_implies_coinitial
          rts.cong_implies_coterminal rts_axioms seqE seqI)

  end

  subsection "Weakly Extensional RTS"

  text \<open>
    A \emph{weakly extensional} RTS is an RTS that satisfies the additional condition that
    identity arrows have trivial congruence classes.  This axiom has a number of useful
    consequences, including that each arrow has a unique source and target.
  \<close>

  locale weakly_extensional_rts = rts +
  assumes weak_extensionality: "\<lbrakk>t \<sim> u; ide t; ide u\<rbrakk> \<Longrightarrow> t = u"
  begin

    lemma con_ide_are_eq:
    assumes "ide a" and "ide a'" and "a \<frown> a'"
    shows "a = a'"
      using assms ide_imp_con_iff_cong weak_extensionality by blast

    lemma coinitial_ide_are_eq:
    assumes "ide a" and "ide a'" and "coinitial a a'"
    shows "a = a'"
      using assms coinitial_def con_ide_are_eq by blast

    lemma arr_has_un_source:
    assumes "arr t"
    shows "\<exists>!a. a \<in> sources t"
      using assms
      by (meson arr_iff_has_source con_ide_are_eq ex_in_conv in_sourcesE sources_are_con)

    lemma arr_has_un_target:
    assumes "arr t"
    shows "\<exists>!b. b \<in> targets t"
      using assms
      by (metis arrE arr_has_un_source arr_resid sources_resid)

    definition src
    where "src t \<equiv> if arr t then THE a. a \<in> sources t else null"

    lemma src_in_sources:
    assumes "arr t"
    shows "src t \<in> sources t"
      using assms src_def arr_has_un_source
            the1I2 [of "\<lambda>a. a \<in> sources t" "\<lambda>a. a \<in> sources t"]
      by simp

    lemma src_eqI:
    assumes "ide a" and "a \<frown> t"
    shows "src t = a"
      using assms src_in_sources
      by (metis arr_has_un_source resid_arr_ide in_sourcesI arr_resid_iff_con con_sym)

    lemma sources_char:
    shows "sources t = {a. arr t \<and> src t = a}"
      using src_in_sources arr_has_un_source arr_iff_has_source by auto

    lemma targets_char\<^sub>W\<^sub>E:
    shows "targets t = {b. arr t \<and> trg t = b}"
      using trg_in_targets arr_has_un_target arr_iff_has_target by auto

    lemma arr_src_iff_arr:
    shows "arr (src t) \<longleftrightarrow> arr t"
      by (metis arrI conE null_is_zero(2) sources_are_con arrE src_def src_in_sources)

    lemma arr_trg_iff_arr:
    shows "arr (trg t) \<longleftrightarrow> arr t"
      by (metis arrI arrE arr_resid_iff_con resid_arr_self)

    lemma arr_src_if_arr [simp]:
    assumes "arr t"
    shows "arr (src t)"
      using assms arr_src_iff_arr by blast

    lemma arr_trg_if_arr [simp]:
    assumes "arr t"
    shows "arr (trg t)"
      using assms arr_trg_iff_arr by blast

    lemma con_imp_eq_src:
    assumes "t \<frown> u"
    shows "src t = src u"
      using assms
      by (metis con_imp_coinitial_ax src_eqI)

    lemma src_resid [simp]:
    assumes "t \<frown> u"
    shows "src (t \\ u) = trg u"
      using assms
      by (metis arr_resid_iff_con con_implies_arr(2) arr_has_un_source trg_in_targets
                sources_resid src_in_sources)

    lemma apex_sym:
    shows "trg (t \\ u) = trg (u \\ t)"
      by (metis arr_has_un_target con_sym_ax residuation.arr_resid_iff_con residuation.conI
          residuation_axioms targets_resid_sym trg_in_targets)

    lemma apex_arr_prfx:
    assumes "prfx t u"
    shows "trg (u \\ t) = trg u"
    and "trg (t \\ u) = trg u"
      using assms
       apply (metis apex_sym arr_resid_iff_con ideE src_resid)
      by (metis arr_resid_iff_con assms ideE src_resid)

    lemma seqI\<^sub>W\<^sub>E [intro, simp]:
    shows "\<lbrakk>arr t; trg t = src u\<rbrakk> \<Longrightarrow> seq t u"
    and "\<lbrakk>arr u; trg t = src u\<rbrakk> \<Longrightarrow> seq t u"
      by (metis arrE arr_src_iff_arr arr_trg_iff_arr in_sourcesE rts.resid_arr_ide
          rts_axioms seqI(1) sources_resid src_in_sources trg_def)+

    lemma seqE\<^sub>W\<^sub>E [elim]:
    assumes "seq t u"
    and "\<lbrakk>arr u; arr t; trg t = src u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms
      by (metis arr_has_un_source seq_def src_in_sources trg_in_targets)

    lemma coinitial_iff\<^sub>W\<^sub>E:
    shows "coinitial t u \<longleftrightarrow> arr t \<and> arr u \<and> src t = src u"
      by (metis arr_has_un_source coinitial_def coinitial_iff disjoint_iff_not_equal
          src_in_sources)

    lemma coterminal_iff\<^sub>W\<^sub>E:
    shows "coterminal t u \<longleftrightarrow> arr t \<and> arr u \<and> trg t = trg u"
      by (metis arr_has_un_target coterminal_iff_con_trg coterminal_iff trg_in_targets)

    lemma coinitialI\<^sub>W\<^sub>E [intro]:
    assumes "arr t" and "src t = src u"
    shows "coinitial t u"
      using assms coinitial_iff\<^sub>W\<^sub>E by (metis arr_src_iff_arr)

    lemma coinitialE\<^sub>W\<^sub>E [elim]:
    assumes "coinitial t u"
    and "\<lbrakk>arr t; arr u; src t = src u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms coinitial_iff\<^sub>W\<^sub>E by blast

    lemma coterminalI\<^sub>W\<^sub>E [intro]:
    assumes "arr t" and "trg t = trg u"
    shows "coterminal t u"
      using assms coterminal_iff\<^sub>W\<^sub>E by (metis arr_trg_iff_arr)

    lemma coterminalE\<^sub>W\<^sub>E [elim]:
    assumes "coterminal t u"
    and "\<lbrakk>arr t; arr u; trg t = trg u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms coterminal_iff\<^sub>W\<^sub>E by blast

    lemma ide_src [simp]:
    assumes "arr t"
    shows "ide (src t)"
      using assms
      by (metis arrE con_imp_coinitial_ax src_eqI)

    lemma src_ide [simp]:
    assumes "ide a"
    shows "src a = a"
      using arrI assms src_eqI by blast

    lemma trg_ide [simp]:
    assumes "ide a"
    shows "trg a = a"
      using assms resid_arr_self by auto

    lemma ide_iff_src_self:
    assumes "arr a"
    shows "ide a \<longleftrightarrow> src a = a"
      using assms by (metis ide_src src_ide)

    lemma ide_iff_trg_self:
    assumes "arr a"
    shows "ide a \<longleftrightarrow> trg a = a"
      using assms ide_def resid_arr_self ide_trg by metis

    lemma src_src [simp]:
    shows "src (src t) = src t"
      using ide_src src_def src_ide by auto

    lemma trg_trg [simp]:
    shows "trg (trg t) = trg t"
      by (metis con_def con_implies_arr(2) cong_reflexive ide_def null_is_zero(2) resid_arr_self)

    lemma src_trg [simp]:
    shows "src (trg t) = trg t"
      by (metis con_def not_arr_null src_def src_resid trg_def)

    lemma trg_src [simp]:
    shows "trg (src t) = src t"
      by (metis ide_src null_is_zero(2) resid_arr_self src_def trg_ide)

    lemma resid_ide:
    assumes "ide a" and "coinitial a t"
    shows (* [simp]: *) "t \\ a = t" and "a \\ t = trg t"
      using assms resid_arr_ide apply blast
      using assms
      by (metis con_def con_sym_ax ideE in_sourcesE in_sourcesI resid_ide_arr
          coinitialE src_ide src_resid)

    lemma con_arr_src [simp]:
    assumes "arr f"
    shows "f \<frown> src f" and "src f \<frown> f"
      using assms src_in_sources con_sym by blast+

    lemma resid_src_arr [simp]:
    assumes "arr f"
    shows "src f \\ f = trg f"
      using assms
      by (simp add: con_imp_coinitial resid_ide(2))

    lemma resid_arr_src [simp]:
    assumes "arr f"
    shows "f \\ src f = f"
      using assms
      by (simp add: resid_arr_ide)

  end

  subsection "Extensional RTS"

  text \<open>
    An \emph{extensional} RTS is an RTS in which all arrows have trivial congruence classes;
    that is, congruent arrows are equal.
  \<close>

  locale extensional_rts = rts +
  assumes extensional: "t \<sim> u \<Longrightarrow> t = u"
  begin

    sublocale weakly_extensional_rts
      using extensional
      by unfold_locales auto

    lemma cong_char:
    shows "t \<sim> u \<longleftrightarrow> arr t \<and> t = u"
      by (metis arrI cong_reflexive prfx_implies_con extensional)

  end

  subsection "Composites of Transitions"

  text \<open>
    Residuation can be used to define a notion of composite of transitions.
    Composites are not unique, but they are unique up to congruence.
  \<close>

  context rts
  begin

    definition composite_of
    where "composite_of u t v \<equiv> u \<lesssim> v \<and> v \\ u \<sim> t"

    lemma composite_ofI [intro]:
    assumes "u \<lesssim> v" and "v \\ u \<sim> t"
    shows "composite_of u t v"
      using assms composite_of_def by blast

    lemma composite_ofE [elim]:
    assumes "composite_of u t v"
    and "\<lbrakk>u \<lesssim> v; v \\ u \<sim> t\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms composite_of_def by auto

    lemma arr_composite_of:
    assumes "composite_of u t v"
    shows "arr v"
      using assms
      by (meson composite_of_def con_implies_arr(2) prfx_implies_con)

    lemma composite_of_unq_upto_cong:
    assumes "composite_of u t v" and "composite_of u t v'"
    shows "v \<sim> v'"
      using assms cube ide_backward_stable prfx_transitive
      by (elim composite_ofE) metis

    lemma composite_of_ide_arr:
    assumes "ide a"
    shows "composite_of a t t \<longleftrightarrow> t \<frown> a"
      using assms
      by (metis composite_of_def con_implies_arr(1) con_sym resid_arr_ide resid_ide_arr
          prfx_implies_con prfx_reflexive)

    lemma composite_of_arr_ide:
    assumes "ide b"
    shows "composite_of t b t \<longleftrightarrow> t \\ t \<frown> b"
      using assms
      by (metis arr_resid_iff_con composite_of_def ide_imp_con_iff_cong con_implies_arr(1)
          prfx_implies_con prfx_reflexive)

    lemma composite_of_source_arr:
    assumes "arr t" and "a \<in> sources t"
    shows "composite_of a t t"
      using assms composite_of_ide_arr sources_def by auto

    lemma composite_of_arr_target:
    assumes "arr t" and "b \<in> targets t"
    shows "composite_of t b t"
      by (metis arrE assms composite_of_arr_ide in_sourcesE sources_resid)

    lemma composite_of_ide_self:
    assumes "ide a"
    shows "composite_of a a a"
      using assms composite_of_ide_arr by blast

    lemma con_prfx_composite_of:
    assumes "composite_of t u w"
    shows "t \<frown> w" and "w \<frown> v \<Longrightarrow> t \<frown> v"
      using assms apply force
      using assms composite_of_def con_target prfx_implies_con
            resid_reflects_con con_sym
        by meson

    lemma sources_composite_of:
    assumes "composite_of u t v"
    shows "sources v = sources u"
      using assms
      by (meson arr_resid_iff_con composite_of_def con_imp_coinitial cong_implies_coinitial
          coinitial_iff)

    lemma targets_composite_of:
    assumes "composite_of u t v"
    shows "targets v = targets t"
    proof -
      have "targets t = targets (v \\ u)"
        using assms composite_of_def
        by (meson cong_implies_coterminal coterminal_iff)
      also have "... = targets (u \\ v)"
        using assms targets_resid_sym con_prfx_composite_of by metis
      also have "... = targets v"
        using assms composite_of_def
        by (metis prfx_implies_con sources_resid ideE)
      finally show ?thesis by auto
    qed

    lemma resid_composite_of:
    assumes "composite_of t u w" and "w \<frown> v"
    shows "v \\ t \<frown> w \\ t"
    and "v \\ t \<frown> u"
    and "v \\ w \<sim> (v \\ t) \\ u"
    and "composite_of (t \\ v) (u \\ (v \\ t)) (w \\ v)"
    proof -
      show 0: "v \\ t \<frown> w \\ t"
        using assms con_def
        by (metis con_target composite_ofE conE con_sym cube)
      show 1: "v \\ w \<sim> (v \\ t) \\ u"
      proof -
        have "v \\ w = (v \\ w) \\ (t \\ w)"
          using assms composite_of_def
          by (metis (no_types, opaque_lifting) con_target con_sym resid_arr_ide)
        also have "... = (v \\ t) \\ (w \\ t)"
          using assms cube by metis
        also have "... \<sim> (v \\ t) \\ u"
          using assms 0 cong_subst_right(2) [of "w \\ t" u "v \\ t"] by blast
        finally show ?thesis by blast
      qed
      show 2: "v \\ t \<frown> u"
        using assms 1 by force
      show "composite_of (t \\ v) (u \\ (v \\ t)) (w \\ v)"
      proof (unfold composite_of_def, intro conjI)
        show "t \\ v \<lesssim> w \\ v"
          using assms cube con_target composite_of_def resid_ide_arr by metis
        show "(w \\ v) \\ (t \\ v) \<lesssim> u \\ (v \\ t)"
          by (metis assms(1) 2 composite_ofE con_sym cong_subst_left(2) cube)
        thus "u \\ (v \\ t) \<lesssim> (w \\ v) \\ (t \\ v)"
          using assms
          by (metis composite_of_def con_implies_arr(2) cong_subst_left(2)
              prfx_implies_con arr_resid_iff_con cube)
      qed
    qed

    lemma con_composite_of_iff:
    assumes "composite_of t u v"
    shows "w \<frown> v \<longleftrightarrow> w \\ t \<frown> u"
      by (meson arr_resid_iff_con assms composite_ofE con_def con_implies_arr(1)
          con_sym_ax cong_subst_right(1) resid_composite_of(2) resid_reflects_con)

    definition composable
    where "composable t u \<equiv> \<exists>v. composite_of t u v"

    lemma composableD [dest]:
    assumes "composable t u"
    shows "arr t" and "arr u" and "targets t = sources u"
      using assms arr_composite_of arr_iff_has_source composable_def sources_composite_of
            arr_composite_of arr_iff_has_target composable_def targets_composite_of
        apply auto[2]
      by (metis assms composable_def composite_ofE con_prfx_composite_of(1) con_sym
          cong_implies_coinitial coinitial_iff sources_resid)

    lemma composable_imp_seq:
    assumes "composable t u"
    shows "seq t u"
      using assms by blast

    lemma bounded_imp_con:
    assumes "composite_of t u v" and "composite_of t' u' v"
    shows "con t t'"
      by (meson assms composite_of_def con_prfx_composite_of prfx_implies_con
          arr_resid_iff_con con_implies_arr(2))

    lemma composite_of_cancel_left:
    assumes "composite_of t u v" and "composite_of t u' v"
    shows "u \<sim> u'"
      using assms composite_of_def cong_transitive by blast

  end

  subsubsection "RTS with Composites"

  locale rts_with_composites = rts +
  assumes has_composites: "seq t u \<Longrightarrow> composable t u"
  begin

    lemma composable_iff_seq:
    shows "composable g f \<longleftrightarrow> seq g f"
      using composable_imp_seq has_composites by blast

    lemma composableI [intro]:
    assumes "seq g f"
    shows "composable g f"
      using assms composable_iff_seq by auto

    lemma composableE [elim]:
    assumes "composable g f" and "seq g f \<Longrightarrow> T"
    shows T
      using assms composable_iff_seq by blast

    lemma obtains_composite_of:
    assumes "seq g f"
    obtains h where "composite_of g f h"
      using assms has_composites composable_def by blast

    lemma diamond_commutes_upto_cong:
    assumes "composite_of t (u \\ t) v" and "composite_of u (t \\ u) v'"
    shows "v \<sim> v'"
      using assms cube ide_backward_stable prfx_transitive
      by (elim composite_ofE) metis

  end

  subsection "Joins of Transitions"

  context rts
  begin

    text \<open>
      Transition \<open>v\<close> is a \emph{join} of \<open>u\<close> and \<open>v\<close> when \<open>v\<close> is the diagonal of the square
      formed by \<open>u\<close>, \<open>v\<close>, and their residuals.  As was the case for composites,
      joins in an RTS are not unique, but they are unique up to congruence.
    \<close>

    definition join_of
    where "join_of t u v \<equiv> composite_of t (u \\ t) v \<and> composite_of u (t \\ u) v"

    lemma join_ofI [intro]:
    assumes "composite_of t (u \\ t) v" and "composite_of u (t \\ u) v"
    shows "join_of t u v"
      using assms join_of_def by simp

    lemma join_ofE [elim]:
    assumes "join_of t u v"
    and "\<lbrakk>composite_of t (u \\ t) v; composite_of u (t \\ u) v\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms join_of_def by simp

    definition joinable
    where "joinable t u \<equiv> \<exists>v. join_of t u v"

    lemma joinable_implies_con:
    assumes "joinable t u"
    shows "t \<frown> u"
      by (meson assms bounded_imp_con join_of_def joinable_def)

    lemma joinable_implies_coinitial:
    assumes "joinable t u"
    shows "coinitial t u"
      using assms
      by (simp add: con_imp_coinitial joinable_implies_con)

    lemma join_of_un_upto_cong:
    assumes "join_of t u v" and "join_of t u v'"
    shows "v \<sim> v'"
      using assms join_of_def composite_of_unq_upto_cong by auto

    lemma join_of_symmetric:
    assumes "join_of t u v"
    shows "join_of u t v"
      using assms join_of_def by simp

    lemma join_of_arr_self:
    assumes "arr t"
    shows "join_of t t t"
      by (meson assms composite_of_arr_ide ideE join_of_def prfx_reflexive)

    lemma join_of_arr_src:
    assumes "arr t" and "a \<in> sources t"
    shows "join_of a t t" and "join_of t a t"
    proof -
      show "join_of a t t"
        by (meson assms composite_of_arr_target composite_of_def composite_of_source_arr join_of_def
                  prfx_transitive resid_source_in_targets)
      thus "join_of t a t"
        using join_of_symmetric by blast
    qed

    lemma sources_join_of:
    assumes "join_of t u v"
    shows "sources t = sources v" and "sources u = sources v"
      using assms join_of_def sources_composite_of by blast+

    lemma targets_join_of:
    assumes "join_of t u v"
    shows "targets (t \\ u) = targets v" and "targets (u \\ t) = targets v"
      using assms join_of_def targets_composite_of by blast+

    lemma join_of_resid:
    assumes "join_of t u w" and "con v w"
    shows "join_of (t \\ v) (u \\ v) (w \\ v)"
      using assms con_sym cube join_of_def resid_composite_of(4) by fastforce
    
    lemma con_with_join_of_iff:
    assumes "join_of t u w"
    shows "u \<frown> v \<and> v \\ u \<frown> t \\ u \<Longrightarrow> w \<frown> v"
    and "w \<frown> v \<Longrightarrow> t \<frown> v \<and> v \\ t \<frown> u \\ t"
    proof -
      have *: "t \<frown> v \<and> v \\ t \<frown> u \\ t \<longleftrightarrow> u \<frown> v \<and> v \\ u \<frown> t \\ u"
        by (metis arr_resid_iff_con con_implies_arr(1) con_sym cube)
      show "u \<frown> v \<and> v \\ u \<frown> t \\ u \<Longrightarrow> w \<frown> v"
        by (meson assms con_composite_of_iff con_sym join_of_def)
      show "w \<frown> v \<Longrightarrow> t \<frown> v \<and> v \\ t \<frown> u \\ t"
        by (meson assms con_prfx_composite_of join_of_def resid_composite_of(2))
    qed

  end

  subsubsection "RTS with Joins"

  locale rts_with_joins = rts +
  assumes has_joins: "t \<frown> u \<Longrightarrow> joinable t u"

  subsection "Joins and Composites in a Weakly Extensional RTS"

  context weakly_extensional_rts
  begin

    lemma src_composite_of:
    assumes "composite_of u t v"
    shows "src v = src u"
      using assms
      by (metis con_imp_eq_src con_prfx_composite_of(1))

    lemma trg_composite_of:
    assumes "composite_of u t v"
    shows "trg v = trg t"
      by (metis arr_composite_of arr_has_un_target arr_iff_has_target assms
          targets_composite_of trg_in_targets)

    lemma src_join_of:
    assumes "join_of t u v"
    shows "src t = src v" and "src u = src v"
      by (metis assms join_ofE src_composite_of)+

    lemma trg_join_of:
    assumes "join_of t u v"
    shows "trg (t \\ u) = trg v" and "trg (u \\ t) = trg v"
      by (metis assms join_of_def trg_composite_of)+

  end

  subsection "Joins and Composites in an Extensional RTS"

  context extensional_rts
  begin

    lemma composite_of_unique:
    assumes "composite_of t u v" and "composite_of t u v'"
    shows "v = v'"
      using assms composite_of_unq_upto_cong extensional by fastforce

    text \<open>
      Here we define composition of transitions.  Note that we compose transitions
      in diagram order, rather than in the order used for function composition.
      This may eventually lead to confusion, but here (unlike in the case of a category)
      transitions are typically not functions, so we don't have the constraint of having
      to conform to the order of function application and composition, and diagram order
      seems more natural.
    \<close>

    definition comp  (infixl "\<cdot>" 55)
    where "t \<cdot> u \<equiv> if composable t u then THE v. composite_of t u v else null"

    lemma comp_is_composite_of:
    shows "composable t u \<Longrightarrow> composite_of t u (t \<cdot> u)"
    and "composite_of t u v \<Longrightarrow> t \<cdot> u = v"
    proof -
      show "composable t u \<Longrightarrow> composite_of t u (t \<cdot> u)"
        using comp_def composite_of_unique the1I2 [of "composite_of t u" "composite_of t u"]
              composable_def
        by metis
      thus "composite_of t u v \<Longrightarrow> t \<cdot> u = v"
        using composite_of_unique composable_def by auto
    qed

    lemma comp_null [simp]:
    shows "null \<cdot> t = null" and "t \<cdot> null = null"
      by (meson composableD not_arr_null comp_def)+

    lemma composable_iff_arr_comp:
    shows "composable t u \<longleftrightarrow> arr (t \<cdot> u)"
      by (metis arr_composite_of comp_is_composite_of(2) composable_def comp_def not_arr_null)

    lemma composable_iff_comp_not_null:
    shows "composable t u \<longleftrightarrow> t \<cdot> u \<noteq> null"
      by (metis composable_iff_arr_comp comp_def not_arr_null)

    lemma comp_src_arr [simp]:
    assumes "arr t" and "src t = a"
    shows "a \<cdot> t = t"
      using assms comp_is_composite_of(2) composite_of_source_arr src_in_sources by blast

    lemma comp_arr_trg [simp]:
    assumes "arr t" and "trg t = b"
    shows "t \<cdot> b = t"
      using assms comp_is_composite_of(2) composite_of_arr_target trg_in_targets by blast

    lemma comp_ide_self:
    assumes "ide a"
    shows "a \<cdot> a = a"
      using assms comp_is_composite_of(2) composite_of_ide_self by fastforce

    lemma arr_comp [intro, simp]:
    assumes "composable t u"
    shows "arr (t \<cdot> u)"
      using assms composable_iff_arr_comp by blast

    lemma trg_comp [simp]:
    assumes "composable t u"
    shows "trg (t \<cdot> u) = trg u"
      by (metis arr_has_un_target assms comp_is_composite_of(2) composable_def
          composable_imp_seq arr_iff_has_target seq_def targets_composite_of trg_in_targets)

    lemma src_comp [simp]:
    assumes "composable t u"
    shows "src (t \<cdot> u) = src t"
      using assms comp_is_composite_of arr_iff_has_source sources_composite_of src_def
            composable_def
      by auto

    lemma con_comp_iff:
    shows "w \<frown> t \<cdot> u \<longleftrightarrow> composable t u \<and> w \\ t \<frown> u"
      by (meson comp_is_composite_of(1) composable_iff_arr_comp con_composite_of_iff
          con_implies_arr(2))

    lemma con_compI [intro]:
    assumes "composable t u" and "w \\ t \<frown> u"
    shows "w \<frown> t \<cdot> u" and "t \<cdot> u \<frown> w"
      using assms con_comp_iff con_sym by blast+

    lemma resid_comp:
    assumes "t \<cdot> u \<frown> w"
    shows "w \\ (t \<cdot> u) = (w \\ t) \\ u"
    and "(t \<cdot> u) \\ w = (t \\ w) \<cdot> (u \\ (w \\ t))"
    proof -
      have 1: "composable t u"
        using assms composable_iff_comp_not_null by force
      show "w \\ (t \<cdot> u) = (w \\ t) \\ u"
        using 1
        by (meson assms cong_char composable_def resid_composite_of(3) comp_is_composite_of(1))
      show "(t \<cdot> u) \\ w = (t \\ w) \<cdot> (u \\ (w \\ t))"
        using assms 1 composable_def comp_is_composite_of(2) resid_composite_of
        by metis
    qed

    lemma prfx_decomp:
    assumes "t \<lesssim> u"
    shows "t \<cdot> (u \\ t) = u"
      by (meson assms arr_resid_iff_con comp_is_composite_of(2) composite_of_def con_sym
          cong_reflexive prfx_implies_con)

    lemma prfx_comp:
    assumes "arr u" and "t \<cdot> v = u"
    shows "t \<lesssim> u"
      by (metis assms comp_is_composite_of(2) composable_def composable_iff_arr_comp
                composite_of_def)

    lemma comp_eqI:
    assumes "t \<lesssim> v" and "u = v \\ t"
    shows "t \<cdot> u = v"
      by (metis assms prfx_decomp)

    lemma comp_assoc:
    assumes "composable (t \<cdot> u) v"
    shows "t \<cdot> (u \<cdot> v) = (t \<cdot> u) \<cdot> v"
    proof -
      have 1: "t \<lesssim> (t \<cdot> u) \<cdot> v"
        by (meson assms composable_iff_arr_comp composableD prfx_comp
            prfx_transitive)
      moreover have "((t \<cdot> u) \<cdot> v) \\ t = u \<cdot> v"
      proof -
        have "((t \<cdot> u) \<cdot> v) \\ t = ((t \<cdot> u) \\ t) \<cdot> (v \\ (t \\ (t \<cdot> u)))" 
          by (meson assms calculation con_sym prfx_implies_con resid_comp(2))
        also have "... = u \<cdot> v"
        proof -
          have 2: "(t \<cdot> u) \\ t = u"
            by (metis assms comp_is_composite_of(2) composable_def composable_iff_arr_comp
                      composable_imp_seq composite_of_def extensional seqE)
          moreover have "v \\ (t \\ (t \<cdot> u)) = v"
            using assms
            by (meson 1 con_comp_iff con_sym composable_imp_seq resid_arr_ide
                prfx_implies_con prfx_comp seqE)
          ultimately show ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
      ultimately show "t \<cdot> (u \<cdot> v) = (t \<cdot> u) \<cdot> v"
        by (metis comp_eqI)
    qed

    text \<open>
      We note the following assymmetry: \<open>composable (t \<cdot> u) v \<Longrightarrow> composable u v\<close> is true,
      but \<open>composable t (u \<cdot> v) \<Longrightarrow> composable t u\<close> is not.
    \<close>

    lemma comp_cancel_left:
    assumes "arr (t \<cdot> u)" and "t \<cdot> u = t \<cdot> v"
    shows "u = v"
      using assms
      by (metis composable_def composable_iff_arr_comp composite_of_cancel_left extensional
          comp_is_composite_of(2))

    lemma comp_resid_prfx [simp]:
    assumes "arr (t \<cdot> u)"
    shows "(t \<cdot> u) \\ t = u"
      using assms
      by (metis comp_cancel_left comp_eqI prfx_comp)

    lemma bounded_imp_con\<^sub>E:
    assumes "t \<cdot> u \<sim> t' \<cdot> u'"
    shows "t \<frown> t'"
      by (metis arr_resid_iff_con assms con_comp_iff con_implies_arr(2) prfx_implies_con
                con_sym)

    lemma join_of_unique:
    assumes "join_of t u v" and "join_of t u v'"
    shows "v = v'"
      using assms join_of_def composite_of_unique by blast

    definition join  (infix "\<squnion>" 52)
    where "t \<squnion> u \<equiv> if joinable t u then THE v. join_of t u v else null"

    lemma join_is_join_of:
    assumes "joinable t u"
    shows "join_of t u (t \<squnion> u)"
      using assms joinable_def join_def join_of_unique the1I2 [of "join_of t u" "join_of t u"]
      by force

    lemma joinable_iff_arr_join:
    shows "joinable t u \<longleftrightarrow> arr (t \<squnion> u)"
      by (metis cong_char join_is_join_of join_of_un_upto_cong not_arr_null join_def)

    lemma joinable_iff_join_not_null:
    shows "joinable t u \<longleftrightarrow> t \<squnion> u \<noteq> null"
      by (metis join_def joinable_iff_arr_join not_arr_null)

    lemma join_sym:
    shows "t \<squnion> u = u \<squnion> t"
      by (metis extensional_rts.join_def extensional_rts.join_of_unique extensional_rts_axioms
          join_is_join_of join_of_symmetric joinable_def)

    lemma src_join:
    assumes "joinable t u"
    shows "src (t \<squnion> u) = src t"
      using assms
      by (metis con_imp_eq_src con_prfx_composite_of(1) join_is_join_of join_of_def)

    lemma trg_join:
    assumes "joinable t u"
    shows "trg (t \<squnion> u) = trg (t \\ u)"
      using assms
      by (metis arr_resid_iff_con join_is_join_of joinable_iff_arr_join joinable_implies_con
          in_targetsE src_eqI targets_join_of(1) trg_in_targets)

    lemma resid_join\<^sub>E [simp]:
    assumes "joinable t u" and "v \<frown> t \<squnion> u"
    shows "v \\ (t \<squnion> u) = (v \\ u) \\ (t \\ u)"
    and "v \\ (t \<squnion> u) = (v \\ t) \\ (u \\ t)"
    and "(t \<squnion> u) \\ v = (t \\ v) \<squnion> (u \\ v)"
    proof -
      show 1: "v \\ (t \<squnion> u) = (v \\ u) \\ (t \\ u)"
        by (meson assms con_sym join_of_def resid_composite_of(3) extensional join_is_join_of)
      show "v \\ (t \<squnion> u) = (v \\ t) \\ (u \\ t)"
        by (metis "1" cube)
      show "(t \<squnion> u) \\ v = (t \\ v) \<squnion> (u \\ v)"
        using assms joinable_def join_of_resid join_is_join_of extensional
        by (meson join_of_unique)
    qed

    lemma join_eqI:
    assumes "t \<lesssim> v" and "u \<lesssim> v" and "v \\ u = t \\ u" and "v \\ t = u \\ t"
    shows "t \<squnion> u = v"
      using assms composite_of_def cube ideE join_of_def joinable_def join_of_unique
            join_is_join_of trg_def
      by metis

    lemma comp_join:
    assumes "joinable (t \<cdot> u) (t \<cdot> u')"
    shows "composable t (u \<squnion> u')"
    and "t \<cdot> (u \<squnion> u') = t \<cdot> u \<squnion> t \<cdot> u'"
    proof -
      have "t \<lesssim> t \<cdot> u \<squnion> t \<cdot> u'"
        using assms
        by (metis composable_def composite_of_def join_of_def join_is_join_of
            joinable_implies_con prfx_transitive comp_is_composite_of(2) con_comp_iff)
      moreover have "(t \<cdot> u \<squnion> t \<cdot> u') \\ t = u \<squnion> u'"
        by (metis arr_resid_iff_con assms calculation comp_resid_prfx con_implies_arr(2)
            joinable_implies_con resid_join\<^sub>E(3) con_implies_arr(1) ide_implies_arr)
      ultimately show "t \<cdot> (u \<squnion> u') = t \<cdot> u \<squnion> t \<cdot> u'"
        by (metis comp_eqI)
      thus "composable t (u \<squnion> u')"
        by (metis assms joinable_iff_join_not_null comp_def)
    qed

    lemma join_src:
    assumes "arr t"
    shows "src t \<squnion> t = t"
      using assms joinable_def join_of_arr_src join_is_join_of join_of_unique src_in_sources
      by meson

    lemma join_arr_self:
    assumes "arr t"
    shows "t \<squnion> t = t"
      using assms joinable_def join_of_arr_self join_is_join_of join_of_unique by blast

    lemma arr_prfx_join_self:
    assumes "joinable t u"
    shows "t \<lesssim> t \<squnion> u"
      using assms
      by (meson composite_of_def join_is_join_of join_of_def)

    lemma con_prfx:
    shows "\<lbrakk>t \<frown> u; v \<lesssim> u\<rbrakk> \<Longrightarrow> t \<frown> v"
    and "\<lbrakk>t \<frown> u; v \<lesssim> t\<rbrakk> \<Longrightarrow> v \<frown> u"
      apply (metis arr_resid con_arr_src(1) ide_iff_src_self prfx_implies_con resid_reflects_con
           src_resid)
      by (metis arr_resid_iff_con comp_eqI con_comp_iff con_implies_arr(1) con_sym)

    lemma join_prfx:
    assumes "t \<lesssim> u"
    shows "t \<squnion> u = u" and "u \<squnion> t = u"
    proof -
      show "t \<squnion> u = u"
        using assms
        by (metis (no_types, lifting) join_eqI ide_iff_src_self ide_implies_arr resid_arr_self
            prfx_implies_con src_resid)
      thus "u \<squnion> t = u"
        by (metis join_sym)
    qed

    lemma con_with_join_if [intro, simp]:
    assumes "joinable t u" and "u \<frown> v" and "v \\ u \<frown> t \\ u"
    shows "t \<squnion> u \<frown> v"
    and "v \<frown> t \<squnion> u"
    proof -
      show "t \<squnion> u \<frown> v"
        using assms con_with_join_of_iff [of t u "join t u" v] join_is_join_of by simp
      thus "v \<frown> t \<squnion> u"
        using assms con_sym by blast
    qed

    lemma join_assoc\<^sub>E:
    assumes "arr ((t \<squnion> u) \<squnion> v)" and "arr (t \<squnion> (u \<squnion> v))"
    shows "(t \<squnion> u) \<squnion> v = t \<squnion> (u \<squnion> v)"
    proof (intro join_eqI)
      have tu: "joinable t u"
        by (metis arr_src_iff_arr assms(1) joinable_iff_arr_join src_join)
      have uv: "joinable u v"
        by (metis assms(2) joinable_iff_arr_join joinable_iff_join_not_null joinable_implies_con
            not_con_null(2))
      have tu_v: "joinable (t \<squnion> u) v"
        by (simp add: assms(1) joinable_iff_arr_join)
      have t_uv: "joinable t (u \<squnion> v)"
        by (simp add: assms(2) joinable_iff_arr_join)
      show 0: "t \<squnion> u \<lesssim> t \<squnion> (u \<squnion> v)"
      proof -
        have "(t \<squnion> u) \\ (t \<squnion> (u \<squnion> v)) = ((u \\ t) \\ (u \\ t)) \\ ((v \\ t) \\ (u \\ t))"
        proof -
          have "(t \<squnion> u) \\ (t \<squnion> (u \<squnion> v)) = ((t \<squnion> u) \\ t) \\ ((u \<squnion> v) \\ t)"
            by (metis t_uv tu arr_prfx_join_self conI con_with_join_if(2)
                join_sym joinable_iff_join_not_null not_ide_null resid_join\<^sub>E(2))
          also have "... = (t \\ t \<squnion> u \\ t) \\ ((u \<squnion> v) \\ t)"
            by (simp add: tu con_sym joinable_implies_con)
          also have "... = (t \\ t \<squnion> u \\ t) \\ (u \\ t \<squnion> v \\ t)"
            by (simp add: t_uv uv joinable_implies_con)
          also have "... = (u \\ t) \\ join (u \\ t) (v \\ t)"
            by (metis tu con_implies_arr(1) cong_subst_left(2) cube join_eqI join_sym
                joinable_iff_join_not_null joinable_implies_con prfx_reflexive trg_def trg_join)
          also have "... = ((u \\ t) \\ (u \\ t)) \\ ((v \\ t) \\ (u \\ t))"
          proof -
            have 1: "joinable (u \\ t) (v \\ t)"
              by (metis t_uv uv con_sym joinable_iff_join_not_null joinable_implies_con
                  resid_join\<^sub>E(3) conE)
            moreover have "u \\ t \<frown> u \\ t \<squnion> v \\ t"
              using arr_prfx_join_self 1 prfx_implies_con by blast
            ultimately show ?thesis
              using resid_join\<^sub>E(2) [of "u \\ t" "v \\ t" "u \\ t"] by blast
          qed
          finally show ?thesis by blast
        qed
        moreover have "ide ..."
          by (metis tu_v tu arr_resid_iff_con con_sym cube joinable_implies_con prfx_reflexive
              resid_join\<^sub>E(2))
        ultimately show ?thesis by simp
      qed
      show 1: "v \<lesssim> t \<squnion> (u \<squnion> v)"
        by (metis arr_prfx_join_self join_sym joinable_iff_join_not_null prfx_transitive t_uv uv)
      show "(t \<squnion> (u \<squnion> v)) \\ v = (t \<squnion> u) \\ v"
      proof -
        have "(t \<squnion> (u \<squnion> v)) \\ v = t \\ v \<squnion> (u \<squnion> v) \\ v"
          by (metis 1 assms(2) join_def not_arr_null resid_join\<^sub>E(3) prfx_implies_con)
        also have "... = t \\ v \<squnion> (u \\ v \<squnion> v \\ v)"
          by (metis 1 conE conI con_sym join_def resid_join\<^sub>E(1) resid_join\<^sub>E(3) null_is_zero(2)
              prfx_implies_con)
        also have "... = t \\ v \<squnion> u \\ v"
          by (metis arr_resid_iff_con con_sym cube cong_char join_prfx(2) joinable_implies_con uv)
        also have "... = (t \<squnion> u) \\ v"
          by (metis 0 1 con_implies_arr(1) con_prfx(1) joinable_iff_arr_join resid_join\<^sub>E(3)
              prfx_implies_con)
        finally show ?thesis by blast
      qed
      show "(t \<squnion> (u \<squnion> v)) \\ (t \<squnion> u) = v \\ (t \<squnion> u)"
      proof -
        have 2: "(t \<squnion> (u \<squnion> v)) \\ (t \<squnion> u) = t \\ (t \<squnion> u) \<squnion> (u \<squnion> v) \\ (t \<squnion> u)"
          by (metis 0 assms(2) join_def not_arr_null resid_join\<^sub>E(3) prfx_implies_con)
        also have 3: "... = (t \\ t) \\ (u \\ t) \<squnion> (u \<squnion> v) \\ (t \<squnion> u)"
          by (metis tu arr_prfx_join_self prfx_implies_con resid_join\<^sub>E(2))
        also have 4: "... = (u \<squnion> v) \\ (t \<squnion> u)"
        proof -
          have "(t \\ t) \\ (u \\ t) = src ((u \<squnion> v) \\ (t \<squnion> u))"
            using src_resid trg_join
            by (metis (full_types) t_uv tu 0 arr_resid_iff_con con_implies_arr(1) con_sym
                cube prfx_implies_con resid_join\<^sub>E(1) trg_def)
          thus ?thesis
            by (metis tu arr_prfx_join_self conE join_src prfx_implies_con resid_join\<^sub>E(2) src_def)
        qed
        also have "... = u \\ (t \<squnion> u) \<squnion> v \\ (t \<squnion> u)"
          by (metis 0 2 3 4 uv conI con_sym_ax not_ide_null resid_join\<^sub>E(3))
        also have "... = (u \\ u) \\ (t \\ u) \<squnion> v \\ (t \<squnion> u)"
          by (metis tu arr_prfx_join_self join_sym joinable_iff_join_not_null prfx_implies_con
              resid_join\<^sub>E(1))
        also have "... = v \\ (t \<squnion> u)"
        proof -
          have "(u \\ u) \\ (t \\ u) = src (v \\ (t \<squnion> u))"
            by (metis tu_v tu con_sym cube joinable_implies_con src_resid trg_def trg_join
                apex_sym)
          thus ?thesis
            using tu_v arr_resid_iff_con con_sym join_src joinable_implies_con
            by presburger
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma join_prfx_monotone:
    assumes "t \<lesssim> u" and "u \<squnion> v \<frown> t \<squnion> v"
    shows "t \<squnion> v \<lesssim> u \<squnion> v"
    proof -
      have "(t \<squnion> v) \\ (u \<squnion> v) = (t \\ u) \\ (v \\ u)"
      proof -
        have "(t \<squnion> v) \\ (u \<squnion> v) = t \\ (u \<squnion> v) \<squnion> v \\ (u \<squnion> v)"
          using assms join_sym resid_join\<^sub>E(3) [of t v "join u v"] joinable_iff_join_not_null
          by fastforce
        also have "... = (t \\ u) \\ (v \\ u) \<squnion> (v \\ u) \\ (v \\ u)"
          by (metis (full_types) assms(2) conE conI joinable_iff_join_not_null null_is_zero(1)
              resid_join\<^sub>E(1-2) con_sym_ax)
        also have "... = (t \\ u) \\ (v \\ u) \<squnion> trg (v \\ u)"
          using trg_def by fastforce
        also have "... = (t \\ u) \\ (v \\ u) \<squnion> src ((t \\ u) \\ (v \\ u))"
          by (metis assms(1-2) con_implies_arr(1) con_target joinable_iff_arr_join
              joinable_implies_con src_resid)
        also have "... = (t \\ u) \\ (v \\ u)"
          by (metis arr_resid_iff_con assms(2) con_implies_arr(1) con_sym join_def
              join_src join_sym not_arr_null resid_join\<^sub>E(2))
        finally show ?thesis by blast
      qed
      moreover have "ide ..."
        by (metis arr_resid_iff_con assms(1-2) calculation con_sym resid_ide_arr)
      ultimately show ?thesis by presburger
    qed

    lemma join_eqI':
    assumes "t \<lesssim> v" and "u \<lesssim> v" and "v \\ u = t \\ u" and "v \\ t = u \\ t"
    shows "v = t \<squnion> u"
      using assms composite_of_def cube ideE join_of_def joinable_def join_of_unique
            join_is_join_of trg_def
      by metis

    text \<open>
      We note that it is not the case that the existence of either of \<open>t \<squnion> (u \<squnion> v)\<close>
      or \<open>(t \<squnion> u) \<squnion> v\<close> implies that of the other.  For example, if \<open>(t \<squnion> u) \<squnion> v \<noteq> null\<close>,
      then it is not necessarily the case that \<open>u \<squnion> v \<noteq> null\<close>.
    \<close>

  end

  subsubsection "Extensional RTS with Joins"

  locale extensional_rts_with_joins =
    rts_with_joins +
    extensional_rts
  begin

    lemma joinable_iff_con [iff]:
    shows "joinable t u \<longleftrightarrow> t \<frown> u"
      by (meson has_joins joinable_implies_con)

    lemma joinableE [elim]:
    assumes "joinable t u" and "t \<frown> u \<Longrightarrow> T"
    shows T
      using assms joinable_iff_con by blast

    lemma src_join\<^sub>E\<^sub>J [simp]:
    assumes "t \<frown> u"
    shows "src (t \<squnion> u) = src t"
      using assms
      by (meson has_joins src_join)

    lemma trg_join\<^sub>E\<^sub>J:
    assumes "t \<frown> u"
    shows "trg (t \<squnion> u) = trg (t \\ u)"
      using assms
      by (meson has_joins trg_join)

    lemma resid_join\<^sub>E\<^sub>J [simp]:
    assumes "t \<frown> u" and "v \<frown> t \<squnion> u"
    shows "v \\ (t \<squnion> u) = (v \\ t) \\ (u \\ t)"
    and "(t \<squnion> u) \\ v = (t \\ v) \<squnion> (u \\ v)"
      using assms has_joins resid_join\<^sub>E [of t u v] by blast+

    lemma join_assoc:
    shows "t \<squnion> (u \<squnion> v) = (t \<squnion> u) \<squnion> v"
    proof -
      have *: "\<And>t u v. con (t \<squnion> u) v \<Longrightarrow> t \<squnion> (u \<squnion> v) = (t \<squnion> u) \<squnion> v"
      proof -
        fix t u v
        assume 1: "con (t \<squnion> u) v"
        have vt_ut: "v \\ t \<frown> u \\ t"
          using 1
          by (metis con_with_join_of_iff(2) join_def join_is_join_of not_con_null(1))
        have tv_uv: "t \\ v \<frown> u \\ v"
          using vt_ut cube con_sym
          by (metis arr_resid_iff_con)
        have 2: "(t \<squnion> u) \<squnion> v = (t \<cdot> (u \\ t)) \<cdot> (v \\ (t \<cdot> (u \\ t)))"
          using 1
          by (metis comp_is_composite_of(2) con_implies_arr(1) has_joins join_is_join_of
                    join_of_def joinable_iff_arr_join)
        also have "... = t \<cdot> ((u \\ t) \<cdot> (v \\ (t \<cdot> (u \\ t))))"
          using 1
          by (metis calculation has_joins joinable_iff_join_not_null comp_assoc comp_def)
        also have "... = t \<cdot> ((u \\ t) \<cdot> ((v \\ t) \\ (u \\ t)))"
          using 1
          by (metis 2 comp_null(2) con_compI(2) con_comp_iff has_joins resid_comp(1)
              conI joinable_iff_join_not_null)
        also have "... = t \<cdot> ((v \\ t) \<squnion> (u \\ t))"
          by (metis vt_ut comp_is_composite_of(2) has_joins join_of_def join_is_join_of)
        also have "... = t \<cdot> ((u \\ t) \<squnion> (v \\ t))"
          using join_sym by metis
        also have "... = t \<cdot> ((u \<squnion> v) \\ t)"
          by (metis tv_uv vt_ut con_implies_arr(2) con_sym con_with_join_of_iff(1) has_joins
                    join_is_join_of arr_resid_iff_con resid_join\<^sub>E(3))
        also have "... = t \<squnion> (u \<squnion> v)"
          by (metis comp_is_composite_of(2) comp_null(2) conI has_joins join_is_join_of
              join_of_def joinable_iff_join_not_null)
        finally show "t \<squnion> (u \<squnion> v) = (t \<squnion> u) \<squnion> v"
          by simp
      qed
      thus ?thesis
        by (metis (full_types) has_joins joinable_iff_join_not_null joinable_implies_con con_sym)
    qed

    lemma join_is_lub:
    assumes "t \<lesssim> v" and "u \<lesssim> v"
    shows "t \<squnion> u \<lesssim> v"
    proof -
      have "(t \<squnion> u) \\ v = (t \\ v) \<squnion> (u \\ v)"
        using assms resid_join\<^sub>E(3) [of t u v]
        by (metis arr_prfx_join_self con_target con_sym join_assoc joinable_iff_con
            joinable_iff_join_not_null prfx_implies_con resid_reflects_con)
      also have "... = trg v \<squnion> trg v"
        using assms
        by (metis ideE prfx_implies_con src_resid trg_ide)
      also have "... = trg v"
        by (metis assms(2) ide_iff_src_self ide_implies_arr join_arr_self prfx_implies_con
            src_resid)
      finally have "(t \<squnion> u) \\ v = trg v" by blast
      moreover have "ide (trg v)"
        using assms
        by (metis con_implies_arr(2) prfx_implies_con cong_char trg_def)
      ultimately show ?thesis by simp
    qed
        
  end

  subsubsection "Extensional RTS with Composites"

  text \<open>
    If an extensional RTS is assumed to have composites for all composable pairs of transitions,
    then the ``semantic'' property of transitions being composable can be replaced by the
    ``syntactic'' property of transitions being sequential.  This results in simpler
    statements of a number of properties.
  \<close>

  locale extensional_rts_with_composites =
    rts_with_composites +
    extensional_rts
  begin

    lemma seq_implies_arr_comp:
    assumes "seq t u"
    shows "arr (t \<cdot> u)"
      using assms
      by (meson composable_iff_arr_comp composable_iff_seq)

    lemma arr_comp\<^sub>E\<^sub>C [intro, simp]:
    assumes "arr t" and "arr u" and "trg t = src u"
    shows "arr (t \<cdot> u)"
      using assms
      by (simp add: seq_implies_arr_comp)

    lemma arr_compE\<^sub>E\<^sub>C [elim]:
    assumes "arr (t \<cdot> u)"
    and "\<lbrakk>arr t; arr u; trg t = src u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms composable_iff_arr_comp composable_iff_seq by blast

    lemma trg_comp\<^sub>E\<^sub>C [simp]:
    assumes "seq t u"
    shows "trg (t \<cdot> u) = trg u"
      by (meson assms has_composites trg_comp)

    lemma src_comp\<^sub>E\<^sub>C [simp]:
    assumes "seq t u"
    shows "src (t \<cdot> u) = src t"
      using assms src_comp has_composites by simp

    lemma con_comp_iff\<^sub>E\<^sub>C [simp]:
    shows "w \<frown> t \<cdot> u \<longleftrightarrow> seq t u \<and> u \<frown> w \\ t"
    and "t \<cdot> u \<frown> w \<longleftrightarrow> seq t u \<and> u \<frown> w \\ t"
      using composable_iff_seq con_comp_iff con_sym by meson+

    lemma comp_assoc\<^sub>E\<^sub>C:
    shows "t \<cdot> (u \<cdot> v) = (t \<cdot> u) \<cdot> v"
      apply (cases "seq t u")
       apply (metis arr_comp comp_assoc comp_def not_arr_null arr_compE\<^sub>E\<^sub>C arr_comp\<^sub>E\<^sub>C
                    seq_implies_arr_comp trg_comp\<^sub>E\<^sub>C)
      by (metis comp_def composable_iff_arr_comp seqI\<^sub>W\<^sub>E(1) src_comp arr_compE\<^sub>E\<^sub>C)

    lemma diamond_commutes:
    shows "t \<cdot> (u \\ t) = u \<cdot> (t \\ u)"
    proof (cases "t \<frown> u")
      show "\<not> t \<frown> u \<Longrightarrow> ?thesis"
        by (metis comp_null(2) conI con_sym)
      assume con: "t \<frown> u"
      have "(t \<cdot> (u \\ t)) \\ u = (t \\ u) \<cdot> ((u \\ t) \\ (u \\ t))"
        using con
        by (metis (no_types, lifting) arr_resid_iff_con con_compI(2) con_implies_arr(1)
            resid_comp(2) con_imp_arr_resid con_sym comp_def arr_comp\<^sub>E\<^sub>C src_resid conI)
      moreover have "u \<lesssim> t \<cdot> (u \\ t)"
        by (metis arr_resid_iff_con calculation con cong_reflexive comp_arr_trg resid_arr_self
            resid_comp(1) apex_sym)
      ultimately show ?thesis
        by (metis comp_eqI con comp_arr_trg resid_arr_self arr_resid apex_sym)
    qed

    lemma mediating_transition:
    assumes "t \<cdot> v = u \<cdot> w"
    shows "v \\ (u \\ t) = w \\ (t \\ u)"
    proof (cases "seq t v")
      assume 1: "seq t v"
      hence 2: "arr (u \<cdot> w)"
        using assms by (metis arr_comp\<^sub>E\<^sub>C seqE\<^sub>W\<^sub>E)
      have 3: "v \\ (u \\ t) = ((t \<cdot> v) \\ t) \\ (u \\ t)"
        by (metis 2 assms comp_resid_prfx)
      also have "... = (t \<cdot> v) \\ (t \<cdot> (u \\ t))"
        by (metis (no_types, lifting) "2" assms con_comp_iff\<^sub>E\<^sub>C(2) con_imp_eq_src
            con_implies_arr(2) con_sym comp_resid_prfx prfx_comp resid_comp(1)
            arr_compE\<^sub>E\<^sub>C arr_comp\<^sub>E\<^sub>C prfx_implies_con)
      also have "... = (u \<cdot> w) \\ (u \<cdot> (t \\ u))"
        using assms diamond_commutes by presburger
      also have "... = ((u \<cdot> w) \\ u) \\ (t \\ u)"
        by (metis 3 assms calculation cube)
      also have "... = w \\ (t \\ u)"
        using 2 by simp
      finally show ?thesis by blast
      next
      assume 1: "\<not> seq t v"
      have "v \\ (u \\ t) = null"
        using 1
        by (metis (mono_tags, lifting) arr_resid_iff_con coinitial_iff\<^sub>W\<^sub>E con_imp_coinitial
            seqI\<^sub>W\<^sub>E(2) src_resid conI)
      also have "... = w \\ (t \\ u)"
        by (metis (no_types, lifting) "1" arr_comp\<^sub>E\<^sub>C assms composable_imp_seq con_imp_eq_src
            con_implies_arr(1) con_implies_arr(2) comp_def not_arr_null conI src_resid)
      finally show ?thesis by blast
    qed

    lemma induced_arrow:
    assumes "seq t u" and "t \<cdot> u = t' \<cdot> u'"
    shows "(t' \\ t) \<cdot> (u \\ (t' \\ t)) = u"
    and "(t \\ t') \<cdot> (u \\ (t' \\ t)) = u'"
    and "(t' \\ t) \<cdot> v = u \<Longrightarrow> v = u \\ (t' \\ t)"
      apply (metis assms comp_eqI arr_compE\<^sub>E\<^sub>C prfx_comp resid_comp(1) arr_resid_iff_con
                   seq_implies_arr_comp)
       apply (metis assms comp_resid_prfx arr_compE\<^sub>E\<^sub>C resid_comp(2) arr_resid_iff_con
                    seq_implies_arr_comp)
      by (metis assms(1) comp_resid_prfx seq_def)

    text \<open>
      If an extensional RTS has composites, then it automatically has joins.
    \<close>

    sublocale extensional_rts_with_joins
    proof
      fix t u
      assume con: "t \<frown> u"
      have 1: "con u (t \<cdot> (u \\ t))"
        using con_compI(1) [of t "u \\ t" u]
        by (metis con con_implies_arr(1) con_sym diamond_commutes prfx_implies_con arr_resid
            prfx_comp src_resid arr_comp\<^sub>E\<^sub>C)
      have "t \<squnion> u = t \<cdot> (u \\ t)"
      proof (intro join_eqI)
        show "t \<lesssim> t \<cdot> (u \\ t)"
          by (metis 1 composable_def comp_is_composite_of(2) composite_of_def con_comp_iff)
        moreover show 2: "u \<lesssim> t \<cdot> (u \\ t)"
          using 1 arr_resid con con_sym prfx_reflexive resid_comp(1) by metis
        moreover show "(t \<cdot> (u \\ t)) \\ u = t \\ u"
          using 1 diamond_commutes induced_arrow(2) resid_comp(2) by force
        ultimately show "(t \<cdot> (u \\ t)) \\ t = u \\ t"
          by (metis con_comp_iff\<^sub>E\<^sub>C(1) con_sym prfx_implies_con resid_comp(2) induced_arrow(1))
      qed
      thus "joinable t u"
        by (metis "1" con_implies_arr(2) joinable_iff_join_not_null not_arr_null)
    qed

    lemma comp_join\<^sub>E\<^sub>C:
    assumes "composable t u" and "joinable u u'"
    shows "composable t (u \<squnion> u')"
    and "t \<cdot> (u \<squnion> u') = t \<cdot> u \<squnion> t \<cdot> u'"
    proof -
      have 1: "u \<squnion> u' = u \<cdot> (u' \\ u) \<and> u \<squnion> u' = u' \<cdot> (u \\ u')"
        using assms joinable_implies_con diamond_commutes
        by (metis comp_is_composite_of(2) join_is_join_of join_ofE)
      show 2: "composable t (u \<squnion> u')"
        using assms 1 composable_iff_seq arr_comp src_join arr_compE\<^sub>E\<^sub>C joinable_iff_arr_join
              seqI\<^sub>W\<^sub>E(1)
        by metis
      have "con (t \<cdot> u) (t \<cdot> u')"
        using 1 2 arr_comp arr_compE\<^sub>E\<^sub>C assms(2) comp_assoc\<^sub>E\<^sub>C comp_resid_prfx
              con_comp_iff joinable_implies_con comp_def not_arr_null
        by metis
      thus "t \<cdot> (u \<squnion> u') = t \<cdot> u \<squnion> t \<cdot> u'"
        using assms comp_join(2) joinable_iff_con by blast
    qed

    lemma join_expansion:
    assumes "t \<frown> u"
    shows "t \<squnion> u = t \<cdot> (u \\ t)" and "seq t (u \\ t)"
    proof -
      show "t \<squnion> u = t \<cdot> (u \\ t)"
        by (metis assms comp_is_composite_of(2) has_joins join_is_join_of join_of_def)
      thus "seq t (u \\ t)"
        by (meson assms composable_def composable_iff_seq has_joins join_is_join_of join_of_def)
    qed

    lemma join3_expansion:
    assumes "t \<frown> u" and "t \<frown> v" and "u \<frown> v"
    shows "(t \<squnion> u) \<squnion> v = (t \<cdot> (u \\ t)) \<cdot> ((v \\ t) \\ (u \\ t))"
    proof (cases "v \\ t \<frown> u \\ t")
      show "\<not> v \\ t \<frown> u \\ t \<Longrightarrow> ?thesis"
        by (metis assms(1) comp_null(2) join_expansion(1) joinable_implies_con
            resid_comp(1) join_def conI)
      assume 1: "v \\ t \<frown> u \\ t "
      have "(t \<squnion> u) \<squnion> v = (t \<squnion> u) \<cdot> (v \\ (t \<squnion> u))"
        by (metis comp_null(1) diamond_commutes ex_un_null join_expansion(1)
            joinable_implies_con null_is_zero(2) join_def conI)
      also have "... = (t \<cdot> (u \\ t)) \<cdot> (v \\ (t \<squnion> u))"
        using join_expansion [of t u] assms(1) by presburger
      also have "... = (t \<cdot> (u \\ t)) \<cdot> ((v \\ u) \\ (t \\ u))"
        using assms 1 join_of_resid(1) [of t u v] cube [of v t u]
        by (metis con_compI(2) con_implies_arr(2) join_expansion(1) not_arr_null resid_comp(1)
            con_sym comp_def src_resid arr_comp\<^sub>E\<^sub>C)
      also have "... = (t \<cdot> (u \\ t)) \<cdot> ((v \\ t) \\ (u \\ t))"
        by (metis cube)
      finally show ?thesis by blast
    qed

    lemma resid_common_prefix:
    assumes "t \<cdot> u \<frown> t \<cdot> v"
    shows "(t \<cdot> u) \\ (t \<cdot> v) = u \\ v"
      using assms
      by (metis con_comp_iff con_sym con_comp_iff\<^sub>E\<^sub>C(2) con_implies_arr(2) induced_arrow(1)
          resid_comp(1) resid_comp(2) residuation.arr_resid_iff_con residuation_axioms)

    lemma join_comp:
    assumes "t \<cdot> u \<frown> v"
    shows "(t \<cdot> u) \<squnion> v = t \<cdot> (v \\ t) \<cdot> (u \\ (v \\ t))"
      using assms
      by (metis comp_assoc\<^sub>E\<^sub>C diamond_commutes join_expansion(1) resid_comp(1))

  end

  subsection "Confluence"

  text \<open>
    An RTS is \emph{confluent} if every coinitial pair of transitions is consistent.
  \<close>
  
  locale confluent_rts = rts +
  assumes confluence: "coinitial t u \<Longrightarrow> con t u"

  section "Simulations"

  text \<open>
    \emph{Simulations} are morphisms of residuated transition systems.
    They are assumed to preserve consistency and residuation.
  \<close>

  locale simulation =
    A: rts A +
    B: rts B
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and F :: "'a \<Rightarrow> 'b" +
  assumes extensional: "\<not> A.arr t \<Longrightarrow> F t = B.null"
  and preserves_con [simp]: "A.con t u \<Longrightarrow> B.con (F t) (F u)"
  and preserves_resid [simp]: "A.con t u \<Longrightarrow> F (t \\\<^sub>A u) = F t \\\<^sub>B F u"
  begin

    notation A.con     (infix "\<frown>\<^sub>A" 50)
    notation A.prfx    (infix "\<lesssim>\<^sub>A" 50)
    notation A.cong    (infix "\<sim>\<^sub>A" 50)

    notation B.con     (infix "\<frown>\<^sub>B" 50)
    notation B.prfx    (infix "\<lesssim>\<^sub>B" 50)
    notation B.cong    (infix "\<sim>\<^sub>B" 50)

    lemma preserves_reflects_arr [iff]:
    shows "B.arr (F t) \<longleftrightarrow> A.arr t"
      by (metis A.arr_def B.con_implies_arr(2) B.not_arr_null extensional preserves_con)

    lemma preserves_ide [simp]:
    assumes "A.ide a"
    shows "B.ide (F a)"
      by (metis A.ideE assms preserves_con preserves_resid B.ideI)

    lemma preserves_sources:
    shows "F ` A.sources t \<subseteq> B.sources (F t)"
      using A.sources_def B.sources_def preserves_con preserves_ide by auto

    lemma preserves_targets:
    shows "F ` A.targets t \<subseteq> B.targets (F t)"
      by (metis A.arrE B.arrE A.sources_resid B.sources_resid equals0D image_subset_iff
          A.arr_iff_has_target preserves_reflects_arr preserves_resid preserves_sources)

    lemma preserves_trg [simp]:
    assumes "A.arr t"
    shows "B.trg (F t) = F (A.trg t)"
      using assms A.trg_def B.trg_def by auto

    lemma preserves_composites:
    assumes "A.composite_of t u v"
    shows "B.composite_of (F t) (F u) (F v)"
      using assms
      by (metis A.composite_ofE A.prfx_implies_con B.composite_of_def preserves_ide
          preserves_resid A.con_sym)

    lemma preserves_joins:
    assumes "A.join_of t u v"
    shows "B.join_of (F t) (F u) (F v)"
      using assms A.join_of_def B.join_of_def A.joinable_def
      by (metis A.joinable_implies_con preserves_composites preserves_resid)

    lemma preserves_prfx:
    assumes "t \<lesssim>\<^sub>A u"
    shows "F t \<lesssim>\<^sub>B F u"
      using assms
      by (metis A.prfx_implies_con preserves_ide preserves_resid)

    lemma preserves_cong:
    assumes "t \<sim>\<^sub>A u"
    shows "F t \<sim>\<^sub>B F u"
      using assms preserves_prfx by simp

  end

  subsection "Identity Simulation"

  locale identity_simulation =
    rts
  begin

    abbreviation map
    where "map \<equiv> \<lambda>t. if arr t then t else null"

    sublocale simulation resid resid map
      using con_implies_arr con_sym arr_resid_iff_con
      by unfold_locales auto

  end

  subsection "Composite of Simulations"

  lemma simulation_comp [intro]:
  assumes "simulation A B F" and "simulation B C G"
  shows "simulation A C (G o F)"
  proof -
    interpret F: simulation A B F using assms(1) by auto
    interpret G: simulation B C G using assms(2) by auto
    show "simulation A C (G o F)"
      using F.extensional G.extensional by unfold_locales auto
  qed

  locale composite_simulation =
    F: simulation A B F +
    G: simulation B C G
  for A :: "'a resid"
  and B :: "'b resid"
  and C :: "'c resid"
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'c"
  begin

    abbreviation map
    where "map \<equiv> G o F"

    sublocale simulation A C map
      using F.simulation_axioms G.simulation_axioms by blast

    lemma is_simulation:
    shows "simulation A C map"
      using F.simulation_axioms G.simulation_axioms by blast

  end

  subsection "Simulations into a Weakly Extensional RTS"

  locale simulation_to_weakly_extensional_rts =
    simulation +
    B: weakly_extensional_rts B
  begin

    lemma preserves_src [simp]:
    shows "a \<in> A.sources t \<Longrightarrow> B.src (F t) = F a"
      by (metis equals0D image_subset_iff B.arr_iff_has_source
          preserves_sources B.arr_has_un_source B.src_in_sources)

    lemma preserves_trg [simp]:
    shows "b \<in> A.targets t \<Longrightarrow> B.trg (F t) = F b"
      by (metis equals0D image_subset_iff B.arr_iff_has_target
          preserves_targets B.arr_has_un_target B.trg_in_targets)

  end

  subsection "Simulations into an Extensional RTS"

  locale simulation_to_extensional_rts =
    simulation +
    B: extensional_rts B
  begin

    notation B.comp  (infixl "\<cdot>\<^sub>B" 55)
    notation B.join  (infix "\<squnion>\<^sub>B" 52)

    lemma preserves_comp:
    assumes "A.composite_of t u v"
    shows "F v = F t \<cdot>\<^sub>B F u"
      using assms
      by (metis preserves_composites B.comp_is_composite_of(2))

    lemma preserves_join:
    assumes "A.join_of t u v"
    shows "F v = F t \<squnion>\<^sub>B F u"
      using assms preserves_joins
      by (meson B.join_is_join_of B.join_of_unique B.joinable_def)

  end

  subsection "Simulations between Extensional RTS's"

  locale simulation_between_extensional_rts =
    simulation_to_extensional_rts +
    A: extensional_rts A
  begin

    notation A.comp  (infixl "\<cdot>\<^sub>A" 55)
    notation A.join  (infix "\<squnion>\<^sub>A" 52)

    lemma preserves_src [simp]:
    shows "B.src (F t) = F (A.src t)"
      by (metis A.arr_src_iff_arr A.src_in_sources extensional image_subset_iff
          preserves_reflects_arr preserves_sources B.arr_has_un_source B.src_def
          B.src_in_sources)

    lemma preserves_trg [simp]:
    shows "B.trg (F t) = F (A.trg t)"
      by (metis A.arr_trg_iff_arr A.residuation_axioms A.trg_def B.null_is_zero(2) B.trg_def
          extensional preserves_resid residuation.arrE)

    lemma preserves_comp:
    assumes "A.composable t u"
    shows "F (t \<cdot>\<^sub>A u) = F t \<cdot>\<^sub>B F u"
      using assms
      by (metis A.arr_comp A.comp_resid_prfx A.composableD(2) A.not_arr_null
          A.prfx_comp A.residuation_axioms B.comp_eqI preserves_prfx preserves_resid
          residuation.conI)

    lemma preserves_join:
    assumes "A.joinable t u"
    shows "F (t \<squnion>\<^sub>A u) = F t \<squnion>\<^sub>B F u"
      using assms
      by (meson A.join_is_join_of B.joinable_def preserves_joins B.join_is_join_of
          B.join_of_unique)

  end

  subsection "Transformations"

  text \<open>
    A \emph{transformation} is a morphism of simulations, analogously to how a natural
    transformation is a morphism of functors, except the normal commutativity
    condition for that ``naturality squares'' is replaced by the requirement that
    the arrows at the apex of such a square are given by residuation of the
    arrows at the base.  If the codomain RTS is extensional, then this
    condition implies the commutativity of the square with respect to composition,
    as would be the case for a natural transformation between functors.

    The proper way to define a transformation when the domain and codomain are
    general RTS's is not yet clear to me.  However, if the domain and codomain are
    weakly extensional, then we have unique sources and targets, so there is no problem.
    The definition below is limited to that case.  I do not make any attempt here
    to develop facts about transformations.  My main reason for including this
    definition here is so that in the subsequent application to the \<open>\<lambda>\<close>-calculus,
    I can exhibit \<open>\<beta>\<close>-reduction as an example of a transformation.
  \<close>

  locale transformation =
    A: weakly_extensional_rts A +
    B: weakly_extensional_rts B +
    F: simulation A B F +
    G: simulation A B G
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes extensional: "\<not> A.arr f \<Longrightarrow> \<tau> f = B.null"
  and preserves_src: "A.ide f \<Longrightarrow> B.src (\<tau> f) = F f"
  and preserves_trg: "A.ide f \<Longrightarrow> B.trg (\<tau> f) = G f"
  and naturality1_ax: "A.arr f \<Longrightarrow> \<tau> (A.src f) \\\<^sub>B F f = \<tau> (A.trg f)"
  and naturality2_ax: "A.arr f \<Longrightarrow> F f \\\<^sub>B \<tau> (A.src f) = G f"
  and naturality3: "A.arr f \<Longrightarrow> B.join_of (\<tau> (A.src f)) (F f) (\<tau> f)"
  begin

    notation A.con     (infix "\<frown>\<^sub>A" 50)
    notation A.prfx    (infix "\<lesssim>\<^sub>A" 50)

    notation B.con     (infix "\<frown>\<^sub>B" 50)
    notation B.prfx    (infix "\<lesssim>\<^sub>B" 50)

    lemma naturality1:
    shows "\<tau> (A.src f) \\\<^sub>B F f = \<tau> (A.trg f)"
      by (metis A.arr_trg_iff_arr B.null_is_zero(2) F.extensional transformation.extensional
          transformation.naturality1_ax transformation_axioms)

    lemma naturality2:
    shows "F f \\\<^sub>B \<tau> (A.src f) = G f"
      by (metis A.weakly_extensional_rts_axioms B.null_is_zero(2) G.extensional extensional
          naturality2_ax weakly_extensional_rts.arr_src_iff_arr)

  end

  section "Normal Sub-RTS's and Congruence"

  text \<open>
    We now develop a general quotient construction on an RTS.
    We define a \emph{normal sub-RTS} of an RTS to be a collection of transitions \<open>\<NN>\<close> having
    certain ``local'' closure properties.  A normal sub-RTS induces an equivalence
    relation \<open>\<approx>\<^sub>0\<close>, which we call \emph{semi-congruence}, by defining \<open>t \<approx>\<^sub>0 u\<close> to hold exactly
    when \<open>t \ u\<close> and \<open>u \ t\<close> are both in \<open>\<NN>\<close>.  This relation generalizes the relation \<open>\<sim>\<close>
    defined for an arbitrary RTS, in the sense that \<open>\<sim>\<close> is obtained when \<open>\<NN>\<close> consists of
    all and only the identity transitions.  However, in general the relation \<open>\<approx>\<^sub>0\<close> is fully
    substitutive only in the left argument position of residuation; for the right argument position,
    a somewhat weaker property is satisfied.  We then coarsen \<open>\<approx>\<^sub>0\<close> to a relation \<open>\<approx>\<close>, by defining
    \<open>t \<approx> u\<close> to hold exactly when \<open>t\<close> and \<open>u\<close> can be transported by residuation along transitions
    in \<open>\<NN>\<close> to a common source, in such a way that the residuals are related by \<open>\<approx>\<^sub>0\<close>.
    To obtain full substitutivity of \<open>\<approx>\<close> with respect to residuation, we need to impose an
    additional condition on \<open>\<NN>\<close>.  This condition, which we call \emph{coherence},
    states that transporting a transition \<open>t\<close> along parallel transitions \<open>u\<close> and \<open>v\<close> in \<open>\<NN>\<close> always
    yields  residuals \<open>t \ u\<close> and \<open>u \ t\<close> that are related by \<open>\<approx>\<^sub>0\<close>.  We show that, under the
    assumption of coherence, the relation \<open>\<approx>\<close> is fully substitutive, and the quotient of the
    original RTS by this relation is an extensional RTS which has the \<open>\<NN>\<close>-connected components of
    the original RTS as identities.  Although the coherence property has a somewhat \emph{ad hoc}
    feel to it, we show that, in the context of the other conditions assumed for \<open>\<NN>\<close>, coherence is
    in fact equivalent to substitutivity for \<open>\<approx>\<close>.
  \<close>

  subsection "Normal Sub-RTS's"

  locale normal_sub_rts =
    R: rts +
    fixes \<NN> :: "'a set"
    assumes elements_are_arr: "t \<in> \<NN> \<Longrightarrow> R.arr t"
    and ide_closed: "R.ide a \<Longrightarrow> a \<in> \<NN>"
    and forward_stable: "\<lbrakk> u \<in> \<NN>; R.coinitial t u \<rbrakk> \<Longrightarrow> u \\ t \<in> \<NN>"
    and backward_stable: "\<lbrakk> u \<in> \<NN>; t \\ u \<in> \<NN> \<rbrakk> \<Longrightarrow> t \<in> \<NN>"
    and composite_closed_left: "\<lbrakk> u \<in> \<NN>; R.seq u t \<rbrakk> \<Longrightarrow> \<exists>v. R.composite_of u t v"
    and composite_closed_right: "\<lbrakk> u \<in> \<NN>; R.seq t u \<rbrakk> \<Longrightarrow> \<exists>v. R.composite_of t u v"
  begin

    lemma prfx_closed:
    assumes "u \<in> \<NN>" and "R.prfx t u"
    shows "t \<in> \<NN>"
      using assms backward_stable ide_closed by blast

    lemma composite_closed:
    assumes "t \<in> \<NN>" and "u \<in> \<NN>" and "R.composite_of t u v"
    shows "v \<in> \<NN>"
      using assms backward_stable R.composite_of_def prfx_closed by blast

    lemma factor_closed:
    assumes "R.composite_of t u v" and "v \<in> \<NN>"
    shows "t \<in> \<NN>" and "u \<in> \<NN>"
       apply (metis assms R.composite_of_def prfx_closed)
      by (meson assms R.composite_of_def R.con_imp_coinitial forward_stable prfx_closed
                R.prfx_implies_con)

    lemma resid_along_elem_preserves_con:
    assumes "t \<frown> t'" and "R.coinitial t u" and "u \<in> \<NN>"
    shows "t \\ u \<frown> t' \\ u"
    proof -
      have "R.coinitial (t \\ t') (u \\ t')"
        by (metis assms R.arr_resid_iff_con R.coinitialI R.con_imp_common_source forward_stable
            elements_are_arr R.con_implies_arr(2) R.sources_resid R.sources_eqI)
      hence "t \\ t' \<frown> u \\ t'"
        by (metis assms(3) R.coinitial_iff R.con_imp_coinitial R.con_sym elements_are_arr
                  forward_stable R.arr_resid_iff_con)
      thus ?thesis
        using assms R.cube forward_stable by fastforce
    qed

  end

  subsubsection "Normal Sub-RTS's of an Extensional RTS with Composites"

  locale normal_in_extensional_rts_with_composites =
     R: extensional_rts +
     R: rts_with_composites +
     normal_sub_rts
  begin

    lemma factor_closed\<^sub>E\<^sub>C:
    assumes "t \<cdot> u \<in> \<NN>"
    shows "t \<in> \<NN>" and "u \<in> \<NN>"
      using assms factor_closed
      by (metis R.arrE R.composable_def R.comp_is_composite_of(2) R.con_comp_iff
                elements_are_arr)+

    lemma comp_in_normal_iff:
    shows "t \<cdot> u \<in> \<NN> \<longleftrightarrow> t \<in> \<NN> \<and> u \<in> \<NN> \<and> R.seq t u"
      by (metis R.comp_is_composite_of(2) composite_closed elements_are_arr
          factor_closed(1-2) R.composable_def R.has_composites R.rts_with_composites_axioms
          R.extensional_rts_axioms extensional_rts_with_composites.arr_compE\<^sub>E\<^sub>C
          extensional_rts_with_composites_def R.seqI\<^sub>W\<^sub>E(1))

  end

  subsection "Semi-Congruence"

  context normal_sub_rts
  begin

    text \<open>
      We will refer to the elements of \<open>\<NN>\<close> as \emph{normal transitions}.
      Generalizing identity transitions to normal transitions in the definition of congruence,
      we obtain the notion of \emph{semi-congruence} of transitions with respect to a
      normal sub-RTS.
    \<close>

    abbreviation Cong\<^sub>0  (infix "\<approx>\<^sub>0" 50)
    where "t \<approx>\<^sub>0 t' \<equiv> t \\ t' \<in> \<NN> \<and> t' \\ t \<in> \<NN>"

    lemma Cong\<^sub>0_reflexive:
    assumes "R.arr t"
    shows "t \<approx>\<^sub>0 t"
      using assms R.cong_reflexive ide_closed by simp

    lemma Cong\<^sub>0_symmetric:
    assumes "t \<approx>\<^sub>0 t'"
    shows "t' \<approx>\<^sub>0 t"
      using assms by simp

    lemma Cong\<^sub>0_transitive [trans]:
    assumes "t \<approx>\<^sub>0 t'" and "t' \<approx>\<^sub>0 t''"
    shows "t \<approx>\<^sub>0 t''"
      by (metis (full_types) R.arr_resid_iff_con assms backward_stable forward_stable
          elements_are_arr R.coinitialI R.cube R.sources_resid)

    lemma Cong\<^sub>0_imp_con:
    assumes "t \<approx>\<^sub>0 t'"
    shows "R.con t t'"
      using assms R.arr_resid_iff_con elements_are_arr by blast

    lemma Cong\<^sub>0_imp_coinitial:
    assumes "t \<approx>\<^sub>0 t'"
    shows "R.sources t = R.sources t'"
      using assms by (meson Cong\<^sub>0_imp_con R.coinitial_iff R.con_imp_coinitial)

    text \<open>
      Semi-congruence is preserved and reflected by residuation along normal transitions.
    \<close>

    lemma Resid_along_normal_preserves_Cong\<^sub>0:
    assumes "t \<approx>\<^sub>0 t'" and "u \<in> \<NN>" and "R.sources t = R.sources u" 
    shows "t \\ u \<approx>\<^sub>0 t' \\ u"
      by (metis Cong\<^sub>0_imp_coinitial R.arr_resid_iff_con R.coinitialI R.coinitial_def
          R.cube R.sources_resid assms elements_are_arr forward_stable)

    lemma Resid_along_normal_reflects_Cong\<^sub>0:
    assumes "t \\ u \<approx>\<^sub>0 t' \\ u" and "u \<in> \<NN>"
    shows "t \<approx>\<^sub>0 t'"
      using assms
      by (metis backward_stable R.con_imp_coinitial R.cube R.null_is_zero(2)
                forward_stable R.conI)

    text \<open>
      Semi-congruence is substitutive for the left-hand argument of residuation.
    \<close>

    lemma Cong\<^sub>0_subst_left:
    assumes "t \<approx>\<^sub>0 t'" and "t \<frown> u"
    shows "t' \<frown> u" and "t \\ u \<approx>\<^sub>0 t' \\ u"
    proof -
      have 1: "t \<frown> u \<and> t \<frown> t' \<and> u \\ t \<frown> t' \\ t"
        using assms
        by (metis Resid_along_normal_preserves_Cong\<^sub>0 Cong\<^sub>0_imp_con Cong\<^sub>0_reflexive R.con_sym
                  R.null_is_zero(2) R.arr_resid_iff_con R.sources_resid R.conI)
      hence 2: "t' \<frown> u \<and> u \\ t \<frown> t' \\ t \<and>
                (t \\ u) \\ (t' \\ u) = (t \\ t') \\ (u \\ t') \<and>
                (t' \\ u) \\ (t \\ u) = (t' \\ t) \\ (u \\ t)"
        by (meson R.con_sym R.cube R.resid_reflects_con)
      show "t' \<frown> u"
        using 2 by simp
      show "t \\ u \<approx>\<^sub>0 t' \\ u"
        using assms 1 2
        by (metis R.arr_resid_iff_con R.con_imp_coinitial R.cube forward_stable)
    qed

    text \<open>
      Semi-congruence is not exactly substitutive for residuation on the right.
      Instead, the following weaker property is satisfied.  Obtaining exact substitutivity
      on the right is the motivation for defining a coarser notion of congruence below.
    \<close>

    lemma Cong\<^sub>0_subst_right:
    assumes "u \<approx>\<^sub>0 u'" and "t \<frown> u"
    shows "t \<frown> u'" and "(t \\ u) \\ (u' \\ u) \<approx>\<^sub>0 (t \\ u') \\ (u \\ u')"
      using assms
       apply (meson Cong\<^sub>0_subst_left(1) R.con_sym)
      using assms
      by (metis R.sources_resid Cong\<^sub>0_imp_con Cong\<^sub>0_reflexive Resid_along_normal_preserves_Cong\<^sub>0
                R.arr_resid_iff_con residuation.cube R.residuation_axioms)

    lemma Cong\<^sub>0_subst_Con:
    assumes "t \<approx>\<^sub>0 t'" and "u \<approx>\<^sub>0 u'"
    shows "t \<frown> u \<longleftrightarrow> t' \<frown> u'"
      using assms
      by (meson Cong\<^sub>0_subst_left(1) Cong\<^sub>0_subst_right(1))

    lemma Cong\<^sub>0_cancel_left:
    assumes "R.composite_of t u v" and "R.composite_of t u' v'" and "v \<approx>\<^sub>0 v'"
    shows "u \<approx>\<^sub>0 u'"
    proof -
      have "u \<approx>\<^sub>0 v \\ t"
        using assms(1) ide_closed by blast
      also have "v \\ t \<approx>\<^sub>0 v' \\ t"
        by (meson assms(1,3) Cong\<^sub>0_subst_left(2) R.composite_of_def R.con_sym R.prfx_implies_con)
      also have "v' \\ t \<approx>\<^sub>0 u'"
        using assms(2) ide_closed by blast
      finally show ?thesis by auto
    qed

    lemma Cong\<^sub>0_iff:
    shows "t \<approx>\<^sub>0 t' \<longleftrightarrow>
           (\<exists>u u' v v'. u \<in> \<NN> \<and> u' \<in> \<NN> \<and> v \<approx>\<^sub>0 v' \<and>
                        R.composite_of t u v \<and> R.composite_of t' u' v')"
    proof (intro iffI)
      show "\<exists>u u' v v'. u \<in> \<NN> \<and> u' \<in> \<NN> \<and> v \<approx>\<^sub>0 v' \<and>
                        R.composite_of t u v \<and> R.composite_of t' u' v'
               \<Longrightarrow> t \<approx>\<^sub>0 t'"
        by (meson Cong\<^sub>0_transitive R.composite_of_def ide_closed prfx_closed)
      show "t \<approx>\<^sub>0 t' \<Longrightarrow> \<exists>u u' v v'. u \<in> \<NN> \<and> u' \<in> \<NN> \<and> v \<approx>\<^sub>0 v' \<and>
                                    R.composite_of t u v \<and> R.composite_of t' u' v'"
        by (metis Cong\<^sub>0_imp_con Cong\<^sub>0_transitive R.composite_of_def R.prfx_reflexive
            R.arrI R.ideE)
    qed

    lemma diamond_commutes_upto_Cong\<^sub>0:
    assumes "t \<frown> u" and "R.composite_of t (u \\ t) v" and "R.composite_of u (t \\ u) v'"
    shows "v \<approx>\<^sub>0 v'"
    proof -
      have "v \\ v \<approx>\<^sub>0 v' \\ v \<and> v' \\ v' \<approx>\<^sub>0 v \\ v'"
      proof-
        have 1: "(v \\ t) \\ (u \\ t) \<approx>\<^sub>0 (v' \\ u) \\ (t \\ u)"
          using assms(2-3) R.cube [of v t u]
          by (metis R.con_target R.composite_ofE R.ide_imp_con_iff_cong ide_closed
              R.conI)
        have 2: "v \\ v \<approx>\<^sub>0 v' \\ v"
        proof -
          have "v \\ v \<approx>\<^sub>0 (v \\ t) \\ (u \\ t)"
            using assms R.composite_of_def ide_closed
            by (meson R.composite_of_unq_upto_cong R.prfx_implies_con R.resid_composite_of(3))
          also have "(v \\ t) \\ (u \\ t) \<approx>\<^sub>0 (v' \\ u) \\ (t \\ u)"
            using 1 by simp
          also have "(v' \\ u) \\ (t \\ u) \<approx>\<^sub>0 (v' \\ t) \\ (u \\ t)"
            by (metis "1" Cong\<^sub>0_transitive R.cube)
          also have "(v' \\ t) \\ (u \\ t) \<approx>\<^sub>0 v' \\ v"
            using assms R.composite_of_def ide_closed
            by (metis "1" R.conI R.con_sym_ax R.cube R.null_is_zero(2) R.resid_composite_of(3))
          finally show ?thesis by auto
        qed
        moreover have "v' \\ v' \<approx>\<^sub>0 v \\ v'"
        proof -
          have "v' \\ v' \<approx>\<^sub>0 (v' \\ u) \\ (t \\ u)"
            using assms R.composite_of_def ide_closed
            by (meson R.composite_of_unq_upto_cong R.prfx_implies_con R.resid_composite_of(3))
          also have "(v' \\ u) \\ (t \\ u) \<approx>\<^sub>0 (v \\ t) \\ (u \\ t)"
            using 1 by simp
          also have "(v \\ t) \\ (u \\ t) \<approx>\<^sub>0 (v \\ u) \\ (t \\ u)"
            using R.cube [of v t u] ide_closed
            by (metis Cong\<^sub>0_reflexive R.arr_resid_iff_con assms(2) R.composite_of_def
                      R.prfx_implies_con)
          also have "(v \\ u) \\ (t \\ u) \<approx>\<^sub>0 v \\ v'"
            using assms R.composite_of_def ide_closed
            by (metis 2 R.conI elements_are_arr R.not_arr_null R.null_is_zero(2)
                R.resid_composite_of(3))
          finally show ?thesis by auto
        qed
        ultimately show ?thesis by blast
      qed
      thus ?thesis
        by (metis assms(2-3) R.composite_of_unq_upto_cong R.resid_arr_ide Cong\<^sub>0_imp_con)
    qed

    subsection "Congruence"

    text \<open>
      We use semi-congruence to define a coarser relation as follows.
    \<close>

    definition Cong  (infix "\<approx>" 50)
    where "Cong t t' \<equiv> \<exists>u u'. u \<in> \<NN> \<and> u' \<in> \<NN> \<and> t \\ u \<approx>\<^sub>0 t' \\ u'"

    lemma CongI [intro]:
    assumes "u \<in> \<NN>" and "u' \<in> \<NN>" and "t \\ u \<approx>\<^sub>0 t' \\ u'"
    shows "Cong t t'"
      using assms Cong_def by auto

    lemma CongE [elim]:
    assumes "t \<approx> t'"
    obtains u u'
    where "u \<in> \<NN>" and "u' \<in> \<NN>" and "t \\ u \<approx>\<^sub>0 t' \\ u'"
      using assms Cong_def by auto

    lemma Cong_imp_arr:
    assumes "t \<approx> t'"
    shows "R.arr t" and "R.arr t'"
      using assms Cong_def
      by (meson R.arr_resid_iff_con R.con_implies_arr(2) R.con_sym elements_are_arr)+

    lemma Cong_reflexive:
    assumes "R.arr t"
    shows "t \<approx> t"
      by (metis CongI Cong\<^sub>0_reflexive assms R.con_imp_coinitial_ax ide_closed
          R.resid_arr_ide R.arrE R.con_sym)

    lemma Cong_symmetric:
    assumes "t \<approx> t'"
    shows "t' \<approx> t"
      using assms Cong_def by auto

    text \<open>
      The existence of composites of normal transitions is used in the following.
    \<close>

    lemma Cong_transitive [trans]:
    assumes "t \<approx> t''" and "t'' \<approx> t'"
    shows "t \<approx> t'"
    proof -
      obtain u u'' where uu'': "u \<in> \<NN> \<and> u'' \<in> \<NN> \<and> t \\ u \<approx>\<^sub>0 t'' \\ u''"
        using assms Cong_def by blast
      obtain v' v'' where v'v'': "v' \<in> \<NN> \<and> v'' \<in> \<NN> \<and> t'' \\ v'' \<approx>\<^sub>0 t' \\ v'"
        using assms Cong_def by blast
      let ?w = "(t \\ u) \\ (v'' \\ u'')"
      let ?w' = "(t' \\ v') \\ (u'' \\ v'')"
      let ?w'' = "(t'' \\ v'') \\ (u'' \\ v'')"
      have w'': "?w'' = (t'' \\ u'') \\ (v'' \\ u'')"
        by (metis R.cube)
      have u''v'': "R.coinitial u'' v''"
        by (metis (full_types) R.coinitial_iff elements_are_arr R.con_imp_coinitial
            R.arr_resid_iff_con uu'' v'v'')
      hence v''u'': "R.coinitial v'' u''"
        by (meson R.con_imp_coinitial elements_are_arr forward_stable R.arr_resid_iff_con v'v'')
      have 1: "?w \\ ?w'' \<in> \<NN>"
      proof -
        have "(v'' \\ u'') \\ (t'' \\ u'') \<in> \<NN>"
          by (metis Cong\<^sub>0_transitive R.con_imp_coinitial forward_stable Cong\<^sub>0_imp_con
              resid_along_elem_preserves_con R.arrI R.arr_resid_iff_con u''v'' uu'' v'v'')
        thus ?thesis
          by (metis Cong\<^sub>0_subst_left(2) R.con_sym R.null_is_zero(1) uu'' w'' R.conI)
      qed
      have 2: "?w'' \\ ?w \<in> \<NN>"
        by (metis 1 Cong\<^sub>0_subst_left(2) uu'' w'' R.conI)
      have 3: "R.seq u (v'' \\ u'')"
        by (metis (full_types) 2 Cong\<^sub>0_imp_coinitial R.sources_resid
            Cong\<^sub>0_imp_con R.arr_resid_iff_con R.con_implies_arr(2) R.seqI(1) uu'' R.conI)
      have 4: "R.seq v' (u'' \\ v'')"
        by (metis 1 Cong\<^sub>0_imp_coinitial Cong\<^sub>0_imp_con R.arr_resid_iff_con
            R.con_implies_arr(2) R.seq_def R.sources_resid v'v'' R.conI)
      obtain x where x: "R.composite_of u (v'' \\ u'') x"
        using 3 composite_closed_left uu'' by blast
      obtain x' where x': "R.composite_of v' (u'' \\ v'') x'"
        using 4 composite_closed_left v'v'' by presburger
      have "?w \<approx>\<^sub>0 ?w'"
      proof -
        have "?w \<approx>\<^sub>0 ?w'' \<and> ?w' \<approx>\<^sub>0 ?w''"
          using 1 2
          by (metis Cong\<^sub>0_subst_left(2) R.null_is_zero(2) v'v'' R.conI)
        thus ?thesis
          using Cong\<^sub>0_transitive by blast
      qed
      moreover have "x \<in> \<NN> \<and> ?w \<approx>\<^sub>0 t \\ x"
        apply (intro conjI)
          apply (meson composite_closed forward_stable u''v'' uu'' v'v'' x)
         apply (metis (full_types) R.arr_resid_iff_con R.con_implies_arr(2) R.con_sym
            ide_closed forward_stable R.composite_of_def R.resid_composite_of(3)
            Cong\<^sub>0_subst_right(1) prfx_closed u''v'' uu'' v'v'' x R.conI)
        by (metis (no_types, lifting) 1 R.con_composite_of_iff ide_closed 
            R.resid_composite_of(3) R.arr_resid_iff_con R.con_implies_arr(1) R.con_sym x R.conI)
      moreover have "x' \<in> \<NN> \<and> ?w' \<approx>\<^sub>0 t' \\ x'"
        apply (intro conjI)
          apply (meson composite_closed forward_stable uu'' v''u'' v'v'' x')
         apply (metis (full_types) Cong\<^sub>0_subst_right(1) R.composite_ofE R.con_sym
            ide_closed forward_stable R.con_imp_coinitial prfx_closed
            R.resid_composite_of(3) R.arr_resid_iff_con R.con_implies_arr(1) uu'' v'v'' x' R.conI)
        by (metis (full_types) Cong\<^sub>0_subst_left(1) R.composite_ofE R.con_sym ide_closed
            forward_stable R.con_imp_coinitial prfx_closed R.resid_composite_of(3)
            R.arr_resid_iff_con R.con_implies_arr(1) uu'' v'v'' x' R.conI)
      ultimately show "t \<approx> t'"
        using Cong_def Cong\<^sub>0_transitive by metis
    qed

    lemma Cong_closure_props:
    shows "t \<approx> u \<Longrightarrow> u \<approx> t"
    and "\<lbrakk>t \<approx> u; u \<approx> v\<rbrakk> \<Longrightarrow> t \<approx> v"
    and "t \<approx>\<^sub>0 u \<Longrightarrow> t \<approx> u"
    and "\<lbrakk>u \<in> \<NN>; R.sources t = R.sources u\<rbrakk> \<Longrightarrow> t \<approx> t \\ u"
    proof -
      show "t \<approx> u \<Longrightarrow> u \<approx> t"
        using Cong_symmetric by blast
      show "\<lbrakk>t \<approx> u; u \<approx> v\<rbrakk> \<Longrightarrow> t \<approx> v"
        using Cong_transitive by blast
      show "t \<approx>\<^sub>0 u \<Longrightarrow> t \<approx> u"
        by (metis Cong\<^sub>0_subst_left(2) Cong_def Cong_reflexive R.con_implies_arr(1)
            R.null_is_zero(2) R.conI)
      show "\<lbrakk>u \<in> \<NN>; R.sources t = R.sources u\<rbrakk> \<Longrightarrow> t \<approx> t \\ u"
      proof -
        assume u: "u \<in> \<NN>" and coinitial: "R.sources t = R.sources u"
        obtain a where a: "a \<in> R.targets u"
          by (meson elements_are_arr empty_subsetI R.arr_iff_has_target subsetI subset_antisym u)
        have "t \\ u \<approx>\<^sub>0 (t \\ u) \\ a"
        proof -
          have "R.arr t"
            using R.arr_iff_has_source coinitial elements_are_arr u by presburger
          thus ?thesis
            by (meson u a R.arr_resid_iff_con coinitial ide_closed forward_stable
                elements_are_arr R.coinitial_iff R.composite_of_arr_target R.resid_composite_of(3))
        qed
        thus ?thesis
          using Cong_def
          by (metis a R.composite_of_arr_target elements_are_arr factor_closed(2) u)
      qed
    qed

    lemma Cong\<^sub>0_implies_Cong:
    assumes "t \<approx>\<^sub>0 t'"
    shows "t \<approx> t'"
      using assms Cong_closure_props(3) by simp

    lemma in_sources_respects_Cong:
    assumes "t \<approx> t'" and "a \<in> R.sources t" and "a' \<in> R.sources t'"
    shows "a \<approx> a'"
    proof -
      obtain u u' where uu': "u \<in> \<NN> \<and> u' \<in> \<NN> \<and> t \\ u \<approx>\<^sub>0 t' \\ u'"
        using assms Cong_def by blast
      show "a \<approx> a'"
      proof
        show "u \<in> \<NN>"
          using uu' by simp
        show "u' \<in> \<NN>"
          using uu' by simp
        show "a \\ u \<approx>\<^sub>0 a' \\ u'"
        proof -
          have "a \\ u \<in> R.targets u"
            by (metis Cong\<^sub>0_imp_con R.arr_resid_iff_con assms(2) R.con_imp_common_source
                R.con_implies_arr(1) R.resid_source_in_targets R.sources_eqI uu')
          moreover have "a' \\ u' \<in> R.targets u'"
            by (metis Cong\<^sub>0_imp_con R.arr_resid_iff_con assms(3) R.con_imp_common_source
                R.resid_source_in_targets R.con_implies_arr(1) R.sources_eqI uu')
          moreover have "R.targets u = R.targets u'"
            by (metis Cong\<^sub>0_imp_coinitial Cong\<^sub>0_imp_con R.arr_resid_iff_con
                R.con_implies_arr(1) R.sources_resid uu')
          ultimately show ?thesis
            using ide_closed R.targets_are_cong by presburger
        qed
      qed
    qed

    lemma in_targets_respects_Cong:
    assumes "t \<approx> t'" and "b \<in> R.targets t" and "b' \<in> R.targets t'"
    shows "b \<approx> b'"
    proof -
      obtain u u' where uu': "u \<in> \<NN> \<and> u' \<in> \<NN> \<and> t \\ u \<approx>\<^sub>0 t' \\ u'"
        using assms Cong_def by blast
      have seq: "R.seq (u \\ t) ((t' \\ u') \\ (t \\ u)) \<and> R.seq (u' \\ t') ((t \\ u) \\ (t' \\ u'))"
        by (metis R.arr_iff_has_source R.arr_iff_has_target R.conI elements_are_arr R.not_arr_null
            R.seqI(2) R.sources_resid R.targets_resid_sym uu')
      obtain v where v: "R.composite_of (u \\ t) ((t' \\ u') \\ (t \\ u)) v"
        using seq composite_closed_right uu' by presburger
      obtain v' where v': "R.composite_of (u' \\ t') ((t \\ u) \\ (t' \\ u')) v'"
        using seq composite_closed_right uu' by presburger
      show "b \<approx> b'"
      proof
        show v_in_\<NN>: "v \<in> \<NN>"
          by (metis composite_closed R.con_imp_coinitial R.con_implies_arr(1) forward_stable
              R.composite_of_def R.prfx_implies_con R.arr_resid_iff_con R.con_sym uu' v)
        show v'_in_\<NN>: "v' \<in> \<NN>"
          by (metis backward_stable R.composite_of_def R.con_imp_coinitial forward_stable
              R.null_is_zero(2) prfx_closed uu' v' R.conI)
        show "b \\ v \<approx>\<^sub>0 b' \\ v'"
          using assms uu' v v'
          by (metis R.arr_resid_iff_con ide_closed R.seq_def R.sources_resid R.targets_resid_sym
              R.resid_source_in_targets seq R.sources_composite_of R.targets_are_cong
              R.targets_composite_of)
      qed
    qed

    lemma sources_are_Cong:
    assumes "a \<in> R.sources t" and "a' \<in> R.sources t"
    shows "a \<approx> a'"
      using assms
      by (simp add: ide_closed R.sources_are_cong Cong_closure_props(3))

    lemma targets_are_Cong:
    assumes "b \<in> R.targets t" and "b' \<in> R.targets t"
    shows "b \<approx> b'"
      using assms
      by (simp add: ide_closed R.targets_are_cong Cong_closure_props(3))

    text \<open>
      It is \emph{not} the case that sources and targets are \<open>\<approx>\<close>-closed;
      \emph{i.e.} \<open>t \<approx> t' \<Longrightarrow> sources t = sources t'\<close> and \<open>t \<approx> t' \<Longrightarrow> targets t = targets t'\<close>
      do not hold, in general.
    \<close>

    lemma Resid_along_normal_preserves_reflects_con:
    assumes "u \<in> \<NN>" and "R.sources t = R.sources u"
    shows "t \\ u \<frown> t' \\ u \<longleftrightarrow> t \<frown> t'"
      by (metis R.arr_resid_iff_con assms R.con_implies_arr(1-2) elements_are_arr R.coinitial_iff
                R.resid_reflects_con resid_along_elem_preserves_con)

    text \<open>
      We can alternatively characterize \<open>\<approx>\<close> as the least symmetric and transitive
      relation on transitions that extends \<open>\<approx>\<^sub>0\<close> and has the property
      of being preserved by residuation along transitions in \<open>\<NN>\<close>.
    \<close>

    inductive Cong'
    where "\<And>t u. Cong' t u \<Longrightarrow> Cong' u t"
        | "\<And>t u v. \<lbrakk>Cong' t u; Cong' u v\<rbrakk> \<Longrightarrow> Cong' t v"
        | "\<And>t u. t \<approx>\<^sub>0 u \<Longrightarrow> Cong' t u"
        | "\<And>t u. \<lbrakk>R.arr t; u \<in> \<NN>; R.sources t = R.sources u\<rbrakk> \<Longrightarrow> Cong' t (t \\ u)"

    lemma Cong'_if:
    shows "\<lbrakk>u \<in> \<NN>; u' \<in> \<NN>; t \\ u \<approx>\<^sub>0 t' \\ u'\<rbrakk> \<Longrightarrow> Cong' t t'"
    proof -
      assume u: "u \<in> \<NN>" and u': "u' \<in> \<NN>" and 1: "t \\ u \<approx>\<^sub>0 t' \\ u'"
      show "Cong' t t'"
        using u u' 1
        by (metis (no_types, lifting) Cong'.simps Cong\<^sub>0_imp_con R.arr_resid_iff_con
            R.coinitial_iff R.con_imp_coinitial)
    qed

    lemma Cong_char:
    shows "Cong t t' \<longleftrightarrow> Cong' t t'"
    proof -
      have "Cong t t' \<Longrightarrow> Cong' t t'"
        using Cong_def Cong'_if by blast
      moreover have "Cong' t t' \<Longrightarrow> Cong t t'"
        apply (induction rule: Cong'.induct)
        using Cong_symmetric apply simp
        using Cong_transitive apply simp
        using Cong_closure_props(3) apply simp
        using Cong_closure_props(4) by simp
      ultimately show ?thesis
        using Cong_def by blast
    qed

    lemma normal_is_Cong_closed:
    assumes "t \<in> \<NN>" and "t \<approx> t'"
    shows "t' \<in> \<NN>"
      using assms
      by (metis (full_types) CongE R.con_imp_coinitial forward_stable
          R.null_is_zero(2) backward_stable R.conI)

    subsection "Congruence Classes"

    text \<open>
      Here we develop some notions relating to the congruence classes of \<open>\<approx>\<close>.
    \<close>

    definition Cong_class ("\<lbrace>_\<rbrace>")
    where "Cong_class t \<equiv> {t'. t \<approx> t'}"

    definition is_Cong_class
    where "is_Cong_class \<T> \<equiv> \<exists>t. t \<in> \<T> \<and> \<T> = \<lbrace>t\<rbrace>"

    definition Cong_class_rep
    where "Cong_class_rep \<T> \<equiv> SOME t. t \<in> \<T>"

    lemma Cong_class_is_nonempty:
    assumes "is_Cong_class \<T>"
    shows "\<T> \<noteq> {}"
      using assms is_Cong_class_def Cong_class_def by auto

    lemma rep_in_Cong_class:
    assumes "is_Cong_class \<T>"
    shows "Cong_class_rep \<T> \<in> \<T>"
      using assms is_Cong_class_def Cong_class_rep_def someI_ex [of "\<lambda>t. t \<in> \<T>"]
      by metis

    lemma arr_in_Cong_class:
    assumes "R.arr t"
    shows "t \<in> \<lbrace>t\<rbrace>"
      using assms Cong_class_def Cong_reflexive by simp

    lemma is_Cong_classI:
    assumes "R.arr t"
    shows "is_Cong_class \<lbrace>t\<rbrace>"
      using assms Cong_class_def is_Cong_class_def Cong_reflexive by blast

    lemma is_Cong_classI' [intro]:
    assumes "\<T> \<noteq> {}"
    and "\<And>t t'. \<lbrakk>t \<in> \<T>; t' \<in> \<T>\<rbrakk> \<Longrightarrow> t \<approx> t'"
    and "\<And>t t'. \<lbrakk>t \<in> \<T>; t' \<approx> t\<rbrakk> \<Longrightarrow> t' \<in> \<T>"
    shows "is_Cong_class \<T>"
    proof -
      obtain t where t: "t \<in> \<T>"
        using assms by auto
      have "\<T> = \<lbrace>t\<rbrace>"
        unfolding Cong_class_def
        using assms(2-3) t by blast
      thus ?thesis
        using is_Cong_class_def t by blast
    qed

    lemma Cong_class_memb_is_arr:
    assumes "is_Cong_class \<T>" and "t \<in> \<T>"
    shows "R.arr t"
      using assms Cong_class_def is_Cong_class_def Cong_imp_arr(2) by force

    lemma Cong_class_membs_are_Cong:
    assumes "is_Cong_class \<T>" and "t \<in> \<T>" and "t' \<in> \<T>"
    shows "Cong t t'"
      using assms Cong_class_def is_Cong_class_def
      by (metis CollectD Cong_closure_props(2) Cong_symmetric)

    lemma Cong_class_eqI:
    assumes "t \<approx> t'"
    shows "\<lbrace>t\<rbrace> = \<lbrace>t'\<rbrace>"
      using assms Cong_class_def
      by (metis (full_types) Collect_cong Cong'.intros(1-2) Cong_char)

    lemma Cong_class_eqI':
    assumes "is_Cong_class \<T>" and "is_Cong_class \<U>" and "\<T> \<inter> \<U> \<noteq> {}"
    shows "\<T> = \<U>"
      using assms is_Cong_class_def Cong_class_eqI Cong_class_membs_are_Cong Int_emptyI
      by (metis (no_types, lifting))

    lemma is_Cong_classE [elim]:
    assumes "is_Cong_class \<T>"
    and "\<lbrakk>\<T> \<noteq> {}; \<And>t t'. \<lbrakk>t \<in> \<T>; t' \<in> \<T>\<rbrakk> \<Longrightarrow> t \<approx> t'; \<And>t t'. \<lbrakk>t \<in> \<T>; t' \<approx> t\<rbrakk> \<Longrightarrow> t' \<in> \<T>\<rbrakk> \<Longrightarrow> T"
    shows T
    proof -
      have \<T>: "\<T> \<noteq> {}"
        using assms Cong_class_is_nonempty by simp
      moreover have 1: "\<And>t t'. \<lbrakk>t \<in> \<T>; t' \<in> \<T>\<rbrakk> \<Longrightarrow> t \<approx> t'"
        using assms Cong_class_membs_are_Cong by metis
      moreover have "\<And>t t'. \<lbrakk>t \<in> \<T>; t' \<approx> t\<rbrakk> \<Longrightarrow> t' \<in> \<T>"
        using assms Cong_class_def
        by (metis 1 Cong_class_eqI Cong_imp_arr(1) is_Cong_class_def arr_in_Cong_class)
      ultimately show ?thesis
        using assms by blast
    qed

    lemma Cong_class_rep [simp]:
    assumes "is_Cong_class \<T>"
    shows "\<lbrace>Cong_class_rep \<T>\<rbrace> = \<T>"
      by (metis Cong_class_membs_are_Cong Cong_class_eqI assms is_Cong_class_def rep_in_Cong_class)

    lemma Cong_class_memb_Cong_rep:
    assumes "is_Cong_class \<T>" and "t \<in> \<T>"
    shows "Cong t (Cong_class_rep \<T>)"
      using assms Cong_class_membs_are_Cong rep_in_Cong_class by simp

    lemma composite_of_normal_arr:
    shows "\<lbrakk> R.arr t; u \<in> \<NN>; R.composite_of u t t' \<rbrakk> \<Longrightarrow> t' \<approx> t"
      by (meson Cong'.intros(3) Cong_char R.composite_of_def R.con_implies_arr(2)
                ide_closed R.prfx_implies_con Cong_closure_props(2,4) R.sources_composite_of)

    lemma composite_of_arr_normal:
    shows "\<lbrakk> arr t; u \<in> \<NN>; R.composite_of t u t' \<rbrakk> \<Longrightarrow> t' \<approx>\<^sub>0 t"
      by (meson Cong_closure_props(3) R.composite_of_def ide_closed prfx_closed)

  end

  subsection "Coherent Normal Sub-RTS's"

  text \<open>
    A \emph{coherent} normal sub-RTS is one that satisfies a parallel moves property with respect
    to arbitrary transitions.  The congruence \<open>\<approx>\<close> induced by a coherent normal sub-RTS is
    fully substitutive with respect to consistency and residuation,
    and in fact coherence is equivalent to substitutivity in this context.
  \<close>

  locale coherent_normal_sub_rts = normal_sub_rts +
    assumes coherent: "\<lbrakk> R.arr t; u \<in> \<NN>; u' \<in> \<NN>; R.sources u = R.sources u';
                         R.targets u = R.targets u'; R.sources t = R.sources u \<rbrakk>
                            \<Longrightarrow> t \\ u \<approx>\<^sub>0 t \\ u'"

  (*
   * TODO: Should coherence be part of normality, or is it an additional property that guarantees
   * the existence of the quotient?
   *
   * e.g. see http://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/normal+subobject
   * Maybe also http://www.tac.mta.ca/tac/volumes/36/3/36-03.pdf for recent work.
   *)

  context normal_sub_rts
  begin

    text \<open>
      The above ``parallel moves'' formulation of coherence is equivalent to the following
      formulation, which involves ``opposing spans''.
    \<close>

    lemma coherent_iff:
    shows "(\<forall>t u u'. R.arr t \<and> u \<in> \<NN> \<and> u' \<in> \<NN> \<and> R.sources t = R.sources u \<and>
                     R.sources u = R.sources u' \<and> R.targets u = R.targets u'
                            \<longrightarrow> t \\ u \<approx>\<^sub>0 t \\ u')
           \<longleftrightarrow>
           (\<forall>t t' v v' w w'. v \<in> \<NN> \<and> v' \<in> \<NN> \<and> w \<in> \<NN> \<and> w' \<in> \<NN> \<and>
                             R.sources v = R.sources w \<and> R.sources v' = R.sources w' \<and>
                             R.targets w = R.targets w' \<and> t \\ v \<approx>\<^sub>0 t' \\ v'
                                \<longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w')"
    proof
      assume 1: "\<forall>t t' v v' w w'. v \<in> \<NN> \<and> v' \<in> \<NN> \<and> w \<in> \<NN> \<and> w' \<in> \<NN> \<and>
                             R.sources v = R.sources w \<and> R.sources v' = R.sources w' \<and>
                             R.targets w = R.targets w' \<and> t \\ v \<approx>\<^sub>0 t' \\ v'
                                \<longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w'"
      show "\<forall>t u u'. R.arr t \<and> u \<in> \<NN> \<and> u' \<in> \<NN> \<and> R.sources t = R.sources u \<and>
                     R.sources u = R.sources u' \<and> R.targets u = R.targets u'
                            \<longrightarrow> t \\ u \<approx>\<^sub>0 t \\ u'"
      proof (intro allI impI, elim conjE)
        fix t u u'
        assume t: "R.arr t" and u: "u \<in> \<NN>" and u': "u' \<in> \<NN>"
        and tu: "R.sources t = R.sources u" and sources: "R.sources u = R.sources u'"
        and targets: "R.targets u = R.targets u'"
        show "t \\ u \<approx>\<^sub>0 t \\ u'"
          by (metis 1 Cong\<^sub>0_reflexive Resid_along_normal_preserves_Cong\<^sub>0 sources t targets
              tu u u')
      qed
      next
      assume 1: "\<forall>t u u'. R.arr t \<and> u \<in> \<NN> \<and> u' \<in> \<NN> \<and> R.sources t = R.sources u \<and>
                     R.sources u = R.sources u' \<and> R.targets u = R.targets u'
                            \<longrightarrow> t \\ u \<approx>\<^sub>0 t \\ u'"
      show "\<forall>t t' v v' w w'. v \<in> \<NN> \<and> v' \<in> \<NN> \<and> w \<in> \<NN> \<and> w' \<in> \<NN> \<and>
                             R.sources v = R.sources w \<and> R.sources v' = R.sources w' \<and>
                             R.targets w = R.targets w' \<and> t \\ v \<approx>\<^sub>0 t' \\ v'
                                \<longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w'"
      proof (intro allI impI, elim conjE)
        fix t t' v v' w w'
        assume v: "v \<in> \<NN>" and v': "v' \<in> \<NN>" and w: "w \<in> \<NN>" and w': "w' \<in> \<NN>"
        and vw: "R.sources v = R.sources w" and v'w': "R.sources v' = R.sources w'"
        and ww': "R.targets w = R.targets w'"
        and tvt'v': "(t \\ v) \\ (t' \\ v') \<in> \<NN>" and t'v'tv: "(t' \\ v') \\ (t \\ v) \<in> \<NN>"
        show "t \\ w \<approx>\<^sub>0 t' \\ w'"
        proof -
          have 3: "R.sources t = R.sources v \<and> R.sources t' = R.sources v'"
            using R.con_imp_coinitial
            by (meson Cong\<^sub>0_imp_con tvt'v' t'v'tv
                R.coinitial_iff R.arr_resid_iff_con)
          have 2: "t \\ w \<approx> t' \\ w'"
            using Cong_closure_props
            by (metis tvt'v' t'v'tv 3 vw v'w' v v' w w')
          obtain z z' where zz': "z \<in> \<NN> \<and> z' \<in> \<NN> \<and> (t \\ w) \\ z \<approx>\<^sub>0 (t' \\ w') \\ z'"
            using 2 by auto
          have "(t \\ w) \\ z \<approx>\<^sub>0 (t \\ w) \\ z'"
          proof -
            have "R.coinitial ((t \\ w) \\ z) ((t \\ w) \\ z')"
            proof -
              have "R.targets z = R.targets z'"
                using ww' zz'
                by (metis Cong\<^sub>0_imp_coinitial Cong\<^sub>0_imp_con R.con_sym_ax R.null_is_zero(2)
                    R.sources_resid R.conI)
              moreover have "R.sources ((t \\ w) \\ z) = R.targets z"
                using ww' zz'
                by (metis R.con_def R.not_arr_null R.null_is_zero(2)
                    R.sources_resid elements_are_arr)
              moreover have "R.sources ((t \\ w) \\ z') = R.targets z'"
                using ww' zz'
                by (metis Cong_closure_props(4) Cong_imp_arr(2) R.arr_resid_iff_con
                    R.coinitial_iff R.con_imp_coinitial R.rts_axioms rts.sources_resid)
              ultimately show ?thesis
                using ww' zz'
                apply (intro R.coinitialI)
                 apply auto
                by (meson R.arr_resid_iff_con R.con_implies_arr(2) elements_are_arr)
            qed
            thus ?thesis
              apply (intro conjI)
              by (metis 1 R.coinitial_iff R.con_imp_coinitial R.arr_resid_iff_con
                        R.sources_resid zz')+
          qed
          hence "(t \\ w) \\ z' \<approx>\<^sub>0 (t' \\ w') \\ z'"
            using zz' Cong\<^sub>0_transitive Cong\<^sub>0_symmetric by blast
          thus ?thesis
            using zz' Resid_along_normal_reflects_Cong\<^sub>0 by metis
        qed
      qed
    qed

  end

  context coherent_normal_sub_rts
  begin

    text \<open>
      The proof of the substitutivity of \<open>\<approx>\<close> with respect to residuation only uses
      coherence in the ``opposing spans'' form.
    \<close>

    lemma coherent':
    assumes "v \<in> \<NN>" and "v' \<in> \<NN>" and "w \<in> \<NN>" and "w' \<in> \<NN>"
    and "R.sources v = R.sources w" and "R.sources v' = R.sources w'"
    and "R.targets w = R.targets w'" and "t \\ v \<approx>\<^sub>0 t' \\ v'"
    shows "t \\ w \<approx>\<^sub>0 t' \\ w'"
    proof
      show "(t \\ w) \\ (t' \\ w') \<in> \<NN>"
        using assms coherent coherent_iff by meson
      show "(t' \\ w') \\ (t \\ w) \<in> \<NN>"
        using assms coherent coherent_iff by meson
    qed

    text \<open>
      The relation \<open>\<approx>\<close> is substitutive with respect to both arguments of residuation.
    \<close>

    lemma Cong_subst:
    assumes "t \<approx> t'" and "u \<approx> u'" and "t \<frown> u" and "R.sources t' = R.sources u'"
    shows "t' \<frown> u'" and "t \\ u \<approx> t' \\ u'"
    proof -
      obtain v v' where vv': "v \<in> \<NN> \<and> v' \<in> \<NN> \<and> t \\ v \<approx>\<^sub>0 t' \\ v'"
        using assms by auto
      obtain w w' where ww': "w \<in> \<NN> \<and> w' \<in> \<NN> \<and> u \\ w \<approx>\<^sub>0 u' \\ w'"
        using assms by auto
      let ?x = "t \\ v" and ?x' = "t' \\ v'"
      let ?y = "u \\ w" and ?y' = "u' \\ w'"
      have xx': "?x \<approx>\<^sub>0 ?x'"
        using assms vv' by blast
      have yy': "?y \<approx>\<^sub>0 ?y'"
        using assms ww' by blast
      have 1: "t \\ w \<approx>\<^sub>0 t' \\ w'"
      proof -
        have "R.sources v = R.sources w"
          by (metis (no_types, lifting) Cong\<^sub>0_imp_con R.arr_resid_iff_con assms(3)
              R.con_imp_common_source R.con_implies_arr(2) R.sources_eqI ww' xx')
        moreover have "R.sources v' = R.sources w'"
          by (metis (no_types, lifting) assms(4) R.coinitial_iff R.con_imp_coinitial
              Cong\<^sub>0_imp_con R.arr_resid_iff_con ww' xx')
        moreover have "R.targets w = R.targets w'"
          by (metis Cong\<^sub>0_implies_Cong Cong\<^sub>0_imp_coinitial Cong_imp_arr(1)
              R.arr_resid_iff_con R.sources_resid ww')
        ultimately show ?thesis
          using assms vv' ww'
          by (intro coherent' [of v v' w w' t]) auto
      qed
      have 2: "t' \\ w' \<frown> u' \\ w'"
        using assms 1 ww'
        by (metis Cong\<^sub>0_subst_left(1) Cong\<^sub>0_subst_right(1) Resid_along_normal_preserves_reflects_con
            R.arr_resid_iff_con R.coinitial_iff R.con_imp_coinitial elements_are_arr)
      thus 3: "t' \<frown> u'"
        using ww' R.cube by force
      have "t \\ u \<approx> ((t \\ u) \\ (w \\ u)) \\ (?y' \\ ?y)"
      proof -
        have "t \\ u \<approx> (t \\ u) \\ (w \\ u)"
          by (metis Cong_closure_props(4) assms(3) R.con_imp_coinitial
              elements_are_arr forward_stable R.arr_resid_iff_con R.con_implies_arr(1)
              R.sources_resid ww')
        also have "... \<approx> ((t \\ u) \\ (w \\ u)) \\ (?y' \\ ?y)"
          by (metis Cong\<^sub>0_imp_con Cong_closure_props(4) Cong_imp_arr(2)
              R.arr_resid_iff_con calculation R.con_implies_arr(2) R.targets_resid_sym
              R.sources_resid ww')
        finally show ?thesis by simp
      qed
      also have "... \<approx> (((t \\ w) \\ ?y) \\ (?y' \\ ?y))"
        using ww'
        by (metis Cong_imp_arr(2) Cong_reflexive calculation R.cube)
      also have "... \<approx> (((t' \\ w') \\ ?y) \\ (?y' \\ ?y))"
        using 1 Cong\<^sub>0_subst_left(2) [of "t \\ w" "(t' \\ w')" ?y]
              Cong\<^sub>0_subst_left(2) [of "(t \\ w) \\ ?y" "(t' \\ w') \\ ?y" "?y' \\ ?y"]
        by (meson 2 Cong\<^sub>0_implies_Cong Cong\<^sub>0_subst_Con Cong_imp_arr(2)
                  R.arr_resid_iff_con calculation ww')
      also have "... \<approx> ((t' \\ w') \\ ?y') \\ (?y \\ ?y')"
        using 2 Cong\<^sub>0_implies_Cong Cong\<^sub>0_subst_right(2) ww' by presburger
      also have 4: "... \<approx> (t' \\ u') \\ (w' \\ u')"
         using 2 ww'
         by (metis Cong\<^sub>0_imp_con Cong_closure_props(4) Cong_symmetric R.cube R.sources_resid)
      also have "... \<approx> t' \\ u'"
         using ww' 3 4
         by (metis Cong_closure_props(4) Cong_imp_arr(2) Cong_symmetric R.con_imp_coinitial
                   R.con_implies_arr(2) forward_stable R.sources_resid R.arr_resid_iff_con)
      finally show "t \\ u \<approx> t' \\ u'" by simp
    qed

    lemma Cong_subst_con:
    assumes "R.sources t = R.sources u" and "R.sources t' = R.sources u'" and "t \<approx> t'" and "u \<approx> u'"
    shows "t \<frown> u \<longleftrightarrow> t' \<frown> u'"
      using assms by (meson Cong_subst(1) Cong_symmetric)

    lemma Cong\<^sub>0_composite_of_arr_normal:
    assumes "R.composite_of t u t'" and "u \<in> \<NN>"
    shows "t' \<approx>\<^sub>0 t"
      using assms backward_stable R.composite_of_def ide_closed by blast

    lemma Cong_composite_of_normal_arr:
    assumes "R.composite_of u t t'" and "u \<in> \<NN>"
    shows "t' \<approx> t"
      using assms
      by (meson Cong_closure_props(2-4) R.arr_composite_of ide_closed R.composite_of_def
                R.sources_composite_of)

  end

  context normal_sub_rts
  begin

    text \<open>
      Coherence is not an arbitrary property: here we show that substitutivity of
      congruence in residuation is equivalent to the ``opposing spans'' form of coherence.
    \<close>

    lemma Cong_subst_iff_coherent':
    shows "(\<forall>t t' u u'. t \<approx> t' \<and> u \<approx> u' \<and> t \<frown> u \<and> R.sources t' = R.sources u'
                           \<longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u')
           \<longleftrightarrow>
           (\<forall>t t' v v' w w'. v \<in> \<NN> \<and> v' \<in> \<NN> \<and> w \<in> \<NN> \<and> w' \<in> \<NN> \<and>
                             R.sources v = R.sources w \<and> R.sources v' = R.sources w' \<and>
                             R.targets w = R.targets w' \<and> t \\ v \<approx>\<^sub>0 t' \\ v'
                                \<longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w')"
    proof
      assume 1: "\<forall>t t' u u'. t \<approx> t' \<and> u \<approx> u' \<and> t \<frown> u \<and> R.sources t' = R.sources u'
                           \<longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u'"
      show "\<forall>t t' v v' w w'. v \<in> \<NN> \<and> v' \<in> \<NN> \<and> w \<in> \<NN> \<and> w' \<in> \<NN> \<and>
                             R.sources v = R.sources w \<and> R.sources v' = R.sources w' \<and>
                             R.targets w = R.targets w' \<and> t \\ v \<approx>\<^sub>0 t' \\ v'
                                \<longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w'"
      proof (intro allI impI, elim conjE)
        fix t t' v v' w w'
        assume v: "v \<in> \<NN>" and v': "v' \<in> \<NN>" and w: "w \<in> \<NN>" and w': "w' \<in> \<NN>"
        and sources_vw: "R.sources v = R.sources w"
        and sources_v'w': "R.sources v' = R.sources w'"
        and targets_ww': "R.targets w = R.targets w'"
        and tt': "(t \\ v) \\ (t' \\ v') \<in> \<NN>" and t't: "(t' \\ v') \\ (t \\ v) \<in> \<NN>"
        show "t \\ w \<approx>\<^sub>0 t' \\ w'"
        proof -
          have 2: "\<And>t t' u u'. \<lbrakk>t \<approx> t'; u \<approx> u'; t \<frown> u; R.sources t' = R.sources u'\<rbrakk>
                                   \<Longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u'"
            using 1 by blast
          have 3: "t \\ w \<approx> t \\ v \<and> t' \\ w' \<approx> t' \\ v'"
            by (metis tt' t't sources_vw sources_v'w' Cong\<^sub>0_subst_right(2) Cong_closure_props(4)
                      Cong_def R.arr_resid_iff_con Cong_closure_props(3) Cong_imp_arr(1)
                      normal_is_Cong_closed v w v' w')
          have "(t \\ w) \\ (t' \\ w') \<approx> (t \\ v) \\ (t' \\ v')"
            using 2 [of "t \\ w" "t \\ v" "t' \\ w'" "t' \\ v'"] 3
            by (metis tt' t't targets_ww' 1 Cong\<^sub>0_imp_con Cong_imp_arr(1) Cong_symmetric
                R.arr_resid_iff_con R.sources_resid)
          moreover have "(t' \\ w') \\ (t \\ w) \<approx> (t' \\ v') \\ (t \\ v)"
            using 2 3
            by (metis tt' t't targets_ww' Cong\<^sub>0_imp_con Cong_symmetric
                Cong_imp_arr(1) R.arr_resid_iff_con R.sources_resid)
          ultimately show ?thesis
            by (meson tt' t't normal_is_Cong_closed Cong_symmetric)
        qed
      qed
      next
      assume 1: "\<forall>t t' v v' w w'. v \<in> \<NN> \<and> v' \<in> \<NN> \<and> w \<in> \<NN> \<and> w' \<in> \<NN> \<and>
                             R.sources v = R.sources w \<and> R.sources v' = R.sources w' \<and>
                             R.targets w = R.targets w' \<and> t \\ v \<approx>\<^sub>0 t' \\ v'
                                \<longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w'"
      show "\<forall>t t' u u'. t \<approx> t' \<and> u \<approx> u' \<and> t \<frown> u \<and> R.sources t' = R.sources u'
                           \<longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u'"
      proof (intro allI impI, elim conjE, intro conjI)
        have *: "\<And>t t' v v' w w'. \<lbrakk>v \<in> \<NN>; v' \<in> \<NN>; w \<in> \<NN>; w' \<in> \<NN>;
                                   R.sources v = R.sources w; R.sources v' = R.sources w';
                                   R.targets v = R.targets v'; R.targets w = R.targets w';
                                   t \\ v \<approx>\<^sub>0 t' \\ v'\<rbrakk>
                                      \<Longrightarrow> t \\ w \<approx>\<^sub>0 t' \\ w'"
          using 1 by metis
        fix t t' u u'
        assume tt': "t \<approx> t'" and uu': "u \<approx> u'" and con: "t \<frown> u"
        and t'u': "R.sources t' = R.sources u'"
        obtain v v' where vv': "v \<in> \<NN> \<and> v' \<in> \<NN> \<and> t \\ v \<approx>\<^sub>0 t' \\ v'"
          using tt' by auto
        obtain w w' where ww': "w \<in> \<NN> \<and> w' \<in> \<NN> \<and> u \\ w \<approx>\<^sub>0 u' \\ w'"
          using uu' by auto
        let ?x = "t \\ v" and ?x' = "t' \\ v'"
        let ?y = "u \\ w" and ?y' = "u' \\ w'"
        have xx': "?x \<approx>\<^sub>0 ?x'"
          using tt' vv' by blast
        have yy': "?y \<approx>\<^sub>0 ?y'"
          using uu' ww' by blast
        have 1: "t \\ w \<approx>\<^sub>0 t' \\ w'"
        proof -
          have "R.sources v = R.sources w \<and> R.sources v' = R.sources w'"
          proof
            show "R.sources v' = R.sources w'"
              using Cong\<^sub>0_imp_con R.arr_resid_iff_con R.coinitial_iff R.con_imp_coinitial
                    t'u' vv' ww'
              by metis
            show "R.sources v = R.sources w"
              by (metis con elements_are_arr R.not_arr_null R.null_is_zero(2) R.conI
                  R.con_imp_common_source rts.sources_eqI R.rts_axioms vv' ww')
          qed
          moreover have "R.targets v = R.targets v' \<and> R.targets w = R.targets w'"
            by (metis Cong\<^sub>0_imp_coinitial Cong\<^sub>0_imp_con R.arr_resid_iff_con
                R.con_implies_arr(2) R.sources_resid vv' ww')
          ultimately show ?thesis
            using vv' ww' xx'
            by (intro * [of v v' w w' t t']) auto
        qed
        have 2: "t' \\ w' \<frown> u' \\ w'"
          using 1 tt' ww'
          by (meson Cong\<^sub>0_imp_con Cong\<^sub>0_subst_Con R.arr_resid_iff_con con R.con_imp_coinitial
              R.con_implies_arr(2) resid_along_elem_preserves_con)
        thus 3: "t' \<frown> u'"
          using ww' R.cube by force
        have "t \\ u \<approx> (t \\ u) \\ (w \\ u)"
          by (metis Cong_closure_props(4) R.arr_resid_iff_con con R.con_imp_coinitial
              elements_are_arr forward_stable R.con_implies_arr(2) R.sources_resid ww')
        also have "(t \\ u) \\ (w \\ u) \<approx> ((t \\ u) \\ (w \\ u)) \\ (?y' \\ ?y)"
          using yy'
          by (metis Cong\<^sub>0_imp_con Cong_closure_props(4) Cong_imp_arr(2)
              R.arr_resid_iff_con calculation R.con_implies_arr(2) R.sources_resid R.targets_resid_sym)
        also have "... \<approx> (((t \\ w) \\ ?y) \\ (?y' \\ ?y))"
          using ww'
          by (metis Cong_imp_arr(2) Cong_reflexive calculation R.cube)
        also have "... \<approx> (((t' \\ w') \\ ?y) \\ (?y' \\ ?y))"
        proof -
          have "((t \\ w) \\ ?y) \\ (?y' \\ ?y) \<approx>\<^sub>0 ((t' \\ w') \\ ?y) \\ (?y' \\ ?y)"
            using 1 2 Cong\<^sub>0_subst_left(2)
            by (meson Cong\<^sub>0_subst_Con calculation Cong_imp_arr(2) R.arr_resid_iff_con ww')
          thus ?thesis
            using Cong\<^sub>0_implies_Cong by presburger
        qed
        also have "... \<approx> ((t' \\ w') \\ ?y') \\ (?y \\ ?y')"
          by (meson "2" Cong\<^sub>0_implies_Cong Cong\<^sub>0_subst_right(2) ww')
        also have 4: "... \<approx> (t' \\ u') \\ (w' \\ u')"
           using 2 ww'
           by (metis Cong\<^sub>0_imp_con Cong_closure_props(4) Cong_symmetric R.cube R.sources_resid)
        also have "... \<approx> t' \\ u'"
           using ww' 2 3 4
           by (metis Cong'.intros(1) Cong'.intros(4) Cong_char Cong_imp_arr(2)
               R.arr_resid_iff_con forward_stable R.con_imp_coinitial R.sources_resid
               R.con_implies_arr(2))
        finally show "t \\ u \<approx> t' \\ u'" by simp
      qed
    qed

  end

  subsection "Quotient by Coherent Normal Sub-RTS"

  text \<open>
    We now define the quotient of an RTS by a coherent normal sub-RTS and show that it is
    an extensional RTS.
  \<close>

  locale quotient_by_coherent_normal =
    R: rts +
    N: coherent_normal_sub_rts
  begin

    definition Resid  (infix "\<lbrace>\\\<rbrace>" 70)
    where "\<T> \<lbrace>\\\<rbrace> \<U> \<equiv>
           if N.is_Cong_class \<T> \<and> N.is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)
           then N.Cong_class
                  (fst (SOME tu. fst tu \<in> \<T> \<and> snd tu \<in> \<U> \<and> fst tu \<frown> snd tu) \\
                   snd (SOME tu. fst tu \<in> \<T> \<and> snd tu \<in> \<U> \<and> fst tu \<frown> snd tu))
           else {}"

    sublocale partial_magma Resid
      using N.Cong_class_is_nonempty Resid_def
      by unfold_locales metis

    lemma is_partial_magma:
    shows "partial_magma Resid"
      ..

    lemma null_char:
    shows "null = {}"
      using N.Cong_class_is_nonempty Resid_def
      by (metis null_is_zero(2))

    lemma Resid_by_members:
    assumes "N.is_Cong_class \<T>" and "N.is_Cong_class \<U>" and "t \<in> \<T>" and "u \<in> \<U>" and "t \<frown> u"
    shows "\<T> \<lbrace>\\\<rbrace> \<U> = \<lbrace>t \\ u\<rbrace>"
      using assms Resid_def someI_ex [of "\<lambda>tu. fst tu \<in> \<T> \<and> snd tu \<in> \<U> \<and> fst tu \<frown> snd tu"]
      apply simp
      by (meson N.Cong_class_membs_are_Cong N.Cong_class_eqI N.Cong_subst(2)
          R.coinitial_iff R.con_imp_coinitial)

    abbreviation Con  (infix "\<lbrace>\<frown>\<rbrace>" 50)
    where "\<T> \<lbrace>\<frown>\<rbrace> \<U> \<equiv> \<T> \<lbrace>\\\<rbrace> \<U> \<noteq> {}"

    lemma Con_char:
    shows "\<T> \<lbrace>\<frown>\<rbrace> \<U> \<longleftrightarrow>
           N.is_Cong_class \<T> \<and> N.is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)"
      by (metis (no_types, opaque_lifting) N.Cong_class_is_nonempty N.is_Cong_classI
          Resid_def Resid_by_members R.arr_resid_iff_con)

    lemma Con_sym:
    assumes "Con \<T> \<U>"
    shows "Con \<U> \<T>"
      using assms Con_char R.con_sym by meson

    lemma is_Cong_class_Resid:
    assumes "\<T> \<lbrace>\<frown>\<rbrace> \<U>"
    shows "N.is_Cong_class (\<T> \<lbrace>\\\<rbrace> \<U>)"
      using assms Con_char Resid_by_members R.arr_resid_iff_con N.is_Cong_classI by auto

    lemma Con_witnesses:
    assumes "\<T> \<lbrace>\<frown>\<rbrace> \<U>" and "t \<in> \<T>" and "u \<in> \<U>"
    shows "\<exists>v w. v \<in> \<NN> \<and> w \<in> \<NN> \<and> t \\ v \<frown> u \\ w"
    proof -
      have 1: "N.is_Cong_class \<T> \<and> N.is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)"
        using assms Con_char by simp
      obtain t' u' where t'u': "t' \<in> \<T> \<and> u' \<in> \<U> \<and> t' \<frown> u'"
        using 1 by auto
      have 2: "t' \<approx> t \<and> u' \<approx> u"
        using assms 1 t'u' N.Cong_class_membs_are_Cong by auto
      obtain v v' where vv': "v \<in> \<NN> \<and> v' \<in> \<NN> \<and> t' \\ v \<approx>\<^sub>0 t \\ v'"
        using 2 by auto
      obtain w w' where ww': "w \<in> \<NN> \<and> w' \<in> \<NN> \<and> u' \\ w \<approx>\<^sub>0 u \\ w'"
        using 2 by auto
      have 3: "w \<frown> v"
        by (metis R.arr_resid_iff_con R.con_def R.con_imp_coinitial R.ex_un_null
            N.elements_are_arr R.null_is_zero(2) N.resid_along_elem_preserves_con t'u' vv' ww')
      have "R.seq v (w \\ v)"
        by (simp add: N.elements_are_arr R.seq_def 3 vv')
      obtain x where x: "R.composite_of v (w \\ v) x"
        using N.composite_closed_left \<open>R.seq v (w \ v)\<close> vv' by blast
      obtain x' where x': "R.composite_of v' (w \\ v) x'"
        using x vv' N.composite_closed_left
        by (metis N.Cong\<^sub>0_implies_Cong N.Cong\<^sub>0_imp_coinitial N.Cong_imp_arr(1)
            R.composable_def R.composable_imp_seq R.con_implies_arr(2)
            R.seq_def R.sources_resid R.arr_resid_iff_con)
      have *: "t' \\ x \<approx>\<^sub>0 t \\ x'"
        by (metis N.coherent' N.composite_closed N.forward_stable R.con_imp_coinitial
            R.targets_composite_of 3 R.con_sym R.sources_composite_of vv' ww' x x')
      obtain y where y: "R.composite_of w (v \\ w) y"
        using x vv' ww'
        by (metis R.arr_resid_iff_con R.composable_def R.composable_imp_seq
            R.con_imp_coinitial R.seq_def R.sources_resid N.elements_are_arr
            N.forward_stable N.composite_closed_left)
      obtain y' where y': "R.composite_of w' (v \\ w) y'"
        using y ww'
        by (metis N.Cong\<^sub>0_imp_coinitial N.Cong_closure_props(3) N.Cong_imp_arr(1)
            R.composable_def R.composable_imp_seq R.con_implies_arr(2) R.seq_def
            R.sources_resid N.composite_closed_left R.arr_resid_iff_con)
      have **: "u' \\ y \<approx>\<^sub>0 u \\ y'"
        by (metis N.composite_closed N.forward_stable R.con_imp_coinitial R.targets_composite_of
            \<open>w \<frown> v\<close> N.coherent' R.sources_composite_of vv' ww' y y')
      have 4: "x \<in> \<NN> \<and> y \<in> \<NN>"
        using x y vv' ww' * **
        by (metis 3 N.composite_closed N.forward_stable R.con_imp_coinitial R.con_sym)
      have "t \\ x' \<frown> u \\ y'"
      proof -
        have "t \\ x' \<approx>\<^sub>0 t' \\ x"
          using * by simp
        moreover have "t' \\ x \<frown> u' \\ y"
        proof -
          have "t' \\ x \<frown> u' \\ x"
            using t'u' vv' ww' 4 *
            by (metis N.Resid_along_normal_preserves_reflects_con N.elements_are_arr
                R.coinitial_iff R.con_imp_coinitial R.arr_resid_iff_con)
          moreover have "u' \\ x \<approx>\<^sub>0 u' \\ y"
            using ww' x y
            by (metis 4 N.Cong\<^sub>0_imp_coinitial N.Cong\<^sub>0_imp_con N.Cong\<^sub>0_transitive
                N.coherent' N.factor_closed(2) R.sources_composite_of
                R.targets_composite_of R.targets_resid_sym)
          ultimately show ?thesis
            using N.Cong\<^sub>0_subst_right by blast
        qed
        moreover have "u' \\ y \<approx>\<^sub>0 u \\ y'"
          using ** R.con_sym by simp
        ultimately show ?thesis
          using N.Cong\<^sub>0_subst_Con by auto
      qed
      moreover have "x' \<in> \<NN> \<and> y' \<in> \<NN>"
        using x' y' vv' ww'
        by (metis N.Cong_composite_of_normal_arr N.Cong_imp_arr(2) N.composite_closed
            R.con_imp_coinitial N.forward_stable R.arr_resid_iff_con)
      ultimately show ?thesis by auto
    qed

    abbreviation Arr
    where "Arr \<T> \<equiv> Con \<T> \<T>"

    lemma Arr_Resid:
    assumes "Con \<T> \<U>"
    shows "Arr (\<T> \<lbrace>\\\<rbrace> \<U>)"
      by (metis Con_char N.Cong_class_memb_is_arr R.arrE N.rep_in_Cong_class
          assms is_Cong_class_Resid)

    lemma Cube:
    assumes "Con (\<V> \<lbrace>\\\<rbrace> \<T>) (\<U> \<lbrace>\\\<rbrace> \<T>)"
    shows "(\<V> \<lbrace>\\\<rbrace> \<T>) \<lbrace>\\\<rbrace> (\<U> \<lbrace>\\\<rbrace> \<T>) = (\<V> \<lbrace>\\\<rbrace> \<U>) \<lbrace>\\\<rbrace> (\<T> \<lbrace>\\\<rbrace> \<U>)"
    proof -
      obtain t u where tu: "t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u \<and> \<T> \<lbrace>\\\<rbrace> \<U> = \<lbrace>t \\ u\<rbrace>"
        using assms
        by (metis Con_char N.Cong_class_is_nonempty R.con_sym Resid_by_members)
      obtain t' v where t'v: "t' \<in> \<T> \<and> v \<in> \<V> \<and> t' \<frown> v \<and> \<T> \<lbrace>\\\<rbrace> \<V> = \<lbrace>t' \\ v\<rbrace>"
        using assms
        by (metis Con_char N.Cong_class_is_nonempty Resid_by_members Con_sym)
      have tt': "t \<approx> t'"
        using assms
        by (metis N.Cong_class_membs_are_Cong N.Cong_class_is_nonempty Resid_def t'v tu)
      obtain w w' where ww': "w \<in> \<NN> \<and> w' \<in> \<NN> \<and> t \\ w \<approx>\<^sub>0 t' \\ w'"
        using tu t'v tt' by auto
      have 1: "\<U> \<lbrace>\\\<rbrace> \<T> = \<lbrace>u \\ t\<rbrace> \<and> \<V> \<lbrace>\\\<rbrace> \<T> = \<lbrace>v \\ t'\<rbrace>"
        by (metis Con_char N.Cong_class_is_nonempty R.con_sym Resid_by_members assms t'v tu)
      obtain x x' where xx': "x \<in> \<NN> \<and> x' \<in> \<NN> \<and> (u \\ t) \\ x \<frown> (v \\ t') \\ x'"
        using 1 Con_witnesses [of "\<U> \<lbrace>\\\<rbrace> \<T>" "\<V> \<lbrace>\\\<rbrace> \<T>" "u \\ t" "v \\ t'"]
        by (metis N.arr_in_Cong_class R.con_sym t'v tu assms Con_sym R.arr_resid_iff_con)
      have "R.seq t x"
        by (metis R.arr_resid_iff_con R.coinitial_iff R.con_imp_coinitial R.seqI(2)
            R.sources_resid xx')
      have "R.seq t' x'"
        by (metis R.arr_resid_iff_con R.sources_resid R.coinitialE R.con_imp_coinitial
            R.seqI(2) xx')
      obtain tx where tx: "R.composite_of t x tx"
        using xx' \<open>R.seq t x\<close> N.composite_closed_right [of x t] R.composable_def by auto
      obtain t'x' where t'x': "R.composite_of t' x' t'x'"
        using xx' \<open>R.seq t' x'\<close> N.composite_closed_right [of x' t'] R.composable_def by auto
      let ?tx_w = "tx \\ w" and ?t'x'_w' = "t'x' \\ w'"
      let ?w_tx = "(w \\ t) \\ x" and ?w'_t'x' = "(w' \\ t') \\ x'"
      let ?u_tx = "(u \\ t) \\ x" and ?v_t'x' = "(v \\ t') \\ x'"
      let ?u_w = "u \\ w" and ?v_w' = "v \\ w'"
      let ?w_u = "w \\ u" and ?w'_v = "w' \\ v"
      have w_tx_in_\<NN>: "?w_tx \<in> \<NN>"
        using tx ww' xx' R.con_composite_of_iff [of t x tx w]
        by (metis (full_types) N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_left(1)
            N.forward_stable R.null_is_zero(2) R.con_imp_coinitial R.conI R.con_sym)
      have w'_t'x'_in_\<NN>: "?w'_t'x' \<in> \<NN>"
        using t'x' ww' xx' R.con_composite_of_iff [of t' x' t'x' w']
        by (metis (full_types) N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_left(1)
            R.con_sym N.forward_stable R.null_is_zero(2) R.con_imp_coinitial R.conI)
      have 2: "?tx_w \<approx>\<^sub>0 ?t'x'_w'"
      proof -
        have "?tx_w \<approx>\<^sub>0 t \\ w"
          using t'x' tx ww' xx' N.Cong\<^sub>0_composite_of_arr_normal [of t x tx] N.Cong\<^sub>0_subst_left(2)
          by (metis N.Cong\<^sub>0_transitive R.conI)
        also have "t \\ w \<approx>\<^sub>0 t' \\ w'"
          using ww' by blast
        also have "t' \\ w' \<approx>\<^sub>0 ?t'x'_w'"
          using t'x' tx ww' xx' N.Cong\<^sub>0_composite_of_arr_normal [of t' x' t'x'] N.Cong\<^sub>0_subst_left(2)
          by (metis N.Cong\<^sub>0_transitive R.conI)
        finally show ?thesis by blast
      qed
      obtain z where z: "R.composite_of ?tx_w (?t'x'_w' \\ ?tx_w) z"
        by (metis "2" R.arr_resid_iff_con R.con_implies_arr(2) N.elements_are_arr
            N.composite_closed_right R.seqI(1) R.sources_resid)
      obtain z' where z': "R.composite_of ?t'x'_w' (?tx_w \\ ?t'x'_w') z'"
        by (metis "2" R.arr_resid_iff_con R.con_implies_arr(2) N.elements_are_arr
            N.composite_closed_right R.seqI(1) R.sources_resid)
      have 3: "z \<approx>\<^sub>0 z'"
        using 2 N.diamond_commutes_upto_Cong\<^sub>0 N.Cong\<^sub>0_imp_con z z' by blast
      have "R.targets z = R.targets z'"
        by (metis R.targets_resid_sym z z' R.targets_composite_of R.conI)
      have Con_z_uw: "z \<frown> ?u_w"
      proof -
        have "?tx_w \<frown> ?u_w"
          by (meson 3 N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_left(1)
              R.bounded_imp_con R.con_implies_arr(1) R.con_imp_coinitial
              N.resid_along_elem_preserves_con tu tx ww' xx' z z' R.arr_resid_iff_con)
        thus ?thesis
          using 2 N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_left(1) z by blast
      qed
      moreover have Con_z'_vw': "z' \<frown> ?v_w'"
      proof -
        have "?t'x'_w' \<frown> ?v_w'"
          by (meson 3 N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_left(1)
              R.bounded_imp_con t'v t'x' ww' xx' z z' R.con_imp_coinitial
              N.resid_along_elem_preserves_con R.arr_resid_iff_con R.con_implies_arr(1))
        thus ?thesis
          by (meson 2 N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_left(1) z')
      qed
      moreover have Con_z_vw': "z \<frown> ?v_w'"
        using 3 Con_z'_vw' N.Cong\<^sub>0_subst_left(1) by blast
      moreover have *: "?u_w \\ z \<frown> ?v_w' \\ z"
      proof -
        obtain y where y: "R.composite_of (w \\ tx) (?t'x'_w' \\ ?tx_w) y"
          by (metis 2 R.arr_resid_iff_con R.composable_def R.composable_imp_seq
              R.con_imp_coinitial N.elements_are_arr N.composite_closed_right
              R.seq_def R.targets_resid_sym ww' z N.forward_stable)
        obtain y' where y': "R.composite_of (w' \\ t'x') (?tx_w \\ ?t'x'_w') y'"
          by (metis 2 R.arr_resid_iff_con R.composable_def R.composable_imp_seq
              R.con_imp_coinitial N.elements_are_arr N.composite_closed_right
              R.targets_resid_sym ww' z' R.seq_def N.forward_stable)
        have y_comp: "R.composite_of (w \\ tx) ((t'x' \\ w') \\ (tx \\ w)) y"
          using y by simp
        have y_in_normal: "y \<in> \<NN>"
          by (metis 2 Con_z_uw R.arr_iff_has_source R.arr_resid_iff_con N.composite_closed
              R.con_imp_coinitial R.con_implies_arr(1) N.forward_stable
              R.sources_composite_of ww' y_comp z)
        have y_coinitial: "R.coinitial y (u \\ tx)"
          using y R.arr_composite_of R.sources_composite_of
          apply (intro R.coinitialI)
           apply auto
           apply (metis N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_right(1)
                        R.composite_of_cancel_left R.con_sym R.not_ide_null R.null_is_zero(2)
                        R.sources_resid R.conI tu tx xx')
          by (metis R.arr_iff_has_source R.not_arr_null R.sources_resid empty_iff R.conI)
        have y_con: "y \<frown> u \\ tx"
          using y_in_normal y_coinitial
            by (metis R.coinitial_iff N.elements_are_arr N.forward_stable
                R.arr_resid_iff_con)
        have A: "?u_w \\ z \<sim> (u \\ tx) \\ y"
        proof -
          have "(u \\ tx) \\ y \<sim> ((u \\ tx) \\ (w \\ tx)) \\ (?t'x'_w' \\ ?tx_w)"
            using y_comp y_con 
                  R.resid_composite_of(3) [of "w \\ tx" "?t'x'_w' \\ ?tx_w" y "u \\ tx"]
            by simp
          also have "((u \\ tx) \\ (w \\ tx)) \\ (?t'x'_w' \\ ?tx_w) \<sim> ?u_w \\ z"
            by (metis Con_z_uw R.resid_composite_of(3) z R.cube)
          finally show ?thesis by blast
        qed
        have y'_comp: "R.composite_of (w' \\ t'x') (?tx_w \\ ?t'x'_w') y'"
          using y' by simp
        have y'_in_normal: "y' \<in> \<NN>"
          by (metis 2 Con_z'_vw' R.arr_iff_has_source R.arr_resid_iff_con
              N.composite_closed R.con_imp_coinitial R.con_implies_arr(1)
              N.forward_stable R.sources_composite_of ww' y'_comp z')
        have y'_coinitial: "R.coinitial y' (v \\ t'x')"
          using y' R.coinitial_def
          by (metis Con_z'_vw' R.arr_resid_iff_con R.composite_ofE R.con_imp_coinitial
              R.con_implies_arr(1) R.cube R.prfx_implies_con R.resid_composite_of(1)
              R.sources_resid z')
        have y'_con: "y' \<frown> v \\ t'x'"
          using y'_in_normal y'_coinitial
          by (metis R.coinitial_iff N.elements_are_arr N.forward_stable
              R.arr_resid_iff_con)
        have B: "?v_w' \\ z' \<sim> (v \\ t'x') \\ y'"
        proof -
          have "(v \\ t'x') \\ y' \<sim> ((v \\ t'x') \\ (w' \\ t'x')) \\ (?tx_w \\ ?t'x'_w')"
            using y'_comp y'_con
                  R.resid_composite_of(3) [of "w' \\ t'x'" "?tx_w \\ ?t'x'_w'" y' "v \\ t'x'"]
            by blast
          also have "((v \\ t'x') \\ (w' \\ t'x')) \\ (?tx_w \\ ?t'x'_w') \<sim> ?v_w' \\ z'"
            by (metis Con_z'_vw' R.cube R.resid_composite_of(3) z')
          finally show ?thesis by blast
        qed
        have C: "u \\ tx \<frown> v \\ t'x'"
          using tx t'x' xx' R.con_sym R.cong_subst_right(1) R.resid_composite_of(3)
          by (meson R.coinitial_iff R.arr_resid_iff_con y'_coinitial y_coinitial)
        have D: "y \<approx>\<^sub>0 y'"
        proof -
          have "y \<approx>\<^sub>0 w \\ tx"
            using 2 N.Cong\<^sub>0_composite_of_arr_normal y_comp by blast
          also have "w \\ tx \<approx>\<^sub>0 w' \\ t'x'"
          proof -
            have "w \\ tx \<in> \<NN> \<and> w' \\ t'x' \<in> \<NN>"
              using N.factor_closed(1) y_comp y_in_normal y'_comp y'_in_normal by blast
            moreover have "R.coinitial (w \\ tx) (w' \\ t'x')"
              by (metis C R.coinitial_def R.con_implies_arr(2) N.elements_are_arr
                  R.sources_resid calculation R.con_imp_coinitial R.arr_resid_iff_con y_con)
            ultimately show ?thesis
              by (meson R.arr_resid_iff_con R.con_imp_coinitial N.forward_stable
                  N.elements_are_arr)
          qed
          also have "w' \\ t'x' \<approx>\<^sub>0 y'"
            using 2 N.Cong\<^sub>0_composite_of_arr_normal y'_comp by blast
          finally show ?thesis by blast
        qed
        have par_y_y': "R.sources y = R.sources y' \<and> R.targets y = R.targets y'"
          using D N.Cong\<^sub>0_imp_coinitial R.targets_composite_of y'_comp y_comp z z'
                \<open>R.targets z = R.targets z'\<close>
          by presburger
        have E: "(u \\ tx) \\ y \<frown> (v \\ t'x') \\ y'"
        proof -
          have "(u \\ tx) \\ y \<frown> (v \\ t'x') \\ y"
            using C N.Resid_along_normal_preserves_reflects_con R.coinitial_iff
                  y_coinitial y_in_normal
            by presburger
          moreover have "(v \\ t'x') \\ y \<approx>\<^sub>0 (v \\ t'x') \\ y'"
            using par_y_y' N.coherent R.coinitial_iff y'_coinitial y'_in_normal y_in_normal
            by presburger
          ultimately show ?thesis
            using N.Cong\<^sub>0_subst_right(1) by blast
        qed
        hence "?u_w \\ z \<frown> ?v_w' \\ z'"
        proof -
          have "(u \\ tx) \\ y \<sim> ?u_w \\ z"
            using A by simp
          moreover have "(u \\ tx) \\ y \<frown> (v \\ t'x') \\ y'"
            using E by blast
          moreover have "(v \\ t'x') \\ y' \<sim> ?v_w' \\ z'"
            using B R.cong_symmetric by blast
          moreover have "R.sources ((u \\ w) \\ z) = R.sources ((v \\ w') \\ z')"
            by (simp add: Con_z'_vw' Con_z_uw R.con_sym \<open>R.targets z = R.targets z'\<close>)
          ultimately show ?thesis
            by (meson N.Cong\<^sub>0_subst_Con N.ide_closed)
        qed
        moreover have "?v_w' \\ z' \<approx> ?v_w' \\ z"
          by (meson 3 Con_z_vw' N.CongI N.Cong\<^sub>0_subst_right(2) R.con_sym)
        moreover have "R.sources ((v \\ w') \\ z) = R.sources ((u \\ w) \\ z)"
          by (metis R.con_implies_arr(1) R.sources_resid calculation(1) calculation(2)
                    N.Cong_imp_arr(2) R.arr_resid_iff_con)
        ultimately show ?thesis
          by (metis N.Cong_reflexive N.Cong_subst(1) R.con_implies_arr(1))
      qed
      ultimately have **: "?v_w' \\ z \<frown> ?u_w \\ z \<and>
                           (?v_w' \\ z) \\ (?u_w \\ z) = (?v_w' \\ ?u_w) \\ (z \\ ?u_w)"
        by (meson R.con_sym R.cube)
      have Cong_t_z: "t \<approx> z"
        by (metis 2 N.Cong\<^sub>0_composite_of_arr_normal N.Cong_closure_props(2-3)
            N.Cong_closure_props(4) N.Cong_imp_arr(2) R.coinitial_iff R.con_imp_coinitial
            tx ww' xx' z R.arr_resid_iff_con)
      have Cong_u_uw: "u \<approx> ?u_w"
        by (meson Con_z_uw N.Cong_closure_props(4) R.coinitial_iff R.con_imp_coinitial
            ww' R.arr_resid_iff_con)
      have Cong_v_vw': "v \<approx> ?v_w'"
        by (meson Con_z_vw' N.Cong_closure_props(4) R.coinitial_iff ww' R.con_imp_coinitial
            R.arr_resid_iff_con)
      have \<T>: "N.is_Cong_class \<T> \<and> z \<in> \<T>"
        by (metis (no_types, lifting) Cong_t_z N.Cong_class_eqI N.Cong_class_is_nonempty
            N.Cong_class_memb_Cong_rep N.Cong_class_rep N.Cong_imp_arr(2) N.arr_in_Cong_class
            tu assms Con_char)
      have \<U>: "N.is_Cong_class \<U> \<and> ?u_w \<in> \<U>"
        by (metis Con_char Con_z_uw Cong_u_uw Int_iff N.Cong_class_eqI' N.Cong_class_eqI
            N.arr_in_Cong_class R.con_implies_arr(2) N.is_Cong_classI tu assms empty_iff)
      have \<V>: "N.is_Cong_class \<V> \<and> ?v_w' \<in> \<V>"
        by (metis Con_char Con_z_vw' Cong_v_vw' Int_iff N.Cong_class_eqI' N.Cong_class_eqI
            N.arr_in_Cong_class R.con_implies_arr(2) N.is_Cong_classI t'v assms empty_iff)
      show "(\<V> \<lbrace>\\\<rbrace> \<T>) \<lbrace>\\\<rbrace> (\<U> \<lbrace>\\\<rbrace> \<T>) = (\<V> \<lbrace>\\\<rbrace> \<U>) \<lbrace>\\\<rbrace> (\<T> \<lbrace>\\\<rbrace> \<U>)"
      proof -
        have "(\<V> \<lbrace>\\\<rbrace> \<T>) \<lbrace>\\\<rbrace> (\<U> \<lbrace>\\\<rbrace> \<T>) = \<lbrace>(?v_w' \\ z) \\ (?u_w \\ z)\<rbrace>"
          using \<T> \<U> \<V> * Resid_by_members
          by (metis ** Con_char N.arr_in_Cong_class R.arr_resid_iff_con assms R.con_implies_arr(2))
        moreover have "(\<V> \<lbrace>\\\<rbrace> \<U>) \<lbrace>\\\<rbrace> (\<T> \<lbrace>\\\<rbrace> \<U>) = \<lbrace>(?v_w' \\ ?u_w) \\ (z \\ ?u_w)\<rbrace>"
          using Resid_by_members [of \<V> \<U> ?v_w' ?u_w] Resid_by_members [of \<T> \<U> z ?u_w]
                Resid_by_members [of "\<V> \<lbrace>\\\<rbrace> \<U>" "\<T> \<lbrace>\\\<rbrace> \<U>" "?v_w' \\ ?u_w" "z \\ ?u_w"]
          by (metis \<T> \<U> \<V> * ** N.arr_in_Cong_class R.con_implies_arr(2) N.is_Cong_classI
              R.resid_reflects_con R.arr_resid_iff_con)
        ultimately show ?thesis
          using ** by simp
      qed
    qed

    sublocale residuation Resid
      using null_char Con_sym Arr_Resid Cube
      by unfold_locales metis+

    lemma is_residuation:
    shows "residuation Resid"
      ..

    lemma arr_char:
    shows "arr \<T> \<longleftrightarrow> N.is_Cong_class \<T>"
      by (metis N.is_Cong_class_def arrI not_arr_null null_char N.Cong_class_memb_is_arr
          Con_char R.arrE arrE arr_resid conI)

    lemma ide_char:
    shows "ide \<U> \<longleftrightarrow> arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {}"
    proof
      show "ide \<U> \<Longrightarrow> arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {}"
        apply (elim ideE)
        by (metis Con_char N.Cong\<^sub>0_reflexive Resid_by_members disjoint_iff null_char
            N.arr_in_Cong_class R.arrE R.arr_resid arr_resid conE)
      show "arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {} \<Longrightarrow> ide \<U>"
      proof -
        assume \<U>: "arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {}"
        obtain u where u: "R.arr u \<and> u \<in> \<U> \<inter> \<NN>"
          using \<U> arr_char
          by (metis IntI N.Cong_class_memb_is_arr disjoint_iff)
        show ?thesis
          by (metis IntD1 IntD2 N.Cong_class_eqI N.Cong_closure_props(4) N.arr_in_Cong_class
              N.is_Cong_classI Resid_by_members \<U> arrE arr_char disjoint_iff ideI
              N.Cong_class_eqI' R.arrE u)
      qed
    qed

    lemma ide_char':
    shows "ide \<A> \<longleftrightarrow> arr \<A> \<and> \<A> \<subseteq> \<NN>"
      by (metis Int_absorb2 Int_emptyI N.Cong_class_memb_Cong_rep N.Cong_closure_props(1)
          ide_char not_arr_null null_char N.normal_is_Cong_closed arr_char subsetI)

    lemma con_char\<^sub>Q\<^sub>C\<^sub>N:
    shows "con \<T> \<U> \<longleftrightarrow>
           N.is_Cong_class \<T> \<and> N.is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)"
      by (metis Con_char conE conI null_char)

    (*
     * TODO: Does the stronger form of con_char hold in this context?
     * I am currently only able to prove it for the more special context of paths,
     * but it doesn't seem like that should be required.
     *
     * The issue is that congruent paths have the same sets of sources,
     * but this does not necessarily hold in general.  If we know that all representatives
     * of a congruence class have the same sets of sources, then we known that if any
     * pair of representatives is consistent, then the arbitrarily chosen representatives
     * of the congruence class are consistent.  This is by substitutivity of congruence,
     * which has coinitiality as a hypothesis.
     *
     * In the general case, we have to reason as follows: if t and u are consistent
     * representatives of \<T> and \<U>, and if t' and u' are arbitrary coinitial representatives
     * of \<T> and \<U>, then we can obtain "opposing spans" connecting t u and t' u'.
     * The opposing span form of coherence then implies that t' and u' are consistent.
     * So we should be able to show that if congruence classes \<T> and \<U> are consistent,
     * then all pairs of coinitial representatives are consistent.
     *)

    lemma con_imp_coinitial_members_are_con:
    assumes "con \<T> \<U>" and "t \<in> \<T>" and "u \<in> \<U>" and "R.sources t = R.sources u"
    shows "t \<frown> u"
      by (meson assms N.Cong_subst(1) N.is_Cong_classE con_char\<^sub>Q\<^sub>C\<^sub>N)

    sublocale rts Resid
    proof
      show 1: "\<And>\<A> \<T>. \<lbrakk>ide \<A>; con \<T> \<A>\<rbrakk> \<Longrightarrow> \<T> \<lbrace>\\\<rbrace> \<A> = \<T>"
      proof -
        fix \<A> \<T>
        assume \<A>: "ide \<A>" and con: "con \<T> \<A>"
        obtain t a where ta: "t \<in> \<T> \<and> a \<in> \<A> \<and> R.con t a \<and> \<T> \<lbrace>\\\<rbrace> \<A> = \<lbrace>t \\ a\<rbrace>"
          using con con_char\<^sub>Q\<^sub>C\<^sub>N Resid_by_members by auto
        have "a \<in> \<NN>"
          using \<A> ta ide_char' by auto
        hence "t \\ a \<approx> t"
          by (meson N.Cong_closure_props(4) N.Cong_symmetric R.coinitialE R.con_imp_coinitial
              ta)
        thus "\<T> \<lbrace>\\\<rbrace> \<A> = \<T>"
          using ta
          by (metis N.Cong_class_eqI N.Cong_class_memb_Cong_rep N.Cong_class_rep con con_char\<^sub>Q\<^sub>C\<^sub>N)
      qed
      show "\<And>\<T>. arr \<T> \<Longrightarrow> ide (trg \<T>)"
        by (metis N.Cong\<^sub>0_reflexive Resid_by_members disjoint_iff ide_char N.Cong_class_memb_is_arr
            N.arr_in_Cong_class N.is_Cong_class_def arr_char R.arrE R.arr_resid resid_arr_self)
      show "\<And>\<A> \<T>. \<lbrakk>ide \<A>; con \<A> \<T>\<rbrakk> \<Longrightarrow> ide (\<A> \<lbrace>\\\<rbrace> \<T>)"
        by (metis 1 arrE arr_resid con_sym ideE ideI cube)
      show "\<And>\<T> \<U>. con \<T> \<U> \<Longrightarrow> \<exists>\<A>. ide \<A> \<and> con \<A> \<T> \<and> con \<A> \<U>"
      proof -
        fix \<T> \<U>
        assume \<T>\<U>: "con \<T> \<U>"
        obtain t u where tu: "\<T> = \<lbrace>t\<rbrace> \<and> \<U> = \<lbrace>u\<rbrace> \<and> t \<frown> u"
          using \<T>\<U> con_char\<^sub>Q\<^sub>C\<^sub>N arr_char
          by (metis N.Cong_class_memb_Cong_rep N.Cong_class_eqI N.Cong_class_rep)
        obtain a where a: "a \<in> R.sources t"
          using \<T>\<U> tu R.con_implies_arr(1) R.arr_iff_has_source by blast
        have "ide \<lbrace>a\<rbrace> \<and> con \<lbrace>a\<rbrace> \<T> \<and> con \<lbrace>a\<rbrace> \<U>"
        proof (intro conjI)
          have 2: "a \<in> \<NN>"
            using \<T>\<U> tu a arr_char N.ide_closed R.sources_def by force
          show 3: "ide \<lbrace>a\<rbrace>"
            using \<T>\<U> tu 2 a ide_char arr_char con_char\<^sub>Q\<^sub>C\<^sub>N
            by (metis IntI N.arr_in_Cong_class N.is_Cong_classI empty_iff N.elements_are_arr)
          show "con \<lbrace>a\<rbrace> \<T>"
            using \<T>\<U> tu 2 3 a ide_char arr_char con_char\<^sub>Q\<^sub>C\<^sub>N
            by (metis N.arr_in_Cong_class R.composite_of_source_arr
                R.composite_of_def R.prfx_implies_con R.con_implies_arr(1))
          show "con \<lbrace>a\<rbrace> \<U>"
            using \<T>\<U> tu a ide_char arr_char con_char\<^sub>Q\<^sub>C\<^sub>N
            by (metis N.arr_in_Cong_class R.composite_of_source_arr R.con_prfx_composite_of
                N.is_Cong_classI R.con_implies_arr(1) R.con_implies_arr(2))
        qed
        thus "\<exists>\<A>. ide \<A> \<and> con \<A> \<T> \<and> con \<A> \<U>" by auto
      qed
      show "\<And>\<T> \<U> \<V>. \<lbrakk>ide (\<T> \<lbrace>\\\<rbrace> \<U>); con \<U> \<V>\<rbrakk> \<Longrightarrow> con (\<T> \<lbrace>\\\<rbrace> \<U>) (\<V> \<lbrace>\\\<rbrace> \<U>)"
      proof -
        fix \<T> \<U> \<V>
        assume \<T>\<U>: "ide (\<T> \<lbrace>\\\<rbrace> \<U>)"
        assume \<U>\<V>: "con \<U> \<V>"
        obtain t u where tu: "t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u \<and> \<T> \<lbrace>\\\<rbrace> \<U> = \<lbrace>t \\ u\<rbrace>"
          using \<T>\<U>
          by (meson Resid_by_members ide_implies_arr quotient_by_coherent_normal.con_char\<^sub>Q\<^sub>C\<^sub>N
              quotient_by_coherent_normal_axioms arr_resid_iff_con)
        obtain v u' where vu': "v \<in> \<V> \<and> u' \<in> \<U> \<and> v \<frown> u' \<and> \<V> \<lbrace>\\\<rbrace> \<U> = \<lbrace>v \\ u'\<rbrace>"
          by (meson R.con_sym Resid_by_members \<U>\<V> con_char\<^sub>Q\<^sub>C\<^sub>N)
        have 1: "u \<approx> u'"
          using \<U>\<V> tu vu'
          by (meson N.Cong_class_membs_are_Cong con_char\<^sub>Q\<^sub>C\<^sub>N)
        obtain w w' where ww': "w \<in> \<NN> \<and> w' \<in> \<NN> \<and> u \\ w \<approx>\<^sub>0 u' \\ w'"
          using 1 by auto
        have 2: "((t \\ u) \\ (w \\ u)) \\ ((u' \\ w') \\ (u \\ w)) \<frown>
                 ((v \\ u') \\ (w' \\ u')) \\ ((u \\ w) \\ (u' \\ w'))"
        proof -
          have "((t \\ u) \\ (w \\ u)) \\ ((u' \\ w') \\ (u \\ w)) \<in> \<NN>"
          proof -
            have "t \\ u \<in> \<NN>"
              using tu N.arr_in_Cong_class R.arr_resid_iff_con \<T>\<U> ide_char' by blast
            hence "(t \\ u) \\ (w \\ u) \<in> \<NN>"
              by (metis N.Cong_closure_props(4) N.forward_stable R.null_is_zero(2)
                  R.con_imp_coinitial R.sources_resid N.Cong_imp_arr(2) R.arr_resid_iff_con
                  tu ww' R.conI)
            thus ?thesis
              by (metis N.Cong_closure_props(4) N.normal_is_Cong_closed R.sources_resid
                  R.targets_resid_sym N.elements_are_arr R.arr_resid_iff_con ww' R.conI)
          qed
          moreover have "R.sources (((t \\ u) \\ (w \\ u)) \\ ((u' \\ w') \\ (u \\ w))) =
                         R.sources (((v \\ u') \\ (w' \\ u')) \\ ((u \\ w) \\ (u' \\ w')))"
          proof -
            have "R.sources (((t \\ u) \\ (w \\ u)) \\ ((u' \\ w') \\ (u \\ w))) =
                  R.targets ((u' \\ w') \\ (u \\ w))"
              using R.arr_resid_iff_con N.elements_are_arr R.sources_resid calculation by blast
            also have "... = R.targets ((u \\ w) \\ (u' \\ w'))"
              by (metis R.targets_resid_sym R.conI)
            also have "... = R.sources (((v \\ u') \\ (w' \\ u')) \\ ((u \\ w) \\ (u' \\ w')))"
              using R.arr_resid_iff_con N.elements_are_arr R.sources_resid
              by (metis N.Cong_closure_props(4) N.Cong_imp_arr(2) R.con_implies_arr(1)
                  R.con_imp_coinitial N.forward_stable R.targets_resid_sym vu' ww')
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            by (metis (no_types, lifting) N.Cong\<^sub>0_imp_con N.Cong_closure_props(4)
                N.Cong_imp_arr(2) R.arr_resid_iff_con R.con_imp_coinitial N.forward_stable
                R.null_is_zero(2) R.conI)
        qed
        moreover have "t \\ u \<approx> ((t \\ u) \\ (w \\ u)) \\ ((u' \\ w') \\ (u \\ w))"
          by (metis (no_types, opaque_lifting) N.Cong_closure_props(4) N.Cong_transitive
              N.forward_stable R.arr_resid_iff_con R.con_imp_coinitial R.rts_axioms calculation
              rts.coinitial_iff ww')
        moreover have "v \\ u' \<approx> ((v \\ u') \\ (w' \\ u')) \\ ((u \\ w) \\ (u' \\ w'))"
        proof -
          have "w' \\ u' \<in> \<NN>"
            by (meson R.con_implies_arr(2) R.con_imp_coinitial N.forward_stable
                ww' N.Cong\<^sub>0_imp_con R.arr_resid_iff_con)
          moreover have "(u \\ w) \\ (u' \\ w') \<in> \<NN>"
            using ww' by blast
          ultimately show ?thesis
            by (meson 2 N.Cong_closure_props(2) N.Cong_closure_props(4) R.arr_resid_iff_con
                R.coinitial_iff R.con_imp_coinitial)
        qed
        ultimately show "con (\<T> \<lbrace>\\\<rbrace> \<U>) (\<V> \<lbrace>\\\<rbrace> \<U>)"
          using con_char\<^sub>Q\<^sub>C\<^sub>N N.Cong_class_def N.is_Cong_classI tu vu' R.arr_resid_iff_con
          by auto
      qed
    qed

    lemma is_rts:
    shows "rts Resid"
      ..

    sublocale extensional_rts Resid
    proof
      fix \<T> \<U>
      assume \<T>\<U>: "cong \<T> \<U>"
      show "\<T> = \<U>"
      proof -
        obtain t u where tu: "\<T> = \<lbrace>t\<rbrace> \<and> \<U> = \<lbrace>u\<rbrace> \<and> t \<frown> u"
          by (metis Con_char N.Cong_class_eqI N.Cong_class_memb_Cong_rep N.Cong_class_rep
              \<T>\<U> ide_char not_arr_null null_char)
        have "t \<approx>\<^sub>0 u"
        proof
          show "t \\ u \<in> \<NN>"
            using tu \<T>\<U> Resid_by_members [of \<T> \<U> t u]
            by (metis (full_types) N.arr_in_Cong_class R.con_implies_arr(1-2)
                N.is_Cong_classI ide_char' R.arr_resid_iff_con subset_iff)
          show "u \\ t \<in> \<NN>"
            using tu \<T>\<U> Resid_by_members [of \<U> \<T> u t] R.con_sym
            by (metis (full_types) N.arr_in_Cong_class R.con_implies_arr(1-2)
                N.is_Cong_classI ide_char' R.arr_resid_iff_con subset_iff)
        qed
        hence "t \<approx> u"
          using N.Cong\<^sub>0_implies_Cong by simp
        thus "\<T> = \<U>"
          by (simp add: N.Cong_class_eqI tu)
      qed
    qed

    theorem is_extensional_rts:
    shows "extensional_rts Resid"
      ..

    lemma sources_char\<^sub>Q\<^sub>C\<^sub>N:
    shows "sources \<T> = {\<A>. arr \<T> \<and> \<A> = {a. \<exists>t a'. t \<in> \<T> \<and> a' \<in> R.sources t \<and> a' \<approx> a}}"
    proof -
      let ?\<A> = "{a. \<exists>t a'. t \<in> \<T> \<and> a' \<in> R.sources t \<and> a' \<approx> a}"
      have 1: "arr \<T> \<Longrightarrow> ide ?\<A>"
      proof (unfold ide_char', intro conjI)
        assume \<T>: "arr \<T>"
        show "?\<A> \<subseteq> \<NN>"
          using N.ide_closed N.normal_is_Cong_closed by blast
        show "arr ?\<A>"
        proof -
          have "N.is_Cong_class ?\<A>"
          proof
            show "?\<A> \<noteq> {}"
              by (metis (mono_tags, lifting) Collect_empty_eq N.Cong_class_def N.Cong_imp_arr(1)
                  N.is_Cong_class_def N.sources_are_Cong R.arr_iff_has_source R.sources_def
                  \<T> arr_char mem_Collect_eq)
            show "\<And>a a'. \<lbrakk>a \<in> ?\<A>; a' \<approx> a\<rbrakk> \<Longrightarrow> a' \<in> ?\<A>"
              using N.Cong_transitive by blast
            show "\<And>a a'. \<lbrakk>a \<in> ?\<A>; a' \<in> ?\<A>\<rbrakk> \<Longrightarrow> a \<approx> a'"
            proof -
              fix a a'
              assume a: "a \<in> ?\<A>" and a': "a' \<in> ?\<A>"
              obtain t b where b: "t \<in> \<T> \<and> b \<in> R.sources t \<and> b \<approx> a"
                using a by blast
              obtain t' b' where b': "t' \<in> \<T> \<and> b' \<in> R.sources t' \<and> b' \<approx> a'"
                using a' by blast
              have "b \<approx> b'"
                using \<T> arr_char b b'
                by (meson IntD1 N.Cong_class_membs_are_Cong N.in_sources_respects_Cong)
              thus "a \<approx> a'"
                by (meson N.Cong_symmetric N.Cong_transitive b b')
            qed
          qed
          thus ?thesis
            using arr_char by auto
        qed
      qed
      moreover have "arr \<T> \<Longrightarrow> con \<T> ?\<A>"
      proof -
        assume \<T>: "arr \<T>"
        obtain t a where a: "t \<in> \<T> \<and> a \<in> R.sources t"
          using \<T> arr_char
          by (metis N.Cong_class_is_nonempty R.arr_iff_has_source empty_subsetI
                    N.Cong_class_memb_is_arr subsetI subset_antisym)
        have "t \<in> \<T> \<and> a \<in> {a. \<exists>t a'. t \<in> \<T> \<and> a' \<in> R.sources t \<and> a' \<approx> a} \<and> t \<frown> a"
          using a N.Cong_reflexive R.sources_def R.con_implies_arr(2) by fast
        thus ?thesis
          using \<T> 1 arr_char con_char\<^sub>Q\<^sub>C\<^sub>N [of \<T> ?\<A>] by auto
      qed
      ultimately have "arr \<T> \<Longrightarrow> ?\<A> \<in> sources \<T>"
        using sources_def by blast
      thus ?thesis
        using "1" ide_char sources_char by auto
    qed

    lemma targets_char\<^sub>Q\<^sub>C\<^sub>N:
    shows "targets \<T> = {\<B>. arr \<T> \<and> \<B> = \<T> \<lbrace>\\\<rbrace> \<T>}"
    proof -
      have "targets \<T> = {\<B>. ide \<B> \<and> con (\<T> \<lbrace>\\\<rbrace> \<T>) \<B>}"
        by (simp add: targets_def trg_def)
      also have "... = {\<B>. arr \<T> \<and> ide \<B> \<and> (\<exists>t u. t \<in> \<T> \<lbrace>\\\<rbrace> \<T> \<and> u \<in> \<B> \<and> t \<frown> u)}"
        using arr_resid_iff_con con_char\<^sub>Q\<^sub>C\<^sub>N arr_char arr_def by auto
      also have "... = {\<B>. arr \<T> \<and> ide \<B> \<and>
                           (\<exists>t t' b u. t \<in> \<T> \<and> t' \<in> \<T> \<and> t \<frown> t' \<and> b \<in> \<lbrace>t \\ t'\<rbrace> \<and> u \<in> \<B> \<and> b \<frown> u)}"
        apply auto
         apply (metis (full_types) Resid_by_members cong_char not_ide_null null_char Con_char)
        by (metis Resid_by_members arr_char)
      also have "... = {\<B>. arr \<T> \<and> ide \<B> \<and>
                           (\<exists>t t' b. t \<in> \<T> \<and> t' \<in> \<T> \<and> t \<frown> t' \<and> b \<in> \<lbrace>t \\ t'\<rbrace> \<and> b \<in> \<B>)}"
      proof -
        have "\<And>\<B> t t' b. \<lbrakk>arr \<T>; ide \<B>; t \<in> \<T>; t' \<in> \<T>; t \<frown> t'; b \<in> \<lbrace>t \\ t'\<rbrace>\<rbrakk>
                            \<Longrightarrow> (\<exists>u. u \<in> \<B> \<and> b \<frown> u) \<longleftrightarrow> b \<in> \<B>"
        proof -
          fix \<B> t t' b
          assume \<T>: "arr \<T>" and \<B>: "ide \<B>" and t: "t \<in> \<T>" and t': "t' \<in> \<T>"
                 and tt': "t \<frown> t'" and b: "b \<in> \<lbrace>t \\ t'\<rbrace>"
          have 0: "b \<in> \<NN>"
            by (metis Resid_by_members \<T> b ide_char' ide_trg arr_char subsetD t t' trg_def tt')
          show "(\<exists>u. u \<in> \<B> \<and> b \<frown> u) \<longleftrightarrow> b \<in> \<B>"
            using 0
            by (meson N.Cong_closure_props(3) N.forward_stable N.elements_are_arr
                \<B> arr_char R.con_imp_coinitial N.is_Cong_classE ide_char' R.arrE
                R.con_sym subsetD)
        qed
        thus ?thesis
          using ide_char arr_char
          by (metis (no_types, lifting))
      qed
      also have "... = {\<B>. arr \<T> \<and> ide \<B> \<and> (\<exists>t t'. t \<in> \<T> \<and> t' \<in> \<T> \<and> t \<frown> t' \<and> \<lbrace>t \\ t'\<rbrace> \<subseteq> \<B>)}"
      proof -
        have "\<And>\<B> t t' b. \<lbrakk>arr \<T>; ide \<B>; t \<in> \<T>; t' \<in> \<T>; t \<frown> t'\<rbrakk>
                            \<Longrightarrow> (\<exists>b. b \<in> \<lbrace>t \\ t'\<rbrace> \<and> b \<in> \<B>) \<longleftrightarrow> \<lbrace>t \\ t'\<rbrace> \<subseteq> \<B>"
          using ide_char arr_char
          apply (intro iffI)
           apply (metis IntI N.Cong_class_eqI' R.arr_resid_iff_con N.is_Cong_classI empty_iff
                        set_eq_subset)
          by (meson N.arr_in_Cong_class R.arr_resid_iff_con subsetD)
        thus ?thesis
          using ide_char arr_char
          by (metis (no_types, lifting))
      qed
      also have "... = {\<B>. arr \<T> \<and> ide \<B> \<and> \<T> \<lbrace>\\\<rbrace> \<T> \<subseteq> \<B>}"
        using arr_char ide_char Resid_by_members [of \<T> \<T>]
        by (metis (no_types, opaque_lifting) arrE con_char\<^sub>Q\<^sub>C\<^sub>N)
      also have "... = {\<B>. arr \<T> \<and> \<B> = \<T> \<lbrace>\\\<rbrace> \<T>}"
        by (metis (no_types, lifting) arr_has_un_target calculation con_ide_are_eq
            cong_reflexive mem_Collect_eq targets_def trg_def)
      finally show ?thesis by blast
    qed

    lemma src_char\<^sub>Q\<^sub>C\<^sub>N:
    shows "src \<T> = {a. arr \<T> \<and> (\<exists>t a'. t \<in> \<T> \<and> a' \<in> R.sources t \<and> a' \<approx> a)}"
      using sources_char\<^sub>Q\<^sub>C\<^sub>N [of \<T>]
      by (simp add: null_char src_def)

    lemma trg_char\<^sub>Q\<^sub>C\<^sub>N:
    shows "trg \<T> = \<T> \<lbrace>\\\<rbrace> \<T>"
      unfolding trg_def by blast

    subsubsection "Quotient Map"

    abbreviation quot
    where "quot t \<equiv> \<lbrace>t\<rbrace>"

    sublocale quot: simulation resid Resid quot
    proof
      show "\<And>t. \<not> R.arr t \<Longrightarrow> \<lbrace>t\<rbrace> = null"
        using N.Cong_class_def N.Cong_imp_arr(1) null_char by force
      show "\<And>t u. t \<frown> u \<Longrightarrow> con \<lbrace>t\<rbrace> \<lbrace>u\<rbrace>"
        by (meson N.arr_in_Cong_class N.is_Cong_classI R.con_implies_arr(1-2) con_char\<^sub>Q\<^sub>C\<^sub>N)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<lbrace>t \\ u\<rbrace> = \<lbrace>t\<rbrace> \<lbrace>\\\<rbrace> \<lbrace>u\<rbrace>"
        by (metis N.arr_in_Cong_class N.is_Cong_classI R.con_implies_arr(1-2) Resid_by_members)
    qed

    lemma quotient_is_simulation:
    shows "simulation resid Resid quot"
      ..

    (*
     * TODO: Show couniversality.
     *)

  end

  subsection "Identities form a Coherent Normal Sub-RTS"

  text \<open>
    We now show that the collection of identities of an RTS form a coherent normal sub-RTS,
    and that the associated congruence \<open>\<approx>\<close> coincides with \<open>\<sim>\<close>.
    Thus, every RTS can be factored by the relation \<open>\<sim>\<close> to obtain an extensional RTS.
    Although we could have shown that fact much earlier, we have delayed proving it so that
    we could simply obtain it as a special case of our general quotient result without
    redundant work.
  \<close>

  context rts
  begin

    interpretation normal_sub_rts resid \<open>Collect ide\<close>
    proof
      show "\<And>t. t \<in> Collect ide \<Longrightarrow> arr t"
        by blast
      show 1: "\<And>a. ide a \<Longrightarrow> a \<in> Collect ide"
        by blast
      show "\<And>u t. \<lbrakk>u \<in> Collect ide; coinitial t u\<rbrakk> \<Longrightarrow> u \\ t \<in> Collect ide"
        by (metis 1 CollectD arr_def coinitial_iff
            con_sym in_sourcesE in_sourcesI resid_ide_arr)
      show "\<And>u t. \<lbrakk>u \<in> Collect ide; t \\ u \<in> Collect ide\<rbrakk> \<Longrightarrow> t \<in> Collect ide"
        using ide_backward_stable by blast
      show "\<And>u t. \<lbrakk>u \<in> Collect ide; seq u t\<rbrakk> \<Longrightarrow> \<exists>v. composite_of u t v"
        by (metis composite_of_source_arr ide_def in_sourcesI mem_Collect_eq seq_def
            resid_source_in_targets)
      show "\<And>u t. \<lbrakk>u \<in> Collect ide; seq t u\<rbrakk> \<Longrightarrow> \<exists>v. composite_of t u v"
        by (metis arrE composite_of_arr_target in_sourcesI seqE mem_Collect_eq)
    qed

    lemma identities_form_normal_sub_rts:
    shows "normal_sub_rts resid (Collect ide)"
      ..

    interpretation coherent_normal_sub_rts resid \<open>Collect ide\<close>
      apply unfold_locales
      by (metis CollectD Cong\<^sub>0_reflexive Cong_closure_props(4) Cong_imp_arr(2)
                arr_resid_iff_con resid_arr_ide)

    lemma identities_form_coherent_normal_sub_rts:
    shows "coherent_normal_sub_rts resid (Collect ide)"
      ..
 
    lemma Cong_iff_cong:
    shows "Cong t u \<longleftrightarrow> t \<sim> u"
      by (metis CollectD Cong_def ide_closed resid_arr_ide
          Cong_closure_props(3) Cong_imp_arr(2) arr_resid_iff_con)

  end

  section "Paths"

  text \<open>
    A \emph{path} in an RTS is a nonempty list of arrows such that the set
    of targets of each arrow suitably matches the set of sources of its successor.
    The residuation on the given RTS extends inductively to a residuation on
    paths, so that paths also form an RTS.  The append operation on lists
    yields a composite for each pair of compatible paths.
  \<close>

  locale paths_in_rts =
    R: rts
  begin

    fun Srcs
    where "Srcs [] = {}"
        | "Srcs [t] = R.sources t"
        | "Srcs (t # T) = R.sources t"

    fun Trgs
    where "Trgs [] = {}"
        | "Trgs [t] = R.targets t"
        | "Trgs (t # T) = Trgs T"

    fun Arr
    where "Arr [] = False"
        | "Arr [t] = R.arr t"
        | "Arr (t # T) = (R.arr t \<and> Arr T \<and> R.targets t \<subseteq> Srcs T)"

    fun Ide
    where "Ide [] = False"
        | "Ide [t] = R.ide t"
        | "Ide (t # T) = (R.ide t \<and> Ide T \<and> R.targets t \<subseteq> Srcs T)"

    lemma set_Arr_subset_arr:
    shows "Arr T \<Longrightarrow> set T \<subseteq> Collect R.arr"
      apply (induct T)
       apply auto
      using Arr.elims(2)
       apply blast
      by (metis Arr.simps(3) Ball_Collect list.set_cases)

    lemma Arr_imp_arr_hd [simp]:
    assumes "Arr T"
    shows "R.arr (hd T)"
      using assms
      by (metis Arr.simps(1) CollectD hd_in_set set_Arr_subset_arr subset_code(1))

    lemma Arr_imp_arr_last [simp]:
    assumes "Arr T"
    shows "R.arr (last T)"
      using assms
      by (metis Arr.simps(1) CollectD in_mono last_in_set set_Arr_subset_arr)

    lemma Arr_imp_Arr_tl [simp]:
    assumes "Arr T" and "tl T \<noteq> []"
    shows "Arr (tl T)"
      using assms
      by (metis Arr.simps(3) list.exhaust_sel list.sel(2))

    lemma set_Ide_subset_ide:
    shows "Ide T \<Longrightarrow> set T \<subseteq> Collect R.ide"
      apply (induct T)
       apply auto
      using Ide.elims(2)
       apply blast
      by (metis Ide.simps(3) Ball_Collect list.set_cases)

    lemma Ide_imp_Ide_hd [simp]:
    assumes "Ide T"
    shows "R.ide (hd T)"
      using assms
      by (metis Ide.simps(1) CollectD hd_in_set set_Ide_subset_ide subset_code(1))

    lemma Ide_imp_Ide_last [simp]:
    assumes "Ide T"
    shows "R.ide (last T)"
      using assms
      by (metis Ide.simps(1) CollectD in_mono last_in_set set_Ide_subset_ide)

    lemma Ide_imp_Ide_tl [simp]:
    assumes "Ide T" and "tl T \<noteq> []"
    shows "Ide (tl T)"
      using assms
      by (metis Ide.simps(3) list.exhaust_sel list.sel(2))

    lemma Ide_implies_Arr:
    shows "Ide T \<Longrightarrow> Arr T"
      apply (induct T)
       apply simp
      using Ide.elims(2) by fastforce

    lemma const_ide_is_Ide:
    shows "\<lbrakk>T \<noteq> []; R.ide (hd T); set T \<subseteq> {hd T}\<rbrakk> \<Longrightarrow> Ide T"
      apply (induct T)
       apply auto
      by (metis Ide.simps(2-3) R.ideE R.sources_resid Srcs.simps(2-3) empty_iff insert_iff
          list.exhaust_sel list.set_sel(1) order_refl subset_singletonD)

    lemma Ide_char:
    shows "Ide T \<longleftrightarrow> Arr T \<and> set T \<subseteq> Collect R.ide"
      apply (induct T)
       apply auto[1]
      by (metis Arr.simps(3) Ide.simps(2-3) Ide_implies_Arr empty_subsetI
          insert_subset list.simps(15) mem_Collect_eq neq_Nil_conv set_empty)

    lemma IdeI [intro]:
    assumes "Arr T" and "set T \<subseteq> Collect R.ide"
    shows "Ide T"
      using assms Ide_char by force

    lemma Arr_has_Src:
    shows "Arr T \<Longrightarrow> Srcs T \<noteq> {}"
      apply (cases T)
       apply simp
      by (metis R.arr_iff_has_source Srcs.elims Arr.elims(2) list.distinct(1) list.sel(1))

    lemma Arr_has_Trg:
    shows "Arr T \<Longrightarrow> Trgs T \<noteq> {}"
      using R.arr_iff_has_target
      apply (induct T)
       apply simp
      by (metis Arr.simps(2) Arr.simps(3) Trgs.simps(2-3) list.exhaust_sel)

    lemma Srcs_are_ide:
    shows "Srcs T \<subseteq> Collect R.ide"
      apply (cases T)
       apply simp
      by (metis (no_types, lifting) Srcs.elims list.distinct(1) mem_Collect_eq
          R.sources_def subsetI)

    lemma Trgs_are_ide:
    shows "Trgs T \<subseteq> Collect R.ide"
      apply (induct T)
       apply simp
      by (metis R.arr_iff_has_target R.sources_resid Srcs.simps(2) Trgs.simps(2-3)
                Srcs_are_ide empty_subsetI list.exhaust R.arrE)

    lemma Srcs_are_con:
    assumes "a \<in> Srcs T" and "a' \<in> Srcs T"
    shows "a \<frown> a'"
      using assms
      by (metis Srcs.elims empty_iff R.sources_are_con)

    lemma Srcs_con_closed:
    assumes "a \<in> Srcs T" and "R.ide a'" and "a \<frown> a'"
    shows "a' \<in> Srcs T"
      using assms R.sources_con_closed
      apply (cases T, auto)
      by (metis Srcs.simps(2-3) neq_Nil_conv)

    lemma Srcs_eqI:
    assumes "Srcs T \<inter> Srcs T' \<noteq> {}"
    shows "Srcs T = Srcs T'"
      using assms R.sources_eqI
      apply (cases T; cases T')
         apply auto
       apply (metis IntI Srcs.simps(2-3) empty_iff neq_Nil_conv)
      by (metis Srcs.simps(2-3) assms neq_Nil_conv)

    lemma Trgs_are_con:
    shows "\<lbrakk>b \<in> Trgs T; b' \<in> Trgs T\<rbrakk> \<Longrightarrow> b \<frown> b'"
      apply (induct T)
       apply auto
      by (metis R.targets_are_con Trgs.simps(2-3) list.exhaust_sel)

    lemma Trgs_con_closed:
    shows "\<lbrakk>b \<in> Trgs T; R.ide b'; b \<frown> b'\<rbrakk> \<Longrightarrow> b' \<in> Trgs T"
      apply (induct T)
       apply auto
      by (metis R.targets_con_closed Trgs.simps(2-3) neq_Nil_conv)

    lemma Trgs_eqI:
    assumes "Trgs T \<inter> Trgs T' \<noteq> {}"
    shows "Trgs T = Trgs T'"
      using assms Trgs_are_ide Trgs_are_con Trgs_con_closed by blast

    lemma Srcs_simp\<^sub>P:
    assumes "Arr T"
    shows "Srcs T = R.sources (hd T)"
      using assms
      by (metis Arr_has_Src Srcs.simps(1) Srcs.simps(2) Srcs.simps(3) list.exhaust_sel)

    lemma Trgs_simp\<^sub>P:
    shows "Arr T \<Longrightarrow> Trgs T = R.targets (last T)"
      apply (induct T)
       apply simp
      by (metis Arr.simps(3) Trgs.simps(2) Trgs.simps(3) last_ConsL last_ConsR neq_Nil_conv)

    subsection "Residuation on Paths"

    text \<open>
      It was more difficult than I thought to get a correct formal definition for residuation
      on paths and to prove things from it.  Straightforward attempts to write a single
      recursive definition ran into problems with being able to prove termination,
      as well as getting the cases correct so that the domain of definition was symmetric.
      Eventually I found the definition below, which simplifies the termination proof
      to some extent through the use of two auxiliary functions, and which has a
      symmetric form that makes symmetry easier to prove.  However, there was still
      some difficulty in proving the recursive expansions with respect to cons and
      append that I needed.
    \<close>

    text \<open>
      The following defines residuation of a single transition along a path, yielding a transition.
    \<close>

    fun Resid1x  (infix "\<^sup>1\\\<^sup>*" 70)
    where "t \<^sup>1\\\<^sup>* [] = R.null"
        | "t \<^sup>1\\\<^sup>* [u] = t \\ u"
        | "t \<^sup>1\\\<^sup>* (u # U) = (t \\ u) \<^sup>1\\\<^sup>* U"

    text \<open>
      Next, we have residuation of a path along a single transition, yielding a path.
    \<close>

    fun Residx1  (infix "\<^sup>*\\\<^sup>1" 70)
    where "[] \<^sup>*\\\<^sup>1 u = []"
        | "[t] \<^sup>*\\\<^sup>1 u = (if t \<frown> u then [t \\ u] else [])"
        | "(t # T) \<^sup>*\\\<^sup>1 u =
             (if t \<frown> u \<and> T \<^sup>*\\\<^sup>1 (u \\ t) \<noteq> [] then (t \\ u) # T \<^sup>*\\\<^sup>1 (u \\ t) else [])"

    text \<open>
      Finally, residuation of a path along a path, yielding a path.
    \<close>

    function (sequential) Resid  (infix "\<^sup>*\\\<^sup>*" 70)
    where "[] \<^sup>*\\\<^sup>* _ = []"
        | "_ \<^sup>*\\\<^sup>* [] = []"
        | "[t] \<^sup>*\\\<^sup>* [u] = (if t \<frown> u then [t \\ u] else [])"
        | "[t] \<^sup>*\\\<^sup>* (u # U) =
             (if t \<frown> u \<and> (t \\ u) \<^sup>1\\\<^sup>* U \<noteq> R.null then [(t \\ u) \<^sup>1\\\<^sup>* U] else [])"
        | "(t # T) \<^sup>*\\\<^sup>* [u] =
             (if t \<frown> u \<and> T \<^sup>*\\\<^sup>1 (u \\ t) \<noteq> [] then (t \\ u) # (T \<^sup>*\\\<^sup>1 (u \\ t)) else [])"
        | "(t # T) \<^sup>*\\\<^sup>* (u # U) =
             (if t \<frown> u \<and> (t \\ u) \<^sup>1\\\<^sup>* U \<noteq> R.null \<and>
                 (T \<^sup>*\\\<^sup>1 (u \\ t)) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>1 (t \\ u)) \<noteq> []
              then (t \\ u) \<^sup>1\\\<^sup>* U # (T \<^sup>*\\\<^sup>1 (u \\ t)) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>1 (t \\ u))
              else [])"
      by pat_completeness auto

    text \<open>
      Residuation of a path along a single transition is length non-increasing.
      Actually, it is length-preserving, except in case the path and the transition
      are not consistent.  We will show that later, but for now this is what we
      need to establish termination for (\<open>\\<close>).
    \<close>

    lemma length_Residx1:
    shows "length (T \<^sup>*\\\<^sup>1 u) \<le> length T"
    proof (induct T arbitrary: u)
      show "\<And>u. length ([] \<^sup>*\\\<^sup>1 u) \<le> length []"
        by simp
      fix t T u
      assume ind: "\<And>u. length (T \<^sup>*\\\<^sup>1 u) \<le> length T"
      show "length ((t # T) \<^sup>*\\\<^sup>1 u) \<le> length (t # T)"
        using ind
        by (cases T, cases "t \<frown> u", cases "T \<^sup>*\\\<^sup>1 (u \\ t)") auto
    qed

    termination Resid
    proof (relation "measure (\<lambda>(T, U). length T + length U)")
      show "wf (measure (\<lambda>(T, U). length T + length U))"
        by simp
      fix t t' T u U
      have "length ((t' # T) \<^sup>*\\\<^sup>1 (u \\ t)) + length (U \<^sup>*\\\<^sup>1 (t \\ u))
              < length (t # t' # T) + length (u # U)"
        using length_Residx1
        by (metis add_less_le_mono impossible_Cons le_neq_implies_less list.size(4) trans_le_add1)
      thus 1: "(((t' # T) \<^sup>*\\\<^sup>1 (u \\ t), U \<^sup>*\\\<^sup>1 (t \\ u)), t # t' # T, u # U)
                 \<in> measure (\<lambda>(T, U). length T + length U)"
        by simp
      show "(((t' # T) \<^sup>*\\\<^sup>1 (u \\ t), U \<^sup>*\\\<^sup>1 (t \\ u)), t # t' # T, u # U)
              \<in> measure (\<lambda>(T, U). length T + length U)"
        using 1 length_Residx1 by blast
      have "length (T \<^sup>*\\\<^sup>1 (u \\ t)) + length (U \<^sup>*\\\<^sup>1 (t \\ u)) \<le> length T + length U"
        using length_Residx1 by (simp add: add_mono)
      thus 2: "((T \<^sup>*\\\<^sup>1 (u \\ t), U \<^sup>*\\\<^sup>1 (t \\ u)), t # T, u # U)
                 \<in> measure (\<lambda>(T, U). length T + length U)"
        by simp
      show "((T \<^sup>*\\\<^sup>1 (u \\ t), U \<^sup>*\\\<^sup>1 (t \\ u)), t # T, u # U)
               \<in> measure (\<lambda>(T, U). length T + length U)"
        using 2 length_Residx1 by blast
    qed

    lemma Resid1x_null:
    shows "R.null \<^sup>1\\\<^sup>* T = R.null"
      apply (induct T)
       apply auto
      by (metis R.null_is_zero(1) Resid1x.simps(2-3) list.exhaust)

    lemma Resid1x_ide:
    shows "\<lbrakk>R.ide a; a \<^sup>1\\\<^sup>* T \<noteq> R.null\<rbrakk> \<Longrightarrow> R.ide (a \<^sup>1\\\<^sup>* T)"
    proof (induct T arbitrary: a)
      show "\<And>a. a \<^sup>1\\\<^sup>* [] \<noteq> R.null \<Longrightarrow> R.ide (a \<^sup>1\\\<^sup>* [])"
        by simp
      fix a t T
      assume a: "R.ide a"
      assume ind: "\<And>a. \<lbrakk>R.ide a; a \<^sup>1\\\<^sup>* T \<noteq> R.null\<rbrakk> \<Longrightarrow> R.ide (a \<^sup>1\\\<^sup>* T)"
      assume con: "a \<^sup>1\\\<^sup>* (t # T) \<noteq> R.null"
      have 1: "a \<frown> t"
        using con
        by (metis R.con_def Resid1x.simps(2-3) Resid1x_null list.exhaust)
      show "R.ide (a \<^sup>1\\\<^sup>* (t # T))"
        using a 1 con ind R.resid_ide_arr
        by (metis Resid1x.simps(2-3) list.exhaust)
    qed

    (*
     * TODO: Try to make this a definition, rather than an abbreviation.
     *
     * I made an attempt at this, but there are many, many places where the
     * definition needs to be unwound.  It is not clear how valuable it might
     * end up being to have this as a definition.
     *)
    abbreviation Con  (infix "\<^sup>*\<frown>\<^sup>*" 50)
    where "T \<^sup>*\<frown>\<^sup>* U \<equiv> T \<^sup>*\\\<^sup>* U \<noteq> []"

    lemma Con_sym1:
    shows "T \<^sup>*\\\<^sup>1 u \<noteq> [] \<longleftrightarrow> u \<^sup>1\\\<^sup>* T \<noteq> R.null"
    proof (induct T arbitrary: u)
      show "\<And>u. [] \<^sup>*\\\<^sup>1 u \<noteq> [] \<longleftrightarrow> u \<^sup>1\\\<^sup>* [] \<noteq> R.null"
        by simp
      show "\<And>t T u. (\<And>u. T \<^sup>*\\\<^sup>1 u \<noteq> [] \<longleftrightarrow> u \<^sup>1\\\<^sup>* T \<noteq> R.null)
                        \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>1 u \<noteq> [] \<longleftrightarrow> u \<^sup>1\\\<^sup>* (t # T) \<noteq> R.null"
      proof -
        fix t T u
        assume ind: "\<And>u. T \<^sup>*\\\<^sup>1 u \<noteq> [] \<longleftrightarrow> u \<^sup>1\\\<^sup>* T \<noteq> R.null"
        show "(t # T) \<^sup>*\\\<^sup>1 u \<noteq> [] \<longleftrightarrow> u \<^sup>1\\\<^sup>* (t # T) \<noteq> R.null"
        proof
          show "(t # T) \<^sup>*\\\<^sup>1 u \<noteq> [] \<Longrightarrow> u \<^sup>1\\\<^sup>* (t # T) \<noteq> R.null"
            by (metis R.con_sym Resid1x.simps(2-3) Residx1.simps(2-3)
                ind neq_Nil_conv R.conE)
          show "u \<^sup>1\\\<^sup>* (t # T) \<noteq> R.null \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>1 u \<noteq> []"
            using ind R.con_sym
            apply (cases T)
             apply auto
            by (metis R.conI Resid1x_null)
        qed
      qed
    qed

    lemma Con_sym_ind:
    shows "length T + length U \<le> n \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
    proof (induct n arbitrary: T U)
      show "\<And>T U. length T + length U \<le> 0 \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
        by simp
      fix n and T U :: "'a list"
      assume ind: "\<And>T U. length T + length U \<le> n \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
      assume 1: "length T + length U \<le> Suc n"
      show "T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
        using R.con_sym Con_sym1
          apply (cases T; cases U)
           apply auto[3]
      proof -
        fix t u T' U'
        assume T: "T = t # T'" and U: "U = u # U'"
        show "T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
        proof (cases "T' = []")
          show "T' = [] \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
            using T U Con_sym1 R.con_sym
            by (cases U') auto
          show "T' \<noteq> [] \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
          proof (cases "U' = []")
            show "\<lbrakk>T' \<noteq> []; U' = []\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
              using T U R.con_sym Con_sym1
              by (cases T') auto
            show "\<lbrakk>T' \<noteq> []; U' \<noteq> []\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
            proof -
              assume T': "T' \<noteq> []" and U': "U' \<noteq> []"
              have 2: "length (U' \<^sup>*\\\<^sup>1 (t \\ u)) + length (T' \<^sup>*\\\<^sup>1 (u \\ t)) \<le> n"
              proof -
                have "length (U' \<^sup>*\\\<^sup>1 (t \\ u)) + length (T' \<^sup>*\\\<^sup>1 (u \\ t))
                         \<le> length U' + length T'"
                  by (simp add: add_le_mono length_Residx1)
                also have "... \<le> length T' + length U'"
                  using T' add.commute not_less_eq_eq by auto
                also have "... \<le> n"
                  using 1 T U by simp
                finally show ?thesis by blast
              qed
              show "T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
              proof
                assume Con: "T \<^sup>*\<frown>\<^sup>* U"
                have 3: "t \<frown> u \<and> T' \<^sup>*\\\<^sup>1 (u \\ t) \<noteq> [] \<and> (t \\ u) \<^sup>1\\\<^sup>* U' \<noteq> R.null \<and>
                         (T' \<^sup>*\\\<^sup>1 (u \\ t)) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>1 (t \\ u)) \<noteq> []"
                  using Con T U T' U' Con_sym1
                  apply (cases T', cases U')
                    apply simp_all
                  by (metis Resid.simps(1) Resid.simps(6) neq_Nil_conv)
                hence "u \<frown> t \<and> U' \<^sup>*\\\<^sup>1 (t \\ u) \<noteq> [] \<and> (u \\ t) \<^sup>1\\\<^sup>* T' \<noteq> R.null"
                  using T' U' R.con_sym Con_sym1 by simp
                moreover have "(U' \<^sup>*\\\<^sup>1 (t \\ u)) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>1 (u \\ t)) \<noteq> []"
                  using 2 3 ind by simp
                ultimately show "U \<^sup>*\<frown>\<^sup>* T"
                  using T U T' U'
                  by (cases T'; cases U') auto
                next
                assume Con: "U \<^sup>*\<frown>\<^sup>* T"
                have 3: "u \<frown> t \<and> U' \<^sup>*\\\<^sup>1 (t \\ u) \<noteq> [] \<and> (u \\ t) \<^sup>1\\\<^sup>* T' \<noteq> R.null \<and>
                         (U' \<^sup>*\\\<^sup>1 (t \\ u)) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>1 (u \\ t)) \<noteq> []"
                  using Con T U T' U' Con_sym1
                  apply (cases T'; cases U')
                     apply auto
                   apply argo
                  by force
                hence "t \<frown> u \<and> T' \<^sup>*\\\<^sup>1 (u \\ t) \<noteq> [] \<and> (t \\ u) \<^sup>1\\\<^sup>* U' \<noteq> R.null"
                  using T' U' R.con_sym Con_sym1 by simp
                moreover have "(T' \<^sup>*\\\<^sup>1 (u \\ t)) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>1 (t \\ u)) \<noteq> []"
                  using 2 3 ind by simp
                ultimately show "T \<^sup>*\<frown>\<^sup>* U"
                  using T U T' U'
                  by (cases T'; cases U') auto
              qed
            qed
          qed
        qed
      qed
    qed

    lemma Con_sym:
    shows "T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> U \<^sup>*\<frown>\<^sup>* T"
      using Con_sym_ind by blast

    lemma Residx1_as_Resid:
    shows "T \<^sup>*\\\<^sup>1 u = T \<^sup>*\\\<^sup>* [u]"
    proof (induct T)
      show "[] \<^sup>*\\\<^sup>1 u = [] \<^sup>*\\\<^sup>* [u]" by simp
      fix t T
      assume ind: "T \<^sup>*\\\<^sup>1 u = T \<^sup>*\\\<^sup>* [u]"
      show "(t # T) \<^sup>*\\\<^sup>1 u = (t # T) \<^sup>*\\\<^sup>* [u]"
        by (cases T) auto
    qed

    lemma Resid1x_as_Resid':
    shows "t \<^sup>1\\\<^sup>* U = (if [t] \<^sup>*\\\<^sup>* U \<noteq> [] then hd ([t] \<^sup>*\\\<^sup>* U) else R.null)"
    proof (induct U)
      show "t \<^sup>1\\\<^sup>* [] = (if [t] \<^sup>*\\\<^sup>* [] \<noteq> [] then hd ([t] \<^sup>*\\\<^sup>* []) else R.null)" by simp
      fix u U
      assume ind: "t \<^sup>1\\\<^sup>* U = (if [t] \<^sup>*\\\<^sup>* U \<noteq> [] then hd ([t] \<^sup>*\\\<^sup>* U) else R.null)"
      show "t \<^sup>1\\\<^sup>* (u # U) = (if [t] \<^sup>*\\\<^sup>* (u # U) \<noteq> [] then hd ([t] \<^sup>*\\\<^sup>* (u # U)) else R.null)"
        using Resid1x_null
        by (cases U) auto
    qed

    text \<open>
      The following recursive expansion for consistency of paths is an intermediate
      result that is not yet quite in the form we really want.
    \<close>

    lemma Con_rec:
    shows "[t] \<^sup>*\<frown>\<^sup>* [u] \<longleftrightarrow> t \<frown> u"
    and "T \<noteq> [] \<Longrightarrow> t # T \<^sup>*\<frown>\<^sup>* [u] \<longleftrightarrow> t \<frown> u \<and> T \<^sup>*\<frown>\<^sup>* [u \\ t]"
    and "U \<noteq> [] \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* (u # U) \<longleftrightarrow> t \<frown> u \<and> [t \\ u] \<^sup>*\<frown>\<^sup>* U"
    and "\<lbrakk>T \<noteq> []; U \<noteq> []\<rbrakk> \<Longrightarrow>
           t # T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> t \<frown> u \<and> T \<^sup>*\<frown>\<^sup>* [u \\ t] \<and> [t \\ u] \<^sup>*\<frown>\<^sup>* U \<and>
                               T \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t \\ u]"
    proof -
      show "[t] \<^sup>*\<frown>\<^sup>* [u] \<longleftrightarrow> t \<frown> u"
        by simp
      show "T \<noteq> [] \<Longrightarrow> t # T \<^sup>*\<frown>\<^sup>* [u] \<longleftrightarrow> t \<frown> u \<and> T \<^sup>*\<frown>\<^sup>* [u \\ t]"
        using Residx1_as_Resid
        by (cases T) auto
      show "U \<noteq> [] \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* (u # U) \<longleftrightarrow> t \<frown> u \<and> [t \\ u] \<^sup>*\<frown>\<^sup>* U"
        using Resid1x_as_Resid' Con_sym Con_sym1 Resid1x.simps(3) Residx1_as_Resid
        by (cases U) auto
      show "\<lbrakk>T \<noteq> []; U \<noteq> []\<rbrakk> \<Longrightarrow>
            t # T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> t \<frown> u \<and> T \<^sup>*\<frown>\<^sup>* [u \\ t] \<and> [t \\ u] \<^sup>*\<frown>\<^sup>* U \<and>
                               T \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t \\ u]"
        using Residx1_as_Resid Resid1x_as_Resid' Con_sym1 Con_sym R.con_sym
        by (cases T; cases U) auto
    qed

    text \<open>
      This version is a more appealing form of the previously proved fact \<open>Resid1x_as_Resid'\<close>.
    \<close>

    lemma Resid1x_as_Resid:
    assumes "[t] \<^sup>*\\\<^sup>* U \<noteq> []"
    shows "[t] \<^sup>*\\\<^sup>* U = [t \<^sup>1\\\<^sup>* U]"
      using assms Con_rec(2,4)
      apply (cases U; cases "tl U")
         apply auto
      by argo+  (* TODO: Why can auto no longer complete this proof? *)

   text \<open>
     The following is an intermediate version of a recursive expansion for residuation,
     to be improved subsequently.
   \<close>

   lemma Resid_rec:
    shows [simp]: "[t] \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> [t] \<^sup>*\\\<^sup>* [u] = [t \\ u]"
    and "\<lbrakk>T \<noteq> []; t # T \<^sup>*\<frown>\<^sup>* [u]\<rbrakk> \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>* [u] = (t \\ u) # (T \<^sup>*\\\<^sup>* [u \\ t])"
    and "\<lbrakk>U \<noteq> []; Con [t] (u # U)\<rbrakk> \<Longrightarrow> [t] \<^sup>*\\\<^sup>* (u # U) = [t \\ u] \<^sup>*\\\<^sup>* U"
    and "\<lbrakk>T \<noteq> []; U \<noteq> []; Con (t # T) (u # U)\<rbrakk> \<Longrightarrow>
         (t # T) \<^sup>*\\\<^sup>* (u # U) = ([t \\ u] \<^sup>*\\\<^sup>* U) @ ((T \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t \\ u]))"
    proof -
      show "[t] \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Resid [t] [u] = [t \\ u]"
        by (meson Resid.simps(3))
      show "\<lbrakk>T \<noteq> []; t # T \<^sup>*\<frown>\<^sup>* [u]\<rbrakk> \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>* [u] = (t \\ u) # (T \<^sup>*\\\<^sup>* [u \\ t])"
        using Residx1_as_Resid
        by (metis Residx1.simps(3) list.exhaust_sel)
      show 1: "\<lbrakk>U \<noteq> []; [t] \<^sup>*\<frown>\<^sup>* u # U\<rbrakk> \<Longrightarrow> [t] \<^sup>*\\\<^sup>* (u # U) = [t \\ u] \<^sup>*\\\<^sup>* U"
        by (metis Con_rec(3) Resid1x.simps(3) Resid1x_as_Resid list.exhaust)
      show "\<lbrakk>T \<noteq> []; U \<noteq> []; t # T \<^sup>*\<frown>\<^sup>* u # U\<rbrakk> \<Longrightarrow>
             (t # T) \<^sup>*\\\<^sup>* (u # U) = ([t \\ u] \<^sup>*\\\<^sup>* U) @ ((T \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t \\ u]))"
      proof -
        assume T: "T \<noteq> []" and U: "U \<noteq> []" and Con: "Con (t # T) (u # U)"
        have tu: "t \<frown> u"
          using Con Con_rec by metis
        have "(t # T) \<^sup>*\\\<^sup>* (u # U) = ((t \\ u) \<^sup>1\\\<^sup>* U) # ((T \<^sup>*\\\<^sup>1 (u \\ t)) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>1 (t \\ u)))"
          using T U Con tu
          by (cases T; cases U) auto
        also have "... = ([t \\ u] \<^sup>*\\\<^sup>* U) @ ((T \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t \\ u]))"
          using T U Con tu Con_rec(4) Resid1x_as_Resid Residx1_as_Resid by force
        finally show ?thesis by simp
      qed
    qed

    text \<open>
      For consistent paths, residuation is length-preserving.
    \<close>

    lemma length_Resid_ind:
    shows "\<lbrakk>length T + length U \<le> n; T \<^sup>*\<frown>\<^sup>* U\<rbrakk> \<Longrightarrow> length (T \<^sup>*\\\<^sup>* U) = length T"
      apply (induct n arbitrary: T U)
       apply simp
    proof -
      fix n T U
      assume ind: "\<And>T U. \<lbrakk>length T + length U \<le> n; T \<^sup>*\<frown>\<^sup>* U\<rbrakk>
                            \<Longrightarrow> length (T \<^sup>*\\\<^sup>* U) = length T"
      assume Con: "T \<^sup>*\<frown>\<^sup>* U"
      assume len: "length T + length U \<le> Suc n"
      show "length (T \<^sup>*\\\<^sup>* U) = length T"
        using Con len ind Resid1x_as_Resid length_Cons Con_rec(2) Resid_rec(2)
        apply (cases T; cases U)
           apply auto
        apply (cases "tl T = []"; cases "tl U = []")
           apply auto
          apply metis
         apply fastforce
      proof -
        fix t T' u U'
        assume T: "T = t # T'" and U: "U = u # U'"
        assume T': "T' \<noteq> []" and U': "U' \<noteq> []"
        show "length ((t # T') \<^sup>*\\\<^sup>* (u # U')) = Suc (length T')"
          using Con Con_rec(4) Con_sym Resid_rec(4) T T' U U' ind len by auto
      qed
    qed

    lemma length_Resid:
    assumes "T \<^sup>*\<frown>\<^sup>* U"
    shows "length (T \<^sup>*\\\<^sup>* U) = length T"
      using assms length_Resid_ind by auto

    lemma Con_initial_left:
    shows "t # T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* U"
      apply (induct U)
       apply simp
      by (metis Con_rec(1-4))

    lemma Con_initial_right:
    shows "T \<^sup>*\<frown>\<^sup>* u # U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* [u]"
      apply (induct T)
        apply simp
      by (metis Con_rec(1-4))

    lemma Resid_cons_ind:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []; length T + length U \<le> n\<rbrakk> \<Longrightarrow>
             (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> [t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]) \<and>
             (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U) \<and>
             (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) \<and>
             (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U)"
    proof (induct n arbitrary: T U)
      show "\<And>T U. \<lbrakk>T \<noteq> []; U \<noteq> []; length T + length U \<le> 0\<rbrakk> \<Longrightarrow>
                   (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> [t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]) \<and>
                   (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U) \<and>
                   (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) \<and>
                   (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U)"
        by simp
      fix n and T U :: "'a list"
      assume ind: "\<And>T U. \<lbrakk>T \<noteq> []; U \<noteq> []; length T + length U \<le> n\<rbrakk> \<Longrightarrow>
                   (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> [t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]) \<and>
                   (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U) \<and>
                   (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) \<and>
                   (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U)"
      assume T: "T \<noteq> []" and U: "U \<noteq> []"
      assume len: "length T + length U \<le> Suc n"
      show "(\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> [t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]) \<and>
            (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U) \<and>
            (\<forall>t. t # T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) \<and>
            (\<forall>u. T \<^sup>*\<frown>\<^sup>* u # U \<longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U)"
      proof (intro allI conjI iffI impI)
        fix t
        show 1: "t # T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
        proof (cases U)
          show "U = [] \<Longrightarrow> ?thesis"
            using U by simp
          fix u U'
          assume U: "U = u # U'"
          assume Con: "t # T \<^sup>*\<frown>\<^sup>* U"
          show ?thesis
          proof (cases "U' = []")
            show "U' = [] \<Longrightarrow> ?thesis"
              using T U Con R.con_sym Con_rec(2) Resid_rec(2) by auto
            assume U': "U' \<noteq> []"
            have "(t # T) \<^sup>*\\\<^sup>* U = [t \\ u] \<^sup>*\\\<^sup>* U' @ (T \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
              using T U U' Con Resid_rec(4) by fastforce
            also have 1: "... = [t] \<^sup>*\\\<^sup>* U @ (T \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
              using T U U' Con Con_rec(3-4) Resid_rec(3) by auto
            also have "... = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* ((u \\ t) # (U' \<^sup>*\\\<^sup>* [t \\ u]))"
            proof -
              have "T \<^sup>*\\\<^sup>* ((u \\ t) # (U' \<^sup>*\\\<^sup>* [t \\ u])) = (T \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
                using T U U' ind [of T "U' \<^sup>*\\\<^sup>* [t \\ u]"] Con Con_rec(4) Con_sym len length_Resid
                by fastforce
              thus ?thesis by auto
            qed
            also have "... = [t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
              using T U U' 1 Con Con_rec(4) Con_sym1 Residx1_as_Resid
                    Resid1x_as_Resid Resid_rec(2) Con_sym Con_initial_left
              by auto
            finally show ?thesis by simp
          qed
        qed
        show "t # T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* U"
          by (simp add: Con_initial_left)
        show "t # T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
          by (metis "1" Suc_inject T append_Nil2 length_0_conv length_Cons length_Resid)
        show "[t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t] \<Longrightarrow> t # T \<^sup>*\<frown>\<^sup>* U"
        proof (cases U)
          show "\<lbrakk>[t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]; U = []\<rbrakk> \<Longrightarrow> t # T \<^sup>*\<frown>\<^sup>* U"
            using U by simp
          fix u U'
          assume U: "U = u # U'"
          assume Con: "[t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]"
          show "t # T \<^sup>*\<frown>\<^sup>* U"
          proof (cases "U' = []")
            show "U' = [] \<Longrightarrow> ?thesis"
              using T U Con
              by (metis Con_rec(2) Resid.simps(3) R.con_sym)
            assume U': "U' \<noteq> []"
            show ?thesis
            proof -
              have "t \<frown> u"
                using T U U' Con Con_rec(3) by blast
              moreover have "T \<^sup>*\<frown>\<^sup>* [u \\ t]"
                using T U U' Con Con_initial_right Con_sym1 Residx1_as_Resid
                      Resid1x_as_Resid Resid_rec(2)
                by (metis Con_sym)
              moreover have "[t \\ u] \<^sup>*\<frown>\<^sup>* U'"
                using T U U' Con Resid_rec(3) by force
              moreover have "T \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* U' \<^sup>*\\\<^sup>* [t \\ u]"
                by (metis (no_types, opaque_lifting) Con Con_sym Resid_rec(2) Suc_le_mono
                    T U U' add_Suc_right calculation(3) ind len length_Cons length_Resid)
              ultimately show ?thesis
                using T U U' Con_rec(4) by simp
            qed
          qed
        qed
        next
        fix u
        show 1: "T \<^sup>*\<frown>\<^sup>* u # U \<Longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U"
        proof (cases T)
          show 2: "\<lbrakk>T \<^sup>*\<frown>\<^sup>* u # U; T = []\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U"
            using T by simp
          fix t T'
          assume T: "T = t # T'"
          assume Con: "T \<^sup>*\<frown>\<^sup>* u # U"
          show ?thesis
          proof (cases "T' = []")
            show "T' = [] \<Longrightarrow> ?thesis"
              using T U Con Con_rec(3) Resid1x_as_Resid Resid_rec(3) by force
            assume T': "T' \<noteq> []"
            have "T \<^sup>*\\\<^sup>* (u # U) = [t \\ u] \<^sup>*\\\<^sup>* U @ (T' \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t \\ u])"
              using T U T' Con Resid_rec(4) [of T' U t u] by simp
            also have "... = ((t \\ u) # (T' \<^sup>*\\\<^sup>* [u \\ t])) \<^sup>*\\\<^sup>* U"
            proof -
              have "length (T' \<^sup>*\\\<^sup>* [u \\ t]) + length U \<le> n"
                by (metis (no_types, lifting) Con Con_rec(4) One_nat_def Suc_eq_plus1 Suc_leI
                    T T' U add_Suc le_less_trans len length_Resid lessI list.size(4)
                    not_le)
              thus ?thesis
                using ind [of "T' \<^sup>*\\\<^sup>* [u \\ t]" U] Con Con_rec(4) T T' U by auto
            qed
            also have "... = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U"
              using T U T' Con Con_rec(2,4) Resid_rec(2) by force
            finally show ?thesis by simp
          qed
        qed
        show "T \<^sup>*\<frown>\<^sup>* u # U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* [u]"
          using 1 by force
        show "T \<^sup>*\<frown>\<^sup>* u # U \<Longrightarrow> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U"
          using 1 by fastforce
        show "T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* u # U"
        proof (cases T)
          show "\<lbrakk>T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U; T = []\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* u # U"
            using T by simp
          fix t T'
          assume T: "T = t # T'"
          assume Con: "T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U"
          show "Con T (u # U)"
          proof (cases "T' = []")
            show "T' = [] \<Longrightarrow> ?thesis"
              using Con T U Con_rec(1,3) by auto
            assume T': "T' \<noteq> []"
            have "t \<frown> u"
              using Con T U T' Con_rec(2) by blast
            moreover have 2: "T' \<^sup>*\<frown>\<^sup>* [u \\ t]"
              using Con T U T' Con_rec(2) by blast
            moreover have "[t \\ u] \<^sup>*\<frown>\<^sup>* U"
              using Con T U T'
              by (metis Con_initial_left Resid_rec(2))
            moreover have "T' \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t \\ u]"
            proof -
              have 0: "length (U \<^sup>*\\\<^sup>* [t \\ u]) = length U"
                using Con T U T' length_Resid Con_sym calculation(3) by blast
              hence 1: "length T' + length (U \<^sup>*\\\<^sup>* [t \\ u]) \<le> n"
                using Con T U T' len length_Resid Con_sym by simp
              have "length ((T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U) =
                    length ([t \\ u] \<^sup>*\\\<^sup>* U) + length ((T' \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t \\ u]))"
              proof -
                have "(T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U =
                      [t \\ u] \<^sup>*\\\<^sup>* U @ (T' \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t \\ u])"
                  by (metis 0 1 2 Con Resid_rec(2) T T' U ind length_Resid)
                thus ?thesis
                  using Con T U T' length_Resid by simp
              qed
              moreover have "length ((T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U) = length T"
                using Con T U T' length_Resid by metis
              moreover have "length ([t \\ u] \<^sup>*\\\<^sup>* U) \<le> 1"
                using Con T U T' Resid1x_as_Resid
                by (metis One_nat_def length_Cons list.size(3) order_refl zero_le)
              ultimately show ?thesis
                using Con T U T' length_Resid by auto
            qed
            ultimately show "T \<^sup>*\<frown>\<^sup>* u # U"
              using T Con_rec(4) [of T' U t u] by fastforce
          qed
        qed
      qed
    qed

    text \<open>
      The following are the final versions of recursive expansion for consistency
      and residuation on paths.  These are what I really wanted the original definitions
      to look like, but if this is tried, then \<open>Con\<close> and \<open>Resid\<close> end up having to be mutually
      recursive, expressing the definitions so that they are single-valued becomes an issue,
      and proving termination is more problematic.
    \<close>

    lemma Con_cons:
    assumes "T \<noteq> []" and "U \<noteq> []"
    shows "t # T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> [t] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]"
    and "T \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [u] \<and> T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U"
      using assms Resid_cons_ind [of T U] by blast+

    lemma Con_consI [intro, simp]:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []; [t] \<^sup>*\<frown>\<^sup>* U; T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]\<rbrakk> \<Longrightarrow> t # T \<^sup>*\<frown>\<^sup>* U"
    and "\<lbrakk>T \<noteq> []; U \<noteq> []; T \<^sup>*\<frown>\<^sup>* [u]; T \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* U\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* u # U"
      using Con_cons by auto

    (* TODO: Making this a simp currently seems to produce undesirable breakage. *)
    lemma Resid_cons:
    assumes "U \<noteq> []"
    shows "t # T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = ([t] \<^sup>*\\\<^sup>* U) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
    and "T \<^sup>*\<frown>\<^sup>* u # U \<Longrightarrow> T \<^sup>*\\\<^sup>* (u # U) = (T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U"
      using assms Resid_cons_ind [of T U] Resid.simps(1)
      by blast+

    text \<open>
      The following expansion of residuation with respect to the first argument
      is stated in terms of the more primitive cons, rather than list append,
      but as a result \<open>\<^sup>1\\<^sup>*\<close> has to be used.
    \<close>

    (* TODO: Making this a simp seems to produce similar breakage as above. *)
    lemma Resid_cons':
    assumes "T \<noteq> []"
    shows "t # T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> (t # T) \<^sup>*\\\<^sup>* U = (t \<^sup>1\\\<^sup>* U) # (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
      using assms
      by (metis Con_sym Resid.simps(1) Resid1x_as_Resid Resid_cons(1)
          append_Cons append_Nil)

    lemma Srcs_Resid_Arr_single:
    assumes "T \<^sup>*\<frown>\<^sup>* [u]"
    shows "Srcs (T \<^sup>*\\\<^sup>* [u]) = R.targets u"
    proof (cases T)
      show "T = [] \<Longrightarrow> Srcs (T \<^sup>*\\\<^sup>* [u]) = R.targets u"
        using assms by simp
      fix t T'
      assume T: "T = t # T'"
      show "Srcs (T \<^sup>*\\\<^sup>* [u]) = R.targets u"
      proof (cases "T' = []")
        show "T' = [] \<Longrightarrow> ?thesis"
          using assms T R.sources_resid by auto
        assume T': "T' \<noteq> []"
        have "Srcs (T \<^sup>*\\\<^sup>* [u]) = Srcs ((t # T') \<^sup>*\\\<^sup>* [u])"
          using T by simp
        also have "... = Srcs ((t \\ u) # (T' \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* T')))"
          using assms T
          by (metis Resid_rec(2) Srcs.elims T' list.distinct(1) list.sel(1))
        also have "... = R.sources (t \\ u)"
          using Srcs.elims by blast
        also have "... = R.targets u"
          using assms Con_rec(2) T T' R.sources_resid by force
        finally show ?thesis by blast
      qed
    qed

    lemma Srcs_Resid_single_Arr:
    shows "[u] \<^sup>*\<frown>\<^sup>* T \<Longrightarrow> Srcs ([u] \<^sup>*\\\<^sup>* T) = Trgs T"
    proof (induct T arbitrary: u)
      show "\<And>u. [u] \<^sup>*\<frown>\<^sup>* [] \<Longrightarrow> Srcs ([u] \<^sup>*\\\<^sup>* []) = Trgs []"
        by simp
      fix t u T
      assume ind: "\<And>u. [u] \<^sup>*\<frown>\<^sup>* T  \<Longrightarrow> Srcs ([u] \<^sup>*\\\<^sup>* T) = Trgs T"
      assume Con: "[u] \<^sup>*\<frown>\<^sup>* t # T"
      show "Srcs ([u] \<^sup>*\\\<^sup>* (t # T)) = Trgs (t # T)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using Con Srcs_Resid_Arr_single Trgs.simps(2) by presburger
        assume T: "T \<noteq> []"
        have "Srcs ([u] \<^sup>*\\\<^sup>* (t # T)) = Srcs ([u \\ t] \<^sup>*\\\<^sup>* T)"
          using Con Resid_rec(3) T by force
        also have "... = Trgs T"
          using Con ind Con_rec(3) T by auto
        also have "... = Trgs (t # T)"
          by (metis T Trgs.elims Trgs.simps(3))
        finally show ?thesis by simp
      qed
    qed

    lemma Trgs_Resid_sym_Arr_single:
    shows "T \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Trgs (T \<^sup>*\\\<^sup>* [u]) = Trgs ([u] \<^sup>*\\\<^sup>* T)"
    proof (induct T arbitrary: u)
      show "\<And>u. [] \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Trgs ([] \<^sup>*\\\<^sup>* [u]) = Trgs ([u] \<^sup>*\\\<^sup>* [])"
        by simp
      fix t u T
      assume ind: "\<And>u. T \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Trgs (T \<^sup>*\\\<^sup>* [u]) = Trgs ([u] \<^sup>*\\\<^sup>* T)"
      assume Con: "t # T \<^sup>*\<frown>\<^sup>* [u]"
      show "Trgs ((t # T) \<^sup>*\\\<^sup>* [u]) = Trgs ([u] \<^sup>*\\\<^sup>* (t # T))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using R.targets_resid_sym
          by (simp add: R.con_sym)
        assume T: "T \<noteq> []"
        show ?thesis
        proof -
          have "Trgs ((t # T) \<^sup>*\\\<^sup>* [u]) = Trgs ((t \\ u) # (T \<^sup>*\\\<^sup>* [u \\ t]))"
            using Con Resid_rec(2) T by auto
          also have "... = Trgs (T \<^sup>*\\\<^sup>* [u \\ t])"
            using T Con Con_rec(2) [of T t u]
            by (metis Trgs.elims Trgs.simps(3))
          also have "... = Trgs ([u \\ t] \<^sup>*\\\<^sup>* T)"
            using T Con ind Con_sym by metis
          also have "... = Trgs ([u] \<^sup>*\\\<^sup>* (t # T))"
            using T Con Con_sym Resid_rec(3) by presburger
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma Srcs_Resid [simp]:
    shows "T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> Srcs (T \<^sup>*\\\<^sup>* U) = Trgs U"
    proof (induct U arbitrary: T)
      show "\<And>T. T \<^sup>*\<frown>\<^sup>* [] \<Longrightarrow> Srcs (T \<^sup>*\\\<^sup>* []) = Trgs []"
        using Con_sym Resid.simps(1) by blast
      fix u U T
      assume ind: "\<And>T. T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> Srcs (T \<^sup>*\\\<^sup>* U) = Trgs U"
      assume Con: "T \<^sup>*\<frown>\<^sup>* u # U"
      show "Srcs (T \<^sup>*\\\<^sup>* (u # U)) = Trgs (u # U)"
        by (metis Con Resid_cons(2) Srcs_Resid_Arr_single Trgs.simps(2-3) ind
            list.exhaust_sel)
    qed

    lemma Trgs_Resid_sym [simp]:
    shows "T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> Trgs (T \<^sup>*\\\<^sup>* U) = Trgs (U \<^sup>*\\\<^sup>* T)"
    proof (induct U arbitrary: T)
      show "\<And>T. T \<^sup>*\<frown>\<^sup>* [] \<Longrightarrow> Trgs (T \<^sup>*\\\<^sup>* []) = Trgs ([] \<^sup>*\\\<^sup>* T)"
        by (meson Con_sym Resid.simps(1))
      fix u U T
      assume ind: "\<And>T. T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> Trgs (T \<^sup>*\\\<^sup>* U) = Trgs (U \<^sup>*\\\<^sup>* T)"
      assume Con: "T \<^sup>*\<frown>\<^sup>* u # U"
      show "Trgs (T \<^sup>*\\\<^sup>* (u # U)) = Trgs ((u # U) \<^sup>*\\\<^sup>* T)"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using Con Trgs_Resid_sym_Arr_single by blast
        assume U: "U \<noteq> []"
        show ?thesis
        proof -
          have "Trgs (T \<^sup>*\\\<^sup>* (u # U)) = Trgs ((T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U)"
            using U by (metis Con Resid_cons(2))
          also have "... = Trgs (U \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* [u]))"
            using U Con by (metis Con_sym ind)
          also have "... = Trgs ((u # U) \<^sup>*\\\<^sup>* T)"
            by (metis (no_types, opaque_lifting) Con_cons(1) Con_sym Resid.simps(1) Resid_cons'
                Trgs.simps(3) U neq_Nil_conv)
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma img_Resid_Srcs:
    shows "Arr T \<Longrightarrow> (\<lambda>a. [a] \<^sup>*\\\<^sup>* T) ` Srcs T \<subseteq> (\<lambda>b. [b]) ` Trgs T"
    proof (induct T)
      show "Arr [] \<Longrightarrow> (\<lambda>a. [a] \<^sup>*\\\<^sup>* []) ` Srcs [] \<subseteq> (\<lambda>b. [b]) ` Trgs []"
        by simp
      fix t :: 'a and T :: "'a list"
      assume tT: "Arr (t # T)"
      assume ind: "Arr T \<Longrightarrow> (\<lambda>a. [a] \<^sup>*\\\<^sup>* T) ` Srcs T \<subseteq> (\<lambda>b. [b]) ` Trgs T"
      show "(\<lambda>a. [a] \<^sup>*\\\<^sup>* (t # T)) ` Srcs (t # T) \<subseteq> (\<lambda>b. [b]) ` Trgs (t # T)"
      proof
        fix B
        assume B: "B \<in> (\<lambda>a. [a] \<^sup>*\\\<^sup>* (t # T)) ` Srcs (t # T)"
        show "B \<in> (\<lambda>b. [b]) ` Trgs (t # T)"
        proof (cases "T = []")
          assume T: "T = []"
          obtain a where a: "a \<in> R.sources t \<and> [a \\ t] = B"
            by (metis (no_types, lifting) B R.composite_of_source_arr R.con_prfx_composite_of(1)
                Resid_rec(1) Srcs.simps(2) T Arr.simps(2) Con_rec(1) imageE tT)
          have "a \\ t \<in> Trgs (t # T)"
            using tT T a
            by (simp add: R.resid_source_in_targets)
          thus ?thesis
            using B a image_iff by fastforce
          next
          assume T: "T \<noteq> []"
          obtain a where a: "a \<in> R.sources t \<and> [a] \<^sup>*\\\<^sup>* (t # T) = B"
            using tT T B Srcs.elims by blast
          have "[a \\ t] \<^sup>*\\\<^sup>* T = B"
            using tT T B a
            by (metis Con_rec(3) R.arrI R.resid_source_in_targets R.targets_are_cong
                Resid_rec(3) R.arr_resid_iff_con R.ide_implies_arr)
          moreover have "a \\ t \<in> Srcs T"
            using a tT
            by (metis Arr.simps(3) R.resid_source_in_targets T neq_Nil_conv subsetD)
          ultimately show ?thesis
            using T tT ind
            by (metis Trgs.simps(3) Arr.simps(3) image_iff list.exhaust_sel subsetD)
        qed
      qed
    qed

    lemma Resid_Arr_Src:
    shows "\<lbrakk>Arr T; a \<in> Srcs T\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* [a] = T"
    proof (induct T arbitrary: a)
      show "\<And>a. \<lbrakk>Arr []; a \<in> Srcs []\<rbrakk> \<Longrightarrow> [] \<^sup>*\\\<^sup>* [a] = []"
        by simp
      fix a t T
      assume ind: "\<And>a. \<lbrakk>Arr T; a \<in> Srcs T\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* [a] = T"
      assume Arr: "Arr (t # T)"
      assume a: "a \<in> Srcs (t # T)"
      show "(t # T) \<^sup>*\\\<^sup>* [a] = t # T"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using a R.resid_arr_ide R.sources_def by auto
        assume T: "T \<noteq> []"
        show "(t # T) \<^sup>*\\\<^sup>* [a] = t # T"
        proof -
          have 1: "R.arr t \<and> Arr T \<and> R.targets t \<subseteq> Srcs T"
            using Arr T
            by (metis Arr.elims(2) list.sel(1) list.sel(3))
          have 2: "t # T \<^sup>*\<frown>\<^sup>* [a]"
            using T a Arr Con_rec(2)
            by (metis (no_types, lifting) img_Resid_Srcs Con_sym imageE image_subset_iff
                list.distinct(1))
          have "(t # T) \<^sup>*\\\<^sup>* [a] = (t \\ a) # (T \<^sup>*\\\<^sup>* [a \\ t])"
            using 2 T Resid_rec(2) by simp
          moreover have "t \\ a = t"
            using Arr a R.sources_def
            by (metis "2" CollectD Con_rec(2) T Srcs_are_ide in_mono R.resid_arr_ide)
          moreover have "T \<^sup>*\\\<^sup>* [a \\ t] = T"
            by (metis "1" "2" R.in_sourcesI R.resid_source_in_targets Srcs_are_ide T a
                      Con_rec(2) in_mono ind mem_Collect_eq)
          ultimately show ?thesis by simp
        qed
      qed
    qed

    lemma Con_single_ide_ind:
    shows "R.ide a \<Longrightarrow> [a] \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> a \<in> Srcs T"
    proof (induct T arbitrary: a)
      show "\<And>a. [a] \<^sup>*\<frown>\<^sup>* [] \<longleftrightarrow> Arr [] \<and> a \<in> Srcs []"
        by simp
      fix a t T
      assume ind: "\<And>a. R.ide a \<Longrightarrow> [a] \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> a \<in> Srcs T"
      assume a: "R.ide a"
      show "[a] \<^sup>*\<frown>\<^sup>* (t # T) \<longleftrightarrow> Arr (t # T) \<and> a \<in> Srcs (t # T)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using a Con_sym
          by (metis Arr.simps(2) Resid_Arr_Src Srcs.simps(2) R.arr_iff_has_source
              Con_rec(1) empty_iff R.in_sourcesI list.distinct(1))
        assume T: "T \<noteq> []"
        have 1: "[a] \<^sup>*\<frown>\<^sup>* (t # T) \<longleftrightarrow> a \<frown> t \<and> [a \\ t] \<^sup>*\<frown>\<^sup>* T"
          using a T Con_cons(2) [of "[a]" T t] by simp
        also have 2: "... \<longleftrightarrow> a \<frown> t \<and> Arr T \<and> a \\ t \<in> Srcs T"
          using a T ind R.resid_ide_arr by blast
        also have "... \<longleftrightarrow> Arr (t # T) \<and> a \<in> Srcs (t # T)"
          using a T Con_sym R.con_sym Resid_Arr_Src R.con_implies_arr Srcs_are_ide
          apply (cases T)
           apply simp
          by (metis Arr.simps(3) R.resid_arr_ide R.targets_resid_sym Srcs.simps(3)
              Srcs_Resid_Arr_single calculation dual_order.eq_iff list.distinct(1)
              R.in_sourcesI)
        finally show ?thesis by simp
      qed
    qed

    lemma Con_single_ide_iff:
    assumes "R.ide a"
    shows "[a] \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> a \<in> Srcs T"
      using assms Con_single_ide_ind by simp

    lemma Con_single_ideI [intro]:
    assumes "R.ide a" and "Arr T" and "a \<in> Srcs T"
    shows "[a] \<^sup>*\<frown>\<^sup>* T" and "T \<^sup>*\<frown>\<^sup>* [a]"
      using assms Con_single_ide_iff Con_sym by auto

    lemma Resid_single_ide:
    assumes "R.ide a" and "[a] \<^sup>*\<frown>\<^sup>* T"
    shows "[a] \<^sup>*\\\<^sup>* T \<in> (\<lambda>b. [b]) ` Trgs T" and [simp]: "T \<^sup>*\\\<^sup>* [a] = T"
      using assms Con_single_ide_ind img_Resid_Srcs Resid_Arr_Src Con_sym
      by blast+

    lemma Resid_Arr_Ide_ind:
    shows "\<lbrakk>Ide A; T \<^sup>*\<frown>\<^sup>* A\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* A = T"
    proof (induct A)
      show "\<lbrakk>Ide []; T \<^sup>*\<frown>\<^sup>* []\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* [] = T"
        by simp
      fix a A
      assume ind: "\<lbrakk>Ide A; T \<^sup>*\<frown>\<^sup>* A\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* A = T"
      assume Ide: "Ide (a # A)"
      assume Con: "T \<^sup>*\<frown>\<^sup>* a # A"
      show "T \<^sup>*\\\<^sup>* (a # A) = T"
        by (metis (no_types, lifting) Con Con_initial_left Con_sym Ide Ide.elims(2)
            Resid_cons(2) Resid_single_ide(2) ind list.inject)
    qed

    lemma Resid_Ide_Arr_ind:
    shows "\<lbrakk>Ide A; A \<^sup>*\<frown>\<^sup>* T\<rbrakk> \<Longrightarrow> Ide (A \<^sup>*\\\<^sup>* T)"
    proof (induct A)
      show "\<lbrakk>Ide []; [] \<^sup>*\<frown>\<^sup>* T\<rbrakk> \<Longrightarrow> Ide ([] \<^sup>*\\\<^sup>* T)"
        by simp
      fix a A
      assume ind: "\<lbrakk>Ide A; A \<^sup>*\<frown>\<^sup>* T\<rbrakk> \<Longrightarrow> Ide (A \<^sup>*\\\<^sup>* T)"
      assume Ide: "Ide (a # A)"
      assume Con: "a # A \<^sup>*\<frown>\<^sup>* T"
      have T: "Arr T"
        using Con Ide Con_single_ide_ind Con_initial_left Ide.elims(2)
        by blast
      show "Ide ((a # A) \<^sup>*\\\<^sup>* T)"
      proof (cases "A = []")
        show "A = [] \<Longrightarrow> ?thesis"
          by (metis Con Con_sym1 Ide Ide.simps(2) Resid1x_as_Resid Resid1x_ide
              Residx1_as_Resid Con_sym)
        assume A: "A \<noteq> []"
        show ?thesis
        proof -
          have "Ide ([a] \<^sup>*\\\<^sup>* T)"
            by (metis Con Con_initial_left Con_sym Con_sym1 Ide Ide.simps(3)
                Resid1x_as_Resid Residx1_as_Resid Ide.simps(2) Resid1x_ide
                list.exhaust_sel)
          moreover have "Trgs ([a] \<^sup>*\\\<^sup>* T) \<subseteq> Srcs (A \<^sup>*\\\<^sup>* T)"
            using A T Ide Con
            by (metis (no_types, lifting) Con_sym Ide.elims(2) Ide.simps(2) Resid_Arr_Ide_ind
                Srcs_Resid Trgs_Resid_sym Con_cons(2) dual_order.eq_iff list.inject)
          moreover have "Ide (A \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* [a]))"
            by (metis A Con Con_cons(1) Con_sym Ide Ide.simps(3) Resid_Arr_Ide_ind
                Resid_single_ide(2) ind list.exhaust_sel)
          moreover have "Ide ((a # A) \<^sup>*\\\<^sup>* T) \<longleftrightarrow> 
                         Ide ([a] \<^sup>*\\\<^sup>* T) \<and> Ide (A \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* [a])) \<and>
                           Trgs ([a] \<^sup>*\\\<^sup>* T) \<subseteq> Srcs (A \<^sup>*\\\<^sup>* T)"
            using calculation(1-3)
            by (metis Arr.simps(1) Con Ide Ide.simps(3) Resid1x_as_Resid Resid_cons'
               Trgs.simps(2) Con_single_ide_iff Ide.simps(2) Ide_implies_Arr Resid_Arr_Src
                list.exhaust_sel)
          ultimately show ?thesis by blast
        qed
      qed
    qed

    lemma Resid_Ide:
    assumes "Ide A" and "A \<^sup>*\<frown>\<^sup>* T"
    shows "T \<^sup>*\\\<^sup>* A = T" and "Ide (A \<^sup>*\\\<^sup>* T)"
      using assms Resid_Ide_Arr_ind Resid_Arr_Ide_ind Con_sym by auto

    lemma Con_Ide_iff:
    shows "Ide A \<Longrightarrow> A \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> Srcs T = Srcs A"
    proof (induct A)
      show "Ide [] \<Longrightarrow> [] \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> Srcs T = Srcs []"
        by simp
      fix a A
      assume ind: "Ide A \<Longrightarrow> A \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> Srcs T = Srcs A"
      assume Ide: "Ide (a # A)"
      show "a # A \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> Srcs T = Srcs (a # A)"
      proof (cases "A = []")
        show "A = [] \<Longrightarrow> ?thesis"
          using Con_single_ide_ind Ide
          by (metis Arr.simps(2) Con_sym Ide.simps(2) Ide_implies_Arr R.arrE
                    Resid_Arr_Src Srcs.simps(2) Srcs_Resid R.in_sourcesI)
        assume A: "A \<noteq> []"
        have "a # A \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> [a] \<^sup>*\<frown>\<^sup>* T \<and> A \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* [a]"
          using A Ide Con_cons(1) [of A T a] by fastforce
        also have 1: "... \<longleftrightarrow> Arr T \<and> a \<in> Srcs T"
          by (metis A Arr_has_Src Con_single_ide_ind Ide Ide.elims(2) Resid_Arr_Src
              Srcs_Resid_Arr_single Con_sym Srcs_eqI ind inf.absorb_iff2 list.inject)
        also have "... \<longleftrightarrow> Arr T \<and> Srcs T = Srcs (a # A)"
          by (metis A 1 Con_sym Ide Ide.simps(3) R.ideE
              R.sources_resid Resid_Arr_Src Srcs.simps(3) Srcs_Resid_Arr_single
              list.exhaust_sel R.in_sourcesI)
        finally show "a # A \<^sup>*\<frown>\<^sup>* T \<longleftrightarrow> Arr T \<and> Srcs T = Srcs (a # A)"
          by blast
      qed
    qed

    lemma Con_IdeI:
    assumes "Ide A" and "Arr T" and "Srcs T = Srcs A"
    shows "A \<^sup>*\<frown>\<^sup>* T" and "T \<^sup>*\<frown>\<^sup>* A"
      using assms Con_Ide_iff Con_sym by auto

    lemma Con_Arr_self:
    shows "Arr T \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* T"
    proof (induct T)
      show "Arr [] \<Longrightarrow> [] \<^sup>*\<frown>\<^sup>* []"
        by simp
      fix t T
      assume ind: "Arr T \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* T"
      assume Arr: "Arr (t # T)"
      show "t # T \<^sup>*\<frown>\<^sup>* t # T"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using Arr R.arrE by simp
        assume T: "T \<noteq> []"
        have "t \<frown> t \<and> T \<^sup>*\<frown>\<^sup>* [t \\ t] \<and> [t \\ t] \<^sup>*\<frown>\<^sup>* T \<and> T \<^sup>*\\\<^sup>* [t \\ t] \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* [t \\ t]"
        proof -
          have "t \<frown> t"
            using Arr Arr.elims(1) by auto
          moreover have "T \<^sup>*\<frown>\<^sup>* [t \\ t]"
          proof -
            have "Ide [t \\ t]"
              by (simp add: R.arr_def R.prfx_reflexive calculation)
            moreover have "Srcs [t \\ t] = Srcs T"
              by (metis Arr Arr.simps(2) Arr_has_Trg R.arrE R.sources_resid Srcs.simps(2)
                  Srcs_eqI T Trgs.simps(2) Arr.simps(3) inf.absorb_iff2 list.exhaust)
            ultimately show ?thesis
              by (metis Arr Con_sym T Arr.simps(3) Con_Ide_iff neq_Nil_conv)
          qed
          ultimately show ?thesis
            by (metis Con_single_ide_ind Con_sym R.prfx_reflexive
                Resid_single_ide(2) ind R.con_implies_arr(1))
        qed
        thus ?thesis
          using Con_rec(4) [of T T t t] by force
      qed
    qed

    lemma Resid_Arr_self:
    shows "Arr T \<Longrightarrow> Ide (T \<^sup>*\\\<^sup>* T)"
    proof (induct T)
      show "Arr [] \<Longrightarrow> Ide ([] \<^sup>*\\\<^sup>* [])"
        by simp
      fix t T
      assume ind: "Arr T \<Longrightarrow> Ide (T \<^sup>*\\\<^sup>* T)"
      assume Arr: "Arr (t # T)"
      show "Ide ((t # T) \<^sup>*\\\<^sup>* (t # T))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using Arr R.prfx_reflexive by auto
        assume T: "T \<noteq> []"
        have 1: "(t # T) \<^sup>*\\\<^sup>* (t # T) = t \<^sup>1\\\<^sup>* (t # T) # T \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* [t])"
          using Arr T Resid_cons' [of T t "t # T"] Con_Arr_self by presburger
        also have "... = (t \\ t) \<^sup>1\\\<^sup>* T # T \<^sup>*\\\<^sup>* (t \<^sup>1\\\<^sup>* [t] # T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t]))"
          using Arr T Resid_cons' [of T t "[t]"]
          by (metis Con_initial_right Resid1x.simps(3) calculation neq_Nil_conv)
        also have "... = (t \\ t) \<^sup>1\\\<^sup>* T # (T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t]))"
          by (metis 1 Resid1x.simps(2) Residx1.simps(2) Residx1_as_Resid T calculation
              Con_cons(1) Con_rec(4) Resid_cons(2) list.distinct(1) list.inject)
        finally have 2: "(t # T) \<^sup>*\\\<^sup>* (t # T) =
                         (t \\ t) \<^sup>1\\\<^sup>* T # (T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t]))"
          by blast
        moreover have "Ide ..."
        proof -
          have "R.ide ((t \\ t) \<^sup>1\\\<^sup>* T)"
            using Arr T
            by (metis Con_initial_right Con_rec(2) Con_sym1 R.con_implies_arr(1)
                Resid1x_ide Con_Arr_self Residx1_as_Resid R.prfx_reflexive)
          moreover have "Ide ((T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t])))"
            using Arr T
            by (metis Con_Arr_self Con_rec(4) Resid_single_ide(2) Con_single_ide_ind
                Resid.simps(3) ind R.prfx_reflexive R.con_implies_arr(2))
          moreover have "R.targets ((t \\ t) \<^sup>1\\\<^sup>* T) \<subseteq>
                           Srcs ((T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t])))"
            by (metis (no_types, lifting) 1 2 Con_cons(1) Resid1x_as_Resid T Trgs.simps(2)
                Trgs_Resid_sym Srcs_Resid dual_order.eq_iff list.discI list.inject)
          ultimately show ?thesis
            using Arr T
            by (metis Ide.simps(1,3) list.exhaust_sel)
        qed
        ultimately show ?thesis by auto
      qed
    qed

    lemma Con_imp_eq_Srcs:
    assumes "T \<^sup>*\<frown>\<^sup>* U"
    shows "Srcs T = Srcs U"
    proof (cases T)
      show "T = [] \<Longrightarrow> ?thesis"
        using assms by simp
      fix t T'
      assume T: "T = t # T'"
      show "Srcs T = Srcs U"
      proof (cases U)
        show "U = [] \<Longrightarrow> ?thesis"
          using assms T by simp
        fix u U'
        assume U: "U = u # U'"
        show "Srcs T = Srcs U"
          by (metis Con_initial_right Con_rec(1) Con_sym R.con_imp_common_source
              Srcs.simps(2-3) Srcs_eqI T Trgs.cases U assms)
      qed
    qed

    lemma Arr_iff_Con_self:
    shows "Arr T \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* T"
    proof (induct T)
      show "Arr [] \<longleftrightarrow> [] \<^sup>*\<frown>\<^sup>* []"
        by simp
      fix t T
      assume ind: "Arr T \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* T"
      show "Arr (t # T) \<longleftrightarrow> t # T \<^sup>*\<frown>\<^sup>* t # T"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          by auto
        assume T: "T \<noteq> []"
        show ?thesis
        proof
          show "Arr (t # T) \<Longrightarrow> t # T \<^sup>*\<frown>\<^sup>* t # T"
            using Con_Arr_self by simp
          show "t # T \<^sup>*\<frown>\<^sup>* t # T \<Longrightarrow> Arr (t # T)"
          proof -
            assume Con: "t # T \<^sup>*\<frown>\<^sup>* t # T"
            have "R.arr t"
              using T Con Con_rec(4) [of T T t t] by blast
            moreover have "Arr T"
              using T Con Con_rec(4) [of T T t t] ind R.arrI
              by (meson R.prfx_reflexive Con_single_ide_ind)
            moreover have "R.targets t \<subseteq> Srcs T"
              using T Con
              by (metis Con_cons(2) Con_imp_eq_Srcs Trgs.simps(2)
                  Srcs_Resid list.distinct(1) subsetI)
            ultimately show ?thesis
              by (cases T) auto
          qed
        qed
      qed
    qed

    lemma Arr_Resid_single:
    shows "T \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Arr (T \<^sup>*\\\<^sup>* [u])"
    proof (induct T arbitrary: u)
      show "\<And>u. [] \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Arr ([] \<^sup>*\\\<^sup>* [u])"
        by simp
      fix t u T
      assume ind: "\<And>u. T \<^sup>*\<frown>\<^sup>* [u] \<Longrightarrow> Arr (T \<^sup>*\\\<^sup>* [u])"
      assume Con: "t # T \<^sup>*\<frown>\<^sup>* [u]"
      show "Arr ((t # T) \<^sup>*\\\<^sup>* [u])"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using Con Arr_iff_Con_self R.con_imp_arr_resid Con_rec(1) by fastforce
        assume T: "T \<noteq> []"
        have "Arr ((t # T) \<^sup>*\\\<^sup>* [u]) \<longleftrightarrow> Arr ((t \\ u) # (T \<^sup>*\\\<^sup>* [u \\ t]))"
          using Con T Resid_rec(2) by auto
        also have "... \<longleftrightarrow> R.arr (t \\ u) \<and> Arr (T \<^sup>*\\\<^sup>* [u \\ t]) \<and>
                           R.targets (t \\ u) \<subseteq> Srcs (T \<^sup>*\\\<^sup>* [u \\ t])"
          using Con T
          by (metis Arr.simps(3) Con_rec(2) neq_Nil_conv)
        also have "... \<longleftrightarrow> R.con t u \<and> Arr (T \<^sup>*\\\<^sup>* [u \\ t])"
          using Con T
          by (metis Srcs_Resid_Arr_single Con_rec(2) R.arr_resid_iff_con subsetI
              R.targets_resid_sym)
        also have "... \<longleftrightarrow> True"
          using Con ind T Con_rec(2) by blast
        finally show ?thesis by auto
      qed
    qed

    lemma Con_imp_Arr_Resid:
    shows "T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> Arr (T \<^sup>*\\\<^sup>* U)"
    proof (induct U arbitrary: T)
      show "\<And>T. T \<^sup>*\<frown>\<^sup>* [] \<Longrightarrow> Arr (T \<^sup>*\\\<^sup>* [])"
        by (meson Con_sym Resid.simps(1))
      fix u U T
      assume ind: "\<And>T. T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> Arr (T \<^sup>*\\\<^sup>* U)"
      assume Con: "T \<^sup>*\<frown>\<^sup>* u # U"
      show "Arr (T \<^sup>*\\\<^sup>* (u # U))"
        by (metis Arr_Resid_single Con Resid_cons(2) ind)
    qed

    lemma Cube_ind:
    shows "\<lbrakk>T \<^sup>*\<frown>\<^sup>* U; V \<^sup>*\<frown>\<^sup>* T; length T + length U + length V \<le> n\<rbrakk> \<Longrightarrow>
             (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U) \<and>
             (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longrightarrow>
               (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U))"
    proof (induct n arbitrary: T U V)
      show "\<And>T U V. \<lbrakk>T \<^sup>*\<frown>\<^sup>* U; V \<^sup>*\<frown>\<^sup>* T; length T + length U + length V \<le> 0\<rbrakk> \<Longrightarrow>
                       (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U) \<and>
                       (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longrightarrow>
                         (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U))"
        by simp
      fix n and T U V :: "'a list"
      assume Con_TU: "T \<^sup>*\<frown>\<^sup>* U" and Con_VT: "V \<^sup>*\<frown>\<^sup>* T"
      have T: "T \<noteq> []"
        using Con_TU by auto
      have U: "U \<noteq> []"
        using Con_TU Con_sym Resid.simps(1) by blast
      have V: "V \<noteq> []"
        using Con_VT by auto
      assume len: "length T + length U + length V \<le> Suc n"
      assume ind: "\<And>T U V. \<lbrakk>T \<^sup>*\<frown>\<^sup>* U; V \<^sup>*\<frown>\<^sup>* T; length T + length U + length V \<le> n\<rbrakk> \<Longrightarrow>
                            (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U) \<and>
                            (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longrightarrow>
                              (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U))"
      show "(V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U) \<and>
            (V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longrightarrow> (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U))"
      proof (cases V)
        show "V = [] \<Longrightarrow> ?thesis"
          using V by simp
        (*
         * TODO: I haven't found a better way to do this than just consider each combination
         * of T U V being a singleton.
         *)
        fix v V'
        assume V: "V = v # V'"
        show ?thesis
        proof (cases U)
          show "U = [] \<Longrightarrow> ?thesis"
            using U by simp
          fix u U'
          assume U: "U = u # U'"
          show ?thesis
          proof (cases T)
            show "T = [] \<Longrightarrow> ?thesis"
              using T by simp
            fix t T'
            assume T: "T = t # T'"
            show ?thesis
            proof (cases "V' = []", cases "U' = []", cases "T' = []")
              show "\<lbrakk>V' = []; U' = []; T' = []\<rbrakk> \<Longrightarrow> ?thesis"
                using T U V R.cube Con_TU Resid.simps(2-3) R.arr_resid_iff_con
                      R.con_implies_arr Con_sym
                by metis
              assume T': "T' \<noteq> []" and V': "V' = []" and U': "U' = []"
              have 1: "U \<^sup>*\<frown>\<^sup>* [t]"
                using T Con_TU Con_cons(2) Con_sym Resid.simps(2) by metis
              have 2: "V \<^sup>*\<frown>\<^sup>* [t]"
                using V Con_VT Con_initial_right T by blast
              show ?thesis
              proof (intro conjI impI)
                have 3: "length [t] + length U + length V \<le> n"
                  using T T' le_Suc_eq len by fastforce
                show *: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                proof -
                  have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T'"
                    using Con_TU Con_VT Con_sym Resid_cons(2) T T' by force
                  also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t] \<and>
                                     (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                  proof (intro iffI conjI)
                    show "(V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<Longrightarrow> V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]"
                      using T U V T' U' V' 1 ind [of "T'"] len Con_TU Con_rec(2) Resid_rec(1)
                            Resid.simps(1) length_Cons Suc_le_mono add_Suc
                      by (metis (no_types))
                    show "(V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<Longrightarrow>
                          (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                      using T U V T' U' V'
                      by (metis Con_sym Resid.simps(1) Resid_rec(1) Suc_le_mono ind len
                          length_Cons list.size(3-4))
                    show "V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t] \<and>
                          (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<Longrightarrow>
                            (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T'"
                      using T U V T' U' V' 1 ind len Con_TU Con_VT Con_rec(1-3)
                      by (metis (no_types, lifting) One_nat_def Resid_rec(1) Suc_le_mono
                          add.commute list.size(3) list.size(4) plus_1_eq_Suc)
                  qed
                  also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                    by (metis 2 3 Con_sym ind Resid.simps(1))
                  also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                    using Con_rec(2) [of T' t]
                    by (metis (no_types, lifting) "1" Con_TU Con_cons(2) Resid.simps(1)
                        Resid.simps(3) Resid_rec(2) T T' U U')
                  finally show ?thesis by simp
                qed
                assume Con: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T"
                show "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                proof -
                  have "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* ((U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T')"
                    using Con_TU Con_VT Con_sym Resid_cons(2) T T' by force
                  also have "... = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
                    using T U V T' U' V' 1 Con ind [of T' "Resid U [t]" "Resid V [t]"]
                    by (metis One_nat_def add.commute calculation len length_0_conv length_Resid
                        list.size(4) nat_add_left_cancel_le Con_sym plus_1_eq_Suc)
                  also have "... = ((V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
                    by (metis "1" "2" "3" Con_sym ind)
                  also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                    using T U T' U' Con *
                    by (metis Con_sym Resid_rec(1-2) Resid.simps(1) Resid_cons(2))
                  finally show ?thesis by simp
                qed
              qed
              next
              assume U': "U' \<noteq> []" and V': "V' = []"
              show ?thesis
              proof (intro conjI impI)
                show *: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                proof (cases "T' = []")
                  assume T': "T' = []"
                  show ?thesis
                  proof -
                    have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* (u \\ t) # (U' \<^sup>*\\\<^sup>* [t \\ u])"
                      using Con_TU Con_sym Resid_rec(2) T T' U U' by auto
                    also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* U' \<^sup>*\\\<^sup>* [t \\ u]"
                      by (metis Con_TU Con_cons(2) Con_rec(3) Con_sym Resid.simps(1) T U U')
                    also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u] \<^sup>*\<frown>\<^sup>* U' \<^sup>*\\\<^sup>* [t \\ u]"
                      using T U V V' R.cube_ax
                      apply simp
                      by (metis R.con_implies_arr(1) R.not_arr_null R.con_def)
                    also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U' \<^sup>*\<frown>\<^sup>* [t \\ u] \<^sup>*\\\<^sup>* U'"
                    proof -
                      have "length [t \\ u] + length U' + length (V \<^sup>*\\\<^sup>* [u]) \<le> n"
                        using T U V V' len by force
                      thus ?thesis
                        by (metis Con_sym Resid.simps(1) add.commute ind)
                    qed
                    also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                      by (metis Con_TU Resid_cons(2) Resid_rec(3) T T' U U' Con_cons(2)
                          length_Resid length_0_conv)
                    finally show ?thesis by simp
                  qed
                  next
                  assume T': "T' \<noteq> []"
                  show ?thesis
                  proof -
                    have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* ((U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T')"
                      using Con_TU Con_VT Con_sym Resid_cons(2) T T' by force
                    also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                    proof -
                      have "length T' + length (U \<^sup>*\\\<^sup>* [t]) + length (V \<^sup>*\\\<^sup>* [t]) \<le> n"
                        by (metis (no_types, lifting) Con_TU Con_VT Con_initial_right Con_sym
                            One_nat_def Suc_eq_plus1 T ab_semigroup_add_class.add_ac(1)
                            add_le_imp_le_left len length_Resid list.size(4) plus_1_eq_Suc)
                      thus ?thesis
                        by (metis Con_TU Con_VT Con_cons(1) Con_cons(2) T T' U V ind list.discI)
                    qed
                    also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                    proof -
                      have "length [t] + length U + length V \<le> n"
                        using T T' le_Suc_eq len by fastforce
                      thus ?thesis
                        by (metis Con_TU Con_VT Con_initial_left Con_initial_right T ind)
                    qed
                    also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                      by (metis Con_cons(2) Con_sym Resid.simps(1) Resid1x_as_Resid
                          Residx1_as_Resid Resid_cons' T T')
                    finally show ?thesis by blast
                  qed
                qed
                show "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<Longrightarrow>
                        (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                proof -
                  assume Con: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T"
                  show ?thesis
                  proof (cases "T' = []")
                    assume T': "T' = []"
                    show ?thesis
                    proof -
                      have 1: "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) =
                               (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* ((u \\ t) # (U'\<^sup>*\\\<^sup>* [t \\ u]))"
                        using Con_TU Con_sym Resid_rec(2) T T' U U' by force
                      also have "... = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
                        by (metis Con Con_TU Con_rec(2) Con_sym Resid_cons(2) T T' U U'
                            calculation)
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
                        by (metis "*" Con Con_rec(3) R.cube Resid.simps(1,3) T T' U V V'
                            calculation R.conI R.conE)
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t \\ u] \<^sup>*\\\<^sup>* U')"
                      proof -
                        have "length [t \\ u] + length (U' \<^sup>*\\\<^sup>* [t \\ u]) + length (V \<^sup>*\\\<^sup>* [u]) \<le> n"
                          by (metis (no_types, lifting) Nat.le_diff_conv2 One_nat_def T U V V'
                              add.commute add_diff_cancel_left' add_leD2 len length_Cons
                              length_Resid list.size(3) plus_1_eq_Suc)
                        thus ?thesis
                          by (metis Con_sym add.commute Resid.simps(1) ind length_Resid)
                      qed
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                        by (metis Con_TU Con_cons(2) Resid_cons(2) T T' U U'
                            Resid_rec(3) length_0_conv length_Resid)
                      finally show ?thesis by blast
                    qed
                    next
                    assume T': "T' \<noteq> []"
                    show ?thesis
                    proof -
                      have "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) =
                            ((V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* T)) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* [u]))"
                        by (metis Con Con_TU Resid.simps(2) Resid1x_as_Resid U U'
                            Con_cons(2) Con_sym Resid_cons' Resid_cons(2))
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* [u])) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* [u]))"
                      proof -
                        have "length T + length [u] + length V \<le> n"
                          using U U' antisym_conv len not_less_eq_eq by fastforce
                        thus ?thesis
                          by (metis Con_TU Con_VT Con_initial_right U ind)
                      qed
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ((T \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U')"
                      proof -
                        have "length (T \<^sup>*\\\<^sup>* [u]) + length U' + length (V \<^sup>*\\\<^sup>* [u]) \<le> n"
                          using Con_TU Con_initial_right U V V' len length_Resid by force
                        thus ?thesis
                          by (metis Con Con_TU Con_cons(2) U U' calculation ind length_0_conv
                              length_Resid)
                      qed
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                        by (metis "*" Con Con_TU Resid_cons(2) U U' length_Resid length_0_conv)
                      finally show ?thesis by blast
                    qed
                  qed
                qed
              qed
              next
              assume V': "V' \<noteq> []"
              show ?thesis
              proof (cases "U' = []")
                assume U': "U' = []"
                show ?thesis
                proof (cases "T' = []")
                  assume T': "T' = []"
                  show ?thesis
                  proof (intro conjI impI)
                    show *: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow>  V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                    proof -
                      have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> (v \\ t) # (V' \<^sup>*\\\<^sup>* [t \\ v]) \<^sup>*\<frown>\<^sup>* [u \\ t]"
                        using Con_TU Con_VT Con_sym Resid_rec(1-2) T T' U U' V V'
                        by metis
                      also have "... \<longleftrightarrow> [v \\ t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and>
                                         V' \<^sup>*\\\<^sup>* [t \\ v] \<^sup>*\<frown>\<^sup>* [u \\ v] \<^sup>*\\\<^sup>* [t \\ v]"
                      proof -
                        have "V' \<^sup>*\<frown>\<^sup>* [t \\ v]"
                          using T T' V V' Con_VT Con_rec(2) by blast
                        thus ?thesis
                          using R.con_def R.con_sym R.cube
                                Con_rec(2) [of "V' \<^sup>*\\\<^sup>* [t \\ v]" "v \\ t" "u \\ t"]
                          by auto
                      qed
                      also have "... \<longleftrightarrow> [v \\ t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and>
                                         V' \<^sup>*\\\<^sup>* [u \\ v] \<^sup>*\<frown>\<^sup>* [t \\ v] \<^sup>*\\\<^sup>* [u \\ v]"
                      proof -
                        have "length [t \\ v] + length [u \\ v] + length V' \<le> n"
                          using T U V len by fastforce
                        thus ?thesis
                          by (metis Con_imp_Arr_Resid Arr_has_Src Con_VT T T' Trgs.simps(1)
                              Trgs_Resid_sym V V' Con_rec(2) Srcs_Resid ind)
                      qed
                      also have "... \<longleftrightarrow> [v \\ t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and>
                                         V' \<^sup>*\\\<^sup>* [u \\ v] \<^sup>*\<frown>\<^sup>* [t \\ u] \<^sup>*\\\<^sup>* [v \\ u]"
                        by (simp add: R.con_def R.cube)
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                      proof
                        assume 1: "V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                        have tu_vu: "t \\ u \<frown> v \\ u"
                          by (metis (no_types, lifting) 1 T T' U U' V V' Con_rec(3)
                              Resid_rec(1-2) Con_sym length_Resid length_0_conv)
                        have vt_ut: "v \\ t \<frown> u \\ t"
                          using 1
                          by (metis R.con_def R.con_sym R.cube tu_vu)
                        show "[v \\ t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and> V' \<^sup>*\\\<^sup>* [u \\ v] \<^sup>*\<frown>\<^sup>* [t \\ u] \<^sup>*\\\<^sup>* [v \\ u]"
                          by (metis (no_types, lifting) "1" Con_TU Con_cons(1) Con_rec(1-2)
                              Resid_rec(1) T T' U U' V V' Resid_rec(2) length_Resid
                              length_0_conv vt_ut)
                        next
                        assume 1: "[v \\ t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and>
                                   V' \<^sup>*\\\<^sup>* [u \\ v] \<^sup>*\<frown>\<^sup>* [t \\ u] \<^sup>*\\\<^sup>* [v \\ u]"
                        have tu_vu: "t \\ u \<frown> v \\ u \<and> v \\ t \<frown> u \\ t"
                          by (metis 1 Con_sym Resid.simps(1) Residx1.simps(2)
                              Residx1_as_Resid)
                        have tu: "t \<frown> u"
                          using Con_TU Con_rec(1) T T' U U' by blast
                        show "V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                          by (metis (no_types, opaque_lifting) 1 Con_rec(2) Con_sym
                              R.con_implies_arr(2) Resid.simps(1,3) T T' U U' V V'
                              Resid_rec(2) R.arr_resid_iff_con)
                      qed
                      finally show ?thesis by simp
                    qed
                    show "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<Longrightarrow>
                            (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                    proof -
                      assume Con: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T"
                      have "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = ((v \\ t) # (V' \<^sup>*\\\<^sup>* [t \\ v])) \<^sup>*\\\<^sup>* [u \\ t]"
                        using Con_TU Con_VT Con_sym Resid_rec(1-2) T T' U U' V V' by metis
                      also have 1: "... = ((v \\ t) \\ (u \\ t)) #
                                            (V' \<^sup>*\\\<^sup>* [t \\ v]) \<^sup>*\\\<^sup>* ([u \\ v] \<^sup>*\\\<^sup>* [t \\ v])"
                        apply simp
                        by (metis Con Con_VT Con_rec(2) R.conE R.conI R.con_sym R.cube
                            Resid_rec(2) T T' V V' calculation(1))
                      also have "... = ((v \\ t) \\ (u \\ t)) #
                                         (V' \<^sup>*\\\<^sup>* [u \\ v]) \<^sup>*\\\<^sup>* ([t \\ v] \<^sup>*\\\<^sup>* [u \\ v])"
                      proof -
                        have "length [t \\ v] + length [u \\ v] + length V' \<le> n"
                          using T U V len by fastforce
                        moreover have "u \\ v \<frown> t \\ v"
                          by (metis 1 Con_VT Con_rec(2) R.con_sym_ax T T' V V' list.discI
                              R.conE R.conI R.cube)
                        moreover have "t \\ v \<frown> u \\ v"
                          using R.con_sym calculation(2) by blast
                        ultimately show ?thesis
                          by (metis Con_VT Con_rec(2) T T' V V' Con_rec(1) ind)
                      qed
                      also have "... = ((v \\ t) \\ (u \\ t)) #
                                         ((V' \<^sup>*\\\<^sup>* [u \\ v]) \<^sup>*\\\<^sup>* ([t \\ u] \<^sup>*\\\<^sup>* [v \\ u]))"
                        using R.cube by fastforce
                      also have "... = ((v \\ u) \\ (t \\ u)) #
                                         ((V' \<^sup>*\\\<^sup>* [u \\ v]) \<^sup>*\\\<^sup>* ([t \\ u] \<^sup>*\\\<^sup>* [v \\ u]))"
                        by (metis R.cube)
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                      proof -
                        have "(V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U) = ((v \\ u) # ((V' \<^sup>*\\\<^sup>* [u \\ v]))) \<^sup>*\\\<^sup>* [t \\ u]"
                           using T T' U U' V Resid_cons(1) [of "[u]" v V']
                           by (metis "*" Con Con_TU Resid.simps(1) Resid_rec(1) Resid_rec(2))
                        also have "... = ((v \\ u) \\ (t \\ u)) #
                                           ((V' \<^sup>*\\\<^sup>* [u \\ v]) \<^sup>*\\\<^sup>* ([t \\ u] \<^sup>*\\\<^sup>* [v \\ u]))"
                          by (metis "*" Con Con_initial_left calculation Con_sym Resid.simps(1)
                                    Resid_rec(1-2))
                        finally show ?thesis by simp
                      qed
                      finally show ?thesis by simp
                    qed
                  qed
                  next
                  assume T': "T' \<noteq> []"
                  show ?thesis
                  proof (intro conjI impI)
                    show *: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow>  V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                    proof -
                      have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* [u \\ t] \<^sup>*\\\<^sup>* T'"
                        using Con_TU Con_VT Con_sym Resid_cons(2) Resid_rec(3) T T' U U'
                        by force
                      also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* [u \\ t]"
                      proof -
                        have "length [u \\ t] + length T' + length (V \<^sup>*\\\<^sup>* [t]) \<le> n"
                          using Con_VT Con_initial_right T U length_Resid len by fastforce
                        thus ?thesis
                          by (metis Con_TU Con_VT Con_rec(2) T T' U V add.commute Con_cons(2)
                              ind list.discI)
                      qed
                      also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u] \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* [u \\ t]"
                      proof -
                        have "length [t] + length [u] + length V \<le> n"
                          using T T' U le_Suc_eq len by fastforce
                        hence "(V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* [t]) = (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [u])"
                          using ind [of "[t]" "[u]" V]
                          by (metis Con_TU Con_VT Con_initial_left Con_initial_right T U)
                        thus ?thesis
                          by (metis (full_types) Con_TU Con_initial_left Con_sym Resid_rec(1) T U)
                      qed
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                        by (metis Con_TU Con_cons(2) Con_rec(2) Resid.simps(1) Resid_rec(2)
                            T T' U U')
                      finally show ?thesis by simp
                    qed
                    show "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<Longrightarrow>
                           (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                    proof -
                      assume Con: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T"
                      have "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* ([u \\ t] \<^sup>*\\\<^sup>* T')"
                        using Con_TU Con_VT Con_sym Resid_cons(2) Resid_rec(3) T T' U U'
                        by force
                      also have "... = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* [u \\ t])"
                      proof -
                        have "length [u \\ t] + length T' + length (Resid V [t]) \<le> n"
                          using Con_VT Con_initial_right T U length_Resid len by fastforce
                        thus ?thesis
                          by (metis Con_TU Con_VT Con_cons(2) Con_rec(2) T T' U V add.commute
                              ind list.discI)
                      qed
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u]) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* [u \\ t])"
                      proof -
                        have "length [t] + length [u] + length V \<le> n"
                          using T T' U le_Suc_eq len by fastforce
                        thus ?thesis
                          using ind [of "[t]" "[u]" V]
                          by (metis Con_TU Con_VT Con_initial_left Con_sym Resid_rec(1) T U)
                      qed
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                        using * Con Con_TU Con_rec(2) Resid_cons(2) Resid_rec(2) T T' U U'
                        by auto
                      finally show ?thesis by simp
                    qed
                  qed
                qed
                next
                assume U': "U' \<noteq> []"
                show ?thesis
                proof (cases "T' = []")
                  assume T': "T' = []"
                  show ?thesis
                  proof (intro conjI impI)
                    show *: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                    proof -
                      have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* (u \\ t) # (U' \<^sup>*\\\<^sup>* [t \\ u])"
                        using T U V T' U' V' Con_TU Con_VT Con_sym Resid_rec(2) by auto
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and>
                                         (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u \\ t] \<^sup>*\<frown>\<^sup>* U' \<^sup>*\\\<^sup>* [t \\ u]"
                        by (metis Con_TU Con_VT Con_cons(2) Con_initial_right
                            Con_rec(2) Con_sym T U U')
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* [t] \<^sup>*\<frown>\<^sup>* [u \\ t] \<and>
                                         (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u] \<^sup>*\<frown>\<^sup>* U' \<^sup>*\\\<^sup>* [t \\ u]"
                      proof -
                        have "length [u] + length [t] + length V \<le> n"
                          using T U V T' U' V' len not_less_eq_eq order_trans by fastforce
                        thus ?thesis
                          using ind [of "[t]" "[u]" V]
                          by (metis Con_TU Con_VT Con_initial_right Resid_rec(1) T U
                                    Con_sym length_Cons)
                      qed
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* [u] \<^sup>*\<frown>\<^sup>* [t \\ u] \<and>
                                         (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u] \<^sup>*\<frown>\<^sup>* U' \<^sup>*\\\<^sup>* [t \\ u]"
                      proof -
                        have "length [t] + length [u] + length V \<le> n"
                          using T U V T' U' V' len antisym_conv not_less_eq_eq by fastforce
                        thus ?thesis
                          using ind [of "[t]"]
                          by (metis (full_types) Con_TU Con_VT Con_initial_right Con_sym
                              Resid_rec(1) T U)
                      qed
                      also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U' \<^sup>*\<frown>\<^sup>* [t \\ u] \<^sup>*\\\<^sup>* U'"
                      proof -
                        have "length [t \\ u] + length U' + length (V \<^sup>*\\\<^sup>* [u]) \<le> n"
                          by (metis T T' U add.assoc add.right_neutral add_leD1
                              add_le_cancel_left length_Resid len length_Cons list.size(3)
                              plus_1_eq_Suc)
                        thus ?thesis
                          by (metis (no_types, opaque_lifting) Con_sym Resid.simps(1)
                              add.commute ind)
                      qed
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                        by (metis Con_TU Resid_cons(2) Resid_rec(3) T T' U U'
                            Con_cons(2) length_Resid length_0_conv)
                      finally show ?thesis by blast
                    qed
                    show "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<Longrightarrow>
                           (V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                    proof -
                      assume Con: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T"
                      have "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) =
                            (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* ((u \\ t) # (U' \<^sup>*\\\<^sup>* [t \\ u]))"
                        using Con_TU Con_sym Resid_rec(2) T T' U U' by auto
                     also have "... = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u \\ t]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
                        by (metis Con Con_TU Con_rec(2) Con_sym T T' U U' calculation
                            Resid_cons(2))
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* [t \\ u]) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t \\ u])"
                      proof -
                        have "length [t] + length [u] + length V \<le> n"
                          using T U U' le_Suc_eq len by fastforce
                        thus ?thesis
                          using T U Con_TU Con_VT Con_sym ind [of "[t]" "[u]" V]
                          by (metis (no_types, opaque_lifting) Con_initial_right Resid.simps(3))
                      qed
                      also have "... = ((V \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t \\ u] \<^sup>*\\\<^sup>* U')"
                      proof -
                        have "length [t \\ u] + length U' + length (V \<^sup>*\\\<^sup>* [u]) \<le> n"
                          by (metis (no_types, opaque_lifting) T T' U add.left_commute
                              add.right_neutral add_leD2 add_le_cancel_left len length_Cons
                              length_Resid list.size(3) plus_1_eq_Suc)
                        thus ?thesis
                          by (metis Con Con_TU Con_rec(3) T T' U U' calculation
                              ind length_0_conv length_Resid)
                      qed
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                        by (metis "*" Con Con_TU Resid_rec(3) T T' U U' Resid_cons(2)
                            length_Resid length_0_conv)
                      finally show ?thesis by blast
                    qed
                  qed
                  next
                  assume T': "T' \<noteq> []"
                  show ?thesis
                  proof (intro conjI impI)
                    have 1: "U \<^sup>*\<frown>\<^sup>* [t]"
                      using T Con_TU
                      by (metis Con_cons(2) Con_sym Resid.simps(2))
                    have 2: "V \<^sup>*\<frown>\<^sup>* [t]"
                      using V Con_VT Con_initial_right T by blast
                    have 3: "length T' + length (U \<^sup>*\\\<^sup>* [t]) + length (V \<^sup>*\\\<^sup>* [t]) \<le> n"
                      using "1" "2" T len length_Resid by force
                    have 4: "length [t] + length U + length V \<le> n"
                      using T T' len antisym_conv not_less_eq_eq by fastforce
                    show *: "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                    proof -
                      have "V \<^sup>*\\\<^sup>* T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* T \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T' \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T'"
                        using Con_TU Con_VT Con_sym Resid_cons(2) T T' by force
                      also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                        by (metis 3 Con_TU Con_VT Con_cons(1) Con_cons(2) T T' U V ind
                            list.discI)
                      also have "... \<longleftrightarrow> (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                        by (metis 1 2 4 Con_sym ind)
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* hd ([t] \<^sup>*\\\<^sup>* U) # T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
                        by (metis 1 Con_TU Con_cons(1) Con_cons(2) Resid.simps(1)
                            Resid1x_as_Resid T T' list.sel(1))
                      also have "... \<longleftrightarrow> V \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T \<^sup>*\\\<^sup>* U"
                        using 1 Resid_cons' [of T' t U] Con_TU T T' Resid1x_as_Resid
                              Con_sym
                        by force
                      finally show ?thesis by simp
                    qed
                    show "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                    proof -
                      have "(V \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T) =
                            ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* ((U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T')"
                        using Con_TU Con_VT Con_sym Resid_cons(2) T T' by force
                      also have "... = ((V \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
                        by (metis (no_types, lifting) "3" Con_TU Con_VT T T' U V Con_cons(1)
                            Con_cons(2) ind list.simps(3))
                      also have "... = ((V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
                        by (metis 1 2 4 Con_sym ind)
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T') \<^sup>*\\\<^sup>* U)"
                        by (metis "*" Con_TU Con_cons(1) Resid1x_as_Resid
                            Resid_cons' T T' U calculation Resid_cons(2) list.distinct(1))
                      also have "... = (V \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U)"
                        using T by fastforce
                      finally show ?thesis by simp
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed

    lemma Cube:
    shows "T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* V \<^sup>*\\\<^sup>* U \<longleftrightarrow> T \<^sup>*\\\<^sup>* V \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* V"
    and "T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* V \<^sup>*\\\<^sup>* U \<Longrightarrow> (T \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* U) = (T \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* V)"
    proof -
      show "T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* V \<^sup>*\\\<^sup>* U \<longleftrightarrow> T \<^sup>*\\\<^sup>* V \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* V"
        using Cube_ind by (metis Con_sym Resid.simps(1) le_add2)
      show "T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* V \<^sup>*\\\<^sup>* U \<Longrightarrow> (T \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* U) = (T \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* V)"
        using Cube_ind by (metis Con_sym Resid.simps(1) order_refl)
    qed

    lemma Con_implies_Arr:
    assumes "T \<^sup>*\<frown>\<^sup>* U"
    shows "Arr T" and "Arr U"
      using assms Con_sym
      by (metis Con_imp_Arr_Resid Arr_iff_Con_self Cube(1) Resid.simps(1))+

    sublocale partial_magma Resid
      by (unfold_locales, metis Resid.simps(1) Con_sym)

    lemma is_partial_magma:
    shows "partial_magma Resid"
      ..

    lemma null_char:
    shows "null = []"
      by (metis null_is_zero(2) Resid.simps(1))

    sublocale residuation Resid
      using null_char Con_sym Arr_iff_Con_self Con_imp_Arr_Resid Cube null_is_zero(2)
      by unfold_locales auto

    lemma is_residuation:
    shows "residuation Resid"
      ..

    lemma arr_char:
    shows "arr T \<longleftrightarrow> Arr T"
      using null_char Arr_iff_Con_self by fastforce

    lemma arrI\<^sub>P [intro]:
    assumes "Arr T"
    shows "arr T"
      using assms arr_char by auto

    lemma ide_char:
    shows "ide T \<longleftrightarrow> Ide T"
      by (metis Con_Arr_self Ide_implies_Arr Resid_Arr_Ide_ind Resid_Arr_self arr_char ide_def
          arr_def)

    lemma con_char:
    shows "con T U \<longleftrightarrow> Con T U"
      using null_char by auto

    lemma conI\<^sub>P [intro]:
    assumes "Con T U"
    shows "con T U"
      using assms con_char by auto

    sublocale rts Resid
    proof
      show "\<And>A T. \<lbrakk>ide A; con T A\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* A = T"
        using Resid_Arr_Ide_ind ide_char null_char by auto
      show "\<And>T. arr T \<Longrightarrow> ide (trg T)"
        by (metis arr_char Resid_Arr_self ide_char resid_arr_self)
      show "\<And>A T. \<lbrakk>ide A; con A T\<rbrakk> \<Longrightarrow> ide (A \<^sup>*\\\<^sup>* T)"
        by (simp add: Resid_Ide_Arr_ind con_char ide_char)
      show "\<And>T U. con T U \<Longrightarrow> \<exists>A. ide A \<and> con A T \<and> con A U"
      proof -
        fix T U
        assume TU: "con T U"
        have 1: "Srcs T = Srcs U"
          using TU Con_imp_eq_Srcs con_char by force
        obtain a where a: "a \<in> Srcs T \<inter> Srcs U"
          using 1
          by (metis Int_absorb Int_emptyI TU arr_char Arr_has_Src con_implies_arr(1))
        show "\<exists>A. ide A \<and> con A T \<and> con A U"
          using a 1
          by (metis (full_types) Ball_Collect Con_single_ide_ind Ide.simps(2) Int_absorb TU
              Srcs_are_ide arr_char con_char con_implies_arr(1-2) ide_char)
      qed
      show "\<And>T U V. \<lbrakk>ide (Resid T U); con U V\<rbrakk> \<Longrightarrow> con (T \<^sup>*\\\<^sup>* U) (V \<^sup>*\\\<^sup>* U)"
        using null_char ide_char
        by (metis Con_imp_Arr_Resid Con_Ide_iff Srcs_Resid con_char con_sym arr_resid_iff_con
            ide_implies_arr)
    qed

    theorem is_rts:
    shows "rts Resid"
      ..

    notation cong  (infix "\<^sup>*\<sim>\<^sup>*" 50)
    notation prfx  (infix "\<^sup>*\<lesssim>\<^sup>*" 50)

    lemma sources_char\<^sub>P:
    shows "sources T = {A. Ide A \<and> Arr T \<and> Srcs A = Srcs T}"
      using Con_Ide_iff Con_sym con_char ide_char sources_def by fastforce

    lemma sources_cons:
    shows "Arr (t # T) \<Longrightarrow> sources (t # T) = sources [t]"
      apply (induct T)
       apply simp
      using sources_char\<^sub>P by auto

    lemma targets_char\<^sub>P:
    shows "targets T = {B. Ide B \<and> Arr T \<and> Srcs B = Trgs T}"
      unfolding targets_def
      by (metis (no_types, lifting) trg_def Arr.simps(1) Ide_implies_Arr Resid_Arr_self
          arr_char Con_Ide_iff Srcs_Resid con_char ide_char con_implies_arr(1))

    lemma seq_char':
    shows "seq T U \<longleftrightarrow> Arr T \<and> Arr U \<and> Trgs T \<inter> Srcs U \<noteq> {}"
    proof
      show "seq T U \<Longrightarrow> Arr T \<and> Arr U \<and> Trgs T \<inter> Srcs U \<noteq> {}"
        unfolding seq_def
        using Arr_has_Trg arr_char Con_Arr_self sources_char\<^sub>P trg_def trg_in_targets
        by fastforce
      assume 1: "Arr T \<and> Arr U \<and> Trgs T \<inter> Srcs U \<noteq> {}"
      have "targets T = sources U"
      proof -
        obtain a where a: "R.ide a \<and> a \<in> Trgs T \<and> a \<in> Srcs U"
          using 1 Trgs_are_ide by blast
        have "Trgs [a] = Trgs T"
          using a 1
          by (metis Con_single_ide_ind Con_sym Resid_Arr_Src Srcs_Resid Trgs_eqI)
        moreover have "Srcs [a] = Srcs U"
          using a 1 Con_single_ide_ind Con_imp_eq_Srcs by blast
        moreover have "Trgs [a] = Srcs [a]"
          using a
          by (metis R.residuation_axioms R.sources_resid Srcs.simps(2) Trgs.simps(2)
              residuation.ideE)
        ultimately show ?thesis
          using 1 sources_char\<^sub>P targets_char\<^sub>P by auto
      qed
      thus "seq T U"
        using 1 by blast
    qed
      
    lemma seq_char:
    shows "seq T U \<longleftrightarrow> Arr T \<and> Arr U \<and> Trgs T = Srcs U"
      by (metis Int_absorb Srcs_Resid Arr_has_Src Arr_iff_Con_self Srcs_eqI seq_char')

    lemma seqI\<^sub>P [intro]:
    assumes "Arr T" and "Arr U" and "Trgs T \<inter> Srcs U \<noteq> {}"
    shows "seq T U"
      using assms seq_char' by auto

    lemma Ide_imp_sources_eq_targets:
    assumes "Ide T"
    shows "sources T = targets T"
      using assms
      by (metis Resid_Arr_Ide_ind arr_iff_has_source arr_iff_has_target con_char
          arr_def sources_resid)

    subsection "Inclusion Map"

    text \<open>
      Inclusion of an RTS to the RTS of its paths.
    \<close>

    abbreviation incl
    where "incl \<equiv> \<lambda>t. if R.arr t then [t] else null"

    lemma incl_is_simulation:
    shows "simulation resid Resid incl"
      using R.con_implies_arr(1-2) con_char R.arr_resid_iff_con null_char
      by unfold_locales auto

    lemma incl_is_injective:
    shows "inj_on incl (Collect R.arr)"
      by (intro inj_onI) simp

    lemma reflects_con:
    assumes "incl t \<^sup>*\<frown>\<^sup>* incl u"
    shows "t \<frown> u"
      using assms
      by (metis (full_types) Arr.simps(1) Con_implies_Arr(1-2) Con_rec(1) null_char)

  end

  subsection "Composites of Paths"

  text \<open>
    The RTS of paths has composites, given by the append operation on lists.
  \<close>

  context paths_in_rts
  begin

    lemma Srcs_append [simp]:
    assumes "T \<noteq> []"
    shows "Srcs (T @ U) = Srcs T"
      by (metis Nil_is_append_conv Srcs.simps(2) Srcs.simps(3) assms hd_append list.exhaust_sel)

    lemma Trgs_append [simp]:
    shows "U \<noteq> [] \<Longrightarrow> Trgs (T @ U) = Trgs U"
    proof (induct T)
      show "U \<noteq> [] \<Longrightarrow> Trgs ([] @ U) = Trgs U"
        by auto
      show "\<And>t T. \<lbrakk>U \<noteq> [] \<Longrightarrow> Trgs (T @ U) = Trgs U; U \<noteq> []\<rbrakk>
                      \<Longrightarrow> Trgs ((t # T) @ U) = Trgs U"
        by (metis Nil_is_append_conv Trgs.simps(3) append_Cons list.exhaust)
    qed

    lemma seq_implies_Trgs_eq_Srcs:
    shows "\<lbrakk>Arr T; Arr U; Trgs T \<subseteq> Srcs U\<rbrakk> \<Longrightarrow> Trgs T = Srcs U"
      by (metis inf.orderE Arr_has_Trg seqI\<^sub>P seq_char)

    lemma Arr_append_iff\<^sub>P:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []\<rbrakk> \<Longrightarrow> Arr (T @ U) \<longleftrightarrow> Arr T \<and> Arr U \<and> Trgs T \<subseteq> Srcs U"
    proof (induct T arbitrary: U)
      show "\<And>U. \<lbrakk>[] \<noteq> []; U \<noteq> []\<rbrakk> \<Longrightarrow> Arr ([] @ U) = (Arr [] \<and> Arr U \<and> Trgs [] \<subseteq> Srcs U)"
        by simp
      fix t T and U :: "'a list"
      assume ind: "\<And>U. \<lbrakk>T \<noteq> []; U \<noteq> []\<rbrakk>
                          \<Longrightarrow> Arr (T @ U) = (Arr T \<and> Arr U \<and> Trgs T \<subseteq> Srcs U)"
      assume U: "U \<noteq> []"
      show "Arr ((t # T) @ U) \<longleftrightarrow> Arr (t # T) \<and> Arr U \<and> Trgs (t # T) \<subseteq> Srcs U"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using Arr.elims(1) U by auto
        assume T: "T \<noteq> []"
        have "Arr ((t # T) @ U) \<longleftrightarrow> Arr (t # (T @ U))"
          by simp
        also have "... \<longleftrightarrow> R.arr t \<and> Arr (T @ U) \<and> R.targets t \<subseteq> Srcs (T @ U)"
          using T U
          by (metis Arr.simps(3) Nil_is_append_conv neq_Nil_conv)
        also have "... \<longleftrightarrow> R.arr t \<and> Arr T \<and> Arr U \<and> Trgs T \<subseteq> Srcs U \<and> R.targets t \<subseteq> Srcs T"
          using T U ind by auto
        also have "... \<longleftrightarrow> Arr (t # T) \<and> Arr U \<and> Trgs (t # T) \<subseteq> Srcs U"
          using T U
          by (metis Arr.simps(3) Trgs.simps(3) neq_Nil_conv)
        finally show ?thesis by auto
      qed
    qed

    lemma Arr_consI\<^sub>P [intro, simp]:
    assumes "R.arr t" and "Arr U" and "R.targets t \<subseteq> Srcs U"
    shows "Arr (t # U)"
      using assms Arr.elims(3) by blast

    lemma Arr_appendI\<^sub>P [intro, simp]:
    assumes "Arr T" and "Arr U" and "Trgs T \<subseteq> Srcs U"
    shows "Arr (T @ U)"
      using assms
      by (metis Arr.simps(1) Arr_append_iff\<^sub>P)

    lemma Arr_appendE\<^sub>P [elim]:
    assumes "Arr (T @ U)" and "T \<noteq> []" and "U \<noteq> []"
    and "\<lbrakk>Arr T; Arr U; Trgs T = Srcs U\<rbrakk> \<Longrightarrow> thesis"
    shows thesis
      using assms Arr_append_iff\<^sub>P seq_implies_Trgs_eq_Srcs by force

    lemma Ide_append_iff\<^sub>P:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []\<rbrakk> \<Longrightarrow> Ide (T @ U) \<longleftrightarrow> Ide T \<and> Ide U \<and> Trgs T \<subseteq> Srcs U"
      using Ide_char by auto

    lemma Ide_appendI\<^sub>P [intro, simp]:
    assumes "Ide T" and "Ide U" and "Trgs T \<subseteq> Srcs U"
    shows "Ide (T @ U)"
      using assms
      by (metis Ide.simps(1) Ide_append_iff\<^sub>P)

    lemma Resid_append_ind:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []; V \<noteq> []\<rbrakk> \<Longrightarrow>
             (V @ T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> V \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* V) \<and>
             (T \<^sup>*\<frown>\<^sup>* V @ U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* V \<and> T \<^sup>*\\\<^sup>* V \<^sup>*\<frown>\<^sup>* U) \<and>
             (V @ T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> (V @ T) \<^sup>*\\\<^sup>* U = V \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* V)) \<and>
             (T \<^sup>*\<frown>\<^sup>* V @ U \<longrightarrow> T \<^sup>*\\\<^sup>* (V @ U) = (T \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* U)"
    proof (induct V arbitrary: T U)
      show "\<And>T U. \<lbrakk>T \<noteq> []; U \<noteq> []; [] \<noteq> []\<rbrakk> \<Longrightarrow>
                   ([] @ T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> [] \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* []) \<and>
                   (T \<^sup>*\<frown>\<^sup>* [] @ U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [] \<and> T \<^sup>*\\\<^sup>* [] \<^sup>*\<frown>\<^sup>* U) \<and>
                   ([] @ T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> ([] @ T) \<^sup>*\\\<^sup>* U = [] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [])) \<and>
                   (T \<^sup>*\<frown>\<^sup>* [] @ U \<longrightarrow> T \<^sup>*\\\<^sup>* ([] @ U) = (T \<^sup>*\\\<^sup>* []) \<^sup>*\\\<^sup>* U)"
        by simp
      fix v :: 'a and T U V :: "'a list"
      assume ind: "\<And>T U. \<lbrakk>T \<noteq> []; U \<noteq> []; V \<noteq> []\<rbrakk> \<Longrightarrow>
                          (V @ T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> V \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* V) \<and>
                          (T \<^sup>*\<frown>\<^sup>* V @ U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* V \<and> T \<^sup>*\\\<^sup>* V \<^sup>*\<frown>\<^sup>* U) \<and>
                          (V @ T \<^sup>*\<frown>\<^sup>* U \<longrightarrow> (V @ T) \<^sup>*\\\<^sup>* U = V \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* V)) \<and>
                          (T \<^sup>*\<frown>\<^sup>* V @ U \<longrightarrow> T \<^sup>*\\\<^sup>* (V @ U) = (T \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* U)"
      assume T: "T \<noteq> []" and U: "U \<noteq> []"
      show "((v # V) @ T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow> (v # V) \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* (v # V)) \<and>
            (T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* (v # V) \<and> T \<^sup>*\\\<^sup>* (v # V) \<^sup>*\<frown>\<^sup>* U) \<and>
            ((v # V) @ T \<^sup>*\<frown>\<^sup>* U \<longrightarrow>
              ((v # V) @ T) \<^sup>*\\\<^sup>* U = (v # V) \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* (v # V))) \<and>
            (T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<longrightarrow> T \<^sup>*\\\<^sup>* ((v # V) @ U) = (T \<^sup>*\\\<^sup>* (v # V)) \<^sup>*\\\<^sup>* U)"
      proof (intro conjI iffI impI)
        show 1: "(v # V) @ T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow>
                   ((v # V) @ T) \<^sup>*\\\<^sup>* U = (v # V) \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* (v # V))"
        proof (cases "V = []")
          show "V = [] \<Longrightarrow> (v # V) @ T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> ?thesis"
            using T U Resid_cons(1) U by auto
          assume V: "V \<noteq> []"
          assume Con: "(v # V) @ T \<^sup>*\<frown>\<^sup>* U"
          have "((v # V) @ T) \<^sup>*\\\<^sup>* U = (v # (V @ T)) \<^sup>*\\\<^sup>* U"
            by simp
          also have "... = [v] \<^sup>*\\\<^sup>* U @ (V @ T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [v])"
            using T U Con Resid_cons by simp
          also have "... = [v] \<^sup>*\\\<^sup>* U @ V \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [v]) @ T \<^sup>*\\\<^sup>* ((U \<^sup>*\\\<^sup>* [v]) \<^sup>*\\\<^sup>* V)"
            using T U V Con ind Resid_cons
            by (metis Con_sym Cons_eq_appendI append_is_Nil_conv Con_cons(1))
          also have "... = (v # V) \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* (v # V))"
            using ind[of T]
            by (metis Con Con_cons(2) Cons_eq_appendI Resid_cons(1) Resid_cons(2) T U V
                append.assoc append_is_Nil_conv Con_sym)
          finally show ?thesis by simp
        qed
        show 2: "T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<Longrightarrow> T \<^sup>*\\\<^sup>* ((v # V) @ U) = (T \<^sup>*\\\<^sup>* (v # V)) \<^sup>*\\\<^sup>* U"
        proof (cases "V = []")
          show "V = [] \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<Longrightarrow> ?thesis"
            using Resid_cons(2) T U by auto
          assume V: "V \<noteq> []"
          assume Con: "T \<^sup>*\<frown>\<^sup>* (v # V) @ U"
          have "T \<^sup>*\\\<^sup>* ((v # V) @ U) = T \<^sup>*\\\<^sup>* (v # (V @ U))"
            by simp
          also have 1: "... = (T \<^sup>*\\\<^sup>* [v]) \<^sup>*\\\<^sup>* (V @ U)"
            using V Con Resid_cons(2) T by force
          also have "... = ((T \<^sup>*\\\<^sup>* [v]) \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* U"
            using T U V 1 Con ind
            by (metis Con_initial_right Cons_eq_appendI)
          also have "... = (T \<^sup>*\\\<^sup>* (v # V)) \<^sup>*\\\<^sup>* U"
            using T V Con
            by (metis Con_cons(2) Con_initial_right Cons_eq_appendI Resid_cons(2))
          finally show ?thesis by blast
        qed
        show "(v # V) @ T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> v # V \<^sup>*\<frown>\<^sup>* U"
          by (metis 1 Con_sym Resid.simps(1) append_Nil)
        show "(v # V) @ T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* (v # V)"
          using T U Con_sym
          by (metis 1 Con_initial_right Resid_cons(1-2) append.simps(2) ind self_append_conv)
        show "T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* v # V"
          using 2 by fastforce
        show "T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<Longrightarrow> T \<^sup>*\\\<^sup>* (v # V) \<^sup>*\<frown>\<^sup>* U"
          using 2 by fastforce
        show "T \<^sup>*\<frown>\<^sup>* v # V \<and> T \<^sup>*\\\<^sup>* (v # V) \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* (v # V) @ U"
        proof -
          assume Con: "T \<^sup>*\<frown>\<^sup>* v # V \<and> T \<^sup>*\\\<^sup>* (v # V) \<^sup>*\<frown>\<^sup>* U"
          have "T \<^sup>*\<frown>\<^sup>* (v # V) @ U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* v # (V @ U)"
            by simp
          also have "... \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* [v] \<and> T \<^sup>*\\\<^sup>* [v] \<^sup>*\<frown>\<^sup>* V @ U"
            using T U Con_cons(2) by simp
          also have "... \<longleftrightarrow> T \<^sup>*\\\<^sup>* [v] \<^sup>*\<frown>\<^sup>* V @ U"
            by fastforce
          also have "... \<longleftrightarrow> True"
            using Con ind
            by (metis Con_cons(2) Resid_cons(2) T U self_append_conv2)
          finally show ?thesis by blast
        qed
        show "v # V \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* (v # V) \<Longrightarrow> (v # V) @ T \<^sup>*\<frown>\<^sup>* U"
        proof -
          assume Con: "v # V \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* (v # V)"
          have "(v # V) @ T \<^sup>*\<frown>\<^sup>* U \<longleftrightarrow>v # (V @ T) \<^sup>*\<frown>\<^sup>* U"
            by simp
          also have "... \<longleftrightarrow> [v] \<^sup>*\<frown>\<^sup>* U \<and> V @ T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [v]"
            using T U Con_cons(1) by simp
          also have "... \<longleftrightarrow> V @ T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [v]"
            by (metis Con Con_cons(1) U)
          also have "... \<longleftrightarrow> True"
            using Con ind
            by (metis Con_cons(1) Con_sym Resid_cons(2) T U append_self_conv2)
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma Con_append:
    assumes "T \<noteq> []" and "U \<noteq> []" and "V \<noteq> []"
    shows "T @ U \<^sup>*\<frown>\<^sup>* V \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* V \<and> U \<^sup>*\<frown>\<^sup>* V \<^sup>*\\\<^sup>* T"
    and "T \<^sup>*\<frown>\<^sup>* U @ V \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* U \<and> T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* V"
      using assms Resid_append_ind by blast+

    lemma Con_appendI [intro]:
    shows "\<lbrakk>T \<^sup>*\<frown>\<^sup>* V; U \<^sup>*\<frown>\<^sup>* V \<^sup>*\\\<^sup>* T\<rbrakk> \<Longrightarrow> T @ U \<^sup>*\<frown>\<^sup>* V"
    and "\<lbrakk>T \<^sup>*\<frown>\<^sup>* U; T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* V\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U @ V"
      by (metis Con_append(1) Con_sym Resid.simps(1))+

    lemma Resid_append [intro, simp]:
    shows "\<lbrakk>T \<noteq> []; T @ U \<^sup>*\<frown>\<^sup>* V\<rbrakk> \<Longrightarrow> (T @ U) \<^sup>*\\\<^sup>* V = (T \<^sup>*\\\<^sup>* V) @ (U \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* T))"
    and "\<lbrakk>U \<noteq> []; V \<noteq> []; T \<^sup>*\<frown>\<^sup>* U @ V\<rbrakk> \<Longrightarrow> T \<^sup>*\\\<^sup>* (U @ V) = (T \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* V"
      using Resid_append_ind
       apply (metis Con_sym Resid.simps(1) append_self_conv)
      using Resid_append_ind
      by (metis Resid.simps(1))

    lemma Resid_append2 [simp]:
    assumes "T \<noteq> []" and "U \<noteq> []" and "V \<noteq> []" and "W \<noteq> []"
    and "T @ U \<^sup>*\<frown>\<^sup>* V @ W"
    shows "(T @ U) \<^sup>*\\\<^sup>* (V @ W) =
           (T \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* W @ (U \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* T)) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* V))"
      using assms Resid_append
      by (metis Con_append(1-2) append_is_Nil_conv)

    lemma append_is_composite_of:
    assumes "seq T U"
    shows "composite_of T U (T @ U)"
      unfolding composite_of_def
      using assms
      apply (intro conjI)
        apply (metis Arr.simps(1) Resid_Arr_self Resid_Ide_Arr_ind Arr_appendI\<^sub>P
                     Resid_append_ind ide_char order_refl seq_char)
       apply (metis Arr.simps(1) Arr_appendI\<^sub>P Con_Arr_self Resid_Arr_self Resid_append_ind
                    ide_char seq_char order_refl)
      by (metis Arr.simps(1) Con_Arr_self Con_append(1) Resid_Arr_self Arr_appendI\<^sub>P
                Ide_append_iff\<^sub>P Resid_append(1) ide_char seq_char order_refl)

    sublocale rts_with_composites Resid
      using append_is_composite_of composable_def by unfold_locales blast

    theorem is_rts_with_composites:
    shows "rts_with_composites Resid"
      ..

    (* TODO: This stuff might be redundant. *)
    lemma arr_append [intro, simp]:
    assumes "seq T U"
    shows "arr (T @ U)"
      using assms arrI\<^sub>P seq_char by simp

    lemma arr_append_imp_seq:
    assumes "T \<noteq> []" and "U \<noteq> []" and "arr (T @ U)"
    shows "seq T U"
      using assms arr_char seq_char Arr_append_iff\<^sub>P seq_implies_Trgs_eq_Srcs by simp

    lemma sources_append [simp]:
    assumes "seq T U"
    shows "sources (T @ U) = sources T"
      using assms
      by (meson append_is_composite_of sources_composite_of)

    lemma targets_append [simp]:
    assumes "seq T U"
    shows "targets (T @ U) = targets U"
      using assms
      by (meson append_is_composite_of targets_composite_of)

    lemma cong_respects_seq\<^sub>P:
    assumes "seq T U" and "T \<^sup>*\<sim>\<^sup>* T'" and "U \<^sup>*\<sim>\<^sup>* U'"
    shows "seq T' U'"
      by (meson assms cong_respects_seq)

    lemma cong_append [intro]:
    assumes "seq T U" and "T \<^sup>*\<sim>\<^sup>* T'" and "U \<^sup>*\<sim>\<^sup>* U'"
    shows "T @ U \<^sup>*\<sim>\<^sup>* T' @ U'"
    proof
      have 1: "\<And>T U T' U'. \<lbrakk>seq T U; T \<^sup>*\<sim>\<^sup>* T'; U \<^sup>*\<sim>\<^sup>* U'\<rbrakk> \<Longrightarrow> seq T' U'"
        using assms cong_respects_seq\<^sub>P by simp
      have 2: "\<And>T U T' U'. \<lbrakk>seq T U; T \<^sup>*\<sim>\<^sup>* T'; U \<^sup>*\<sim>\<^sup>* U'\<rbrakk> \<Longrightarrow> T @ U \<^sup>*\<lesssim>\<^sup>* T' @ U'"
      proof -
        fix T U T' U'
        assume TU: "seq T U" and TT': "T \<^sup>*\<sim>\<^sup>* T'" and UU': "U \<^sup>*\<sim>\<^sup>* U'"
        have T'U': "seq T' U'"
          using TU TT' UU' cong_respects_seq\<^sub>P by simp
        have 3: "Ide (T \<^sup>*\\\<^sup>* T') \<and> Ide (T' \<^sup>*\\\<^sup>* T) \<and> Ide (U \<^sup>*\\\<^sup>* U') \<and> Ide (U' \<^sup>*\\\<^sup>* U)"
          using TU TT' UU' ide_char by blast
        have "(T @ U) \<^sup>*\\\<^sup>* (T' @ U') =
              ((T \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* U') @ U \<^sup>*\\\<^sup>* ((T' \<^sup>*\\\<^sup>* T) @ U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* T'))"
        proof -
          have 4: "T \<noteq> [] \<and> U \<noteq> [] \<and> T' \<noteq> [] \<and> U' \<noteq> []"
            using TU TT' UU' Arr.simps(1) seq_char ide_char by auto
          moreover have "(T @ U) \<^sup>*\\\<^sup>* (T' @ U') \<noteq> []"
          proof (intro Con_appendI)
            show "T \<^sup>*\\\<^sup>* T' \<noteq> []"
              using "3" by force
            show "(T \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* U' \<noteq> []"
              using "3" T'U' \<open>T \<^sup>*\\<^sup>* T' \<noteq> []\<close> Con_Ide_iff seq_char by fastforce
            show "U \<^sup>*\\\<^sup>* ((T' @ U') \<^sup>*\\\<^sup>* T) \<noteq> []"
            proof -
              have "U \<^sup>*\\\<^sup>* ((T' @ U') \<^sup>*\\\<^sup>* T) = U \<^sup>*\\\<^sup>* ((T' \<^sup>*\\\<^sup>* T) @ U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* T'))"
                by (metis Con_appendI(1) Resid_append(1) \<open>(T \<^sup>*\\<^sup>* T') \<^sup>*\\<^sup>* U' \<noteq> []\<close>
                    \<open>T \<^sup>*\\<^sup>* T' \<noteq> []\<close> calculation Con_sym)
              also have "... = (U \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* T)) \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* T'))"
                by (metis Arr.simps(1) Con_append(2) Resid_append(2) \<open>(T \<^sup>*\\<^sup>* T') \<^sup>*\\<^sup>* U' \<noteq> []\<close>
                    Con_implies_Arr(1) Con_sym)
              also have "... = U \<^sup>*\\\<^sup>* U'"
                by (metis (mono_tags, lifting) "3" Ide.simps(1) Resid_Ide(1) Srcs_Resid TU
                    \<open>(T \<^sup>*\\<^sup>* T') \<^sup>*\\<^sup>* U' \<noteq> []\<close> Con_Ide_iff seq_char)
              finally show ?thesis
                using 3 UU' by force
            qed
          qed
          ultimately show ?thesis
            using Resid_append2 [of T U T' U'] seq_char
            by (metis Con_append(2) Con_sym Resid_append(2) Resid.simps(1))
        qed
        moreover have "Ide ..."
        proof
          have 3: "Ide (T \<^sup>*\\\<^sup>* T') \<and> Ide (T' \<^sup>*\\\<^sup>* T) \<and> Ide (U \<^sup>*\\\<^sup>* U') \<and> Ide (U' \<^sup>*\\\<^sup>* U)"
            using TU TT' UU' ide_char by blast
          show 4: "Ide ((T \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* U')"
            using TU T'U' TT' UU' 1 3
            by (metis (full_types) Srcs_Resid Con_Ide_iff Resid_Ide_Arr_ind seq_char)
          show 5: "Ide (U \<^sup>*\\\<^sup>* ((T' \<^sup>*\\\<^sup>* T) @ U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* T')))"
          proof -
            have "U \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* T) = U"
              by (metis (full_types) "3" TT' TU Con_Ide_iff Resid_Ide(1) Srcs_Resid
                  con_char seq_char prfx_implies_con)
            moreover have "U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* T') = U'"
              by (metis "3" "4" Ide.simps(1) Resid_Ide(1))
            ultimately show ?thesis
              by (metis "3" "4" Arr.simps(1) Con_append(2) Ide.simps(1) Resid_append(2)
                  TU Con_sym seq_char)
          qed
          show "Trgs ((T \<^sup>*\\\<^sup>* T') \<^sup>*\\\<^sup>* U') \<subseteq> Srcs (U \<^sup>*\\\<^sup>* (T' \<^sup>*\\\<^sup>* T @ U' \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* T')))"
            by (metis 4 5 Arr_append_iff\<^sub>P Ide.simps(1) Nil_is_append_conv
                calculation Con_imp_Arr_Resid)
        qed
        ultimately show "T @ U \<^sup>*\<lesssim>\<^sup>* T' @ U'"
          using ide_char by presburger
      qed
      show "T @ U \<^sup>*\<lesssim>\<^sup>* T' @ U'"
        using assms 2 by simp
      show "T' @ U' \<^sup>*\<lesssim>\<^sup>* T @ U"
        using assms 1 2 cong_symmetric by blast
    qed

    lemma cong_cons [intro]:
    assumes "seq [t] U" and "t \<sim> t'" and "U \<^sup>*\<sim>\<^sup>* U'"
    shows "t # U \<^sup>*\<sim>\<^sup>* t' # U'"
      using assms cong_append [of "[t]" U "[t']" U']
      by (simp add: R.prfx_implies_con ide_char)

    lemma cong_append_ideI [intro]:
    assumes "seq T U"
    shows "ide T \<Longrightarrow> T @ U \<^sup>*\<sim>\<^sup>* U" and "ide U \<Longrightarrow> T @ U \<^sup>*\<sim>\<^sup>* T"
    and "ide T \<Longrightarrow> U \<^sup>*\<sim>\<^sup>* T @ U" and "ide U \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* T @ U"
    proof -
      show 1: "ide T \<Longrightarrow> T @ U \<^sup>*\<sim>\<^sup>* U"
        using assms
        by (metis append_is_composite_of composite_ofE resid_arr_ide prfx_implies_con
            con_sym)
      show 2: "ide U \<Longrightarrow> T @ U \<^sup>*\<sim>\<^sup>* T"
        by (meson assms append_is_composite_of composite_ofE ide_backward_stable)
      show "ide T \<Longrightarrow> U \<^sup>*\<sim>\<^sup>* T @ U"
        using 1 cong_symmetric by auto
      show "ide U \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* T @ U"
        using 2 cong_symmetric by auto
    qed

    lemma cong_cons_ideI [intro]:
    assumes "seq [t] U" and "R.ide t"
    shows "t # U \<^sup>*\<sim>\<^sup>* U" and "U \<^sup>*\<sim>\<^sup>* t # U"
      using assms cong_append_ideI [of "[t]" U]
      by (auto simp add: ide_char)

    lemma prfx_decomp:
    assumes "[t] \<^sup>*\<lesssim>\<^sup>* [u]"
    shows "[t] @ [u \\ t] \<^sup>*\<sim>\<^sup>* [u]"
    proof
      (* TODO: I really want these to be doable by auto. *)
      show 1: "[u] \<^sup>*\<lesssim>\<^sup>* [t] @ [u \\ t]"
        using assms
        by (metis Con_imp_Arr_Resid Con_rec(3) Resid.simps(3) Resid_rec(3) R.con_sym
            append.left_neutral append_Cons arr_char cong_reflexive list.distinct(1))
      show "[t] @ [u \\ t] \<^sup>*\<lesssim>\<^sup>* [u]"
      proof -
        have "([t] @ [u \\ t]) \<^sup>*\\\<^sup>* [u] = ([t] \<^sup>*\\\<^sup>* [u]) @ ([u \\ t] \<^sup>*\\\<^sup>* [u \\ t])"
          using assms
          by (metis Arr_Resid_single Con_Arr_self Con_appendI(1) Con_sym Resid_append(1)
              Resid_rec(1) con_char list.discI prfx_implies_con)
        moreover have "Ide ..."
          using assms
          by (metis 1 Con_sym append_Nil2 arr_append_imp_seq calculation cong_append_ideI(4)
              ide_backward_stable Con_implies_Arr(2) Resid_Arr_self con_char ide_char
              prfx_implies_con arr_resid_iff_con)
        ultimately show ?thesis
          using ide_char by presburger
      qed
    qed

    lemma composite_of_single_single:
    assumes "R.composite_of t u v"
    shows "composite_of [t] [u] ([t] @ [u])"
    proof
      show "[t] \<^sup>*\<lesssim>\<^sup>* [t] @ [u]"
      proof -
        have "[t] \<^sup>*\\\<^sup>* ([t] @ [u]) = ([t] \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* [u]"
          using assms by auto
        moreover have "Ide ..."
          by (metis (no_types, lifting) Con_implies_Arr(2) R.bounded_imp_con
              R.con_composite_of_iff R.con_prfx_composite_of(1) assms resid_ide_arr
              Con_rec(1) Resid.simps(3) Resid_Arr_self con_char ide_char)
        ultimately show ?thesis
          using ide_char by presburger
      qed
      show "([t] @ [u]) \<^sup>*\\\<^sup>* [t] \<^sup>*\<sim>\<^sup>* [u]"
        using assms
        by (metis \<open>prfx [t] ([t] @ [u])\<close> append_is_composite_of arr_append_imp_seq
            composite_ofE con_def not_Cons_self2 Con_implies_Arr(2) arr_char null_char
            prfx_implies_con)
    qed

  end

  subsection "Paths in a Weakly Extensional RTS"

  locale paths_in_weakly_extensional_rts =
    R: weakly_extensional_rts +
    paths_in_rts
  begin

    lemma ex_un_Src:
    assumes "Arr T"
    shows "\<exists>!a. a \<in> Srcs T"
      using assms
      by (simp add: R.weakly_extensional_rts_axioms Srcs_simp\<^sub>P R.arr_has_un_source)

    fun Src
    where "Src T = R.src (hd T)"

    lemma Srcs_simp\<^sub>P\<^sub>W\<^sub>E:
    assumes "Arr T"
    shows "Srcs T = {Src T}"
    proof -
      have "[R.src (hd T)] \<in> sources T"
        by (metis Arr_imp_arr_hd Con_single_ide_ind Ide.simps(2) Srcs_simp\<^sub>P assms
                  con_char ide_char in_sourcesI con_sym R.ide_src R.src_in_sources)
      hence "R.src (hd T) \<in> Srcs T"
        using assms
        by (metis Srcs.elims Arr_has_Src list.sel(1) R.arr_iff_has_source R.src_in_sources)
      thus ?thesis
        using assms ex_un_Src by auto
    qed

    lemma ex_un_Trg:
    assumes "Arr T"
    shows "\<exists>!b. b \<in> Trgs T"
      using assms
      apply (induct T)
       apply auto[1]
      by (metis Con_Arr_self Ide_implies_Arr Resid_Arr_self Srcs_Resid ex_un_Src)

    fun Trg
    where "Trg [] = R.null"
        | "Trg [t] = R.trg t"
        | "Trg (t # T) = Trg T"

    lemma Trg_simp [simp]:
    shows "T \<noteq> [] \<Longrightarrow> Trg T = R.trg (last T)"
      apply (induct T)
       apply auto
      by (metis Trg.simps(3) list.exhaust_sel)

    lemma Trgs_simp\<^sub>P\<^sub>W\<^sub>E [simp]:
    assumes "Arr T"
    shows "Trgs T = {Trg T}"
      using assms
      by (metis Arr_imp_arr_last Con_Arr_self Con_imp_Arr_Resid R.trg_in_targets
          Srcs.simps(1) Srcs_Resid Srcs_simp\<^sub>P\<^sub>W\<^sub>E Trg_simp insertE insert_absorb insert_not_empty
          Trgs_simp\<^sub>P)

    lemma Src_resid [simp]:
    assumes "T \<^sup>*\<frown>\<^sup>* U"
    shows "Src (T \<^sup>*\\\<^sup>* U) = Trg U"
      using assms Con_imp_Arr_Resid Con_implies_Arr(2) Srcs_Resid Srcs_simp\<^sub>P\<^sub>W\<^sub>E by force

    lemma Trg_resid_sym:
    assumes "T \<^sup>*\<frown>\<^sup>* U"
    shows "Trg (T \<^sup>*\\\<^sup>* U) = Trg (U \<^sup>*\\\<^sup>* T)"
      using assms Con_imp_Arr_Resid Con_sym Trgs_Resid_sym by auto

    lemma Src_append [simp]:
    assumes "seq T U"
    shows "Src (T @ U) = Src T"
      using assms
      by (metis Arr.simps(1) Src.simps hd_append seq_char)

    lemma Trg_append [simp]:
    assumes "seq T U"
    shows "Trg (T @ U) = Trg U"
      using assms
      by (metis Ide.simps(1) Resid.simps(1) Trg_simp append_is_Nil_conv ide_char ide_trg
          last_appendR seqE trg_def)

    lemma Arr_append_iff\<^sub>P\<^sub>W\<^sub>E:
    assumes "T \<noteq> []" and "U \<noteq> []"
    shows "Arr (T @ U) \<longleftrightarrow> Arr T \<and> Arr U \<and> Trg T = Src U"
      using assms Arr_appendE\<^sub>P Srcs_simp\<^sub>P\<^sub>W\<^sub>E by auto

    lemma Arr_consI\<^sub>P\<^sub>W\<^sub>E [intro, simp]:
    assumes "R.arr t" and "Arr U" and "R.trg t = Src U"
    shows "Arr (t # U)"
      using assms
      by (metis Arr.simps(2) Srcs_simp\<^sub>P\<^sub>W\<^sub>E Trg.simps(2) Trgs.simps(2) Trgs_simp\<^sub>P\<^sub>W\<^sub>E
          dual_order.eq_iff Arr_consI\<^sub>P)

    lemma Arr_consE [elim]:
    assumes "Arr (t # U)"
    and "\<lbrakk>R.arr t; U \<noteq> [] \<Longrightarrow> Arr U; U \<noteq> [] \<Longrightarrow> R.trg t = Src U\<rbrakk> \<Longrightarrow> thesis"
    shows thesis
      using assms
      by (metis Arr_append_iff\<^sub>P\<^sub>W\<^sub>E Trg.simps(2) append_Cons append_Nil list.distinct(1)
          Arr.simps(2))

    lemma Arr_appendI\<^sub>P\<^sub>W\<^sub>E [intro, simp]:
    assumes "Arr T" and "Arr U" and "Trg T = Src U"
    shows "Arr (T @ U)"
      using assms
      by (metis Arr.simps(1) Arr_append_iff\<^sub>P\<^sub>W\<^sub>E)

    lemma Arr_appendE\<^sub>P\<^sub>W\<^sub>E [elim]:
    assumes "Arr (T @ U)" and "T \<noteq> []" and "U \<noteq> []"
    and "\<lbrakk>Arr T; Arr U; Trg T = Src U\<rbrakk> \<Longrightarrow> thesis"
    shows thesis
      using assms Arr_append_iff\<^sub>P\<^sub>W\<^sub>E seq_implies_Trgs_eq_Srcs by force

    lemma Ide_append_iff\<^sub>P\<^sub>W\<^sub>E:
    assumes "T \<noteq> []" and "U \<noteq> []"
    shows "Ide (T @ U) \<longleftrightarrow> Ide T \<and> Ide U \<and> Trg T = Src U"
      using assms Ide_char
      apply (intro iffI)
      by force auto

    lemma Ide_appendI\<^sub>P\<^sub>W\<^sub>E [intro, simp]:
    assumes "Ide T" and "Ide U" and "Trg T = Src U"
    shows "Ide (T @ U)"
      using assms
      by (metis Ide.simps(1) Ide_append_iff\<^sub>P\<^sub>W\<^sub>E)

    lemma Ide_appendE [elim]:
    assumes "Ide (T @ U)" and "T \<noteq> []" and "U \<noteq> []"
    and "\<lbrakk>Ide T; Ide U; Trg T = Src U\<rbrakk> \<Longrightarrow> thesis"
    shows thesis
      using assms Ide_append_iff\<^sub>P\<^sub>W\<^sub>E by metis

    lemma Ide_consI [intro, simp]:
    assumes "R.ide t" and "Ide U" and "R.trg t = Src U"
    shows "Ide (t # U)"
      using assms
      by (simp add: Ide_char)

    lemma Ide_consE [elim]:
    assumes "Ide (t # U)"
    and "\<lbrakk>R.ide t; U \<noteq> [] \<Longrightarrow> Ide U; U \<noteq> [] \<Longrightarrow> R.trg t = Src U\<rbrakk> \<Longrightarrow> thesis"
    shows thesis
      using assms
      by (metis Con_rec(4) Ide.simps(2) Ide_imp_Ide_hd Ide_imp_Ide_tl R.trg_def R.trg_ide
          Resid_Arr_Ide_ind Trg.simps(2) ide_char list.sel(1) list.sel(3) list.simps(3)
          Src_resid ide_def)

    lemma Ide_imp_Src_eq_Trg:
    assumes "Ide T"
    shows "Src T = Trg T"
      using assms
      by (metis Ide.simps(1) Src_resid ide_char ide_def)

  end

  subsection "Paths in a Confluent RTS"

  text \<open>
    Here we show that confluence of an RTS extends to  confluence of the RTS of its paths.
  \<close>

  locale paths_in_confluent_rts =
    paths_in_rts +
    R: confluent_rts
  begin

    lemma confluence_single:
    assumes "\<And>t u. R.coinitial t u \<Longrightarrow> t \<frown> u"
    shows "\<lbrakk>R.arr t; Arr U; R.sources t = Srcs U\<rbrakk> \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* U"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>R.arr t; Arr []; R.sources t = Srcs []\<rbrakk> \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* []"
        by simp
      fix t u U
      assume ind: "\<And>t. \<lbrakk>R.arr t; Arr U; R.sources t = Srcs U\<rbrakk> \<Longrightarrow> [t] \<^sup>*\<frown>\<^sup>* U"
      assume t: "R.arr t"
      assume uU: "Arr (u # U)"
      assume coinitial: "R.sources t = Srcs (u # U)"
      hence 1: "R.coinitial t u"
        using t uU
        by (metis Arr.simps(2) Con_implies_Arr(1) Con_imp_eq_Srcs Con_initial_left
            Srcs.simps(2) Con_Arr_self R.coinitial_iff)
      show "[t] \<^sup>*\<frown>\<^sup>* u # U"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using assms t uU coinitial R.coinitial_iff by fastforce
        assume U: "U \<noteq> []"
        show ?thesis
        proof -
          have 2: "Arr [t \\ u] \<and> Arr U \<and> Srcs [t \\ u] = Srcs U"
            using assms 1 t uU U R.arr_resid_iff_con
            apply (intro conjI)
              apply simp
             apply (metis Con_Arr_self Con_implies_Arr(2) Resid_cons(2))
            by (metis (full_types) Con_cons(2) Srcs.simps(2) Srcs_Resid Trgs.simps(2)
                Con_Arr_self Con_imp_eq_Srcs list.simps(3) R.sources_resid)
          have "[t] \<^sup>*\<frown>\<^sup>* u # U \<longleftrightarrow> t \<frown> u \<and> [t \\ u] \<^sup>*\<frown>\<^sup>* U"
            using U Con_rec(3) [of U t u] by simp
          also have "... \<longleftrightarrow> True"
            using assms t uU U 1 2 ind by force
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma confluence_ind:
    shows "\<lbrakk>Arr T; Arr U; Srcs T = Srcs U\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U"
    proof (induct T arbitrary: U)
      show "\<And>U. \<lbrakk>Arr []; Arr U; Srcs [] = Srcs U\<rbrakk> \<Longrightarrow> [] \<^sup>*\<frown>\<^sup>* U"
        by simp
      fix t T U
      assume ind: "\<And>U. \<lbrakk>Arr T; Arr U; Srcs T = Srcs U\<rbrakk> \<Longrightarrow> T \<^sup>*\<frown>\<^sup>* U"
      assume tT: "Arr (t # T)"
      assume U: "Arr U"
      assume coinitial: "Srcs (t # T) = Srcs U"
      show "t # T \<^sup>*\<frown>\<^sup>* U"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using U tT coinitial confluence_single [of t U] R.confluence by simp
        assume T: "T \<noteq> []"
        show ?thesis
        proof -
          have 1: "[t] \<^sup>*\<frown>\<^sup>* U"
            using tT U coinitial R.confluence
            by (metis R.arr_def Srcs.simps(2) T Con_Arr_self Con_imp_eq_Srcs
                Con_initial_right Con_rec(4) confluence_single)
          moreover have "T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]"
            using 1 tT U T coinitial ind [of "U \<^sup>*\\\<^sup>* [t]"]
            by (metis (full_types) Con_imp_Arr_Resid Arr_iff_Con_self Con_implies_Arr(2)
                Con_imp_eq_Srcs Con_sym R.sources_resid Srcs.simps(2) Srcs_Resid
                Trgs.simps(2) Con_rec(4))
          ultimately show ?thesis
            using Con_cons(1) [of T U t] by fastforce
        qed
      qed
    qed

    lemma confluence\<^sub>P:
    assumes "coinitial T U"
    shows "con T U"
      using assms confluence_ind sources_char\<^sub>P coinitial_def con_char by auto

    sublocale confluent_rts Resid
      apply (unfold_locales)
      using confluence\<^sub>P by simp

    lemma is_confluent_rts:
    shows "confluent_rts Resid"
      ..

  end

  subsection "Simulations Lift to Paths"

  text \<open>
    In this section we show that a simulation from RTS \<open>A\<close> to RTS \<open>B\<close> determines a simulation
    from the RTS of paths in \<open>A\<close> to the RTS of paths in \<open>B\<close>.  In other words, the path-RTS
    construction is functorial with respect to simulation.
  \<close>

  context simulation
  begin

    interpretation P\<^sub>A: paths_in_rts A
      ..
    interpretation P\<^sub>B: paths_in_rts B
      ..

    lemma map_Resid_single:
    shows "P\<^sub>A.con T [u] \<Longrightarrow> map F (P\<^sub>A.Resid T [u]) = P\<^sub>B.Resid (map F T) [F u]"
      apply (induct T arbitrary: u)
       apply simp
    proof -
      fix t u T
      assume ind: "\<And>u. P\<^sub>A.con T [u] \<Longrightarrow> map F (P\<^sub>A.Resid T [u]) = P\<^sub>B.Resid (map F T) [F u]"
      assume 1: "P\<^sub>A.con (t # T) [u]"
      show "map F (P\<^sub>A.Resid (t # T) [u]) = P\<^sub>B.Resid (map F (t # T)) [F u]"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using "1" P\<^sub>A.null_char by fastforce
        assume T: "T \<noteq> []"
        show ?thesis
          using T 1 ind P\<^sub>A.con_def P\<^sub>A.null_char P\<^sub>A.Con_rec(2) P\<^sub>A.Resid_rec(2) P\<^sub>B.Con_rec(2)
                P\<^sub>B.Resid_rec(2)
          apply simp
          by (metis A.con_sym Nil_is_map_conv preserves_con preserves_resid)
      qed
    qed

    lemma map_Resid:
    shows "P\<^sub>A.con T U \<Longrightarrow> map F (P\<^sub>A.Resid T U) = P\<^sub>B.Resid (map F T) (map F U)"
      apply (induct U arbitrary: T)
      using P\<^sub>A.Resid.simps(1) P\<^sub>A.con_char P\<^sub>A.con_sym
       apply blast
    proof -
      fix u U T
      assume ind: "\<And>T. P\<^sub>A.con T U \<Longrightarrow>
                          map F (P\<^sub>A.Resid T U) = P\<^sub>B.Resid (map F T) (map F U)"
      assume 1: "P\<^sub>A.con T (u # U)"
      show "map F (P\<^sub>A.Resid T (u # U)) = P\<^sub>B.Resid (map F T) (map F (u # U))"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using "1" map_Resid_single by force
        assume U: "U \<noteq> []"
        have "P\<^sub>B.Resid (map F T) (map F (u # U)) =
              P\<^sub>B.Resid (P\<^sub>B.Resid (map F T) [F u]) (map F U)"
          using U 1 P\<^sub>B.Resid_cons(2)
          apply simp
          by (metis P\<^sub>B.Arr.simps(1) P\<^sub>B.Con_consI(2) P\<^sub>B.Con_implies_Arr(1) list.map_disc_iff)
        also have "... = map F (P\<^sub>A.Resid (P\<^sub>A.Resid T [u]) U)"
          using U 1 ind
          by (metis P\<^sub>A.Con_initial_right P\<^sub>A.Resid_cons(2) P\<^sub>A.con_char map_Resid_single)
        also have "... = map F (P\<^sub>A.Resid T (u # U))"
          using "1" P\<^sub>A.Resid_cons(2) P\<^sub>A.con_char U by auto
        finally show ?thesis by simp
      qed
    qed

    lemma preserves_paths:
    shows "P\<^sub>A.Arr T \<Longrightarrow> P\<^sub>B.Arr (map F T)"
      by (metis P\<^sub>A.Con_Arr_self P\<^sub>A.conI\<^sub>P P\<^sub>B.Arr_iff_Con_self map_Resid map_is_Nil_conv)

    interpretation Fx: simulation P\<^sub>A.Resid P\<^sub>B.Resid \<open>\<lambda>T. if P\<^sub>A.Arr T then map F T else []\<close>
    proof
      let ?Fx = "\<lambda>T. if P\<^sub>A.Arr T then map F T else []"
      show "\<And>T. \<not> P\<^sub>A.arr T \<Longrightarrow> ?Fx T = P\<^sub>B.null"
        by (simp add: P\<^sub>A.arr_char P\<^sub>B.null_char)
      show "\<And>T U. P\<^sub>A.con T U \<Longrightarrow> P\<^sub>B.con (?Fx T) (?Fx U)"
        using P\<^sub>A.Con_implies_Arr(1) P\<^sub>A.Con_implies_Arr(2) P\<^sub>A.con_char map_Resid by fastforce
      show "\<And>T U. P\<^sub>A.con T U \<Longrightarrow> ?Fx (P\<^sub>A.Resid T U) = P\<^sub>B.Resid (?Fx T) (?Fx U)"
        by (simp add: P\<^sub>A.Con_imp_Arr_Resid P\<^sub>A.Con_implies_Arr(1) P\<^sub>A.Con_implies_Arr(2)
            P\<^sub>A.con_char map_Resid)
    qed

    lemma lifts_to_paths:
    shows "simulation P\<^sub>A.Resid P\<^sub>B.Resid (\<lambda>T. if P\<^sub>A.Arr T then map F T else [])"
      ..

  end

  subsection "Normal Sub-RTS's Lift to Paths"

  text \<open>
    Here we show that a normal sub-RTS \<open>N\<close> of an RTS \<open>R\<close> lifts to a normal sub-RTS
    of the RTS of paths in \<open>N\<close>, and that it is coherent if \<open>N\<close> is.
  \<close>

  locale paths_in_rts_with_normal =
    R: rts +
    N: normal_sub_rts +
    paths_in_rts
  begin

    text \<open>
      We define a ``normal path'' to be a path that consists entirely of normal transitions.
      We show that the collection of all normal paths is a normal sub-RTS of the RTS of paths.
    \<close>

    definition NPath
    where "NPath T \<equiv> (Arr T \<and> set T \<subseteq> \<NN>)"

    lemma Ide_implies_NPath:
    assumes "Ide T"
    shows "NPath T"
      using assms
      by (metis Ball_Collect NPath_def Ide_implies_Arr N.ide_closed set_Ide_subset_ide
          subsetI)

    lemma NPath_implies_Arr:
    assumes "NPath T"
    shows "Arr T"
      using assms NPath_def by simp

    lemma NPath_append:
    assumes "T \<noteq> []" and "U \<noteq> []"
    shows "NPath (T @ U) \<longleftrightarrow> NPath T \<and> NPath U \<and> Trgs T \<subseteq> Srcs U"
      using assms NPath_def by auto
      
    lemma NPath_appendI [intro, simp]:
    assumes "NPath T" and "NPath U" and "Trgs T \<subseteq> Srcs U"
    shows "NPath (T @ U)"
      using assms NPath_def by simp

    lemma NPath_Resid_single_Arr:
    shows "\<lbrakk>t \<in> \<NN>; Arr U; R.sources t = Srcs U\<rbrakk> \<Longrightarrow> NPath (Resid [t] U)"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>t \<in> \<NN>; Arr []; R.sources t = Srcs []\<rbrakk> \<Longrightarrow> NPath (Resid [t] [])"
        by simp
      fix t u U
      assume ind: "\<And>t. \<lbrakk>t \<in> \<NN>; Arr U; R.sources t = Srcs U\<rbrakk> \<Longrightarrow> NPath (Resid [t] U)"
      assume t: "t \<in> \<NN>"
      assume uU: "Arr (u # U)"
      assume src: "R.sources t = Srcs (u # U)"
      show "NPath (Resid [t] (u # U))"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using NPath_def t src
          apply simp
          by (metis Arr.simps(2) R.arr_resid_iff_con R.coinitialI N.forward_stable
              N.elements_are_arr uU)
        assume U: "U \<noteq> []"
        show ?thesis
        proof -
          have "NPath (Resid [t] (u # U)) \<longleftrightarrow> NPath (Resid [t \\ u] U)"
            using t U uU src
            by (metis Arr.simps(2) Con_implies_Arr(1) Resid_rec(3) Con_rec(3) R.arr_resid_iff_con)
          also have "... \<longleftrightarrow> True"
          proof -
            have "t \\ u \<in> \<NN>"
              using t U uU src N.forward_stable [of t u]
              by (metis Con_Arr_self Con_imp_eq_Srcs Con_initial_left
                        Srcs.simps(2) inf.idem Arr_has_Src R.coinitial_def)
            moreover have "Arr U"
              using U uU
              by (metis Arr.simps(3) neq_Nil_conv)
            moreover have "R.sources (t \\ u) = Srcs U"
              using t uU src
              by (metis Con_Arr_self Srcs.simps(2) U calculation(1) Con_imp_eq_Srcs
                        Con_rec(4) N.elements_are_arr R.sources_resid R.arr_resid_iff_con)
            ultimately show ?thesis
              using ind [of "t \\ u"] by simp
          qed
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma NPath_Resid_Arr_single:
    shows "\<lbrakk> NPath T; R.arr u; Srcs T = R.sources u \<rbrakk> \<Longrightarrow> NPath (Resid T [u])"
    proof (induct T arbitrary: u)
      show "\<And>u. \<lbrakk>NPath []; R.arr u; Srcs [] = R.sources u\<rbrakk> \<Longrightarrow> NPath (Resid [] [u])"
        by simp
      fix t u T
      assume ind: "\<And>u. \<lbrakk>NPath T; R.arr u; Srcs T = R.sources u\<rbrakk> \<Longrightarrow> NPath (Resid T [u])"
      assume tT: "NPath (t # T)"
      assume u: "R.arr u"
      assume src: "Srcs (t # T) = R.sources u"
      show "NPath (Resid (t # T) [u])"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT u src NPath_def
          by (metis Arr.simps(2) NPath_Resid_single_Arr Srcs.simps(2) list.set_intros(1) subsetD)
        assume T: "T \<noteq> []"
        have "R.coinitial u t"
          by (metis R.coinitialI Srcs.simps(3) T list.exhaust_sel src u)
        hence con: "t \<frown> u"
          using tT T u src R.con_sym NPath_def
          by (metis N.forward_stable N.elements_are_arr R.not_arr_null
              list.set_intros(1) R.conI subsetD)
        have 1: "NPath (Resid (t # T) [u]) \<longleftrightarrow> NPath ((t \\ u) # Resid T [u \\ t])"
        proof -
          have "t # T \<^sup>*\<frown>\<^sup>* [u]"
          proof -
            have 2: "[t] \<^sup>*\<frown>\<^sup>* [u]"
              by (simp add: Con_rec(1) con)
            moreover have "T \<^sup>*\<frown>\<^sup>* Resid [u] [t]"
            proof -
              have "NPath T"
                using tT T NPath_def
                by (metis NPath_append append_Cons append_Nil)
              moreover have 3: "R.arr (u \\ t)"
                using con by (meson R.arr_resid_iff_con R.con_sym)
              moreover have "Srcs T = R.sources (u \\ t)"
                using tT T u src con
                by (metis "3" Arr_iff_Con_self Con_cons(2) Con_imp_eq_Srcs
                    R.sources_resid Srcs_Resid Trgs.simps(2) NPath_implies_Arr list.discI
                    R.arr_resid_iff_con)
              ultimately show ?thesis
                using 2 ind [of "u \\ t"] NPath_def by auto
            qed
            ultimately show ?thesis
              using tT T u src Con_cons(1) [of T "[u]" t] by simp
          qed
          thus ?thesis
            using tT T u src Resid_cons(1) [of T t "[u]"] Resid_rec(2) by presburger
        qed
        also have "... \<longleftrightarrow> True"
        proof -
          have 2: "t \\ u \<in> \<NN> \<and> R.arr (u \\ t)"
            using tT u src con NPath_def
            by (meson R.arr_resid_iff_con R.con_sym N.forward_stable \<open>R.coinitial u t\<close>
                list.set_intros(1) subsetD)
          moreover have 3: "NPath (T \<^sup>*\\\<^sup>* [u \\ t])"
            using tT ind [of "u \\ t"] NPath_def
            by (metis Con_Arr_self Con_imp_eq_Srcs Con_rec(4) R.arr_resid_iff_con
                R.sources_resid Srcs.simps(2) T calculation insert_subset list.exhaust
                list.simps(15) Arr.simps(3))
          moreover have "R.targets (t \\ u) \<subseteq> Srcs (Resid T [u \\ t])"
            using tT T u src NPath_def
            by (metis "3" Arr.simps(1) R.targets_resid_sym Srcs_Resid_Arr_single con subset_refl)
          ultimately show ?thesis
            using NPath_def
            by (metis Arr_consI\<^sub>P N.elements_are_arr insert_subset list.simps(15))
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma NPath_Resid [simp]:
    shows "\<lbrakk>NPath T; Arr U; Srcs T = Srcs U\<rbrakk> \<Longrightarrow> NPath (T \<^sup>*\\\<^sup>* U)"
    proof (induct T arbitrary: U)
      show "\<And>U. \<lbrakk>NPath []; Arr U; Srcs [] = Srcs U\<rbrakk> \<Longrightarrow> NPath ([] \<^sup>*\\\<^sup>* U)"
        by simp
      fix t T U
      assume ind: "\<And>U. \<lbrakk>NPath T; Arr U; Srcs T = Srcs U\<rbrakk> \<Longrightarrow> NPath (T \<^sup>*\\\<^sup>* U)"
      assume tT: "NPath (t # T)"
      assume U: "Arr U"
      assume Coinitial: "Srcs (t # T) = Srcs U"
      show "NPath ((t # T) \<^sup>*\\\<^sup>* U)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT U Coinitial NPath_Resid_single_Arr [of t U] NPath_def by force
        assume T: "T \<noteq> []"
        have 0: "NPath ((t # T) \<^sup>*\\\<^sup>* U) \<longleftrightarrow> NPath ([t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
        proof -
          have "U \<noteq> []"
            using U by auto
          moreover have "(t # T) \<^sup>*\<frown>\<^sup>* U"
          proof -
            have "t \<in> \<NN>"
              using tT NPath_def by auto
            moreover have "R.sources t = Srcs U"
              using Coinitial
              by (metis Srcs.elims U list.sel(1) Arr_has_Src)
            ultimately have 1: "[t] \<^sup>*\<frown>\<^sup>* U"
              using U NPath_Resid_single_Arr [of t U] NPath_def by auto
            moreover have "T \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
            proof -
              have "Srcs T = Srcs (U \<^sup>*\\\<^sup>* [t])"
                using tT U Coinitial 1
                by (metis Con_Arr_self Con_cons(2) Con_imp_eq_Srcs Con_sym Srcs_Resid_Arr_single
                    T list.discI NPath_implies_Arr)
              hence "NPath (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
                using tT U Coinitial 1 Con_sym ind [of "Resid U [t]"] NPath_def
                by (metis Con_imp_Arr_Resid Srcs.elims T insert_subset list.simps(15)
                    Arr.simps(3))
              thus ?thesis
                using NPath_def by auto
            qed
            ultimately show ?thesis
              using Con_cons(1) [of T U t] by fastforce
          qed
          ultimately show ?thesis
            using tT U T Coinitial Resid_cons(1) by auto
        qed
        also have "... \<longleftrightarrow> True"
        proof (intro iffI, simp_all)
          have 1: "NPath ([t] \<^sup>*\\\<^sup>* U)"
            by (metis Coinitial NPath_Resid_single_Arr Srcs_simp\<^sub>P U insert_subset
                list.sel(1) list.simps(15) NPath_def tT)
          moreover have 2: "NPath (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
            by (metis "0" Arr.simps(1) Con_cons(1) Con_imp_eq_Srcs Con_implies_Arr(1-2)
                NPath_def T append_Nil2 calculation ind insert_subset list.simps(15) tT)
          moreover have "Trgs ([t] \<^sup>*\\\<^sup>* U) \<subseteq> Srcs (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
            by (metis Arr.simps(1) NPath_def Srcs_Resid Trgs_Resid_sym calculation(2)
                dual_order.refl)
          ultimately show "NPath ([t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
            using NPath_append [of "T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])" "[t] \<^sup>*\\\<^sup>* U"] by fastforce
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma Backward_stable_single:
    shows "\<lbrakk>NPath U; NPath ([t] \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath [t]"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>NPath []; NPath ([t] \<^sup>*\\\<^sup>* [])\<rbrakk> \<Longrightarrow> NPath [t]"
        using NPath_def by simp
      fix t u U
      assume ind: "\<And>t. \<lbrakk>NPath U; NPath ([t] \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath [t]"
      assume uU: "NPath (u # U)"
      assume resid: "NPath ([t] \<^sup>*\\\<^sup>* (u # U))"
      show "NPath [t]"
        using uU ind NPath_def
        by (metis Arr.simps(1) Arr.simps(2) Con_implies_Arr(2) N.backward_stable
            N.elements_are_arr Resid_rec(1) Resid_rec(3) insert_subset list.simps(15) resid)
    qed

    lemma Backward_stable:
    shows "\<lbrakk>NPath U; NPath (T \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath T"
    proof (induct T arbitrary: U)
      show "\<And>U. \<lbrakk>NPath U; NPath ([] \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath []"
        by simp
      fix t T U
      assume ind: "\<And>U. \<lbrakk>NPath U; NPath (T \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath T"
      assume U: "NPath U"
      assume resid: "NPath ((t # T) \<^sup>*\\\<^sup>* U)"
      show "NPath (t # T)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using U resid Backward_stable_single by blast
        assume T: "T \<noteq> []"
        have 1: "NPath ([t] \<^sup>*\\\<^sup>* U) \<and> NPath (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
          using T U NPath_append resid NPath_def
          by (metis Arr.simps(1) Con_cons(1) Resid_cons(1))
        have 2: "t \<in> \<NN>"
          using 1 U Backward_stable_single NPath_def by simp
        moreover have "NPath T"
          using 1 U resid ind
          by (metis 2 Arr.simps(2) Con_imp_eq_Srcs NPath_Resid N.elements_are_arr)
        moreover have "R.targets t \<subseteq> Srcs T"
          using resid 1 Con_imp_eq_Srcs Con_sym Srcs_Resid_Arr_single NPath_def
          by (metis Arr.simps(1) dual_order.eq_iff)
        ultimately show ?thesis
          using NPath_def
          by (simp add: N.elements_are_arr)
      qed
    qed

    sublocale normal_sub_rts Resid \<open>Collect NPath\<close>
      using Ide_implies_NPath NPath_implies_Arr arr_char ide_char coinitial_def
            sources_char\<^sub>P append_is_composite_of
      apply unfold_locales
           apply auto
      using Backward_stable
      by metis+

    theorem normal_extends_to_paths:
    shows "normal_sub_rts Resid (Collect NPath)"
      ..

    lemma Resid_NPath_preserves_reflects_Con:
    assumes "NPath U" and "Srcs T = Srcs U"
    shows "T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* T'"
      using assms NPath_def NPath_Resid con_char con_imp_coinitial resid_along_elem_preserves_con
            Con_implies_Arr(2) Con_sym Cube(1)
      by (metis Arr.simps(1) mem_Collect_eq)

    notation Cong\<^sub>0  (infix "\<approx>\<^sup>*\<^sub>0" 50)
    notation Cong  (infix "\<approx>\<^sup>*" 50)

    (*
     * TODO: Leave these for now -- they still seem a little difficult to prove
     * in this context, but are probably useful.
     *)
    lemma Cong\<^sub>0_cancel_left\<^sub>C\<^sub>S:
    assumes "T @ U \<approx>\<^sup>*\<^sub>0 T @ U'" and "T \<noteq> []" and "U \<noteq> []" and "U' \<noteq> []"
    shows "U \<approx>\<^sup>*\<^sub>0 U'"
      using assms Cong\<^sub>0_cancel_left [of T U "T @ U" U' "T @ U'"] Cong\<^sub>0_reflexive
            append_is_composite_of
      by (metis Cong\<^sub>0_implies_Cong Cong_imp_arr(1) arr_append_imp_seq)

    lemma Srcs_respects_Cong:
    assumes "T \<approx>\<^sup>* T'" and "a \<in> Srcs T" and "a' \<in> Srcs T'"
    shows "[a] \<approx>\<^sup>* [a']"
    proof -
      obtain U U' where UU': "NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U'"
        using assms(1) by blast
      show ?thesis
      proof
        show "U \<in> Collect NPath"
          using UU' by simp
        show "U' \<in> Collect NPath"
          using UU' by simp
        show "[a] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [a'] \<^sup>*\\\<^sup>* U'"
        proof -
          have "NPath ([a] \<^sup>*\\\<^sup>* U) \<and> NPath ([a'] \<^sup>*\\\<^sup>* U')"
            by (metis Arr.simps(1) Con_imp_eq_Srcs Con_implies_Arr(1) Con_single_ide_ind
                NPath_implies_Arr N.ide_closed R.in_sourcesE Srcs.simps(2) Srcs_simp\<^sub>P
                UU' assms(2-3) elements_are_arr not_arr_null null_char NPath_Resid_single_Arr)
          thus ?thesis
            using UU'
            by (metis Con_imp_eq_Srcs Cong\<^sub>0_imp_con NPath_Resid Srcs_Resid
                con_char NPath_implies_Arr mem_Collect_eq arr_resid_iff_con con_implies_arr(2))
        qed
      qed
    qed

    lemma Trgs_respects_Cong:
    assumes "T \<approx>\<^sup>* T'" and "b \<in> Trgs T" and "b' \<in> Trgs T'"
    shows "[b] \<approx>\<^sup>* [b']"
    proof -
      have "[b] \<in> targets T \<and> [b'] \<in> targets T'"
      proof -
        have 1: "Ide [b] \<and> Ide [b']"
          using assms
          by (metis Ball_Collect Trgs_are_ide Ide.simps(2))
        moreover have "Srcs [b] = Trgs T"
          using assms
          by (metis 1 Con_imp_Arr_Resid Con_imp_eq_Srcs Cong_imp_arr(1) Ide.simps(2)
              Srcs_Resid Con_single_ide_ind con_char arrE)
        moreover have "Srcs [b'] = Trgs T'"
          using assms
          by (metis Con_imp_Arr_Resid Con_imp_eq_Srcs Cong_imp_arr(2) Ide.simps(2)
              Srcs_Resid 1 Con_single_ide_ind con_char arrE)
        ultimately show ?thesis
          unfolding targets_char\<^sub>P
          using assms Cong_imp_arr(2) arr_char by blast
      qed
      thus ?thesis
        using assms targets_char in_targets_respects_Cong [of T T' "[b]" "[b']"] by simp
    qed

    lemma Cong\<^sub>0_append_resid_NPath:
    assumes "NPath (T \<^sup>*\\\<^sup>* U)"
    shows "Cong\<^sub>0 (T @ (U \<^sup>*\\\<^sup>* T)) U"
    proof (intro conjI)
      show 0: "(T @ U \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* U \<in> Collect NPath"
      proof -
        have 1: "(T @ U \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* U = T \<^sup>*\\\<^sup>* U @ (U \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T)"
          by (metis Arr.simps(1) NPath_implies_Arr assms Con_append(1) Con_implies_Arr(2)
              Con_sym Resid_append(1) con_imp_arr_resid null_char)
        moreover have "NPath ..."
          using assms
          by (metis 1 Arr_append_iff\<^sub>P NPath_append NPath_implies_Arr Ide_implies_NPath
              Nil_is_append_conv Resid_Arr_self arr_char con_char arr_resid_iff_con
              self_append_conv)
        ultimately show ?thesis by simp
      qed
      show "U \<^sup>*\\\<^sup>* (T @ U \<^sup>*\\\<^sup>* T) \<in> Collect NPath"
        using assms 0
        by (metis Arr.simps(1) Con_implies_Arr(2) Cong\<^sub>0_reflexive Resid_append(2)
            append.right_neutral arr_char Con_sym)
    qed

  end

  locale paths_in_rts_with_coherent_normal =
    R: rts +
    N: coherent_normal_sub_rts +
    paths_in_rts
  begin

    sublocale paths_in_rts_with_normal resid \<NN> ..

    notation Cong\<^sub>0  (infix "\<approx>\<^sup>*\<^sub>0" 50)
    notation Cong  (infix "\<approx>\<^sup>*" 50)

    text \<open>
      Since composites of normal transitions are assumed to exist, normal paths can be
      ``folded'' by composition down to single transitions.
    \<close>

    lemma NPath_folding:
    shows "NPath U \<Longrightarrow> \<exists>u. u \<in> \<NN> \<and> R.sources u = Srcs U \<and> R.targets u = Trgs U \<and>
                           (\<forall>t. con [t] U \<longrightarrow> [t] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [t \\ u])"
    proof (induct U)
      show "NPath [] \<Longrightarrow> \<exists>u. u \<in> \<NN> \<and> R.sources u = Srcs [] \<and> R.targets u = Trgs [] \<and>
                             (\<forall>t. con [t] [] \<longrightarrow> [t] \<^sup>*\\\<^sup>* [] \<approx>\<^sup>*\<^sub>0 [t \\ u])"
        using NPath_def by auto
      fix v U
      assume ind: "NPath U \<Longrightarrow> \<exists>u. u \<in> \<NN> \<and> R.sources u = Srcs U \<and> R.targets u = Trgs U \<and>
                                   (\<forall>t. con [t] U \<longrightarrow> [t] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [t \\ u])"
      assume vU: "NPath (v # U)"
      show "\<exists>vU. vU \<in> \<NN> \<and> R.sources vU = Srcs (v # U) \<and> R.targets vU = Trgs (v # U) \<and>
                 (\<forall>t. con [t] (v # U) \<longrightarrow> [t] \<^sup>*\\\<^sup>* (v # U) \<approx>\<^sup>*\<^sub>0 [t \\ vU])"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> \<exists>vU. vU \<in> \<NN> \<and> R.sources vU = Srcs (v # U) \<and>
                              R.targets vU = Trgs (v # U) \<and>
                              (\<forall>t. con [t] (v # U) \<longrightarrow> [t] \<^sup>*\\\<^sup>* (v # U) \<approx>\<^sup>*\<^sub>0 [t \\ vU])"
          using vU Resid_rec(1) con_char
          by (metis Cong\<^sub>0_reflexive NPath_def Srcs.simps(2) Trgs.simps(2) arr_resid_iff_con
              insert_subset list.simps(15))
        assume "U \<noteq> []"
        hence U: "NPath U"
          using vU by (metis NPath_append append_Cons append_Nil)
        obtain u where u: "u \<in> \<NN> \<and> R.sources u = Srcs U \<and> R.targets u = Trgs U \<and>
                           (\<forall>t. con [t] U \<longrightarrow> [t] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [t \\ u])"
          using U ind by blast
        have seq: "R.seq v u"
        proof
          show "R.arr u"
            by (simp add: N.elements_are_arr u)
          show "R.targets v = R.sources u"
            by (metis (full_types) NPath_implies_Arr R.sources_resid Srcs.simps(2) \<open>U \<noteq> []\<close>
                Con_Arr_self Con_imp_eq_Srcs Con_initial_right Con_rec(2) u vU)
        qed
        obtain vu where vu: "R.composite_of v u vu"
          using N.composite_closed_right seq u by presburger
        have "vu \<in> \<NN> \<and> R.sources vu = Srcs (v # U) \<and> R.targets vu = Trgs (v # U) \<and>
              (\<forall>t. con [t] (v # U) \<longrightarrow> [t] \<^sup>*\\\<^sup>* (v # U) \<approx>\<^sup>*\<^sub>0 [t \\ vu])"
        proof (intro conjI allI)
          show "vu \<in> \<NN>"
            by (meson NPath_def N.composite_closed list.set_intros(1) subsetD u vU vu)
          show "R.sources vu = Srcs (v # U)"
            by (metis Con_imp_eq_Srcs Con_initial_right NPath_implies_Arr
                      R.sources_composite_of Srcs.simps(2) Arr_iff_Con_self vU vu)
          show "R.targets vu = Trgs (v # U)"
            by (metis R.targets_composite_of Trgs.simps(3) \<open>U \<noteq> []\<close> list.exhaust_sel u vu)
          fix t
          show "con [t] (v # U) \<longrightarrow> [t] \<^sup>*\\\<^sup>* (v # U) \<approx>\<^sup>*\<^sub>0 [t \\ vu]"
          proof (intro impI)
            assume t: "con [t] (v # U)"
            have 1: "[t] \<^sup>*\\\<^sup>* (v # U) = [t \\ v] \<^sup>*\\\<^sup>* U"
              using t Resid_rec(3) \<open>U \<noteq> []\<close> con_char by force
            also have "... \<approx>\<^sup>*\<^sub>0 [(t \\ v) \\ u]"
              using 1 t u by force
            also have "[(t \\ v) \\ u] \<approx>\<^sup>*\<^sub>0 [t \\ vu]"
            proof -
              have "(t \\ v) \\ u \<sim> t \\ vu"
                using vu R.resid_composite_of
                by (metis (no_types, lifting) N.Cong\<^sub>0_composite_of_arr_normal N.Cong\<^sub>0_subst_right(1)
                    \<open>U \<noteq> []\<close> Con_rec(3) con_char R.con_sym t u)
              thus ?thesis
                using Ide.simps(2) R.prfx_implies_con Resid.simps(3) ide_char ide_closed
                by presburger
            qed
            finally show "[t] \<^sup>*\\\<^sup>* (v # U) \<approx>\<^sup>*\<^sub>0 [t \\ vu]" by blast
          qed
        qed
        thus ?thesis by blast
      qed
    qed

    text \<open>
      Coherence for single transitions extends inductively to paths.
    \<close>

    lemma Coherent_single:
    assumes "R.arr t" and "NPath U" and "NPath U'"
    and "R.sources t = Srcs U" and "Srcs U = Srcs U'" and "Trgs U = Trgs U'"
    shows "[t] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [t] \<^sup>*\\\<^sup>* U'"
    proof -
      have 1: "con [t] U \<and> con [t] U'"
        using assms
        by (metis Arr.simps(1-2) Arr_iff_Con_self Resid_NPath_preserves_reflects_Con
            Srcs.simps(2) con_char)
      obtain u where u: "u \<in> \<NN> \<and> R.sources u = Srcs U \<and> R.targets u = Trgs U \<and>
                         (\<forall>t. con [t] U \<longrightarrow> [t] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [t \\ u])"
        using assms NPath_folding by metis
      obtain u' where u': "u' \<in> \<NN> \<and> R.sources u' = Srcs U' \<and> R.targets u' = Trgs U' \<and>
                           (\<forall>t. con [t] U' \<longrightarrow> [t] \<^sup>*\\\<^sup>* U' \<approx>\<^sup>*\<^sub>0 [t \\ u'])"
        using assms NPath_folding by metis
      have "[t] \<^sup>*\\\<^sup>* U  \<approx>\<^sup>*\<^sub>0 [t \\ u]"
        using u 1 by blast
      also have "[t \\ u] \<approx>\<^sup>*\<^sub>0 [t \\ u']"
        using assms(1,4-6) N.Cong\<^sub>0_imp_con N.coherent u u' NPath_def by simp
      also have "[t \\ u'] \<approx>\<^sup>*\<^sub>0 [t] \<^sup>*\\\<^sup>* U'"
        using u' 1 by simp
      finally show ?thesis by simp
    qed

    lemma Coherent:
    shows "\<lbrakk> Arr T; NPath U; NPath U'; Srcs T = Srcs U;
             Srcs U = Srcs U'; Trgs U = Trgs U' \<rbrakk>
                \<Longrightarrow> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T \<^sup>*\\\<^sup>* U'"
    proof (induct T arbitrary: U U')
      show "\<And>U U'. \<lbrakk> Arr []; NPath U; NPath U'; Srcs [] = Srcs U;
                    Srcs U = Srcs U'; Trgs U = Trgs U' \<rbrakk>
                      \<Longrightarrow> [] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [] \<^sup>*\\\<^sup>* U'"
        by (simp add: arr_char)
      fix t T U U'
      assume tT: "Arr (t # T)" and U: "NPath U" and U': "NPath U'"
      and Srcs1: "Srcs (t # T) = Srcs U" and Srcs2: "Srcs U = Srcs U'"
      and Trgs: "Trgs U = Trgs U'"
      and ind: "\<And>U U'. \<lbrakk> Arr T; NPath U; NPath U'; Srcs T = Srcs U;
                        Srcs U = Srcs U'; Trgs U = Trgs U' \<rbrakk>
                            \<Longrightarrow> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T \<^sup>*\\\<^sup>* U'"
      have t: "R.arr t"
        using tT by (metis Arr.simps(2) Con_Arr_self Con_rec(4) R.arrI)
      show "(t # T) \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 (t # T) \<^sup>*\\\<^sup>* U'"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
           by (metis Srcs.simps(2) Srcs1 Srcs2 Trgs U U' Coherent_single Arr.simps(2) tT)
        assume T: "T \<noteq> []"
        let ?t = "[t] \<^sup>*\\\<^sup>* U" and ?t' = "[t] \<^sup>*\\\<^sup>* U'"
        let ?T = "T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
        let ?T' = "T \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t])"
        have 0: "(t # T) \<^sup>*\\\<^sup>* U = ?t @ ?T \<and> (t # T) \<^sup>*\\\<^sup>* U' = ?t' @ ?T'"
          using tT U U' Srcs1 Srcs2
          by (metis Arr_has_Src Arr_iff_Con_self Resid_cons(1) Srcs.simps(1)
              Resid_NPath_preserves_reflects_Con)
        have 1: "?t \<approx>\<^sup>*\<^sub>0 ?t'"
          by (metis Srcs1 Srcs2 Srcs_simp\<^sub>P Trgs U U' list.sel(1) Coherent_single t tT)
        have A: "?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t) = T \<^sup>*\\\<^sup>* ((U \<^sup>*\\\<^sup>* [t]) @ (?t' \<^sup>*\\\<^sup>* ?t))"
          using 1 Arr.simps(1) Con_append(2) Con_sym Resid_append(2) Con_implies_Arr(1)
                NPath_def
          by (metis arr_char elements_are_arr)
        have B: "?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t') = T \<^sup>*\\\<^sup>* ((U' \<^sup>*\\\<^sup>* [t]) @ (?t \<^sup>*\\\<^sup>* ?t'))"
          by (metis "1" Con_appendI(2) Con_sym Resid.simps(1) Resid_append(2) elements_are_arr
              not_arr_null null_char)
        have E: "?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t) \<approx>\<^sup>*\<^sub>0 ?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')"
        proof -
          have "Arr T"
            using Arr.elims(1) T tT by blast
          moreover have "NPath (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            using 1 U t tT Srcs1 Srcs_simp\<^sub>P
            apply (intro NPath_appendI)
              apply auto
            by (metis Arr.simps(1) NPath_def Srcs_Resid Trgs_Resid_sym)
          moreover have "NPath (U' \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
            using t U' 1 Con_imp_eq_Srcs Trgs_Resid_sym
            apply (intro NPath_appendI)
              apply auto
             apply (metis Arr.simps(2) NPath_Resid Resid.simps(1))
            by (metis Arr.simps(1) NPath_def Srcs_Resid)
          moreover have "Srcs T = Srcs (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            using A B
            by (metis (full_types) "0" "1" Arr_has_Src Con_cons(1) Con_implies_Arr(1)
                Srcs.simps(1) Srcs_append T elements_are_arr not_arr_null null_char
                Con_imp_eq_Srcs)
          moreover have "Srcs (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) =
                         Srcs (U' \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
            by (metis "1" Con_implies_Arr(2) Con_sym Cong\<^sub>0_imp_con Srcs_Resid Srcs_append
                arr_char con_char arr_resid_iff_con)
          moreover have "Trgs (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) =
                         Trgs (U' \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
            using "1" Cong\<^sub>0_imp_con con_char by force
          ultimately show ?thesis
            using A B ind [of "(U \<^sup>*\\\<^sup>* [t]) @ (?t' \<^sup>*\\\<^sup>* ?t)" "(U' \<^sup>*\\\<^sup>* [t]) @ (?t \<^sup>*\\\<^sup>* ?t')"]
            by simp
        qed
        have C: "NPath ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
          using E by blast
        have D: "NPath ((?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')) \<^sup>*\\\<^sup>* (?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)))"
          using E by blast
        show ?thesis
        proof
          have 2: "((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U') =
                   ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T') @ ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
          proof -
            have "((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U') = (?t @ ?T) \<^sup>*\\\<^sup>* (?t' @ ?T')"
              using 0 by fastforce
            also have "... = ((?t @ ?T) \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T'"
              using tT T U U' Srcs1 Srcs2 0
              by (metis Con_appendI(2) Con_cons(1) Con_sym Resid.simps(1) Resid_append(2))
            also have "... = ((?t \<^sup>*\\\<^sup>* ?t') @ (?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t))) \<^sup>*\\\<^sup>* ?T'"
              by (metis (no_types, lifting) Arr.simps(1) Con_appendI(1) Con_implies_Arr(1)
                  D NPath_def Resid_append(1) null_is_zero(2))
            also have "... = ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T') @
                               ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
            proof -
              have "?t \<^sup>*\\\<^sup>* ?t' @ ?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t) \<^sup>*\<frown>\<^sup>* ?T'"
                using C D E Con_sym
                by (metis Con_append(2) Cong\<^sub>0_imp_con con_char arr_resid_iff_con
                          con_implies_arr(2))
              thus ?thesis
                using Resid_append(1)
                by (metis Con_sym append.right_neutral Resid.simps(1))
            qed
            finally show ?thesis by simp
          qed
          moreover have 3: "NPath ..."
          proof -
            have "NPath ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T')"
              using 0 1 E
              by (metis Con_imp_Arr_Resid Con_imp_eq_Srcs NPath_Resid Resid.simps(1)
                  ex_un_null mem_Collect_eq)
            moreover have "Trgs ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T') =
                           Srcs ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
              using C
              by (metis NPath_implies_Arr Srcs.simps(1) Srcs_Resid
                  Trgs_Resid_sym Arr_has_Src)
            ultimately show ?thesis
              using C by blast
          qed
          ultimately show "((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U') \<in> Collect NPath"
            by simp

          have 4: "((t # T) \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U) =
                ((?t' \<^sup>*\\\<^sup>* ?t) \<^sup>*\\\<^sup>* ?T) @ ((?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')) \<^sup>*\\\<^sup>* (?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)))"
            by (metis "0" "2" "3" Arr.simps(1) Con_implies_Arr(1) Con_sym D NPath_def Resid_append2)
          moreover have "NPath ..."
          proof -
            have "NPath ((?t' \<^sup>*\\\<^sup>* ?t) \<^sup>*\\\<^sup>* ?T)"
              by (metis "1" CollectD Cong\<^sub>0_imp_con E con_imp_coinitial forward_stable
                  arr_resid_iff_con con_implies_arr(2))
            moreover have "NPath ((?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')) \<^sup>*\\\<^sup>* (?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)))"
              using U U' 1 D ind Coherent_single [of t U' U] by blast
            moreover have "Trgs ((?t' \<^sup>*\\\<^sup>* ?t) \<^sup>*\\\<^sup>* ?T) =
                           Srcs ((?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')) \<^sup>*\\\<^sup>* (?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)))"
              by (metis Arr.simps(1) NPath_def Srcs_Resid Trgs_Resid_sym calculation(2))
            ultimately show ?thesis by blast
          qed
          ultimately show "((t # T) \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U) \<in> Collect NPath"
            by simp
        qed
      qed
    qed

    sublocale rts_with_composites Resid
      using is_rts_with_composites by simp

    sublocale coherent_normal_sub_rts Resid \<open>Collect NPath\<close>
    proof
      fix T U U'
      assume T: "arr T" and U: "U \<in> Collect NPath" and U': "U' \<in> Collect NPath"
      assume sources_UU': "sources U = sources U'" and targets_UU': "targets U = targets U'"
      and TU: "sources T = sources U"
      have "Srcs T = Srcs U"
        using TU sources_char\<^sub>P T arr_iff_has_source by auto
      moreover have "Srcs U = Srcs U'"
        by (metis Con_imp_eq_Srcs T TU con_char con_imp_coinitial_ax con_sym in_sourcesE
            in_sourcesI arr_def sources_UU')
      moreover have "Trgs U = Trgs U'"
        using U U' targets_UU' targets_char
        by (metis (full_types) arr_iff_has_target composable_def composable_iff_seq
            composite_of_arr_target elements_are_arr equals0I seq_char)
      ultimately show "T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T \<^sup>*\\\<^sup>* U'"
        using T U U' Coherent [of T U U'] arr_char by blast
    qed

    theorem coherent_normal_extends_to_paths:
    shows "coherent_normal_sub_rts Resid (Collect NPath)"
      ..

    lemma Cong\<^sub>0_append_Arr_NPath:
    assumes "T \<noteq> []" and "Arr (T @ U)" and "NPath U"
    shows "Cong\<^sub>0 (T @ U) T"
      using assms
      by (metis Arr.simps(1) Arr_appendE\<^sub>P NPath_implies_Arr append_is_composite_of arrI\<^sub>P
          arr_append_imp_seq composite_of_arr_normal mem_Collect_eq)

    lemma Cong_append_NPath_Arr:
    assumes "T \<noteq> []" and "Arr (U @ T)" and "NPath U"
    shows "U @ T \<approx>\<^sup>* T"
      using assms
      by (metis (full_types) Arr.simps(1) Con_Arr_self Con_append(2) Con_implies_Arr(2)
          Con_imp_eq_Srcs composite_of_normal_arr Srcs_Resid append_is_composite_of arr_char
          NPath_implies_Arr mem_Collect_eq seq_char)

    subsubsection "Permutation Congruence"

    text \<open>
      Here we show that \<open>\<^sup>*\<sim>\<^sup>*\<close> coincides with ``permutation congruence'':
      the least congruence respecting composition that relates \<open>[t, u \ t]\<close> and \<open>[u, t \ u]\<close>
      whenever \<open>t \<frown> u\<close> and that relates \<open>T @ [b]\<close> and \<open>T\<close> whenever \<open>b\<close> is an identity
      such that \<open>seq T [b]\<close>.
    \<close>

    inductive PCong
    where "Arr T \<Longrightarrow> PCong T T"
        | "PCong T U \<Longrightarrow> PCong U T"
        | "\<lbrakk>PCong T U; PCong U V\<rbrakk> \<Longrightarrow> PCong T V"
        | "\<lbrakk>seq T U; PCong T T'; PCong U U'\<rbrakk> \<Longrightarrow> PCong (T @ U) (T' @ U')"
        | "\<lbrakk>seq T [b]; R.ide b\<rbrakk> \<Longrightarrow> PCong (T @ [b]) T"
        | "t \<frown> u \<Longrightarrow> PCong [t, u \\ t] [u, t \\ u]"

    lemmas PCong.intros(3) [trans]

    lemma PCong_append_Ide:
    shows "\<lbrakk>seq T B; Ide B\<rbrakk> \<Longrightarrow> PCong (T @ B) T"
    proof (induct B)
      show "\<lbrakk>seq T []; Ide []\<rbrakk> \<Longrightarrow> PCong (T @ []) T"
        by auto
      fix b B T
      assume ind: "\<lbrakk>seq T B; Ide B\<rbrakk> \<Longrightarrow> PCong (T @ B) T"
      assume seq: "seq T (b # B)"
      assume Ide: "Ide (b # B)"
      have "T @ (b # B) = (T @ [b]) @ B"
        by simp
      also have "PCong ... (T @ B)"
        apply (cases "B = []")
        using Ide PCong.intros(5) seq apply force
        using seq Ide PCong.intros(4) [of "T @ [b]" B T B]
        by (metis Arr.simps(1) Ide_imp_Ide_hd PCong.intros(1) PCong.intros(5)
            append_is_Nil_conv arr_append arr_append_imp_seq arr_char calculation
            list.distinct(1) list.sel(1) seq_char)
      also have "PCong (T @ B) T"
      proof (cases "B = []")
        show "B = [] \<Longrightarrow> ?thesis"
          using PCong.intros(1) seq seq_char by force
        assume B: "B \<noteq> []"
        have "seq T B"
          using B seq Ide
          by (metis Con_imp_eq_Srcs Ide_imp_Ide_hd Trgs_append \<open>T @ b # B = (T @ [b]) @ B\<close>
              append_is_Nil_conv arr_append arr_append_imp_seq arr_char cong_cons_ideI(2)
              list.distinct(1) list.sel(1) not_arr_null null_char seq_char ide_implies_arr)
        thus ?thesis
          using seq Ide ind
          by (metis Arr.simps(1) Ide.elims(3) Ide.simps(3) seq_char)
      qed
      finally show "PCong (T @ (b # B)) T" by blast
    qed

    lemma PCong_imp_Cong:
    shows "PCong T U \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* U"
    proof (induct rule: PCong.induct)
      show "\<And>T. Arr T \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* T"
        using cong_reflexive by blast
      show "\<And>T U. \<lbrakk>PCong T U; T \<^sup>*\<sim>\<^sup>* U\<rbrakk> \<Longrightarrow> U \<^sup>*\<sim>\<^sup>* T"
        by blast
      show "\<And>T U V. \<lbrakk>PCong T U; T \<^sup>*\<sim>\<^sup>* U; PCong U V; U \<^sup>*\<sim>\<^sup>* V\<rbrakk> \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* V"
        using cong_transitive by blast
      show "\<And>T U U' T'. \<lbrakk>seq T U; PCong T T'; T \<^sup>*\<sim>\<^sup>* T'; PCong U U'; U \<^sup>*\<sim>\<^sup>* U'\<rbrakk>
                           \<Longrightarrow> T @ U \<^sup>*\<sim>\<^sup>* T' @ U'"
        using cong_append by simp
      show "\<And>T b. \<lbrakk>seq T [b]; R.ide b\<rbrakk> \<Longrightarrow> T @ [b] \<^sup>*\<sim>\<^sup>* T"
        using cong_append_ideI(4) ide_char by force
      show "\<And>t u. t \<frown> u \<Longrightarrow> [t, u \\ t] \<^sup>*\<sim>\<^sup>* [u, t \\ u]"
      proof -
        have "\<And>t u. t \<frown> u \<Longrightarrow> [t, u \\ t] \<^sup>*\<lesssim>\<^sup>* [u, t \\ u]"
        proof -
          fix t u
          assume con: "t \<frown> u"
          have "([t] @ [u \\ t]) \<^sup>*\\\<^sup>* ([u] @ [t \\ u]) =
                [(t \\ u) \\ (t \\ u), ((u \\ t) \\ (u \\ t)) \\ ((t \\ u) \\ (t \\ u))]"
            using con Resid_append2 [of "[t]" "[u \\ t]" "[u]" "[t \\ u]"]
            apply simp
            by (metis R.arr_resid_iff_con R.con_target R.conE R.con_sym
                R.prfx_implies_con R.prfx_reflexive R.cube)
          moreover have "Ide ..."
            using con
            by (metis Arr.simps(2) Arr.simps(3) Ide.simps(2) Ide.simps(3) R.arr_resid_iff_con
                R.con_sym R.resid_ide_arr R.prfx_reflexive calculation Con_imp_Arr_Resid)
          ultimately show"[t, u \\ t] \<^sup>*\<lesssim>\<^sup>* [u, t \\ u]"
            using ide_char by auto
        qed
        thus "\<And>t u. t \<frown> u \<Longrightarrow> [t, u \\ t] \<^sup>*\<sim>\<^sup>* [u, t \\ u]"
          using R.con_sym by blast
      qed
    qed

    lemma PCong_permute_single:
    shows "[t] \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> PCong ([t] @ (U \<^sup>*\\\<^sup>* [t])) (U @ ([t] \<^sup>*\\\<^sup>* U))"
    proof (induct U arbitrary: t)
      show "\<And>t. [t] \<^sup>*\<frown>\<^sup>* [] \<Longrightarrow> PCong ([t] @ [] \<^sup>*\\\<^sup>* [t]) ([] @ [t] \<^sup>*\\\<^sup>* [])"
        by auto
      fix t u U
      assume ind: "\<And>t. [t] \<^sup>*\\\<^sup>* U \<noteq> [] \<Longrightarrow> PCong ([t] @( U \<^sup>*\\\<^sup>* [t])) (U @ ([t] \<^sup>*\\\<^sup>* U))"
      assume con: "[t] \<^sup>*\<frown>\<^sup>* u # U"
      show "PCong ([t] @ (u # U) \<^sup>*\\\<^sup>* [t]) ((u # U) @ [t] \<^sup>*\\\<^sup>* (u # U))"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          by (metis PCong.intros(6) Resid.simps(3) append_Cons append_eq_append_conv2
              append_self_conv con_char con_def con con_sym_ax)
        assume U: "U \<noteq> []"
        show "PCong ([t] @ ((u # U) \<^sup>*\\\<^sup>* [t])) ((u # U) @ ([t] \<^sup>*\\\<^sup>* (u # U)))"
        proof -
          have "[t] @ ((u # U) \<^sup>*\\\<^sup>* [t]) = [t] @ ([u \\ t] @ (U \<^sup>*\\\<^sup>* [t \\ u]))"
            using Con_sym Resid_rec(2) U con by auto
          also have "... = ([t] @ [u \\ t]) @ (U \<^sup>*\\\<^sup>* [t \\ u])"
            by auto
          also have "PCong ... (([u] @ [t \\ u]) @ (U \<^sup>*\\\<^sup>* [t \\ u]))"
          proof -
            have "PCong ([t] @ [u \\ t]) ([u] @ [t \\ u])"
              using con
              by (simp add: Con_rec(3) PCong.intros(6) U)  
            thus ?thesis
              by (metis Arr_Resid_single Con_implies_Arr(1) Con_rec(2) Con_sym
                  PCong.intros(1,4) Srcs_Resid U append_is_Nil_conv append_is_composite_of
                  arr_append_imp_seq arr_char calculation composite_of_unq_upto_cong
                  con not_arr_null null_char ide_implies_arr seq_char)
          qed
          also have "([u] @ [t \\ u]) @ (U \<^sup>*\\\<^sup>* [t \\ u]) = [u] @ ([t \\ u] @ (U \<^sup>*\\\<^sup>* [t \\ u]))"
            by simp
          also have "PCong ... ([u] @ (U @ ([t \\ u] \<^sup>*\\\<^sup>* U)))"
          proof -
            have "PCong ([t \\ u] @ (U \<^sup>*\\\<^sup>* [t \\ u])) (U @ ([t \\ u] \<^sup>*\\\<^sup>* U))"
              using ind
              by (metis Resid_rec(3) U con)
            moreover have "seq [u] ([t \\ u] @ U \<^sup>*\\\<^sup>* [t \\ u])"
            proof
              show "Arr [u]"
                using Con_implies_Arr(2) Con_initial_right con by blast
              show "Arr ([t \\ u] @ U \<^sup>*\\\<^sup>* [t \\ u])"
                using Con_implies_Arr(1) U con Con_imp_Arr_Resid Con_rec(3) Con_sym
                by fastforce
              show "Trgs [u] \<inter> Srcs ([t \\ u] @ U \<^sup>*\\\<^sup>* [t \\ u]) \<noteq> {}"
                by (metis Arr.simps(1) Arr.simps(2) Arr_has_Trg Con_implies_Arr(1)
                    Int_absorb R.arr_resid_iff_con R.sources_resid Resid_rec(3)
                    Srcs.simps(2) Srcs_append Trgs.simps(2) U \<open>Arr [u]\<close> con)
            qed
            moreover have "PCong [u] [u]"
              using PCong.intros(1) calculation(2) seq_char by force
            ultimately show ?thesis
              using U arr_append arr_char con seq_char
                    PCong.intros(4) [of "[u]" "[t \\ u] @ (U \<^sup>*\\\<^sup>* [t \\ u])"
                                        "[u]" "U @ ([t \\ u] \<^sup>*\\\<^sup>* U)"]
              by blast
          qed
          also have "([u] @ (U @ ([t \\ u] \<^sup>*\\\<^sup>* U))) = ((u # U) @ [t] \<^sup>*\\\<^sup>* (u # U))"
            by (metis Resid_rec(3) U append_Cons append_Nil con)
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma PCong_permute:
    shows "T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> PCong (T @ (U \<^sup>*\\\<^sup>* T)) (U @ (T \<^sup>*\\\<^sup>* U))"
    proof (induct T arbitrary: U)
      show "\<And>U. [] \<^sup>*\\\<^sup>* U \<noteq> [] \<Longrightarrow> PCong ([] @ U \<^sup>*\\\<^sup>* []) (U @ [] \<^sup>*\\\<^sup>* U)"
         by simp
      fix t T U
      assume ind: "\<And>U. T \<^sup>*\<frown>\<^sup>* U \<Longrightarrow> PCong (T @ (U \<^sup>*\\\<^sup>* T)) (U @ (T \<^sup>*\\\<^sup>* U))"
      assume con: "t # T \<^sup>*\<frown>\<^sup>* U"
      show "PCong ((t # T) @ (U \<^sup>*\\\<^sup>* (t # T))) (U @ ((t # T) \<^sup>*\\\<^sup>* U))"
      proof (cases "T = []")
        assume T: "T = []"
        have "(t # T) @ (U \<^sup>*\\\<^sup>* (t # T)) = [t] @ (U \<^sup>*\\\<^sup>* [t])"
          using con T by simp
        also have "PCong ... (U @ ([t] \<^sup>*\\\<^sup>* U))"
          using PCong_permute_single T con by blast
        finally show ?thesis
          using T by fastforce
        next
        assume T: "T \<noteq> []"
        have "(t # T) @ (U \<^sup>*\\\<^sup>* (t # T)) = [t] @ (T @ (U \<^sup>*\\\<^sup>* (t # T)))"
          by simp
        also have "PCong ... ([t] @ (U \<^sup>*\\\<^sup>* [t]) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])))"
          using ind [of "U \<^sup>*\\\<^sup>* [t]"]
          by (metis Arr.simps(1) Con_imp_Arr_Resid Con_implies_Arr(2) Con_sym
              PCong.intros(1,4) Resid_cons(2) Srcs_Resid T arr_append arr_append_imp_seq
              calculation con not_arr_null null_char seq_char)
        also have "[t] @ (U \<^sup>*\\\<^sup>* [t]) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) =
                   ([t] @ (U \<^sup>*\\\<^sup>* [t])) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
          by simp
        also have "PCong (([t] @ (U \<^sup>*\\\<^sup>* [t])) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])))
                         ((U @ ([t] \<^sup>*\\\<^sup>* U)) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])))"
          by (metis Arr.simps(1) Con_cons(1) Con_imp_Arr_Resid Con_implies_Arr(2)
              PCong.intros(1,4) PCong_permute_single Srcs_Resid T Trgs_append arr_append
              arr_char con seq_char)
        also have "(U @ ([t] \<^sup>*\\\<^sup>* U)) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])) = U @ ((t # T) \<^sup>*\\\<^sup>* U)"
          by (metis Resid.simps(2) Resid_cons(1) append.assoc con)
        finally show ?thesis by blast
      qed
    qed

    lemma Cong_imp_PCong:
    assumes "T \<^sup>*\<sim>\<^sup>* U"
    shows "PCong T U"
    proof -
      have "PCong T (T @ (U \<^sup>*\\\<^sup>* T))"
        using assms PCong.intros(2) PCong_append_Ide
        by (metis Con_implies_Arr(1) Ide.simps(1) Srcs_Resid ide_char Con_imp_Arr_Resid
            seq_char)
      also have "PCong (T @ (U \<^sup>*\\\<^sup>* T)) (U @ (T \<^sup>*\\\<^sup>* U))"
        using PCong_permute assms con_char prfx_implies_con by presburger
      also have "PCong (U @ (T \<^sup>*\\\<^sup>* U)) U"
        using assms PCong_append_Ide
        by (metis Con_imp_Arr_Resid Con_implies_Arr(1) Srcs_Resid arr_resid_iff_con
            ide_implies_arr con_char ide_char seq_char)
      finally show ?thesis by blast
    qed

    lemma Cong_iff_PCong:
    shows "T \<^sup>*\<sim>\<^sup>* U \<longleftrightarrow> PCong T U"
      using PCong_imp_Cong Cong_imp_PCong by blast

  end

  section "Composite Completion"

  text \<open>
    The RTS of paths in an RTS factors via the coherent normal sub-RTS of identity
    paths into an extensional RTS with composites, which can be regarded as a
    ``composite completion'' of the original RTS.
  \<close>

  locale composite_completion =
    R: rts
  begin

    interpretation N: coherent_normal_sub_rts resid \<open>Collect R.ide\<close>
      using R.rts_axioms R.identities_form_coherent_normal_sub_rts by auto
    sublocale P: paths_in_rts_with_coherent_normal resid \<open>Collect R.ide\<close> ..
    sublocale quotient_by_coherent_normal P.Resid \<open>Collect P.NPath\<close> ..

    notation P.Resid  (infix "\<^sup>*\\\<^sup>*" 70)
    notation P.Con    (infix "\<^sup>*\<frown>\<^sup>*" 50)
    notation P.Cong   (infix "\<^sup>*\<approx>\<^sup>*" 50)
    notation P.Cong\<^sub>0  (infix "\<^sup>*\<approx>\<^sub>0\<^sup>*" 50)
    notation P.Cong_class ("\<lbrace>_\<rbrace>")

    notation Resid    (infix "\<lbrace>\<^sup>*\\\<^sup>*\<rbrace>" 70)
    notation con      (infix "\<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace>" 50)
    notation prfx     (infix "\<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace>" 50)

    lemma NPath_char:
    shows "P.NPath T \<longleftrightarrow> P.Ide T"
      using P.NPath_def P.Ide_implies_NPath by blast

    lemma Cong_eq_Cong\<^sub>0:
    shows "T \<^sup>*\<approx>\<^sup>* T' \<longleftrightarrow> T \<^sup>*\<approx>\<^sub>0\<^sup>* T'"
      by (metis P.Cong_iff_cong P.ide_char P.ide_closed CollectD Collect_cong
          NPath_char)

    lemma Srcs_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.Srcs T = P.Srcs T'"
      using assms
      by (meson P.Con_imp_eq_Srcs P.Cong\<^sub>0_imp_con P.con_char Cong_eq_Cong\<^sub>0)

    lemma sources_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.sources T = P.sources T'"
      using assms
      by (meson P.Cong\<^sub>0_imp_coinitial Cong_eq_Cong\<^sub>0)

    lemma Trgs_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.Trgs T = P.Trgs T'"
    proof -
      have "P.Trgs T = P.Trgs (T @ (T' \<^sup>*\\\<^sup>* T))"
        using assms NPath_char P.Arr.simps(1) P.Con_imp_Arr_Resid
              P.Con_sym P.Cong_def P.Con_Arr_self
              P.Con_implies_Arr(2) P.Resid_Ide(1) P.Srcs_Resid P.Trgs_append
        by (metis P.Cong\<^sub>0_imp_con P.con_char CollectD)
      also have "... = P.Trgs (T' @ (T \<^sup>*\\\<^sup>* T'))"
        using P.Cong\<^sub>0_imp_con P.con_char Cong_eq_Cong\<^sub>0 assms by force
      also have "... = P.Trgs T'"
        using assms NPath_char P.Arr.simps(1) P.Con_imp_Arr_Resid
              P.Con_sym P.Cong_def P.Con_Arr_self
              P.Con_implies_Arr(2) P.Resid_Ide(1) P.Srcs_Resid P.Trgs_append
        by (metis P.Cong\<^sub>0_imp_con P.con_char CollectD)
      finally show ?thesis by blast
    qed

    lemma targets_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.targets T = P.targets T'"
      using assms P.Cong_imp_arr(1) P.Cong_imp_arr(2) P.arr_iff_has_target
            P.targets_char\<^sub>P Trgs_respects_Cong
      by force

    lemma ide_char\<^sub>C\<^sub>C:
    shows "ide \<T> \<longleftrightarrow> arr \<T> \<and> (\<forall>T. T \<in> \<T> \<longrightarrow> P.Ide T)"
      using NPath_char ide_char' by blast

    lemma con_char\<^sub>C\<^sub>C:
    shows "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<longleftrightarrow> arr \<T> \<and> arr \<U> \<and> P.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* P.Cong_class_rep \<U>"
    proof
      show "arr \<T> \<and> arr \<U> \<and> P.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* P.Cong_class_rep \<U> \<Longrightarrow> \<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        using arr_char P.con_char
        by (meson P.rep_in_Cong_class con_char\<^sub>Q\<^sub>C\<^sub>N)
      show "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<Longrightarrow> arr \<T> \<and> arr \<U> \<and> P.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* P.Cong_class_rep \<U>"
      proof -
        assume con: "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        have 1: "arr \<T> \<and> arr \<U>"
          using con coinitial_iff con_imp_coinitial by blast
        moreover have "P.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* P.Cong_class_rep \<U>"
        proof -
          obtain T U where TU: "T \<in> \<T> \<and> U \<in> \<U> \<and> P.Con T U"
            using con Resid_def
            by (meson P.con_char con_char\<^sub>Q\<^sub>C\<^sub>N)
          have "T \<^sup>*\<approx>\<^sup>* P.Cong_class_rep \<T> \<and> U \<^sup>*\<approx>\<^sup>* P.Cong_class_rep \<U>"
            using TU 1 by (meson P.Cong_class_memb_Cong_rep arr_char)
          thus ?thesis
            using TU P.Cong_subst(1) [of T "P.Cong_class_rep \<T>" U "P.Cong_class_rep \<U>"]
            by (metis P.coinitial_iff P.con_char P.con_imp_coinitial sources_respects_Cong)
        qed
        ultimately show ?thesis by simp
      qed
    qed

    lemma con_char\<^sub>C\<^sub>C':
    shows "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<longleftrightarrow> arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> T \<^sup>*\<frown>\<^sup>* U)"
    proof
      show "arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> T \<^sup>*\<frown>\<^sup>* U) \<Longrightarrow> \<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        using con_char\<^sub>C\<^sub>C
        by (simp add: P.rep_in_Cong_class arr_char)
      show "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<Longrightarrow> arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> T \<^sup>*\<frown>\<^sup>* U)"
      proof (intro conjI allI impI)
        assume 1: "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        show "arr \<T>"
          using 1 con_implies_arr by simp
        show "arr \<U>"
          using 1 con_implies_arr by simp
        fix T U
        assume 2: "T \<in> \<T> \<and> U \<in> \<U>"
        show "T \<^sup>*\<frown>\<^sup>* U"
          using 1 2 P.Cong_class_memb_Cong_rep
          by (meson P.Cong\<^sub>0_subst_Con P.con_char Cong_eq_Cong\<^sub>0 arr_char con_char\<^sub>C\<^sub>C)
      qed
    qed

    lemma resid_char:
    shows "\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U> =
           (if \<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> then \<lbrace>P.Cong_class_rep \<T> \<^sup>*\\\<^sup>* P.Cong_class_rep \<U>\<rbrace> else {})"
      by (metis P.con_char P.rep_in_Cong_class Resid_by_members arr_char arr_resid_iff_con
          con_char\<^sub>C\<^sub>C is_Cong_class_Resid)

    lemma src_char':
    shows "src \<T> = {A. arr \<T> \<and> P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        by (simp add: null_char src_def)
      assume \<T>: "arr \<T>"
      have 1: "\<exists>A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A"
        by (metis P.Arr.simps(1) P.Con_imp_eq_Srcs P.Cong\<^sub>0_imp_con
            P.Cong_class_memb_Cong_rep P.Cong_def P.con_char P.rep_in_Cong_class
            CollectD \<T> NPath_char P.Con_implies_Arr(1) arr_char)
      let ?A = "SOME A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A"
      have A: "P.Ide ?A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs ?A"
        using 1 someI_ex [of "\<lambda>A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A"] by simp
      have a: "arr \<lbrace>?A\<rbrace>"
        using A P.ide_char P.is_Cong_classI arr_char by blast
      have ide_a: "ide \<lbrace>?A\<rbrace>"
        using a A P.Cong_class_def P.normal_is_Cong_closed NPath_char ide_char\<^sub>C\<^sub>C by auto
      have "sources \<T> = {\<lbrace>?A\<rbrace>}"
      proof -
        have "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<lbrace>?A\<rbrace>"
          by (metis (no_types, lifting) A P.Con_Ide_iff P.Cong_class_memb_Cong_rep
              P.Cong_imp_arr(1) P.arr_char P.arr_in_Cong_class P.ide_char
              P.ide_implies_arr P.rep_in_Cong_class Con_char a \<T> P.con_char
              null_char arr_char P.con_sym conI)
        hence "\<lbrace>?A\<rbrace> \<in> sources \<T>"
          using ide_a in_sourcesI by simp
        thus ?thesis
          using sources_char by auto
      qed
      moreover have "\<lbrace>?A\<rbrace> = {A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A}"
      proof
        show "{A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A} \<subseteq> \<lbrace>?A\<rbrace>"
          using A P.Cong_class_def P.Cong_closure_props(3) P.Ide_implies_Arr
                P.ide_closed P.ide_char
          by fastforce
        show "\<lbrace>?A\<rbrace> \<subseteq> {A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<T>) = P.Srcs A}"
          using a A P.Cong_class_def Srcs_respects_Cong ide_a ide_char\<^sub>C\<^sub>C by blast
      qed
      ultimately show ?thesis
        using \<T> src_in_sources sources_char by auto
    qed

    lemma src_char:
    shows "src \<T> = {A. arr \<T> \<and> P.Ide A \<and> (\<forall>T. T \<in> \<T> \<longrightarrow> P.Srcs T = P.Srcs A)}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        by (simp add: null_char src_def)
      assume \<T>: "arr \<T>"
      have "\<And>T. T \<in> \<T> \<Longrightarrow> P.Srcs T = P.Srcs (P.Cong_class_rep \<T>)"
        using \<T> P.Cong_class_memb_Cong_rep Srcs_respects_Cong arr_char by auto
      thus ?thesis
        using \<T> src_char' P.is_Cong_class_def arr_char by force
    qed

    lemma trg_char':
    shows "trg \<T> = {B. arr \<T> \<and> P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        by (metis (no_types, lifting) Collect_empty_eq arrI resid_arr_self resid_char)
      assume \<T>: "arr \<T>"
      have 1: "\<exists>B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B"
        by (metis P.Con_implies_Arr(2) P.Resid_Arr_self P.Srcs_Resid \<T> con_char\<^sub>C\<^sub>C arrE)
      define B where "B = (SOME B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B)"
      have B: "P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B"
        unfolding B_def
        using 1 someI_ex [of "\<lambda>B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B"] by simp
      hence 2: "P.Ide B \<and> P.Con (P.Resid (P.Cong_class_rep \<T>) (P.Cong_class_rep \<T>)) B"
        using \<T>
        by (metis (no_types, lifting) P.Con_Ide_iff P.Ide_implies_Arr P.Resid_Arr_self
            P.Srcs_Resid arrE P.Con_implies_Arr(2) con_char\<^sub>C\<^sub>C)
      have b: "arr \<lbrace>B\<rbrace>"
        by (simp add: "2" P.ide_char P.is_Cong_classI arr_char)
      have ide_b: "ide \<lbrace>B\<rbrace>"
        by (meson "2" P.arr_in_Cong_class P.ide_char P.ide_closed
            b disjoint_iff ide_char P.ide_implies_arr)
      have "targets \<T> = {\<lbrace>B\<rbrace>}"
      proof -
        have "cong (\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<lbrace>B\<rbrace>"
        proof -
          have "\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T> = \<lbrace>B\<rbrace>"
            by (metis (no_types, lifting) "2" P.Cong_class_eqI P.Cong_closure_props(3)
                P.Resid_Arr_Ide_ind P.Resid_Ide(1) NPath_char \<T> con_char\<^sub>C\<^sub>C resid_char
                P.Con_implies_Arr(2) P.Resid_Arr_self mem_Collect_eq)
          thus ?thesis
            using b cong_reflexive by presburger
        qed
        thus ?thesis
          using \<T> targets_char\<^sub>Q\<^sub>C\<^sub>N [of \<T>] cong_char by auto
      qed 
      moreover have "\<lbrace>B\<rbrace> = {B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B}"
      proof
        show "{B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B} \<subseteq> \<lbrace>B\<rbrace>"
          using B P.Cong_class_def P.Cong_closure_props(3) P.Ide_implies_Arr
                P.ide_closed P.ide_char
          by force
        show "\<lbrace>B\<rbrace> \<subseteq> {B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B}"
        proof -
          have "\<And>B'. P.Cong B' B \<Longrightarrow> P.Ide B' \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B'"
            using B NPath_char P.normal_is_Cong_closed Srcs_respects_Cong
            by (metis P.Cong_closure_props(1) mem_Collect_eq)
          thus ?thesis
            using P.Cong_class_def by blast
        qed
      qed
      ultimately show ?thesis
        using \<T> trg_in_targets targets_char by auto
    qed

    lemma trg_char:
    shows "trg \<T> = {B. arr \<T> \<and> P.Ide B \<and> (\<forall>T. T \<in> \<T> \<longrightarrow> P.Trgs T = P.Srcs B)}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        using trg_char' by presburger
      assume \<T>: "arr \<T>"
      have "\<And>T. T \<in> \<T> \<Longrightarrow> P.Trgs T = P.Trgs (P.Cong_class_rep \<T>)"
        using \<T>
        by (metis P.Cong_class_memb_Cong_rep Trgs_respects_Cong arr_char)
      thus ?thesis
        using \<T> trg_char' P.is_Cong_class_def arr_char by force
    qed

    lemma is_extensional_rts_with_composites:
    shows "extensional_rts_with_composites Resid"
    proof
      fix \<T> \<U>
      assume seq: "seq \<T> \<U>"
      obtain T where T: "\<T> = \<lbrace>T\<rbrace>"
        using seq P.Cong_class_rep arr_char seq_def by blast
      obtain U where U: "\<U> = \<lbrace>U\<rbrace>"
        using seq P.Cong_class_rep arr_char seq_def by blast
      have 1: "P.Arr T \<and> P.Arr U"
        using seq T U P.Con_implies_Arr(2) P.Cong\<^sub>0_subst_right(1) P.Cong_class_def
              P.con_char seq_def
        by (metis Collect_empty_eq P.Cong_imp_arr(1) P.arr_char P.rep_in_Cong_class
            empty_iff arr_char)
      have 2: "P.Trgs T = P.Srcs U"
      proof -
        have "targets \<T> = sources \<U>"
          using seq seq_def sources_char targets_char\<^sub>W\<^sub>E by force
        hence 3: "trg \<T> = src \<U>"
          using seq arr_has_un_source arr_has_un_target
          by (metis seq_def src_in_sources trg_in_targets)
        hence "{B. P.Ide B \<and> P.Trgs (P.Cong_class_rep \<T>) = P.Srcs B} =
               {A. P.Ide A \<and> P.Srcs (P.Cong_class_rep \<U>) = P.Srcs A}"
          using seq seq_def src_char' [of \<U>] trg_char' [of \<T>] by force
        hence "P.Trgs (P.Cong_class_rep \<T>) = P.Srcs (P.Cong_class_rep \<U>)"
          using seq seq_def arr_char
          by (metis (mono_tags, lifting) "3" P.Cong_class_is_nonempty Collect_empty_eq
              arr_src_iff_arr mem_Collect_eq trg_char')
        thus ?thesis
          using seq seq_def arr_char T U P.Srcs_respects_Cong P.Trgs_respects_Cong
                P.Cong_class_memb_Cong_rep P.Cong_symmetric
          by (metis "1" P.arr_char P.arr_in_Cong_class Srcs_respects_Cong Trgs_respects_Cong)
      qed
      have "P.Arr (T @ U)"
        using 1 2 by simp
      moreover have "P.Ide (T \<^sup>*\\\<^sup>* (T @ U))"
        by (metis "1" P.Con_append(2) P.Con_sym P.Resid_Arr_self P.Resid_Ide_Arr_ind
            P.Resid_append(2) P.Trgs.simps(1) calculation P.Arr_has_Trg)
      moreover have "(T @ U) \<^sup>*\\\<^sup>* T \<^sup>*\<approx>\<^sup>* U"
        by (metis "1" P.Arr.simps(1) P.Con_sym P.Cong\<^sub>0_append_resid_NPath P.Cong\<^sub>0_cancel_left\<^sub>C\<^sub>S
            P.Ide.simps(1) calculation(2) Cong_eq_Cong\<^sub>0 NPath_char)
      ultimately have "composite_of \<T> \<U> \<lbrace>T @ U\<rbrace>"
      proof (unfold composite_of_def, intro conjI)
        show "prfx \<T> (P.Cong_class (T @ U))"
        proof -
          have "ide (\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>T @ U\<rbrace>)"
          proof (unfold ide_char, intro conjI)
            have 3: "T \<^sup>*\\\<^sup>* (T @ U) \<in> \<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>T @ U\<rbrace>"
            proof -
              have "\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>T @ U\<rbrace> = \<lbrace>T \<^sup>*\\\<^sup>* (T @ U)\<rbrace>"
                by (metis "1" P.Ide.simps(1) P.arr_char P.arr_in_Cong_class P.con_char
                    P.is_Cong_classI Resid_by_members T \<open>P.Arr (T @ U)\<close>
                    \<open>P.Ide (T \<^sup>*\\<^sup>* (T @ U))\<close>)
              thus ?thesis
                by (simp add: P.arr_in_Cong_class P.elements_are_arr NPath_char
                              \<open>P.Ide (T \<^sup>*\\<^sup>* (T @ U))\<close>)
            qed
            show "arr (\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>T @ U\<rbrace>)"
              using 3 arr_char is_Cong_class_Resid by blast
            show "\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>T @ U\<rbrace> \<inter> Collect P.NPath \<noteq> {}"
              using 3 P.ide_closed P.ide_char \<open>P.Ide (T \<^sup>*\\<^sup>* (T @ U))\<close> by blast
          qed
          thus ?thesis by blast
        qed
        show "\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<U>"
        proof -
          have 3: "((T @ U) \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* U \<in> (\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U>"
          proof -
            have "(\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U> = \<lbrace>((T @ U) \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* U\<rbrace>"
            proof -
              have "\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T> = \<lbrace>(T @ U) \<^sup>*\\\<^sup>* T\<rbrace>"
                by (metis "1" P.Cong_imp_arr(1) P.arr_char P.arr_in_Cong_class
                    P.is_Cong_classI T \<open>P.Arr (T @ U)\<close> \<open>(T @ U) \<^sup>*\\<^sup>* T \<^sup>*\<approx>\<^sup>* U\<close>
                    Resid_by_members P.arr_resid_iff_con)
              moreover
              have "\<lbrace>(T @ U) \<^sup>*\\\<^sup>* T\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U> = \<lbrace>((T @ U) \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* U\<rbrace>"
                by (metis "1" P.Cong_class_eqI P.Cong_imp_arr(1) P.arr_char
                    P.arr_in_Cong_class P.con_char P.is_Cong_classI arr_char arrE U
                    \<open>(T @ U) \<^sup>*\\<^sup>* T \<^sup>*\<approx>\<^sup>* U\<close> con_char\<^sub>C\<^sub>C' Resid_by_members)
              ultimately show ?thesis by auto
            qed
            thus ?thesis
              by (metis "1" P.Arr.simps(1) P.Cong\<^sub>0_reflexive P.Resid_append(2) P.arr_char
                        P.arr_in_Cong_class P.elements_are_arr \<open>P.Arr (T @ U)\<close>)
          qed
          have "\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<U>"
          proof (unfold ide_char, intro conjI)
            show "arr ((\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U>)"
              using 3 arr_char is_Cong_class_Resid by blast
            show "(\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U> \<inter> Collect P.NPath \<noteq> {}"
              by (metis 1 3 P.Arr.simps(1) P.Resid_append(2) P.con_char
                  IntI \<open>P.Arr (T @ U)\<close> NPath_char P.Resid_Arr_self P.arr_char empty_iff
                  mem_Collect_eq P.arrE)
          qed
          thus ?thesis by blast
        qed
        show "\<U> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>"
        proof (unfold ide_char, intro conjI)
          have 3: "U \<^sup>*\\\<^sup>* ((T @ U) \<^sup>*\\\<^sup>* T) \<in> \<U> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> (\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>)"
          proof -
            have "\<U> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> (\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) = \<lbrace>U \<^sup>*\\\<^sup>* ((T @ U) \<^sup>*\\\<^sup>* T)\<rbrace>"
            proof -
              have "\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T> = \<lbrace>(T @ U) \<^sup>*\\\<^sup>* T\<rbrace>"
                by (metis "1" P.Con_sym P.Ide.simps(1) P.arr_char P.arr_in_Cong_class
                    P.con_char P.is_Cong_classI Resid_by_members T \<open>P.Arr (T @ U)\<close>
                    \<open>P.Ide (T \<^sup>*\\<^sup>* (T @ U))\<close>)
              moreover have "\<U> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> (\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) = \<lbrace>U \<^sup>*\\\<^sup>* ((T @ U) \<^sup>*\\\<^sup>* T)\<rbrace>"
                by (metis "1" P.Cong_class_eqI P.Cong_imp_arr(1) P.arr_char
                    P.arr_in_Cong_class P.con_char P.is_Cong_classI prfx_implies_con
                    U \<open>(T @ U) \<^sup>*\\<^sup>* T \<^sup>*\<approx>\<^sup>* U\<close> \<open>\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\<^sup>*\<rbrace> \<T> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<U>\<close>
                    calculation con_char\<^sub>C\<^sub>C' Resid_by_members)
              ultimately show ?thesis by blast
            qed
            thus ?thesis
              by (metis "1" P.Arr.simps(1) P.Resid_append_ind P.arr_in_Cong_class
                  P.con_char \<open>P.Arr (T @ U)\<close> P.Con_Arr_self P.arr_resid_iff_con)
          qed
          show "arr (\<U> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> (\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>))"
            by (metis "3" arr_resid_iff_con empty_iff resid_char)
          show "\<U> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> (\<lbrace>T @ U\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<inter> Collect P.NPath \<noteq> {}"
            by (metis "1" "3" P.Arr.simps(1) P.Cong\<^sub>0_append_resid_NPath P.Cong\<^sub>0_cancel_left\<^sub>C\<^sub>S
                P.Cong_imp_arr(1) P.arr_char NPath_char IntI \<open>(T @ U) \<^sup>*\\<^sup>* T \<^sup>*\<approx>\<^sup>* U\<close>
                \<open>P.Ide (T \<^sup>*\\<^sup>* (T @ U))\<close> empty_iff)
        qed
      qed
      thus "composable \<T> \<U>"
        using composable_def by auto
    qed

    sublocale extensional_rts_with_composites Resid
      using is_extensional_rts_with_composites by simp

    subsection "Inclusion Map"

    abbreviation incl
    where "incl t \<equiv> \<lbrace>[t]\<rbrace>"

    text \<open>
      The inclusion into the composite completion preserves consistency and residuation.
    \<close>

    lemma incl_preserves_con:
    assumes "t \<frown> u"
    shows "\<lbrace>[t]\<rbrace> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<lbrace>[u]\<rbrace>"
      using assms
      by (meson P.Con_rec(1) P.arr_in_Cong_class P.con_char P.is_Cong_classI
          con_char\<^sub>Q\<^sub>C\<^sub>N P.con_implies_arr(1-2))

    lemma incl_preserves_resid:
    shows "\<lbrace>[t \\ u]\<rbrace> = \<lbrace>[t]\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>[u]\<rbrace>"
    proof (cases "t \<frown> u")
      show "t \<frown> u \<Longrightarrow> ?thesis"
      proof -
        assume 1: "t \<frown> u"
        have "P.is_Cong_class \<lbrace>[t]\<rbrace> \<and> P.is_Cong_class \<lbrace>[u]\<rbrace>"
          using 1 con_char\<^sub>Q\<^sub>C\<^sub>N incl_preserves_con by presburger
        moreover have "[t] \<in> \<lbrace>[t]\<rbrace> \<and> [u] \<in> \<lbrace>[u]\<rbrace>"
          using 1
          by (meson P.Con_rec(1) P.arr_in_Cong_class P.con_char
              P.Con_implies_Arr(2) P.arr_char P.con_implies_arr(1))
        moreover have "P.con [t] [u]"
          using 1 by (simp add: P.con_char)
        ultimately show ?thesis
          using Resid_by_members [of "\<lbrace>[t]\<rbrace>" "\<lbrace>[u]\<rbrace>" "[t]" "[u]"]
          by (simp add: "1")
      qed
      assume 1: "\<not> t \<frown> u"
      have "\<lbrace>[t \\ u]\<rbrace> = {}"
        using 1 R.arrI
        by (metis Collect_empty_eq P.Con_Arr_self P.Con_rec(1)
            P.Cong_class_def P.Cong_imp_arr(1) P.arr_char R.arr_resid_iff_con)
      also have "... = \<lbrace>[t]\<rbrace> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<lbrace>[u]\<rbrace>"
        by (metis (full_types) "1" Con_char CollectD P.Con_rec(1) P.Cong_class_def
            P.Cong_imp_arr(1) P.arr_in_Cong_class con_char\<^sub>C\<^sub>C' null_char conI)
      finally show ?thesis by simp
    qed

    lemma incl_reflects_con:
    assumes "\<lbrace>[t]\<rbrace> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<lbrace>[u]\<rbrace>"
    shows "t \<frown> u"
      by (metis P.Con_rec(1) P.Cong_class_def P.Cong_imp_arr(1) P.arr_in_Cong_class
          CollectD assms con_char\<^sub>C\<^sub>C' con_char\<^sub>Q\<^sub>C\<^sub>N)

    text \<open>
      The inclusion map is a simulation.
    \<close>

    sublocale incl: simulation resid Resid incl
    proof
      show "\<And>t. \<not> R.arr t \<Longrightarrow> incl t = null"
        by (metis Collect_empty_eq P.Cong_class_def P.Cong_imp_arr(1) P.Ide.simps(2)
            P.Resid_rec(1) P.cong_reflexive P.elements_are_arr P.ide_char P.ide_closed
            P.not_arr_null P.null_char R.prfx_implies_con null_char R.con_implies_arr(1))
      show "\<And>t u. t \<frown> u \<Longrightarrow> incl t \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> incl u"
        using incl_preserves_con by blast
      show "\<And>t u. t \<frown> u \<Longrightarrow> incl (t \\ u) = incl t \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> incl u"
        using incl_preserves_resid by blast
    qed

    lemma inclusion_is_simulation:
    shows "simulation resid Resid incl"
      ..

    lemma incl_preserves_arr:
    assumes "R.arr a"
    shows "arr \<lbrace>[a]\<rbrace>"
      using assms incl_preserves_con by auto

    lemma incl_preserves_ide:
    assumes "R.ide a"
    shows "ide \<lbrace>[a]\<rbrace>"
      by (metis assms incl_preserves_con incl_preserves_resid R.ide_def ide_def)

    lemma cong_iff_eq_incl:
    assumes "R.arr t" and "R.arr u"
    shows "\<lbrace>[t]\<rbrace> = \<lbrace>[u]\<rbrace> \<longleftrightarrow> t \<sim> u"
    proof
      show "\<lbrace>[t]\<rbrace> = \<lbrace>[u]\<rbrace> \<Longrightarrow> t \<sim> u"
        by (metis P.Con_rec(1) P.Ide.simps(2) P.Resid.simps(3) P.arr_in_Cong_class
            P.con_char R.arr_def R.cong_reflexive assms(1) ide_char\<^sub>C\<^sub>C
            incl_preserves_con incl_preserves_ide incl_preserves_resid incl_reflects_con
            P.arr_resid_iff_con)
      show "t \<sim> u \<Longrightarrow> \<lbrace>[t]\<rbrace> = \<lbrace>[u]\<rbrace>"
        using assms
        by (metis incl_preserves_resid extensional incl_preserves_ide)
    qed

    text \<open>
      The inclusion is surjective on identities.
    \<close>

    lemma img_incl_ide:
    shows "incl ` (Collect R.ide) = Collect ide"
    proof
      show "incl ` Collect R.ide \<subseteq> Collect ide"
        by (simp add: image_subset_iff)
      show "Collect ide \<subseteq> incl ` Collect R.ide"
      proof
        fix \<A>
        assume \<A>: "\<A> \<in> Collect ide"
        obtain A where A: "A \<in> \<A>"
          using \<A> ide_char by blast
        have "P.NPath A"
          by (metis A Ball_Collect \<A> ide_char' mem_Collect_eq)
        obtain a where a: "a \<in> P.Srcs A"
          using \<open>P.NPath A\<close>
          by (meson P.NPath_implies_Arr equals0I P.Arr_has_Src)
        have "P.Cong\<^sub>0 A [a]"
        proof -
          have "P.Ide [a]"
            by (metis NPath_char P.Con_Arr_self P.Ide.simps(2) P.NPath_implies_Arr
                P.Resid_Ide(1) P.Srcs.elims R.in_sourcesE \<open>P.NPath A\<close> a)
          thus ?thesis
            using a A
            by (metis P.Ide.simps(2) P.ide_char P.ide_closed \<open>P.NPath A\<close> NPath_char
                P.Con_single_ide_iff P.Ide_implies_Arr P.Resid_Arr_Ide_ind P.Resid_Arr_Src)
        qed
        have "\<A> = \<lbrace>[a]\<rbrace>"
          by (metis A P.Cong\<^sub>0_imp_con P.Cong\<^sub>0_implies_Cong P.Cong\<^sub>0_transitive P.Cong_class_eqI
              P.ide_char P.resid_arr_ide Resid_by_members \<A> \<open>A \<^sup>*\<approx>\<^sub>0\<^sup>* [a]\<close> \<open>P.NPath A\<close> arr_char
              NPath_char ideE ide_implies_arr mem_Collect_eq)
        thus "\<A> \<in> incl ` Collect R.ide"
          using NPath_char P.Ide.simps(2) P.backward_stable \<open>A \<^sup>*\<approx>\<^sub>0\<^sup>* [a]\<close> \<open>P.NPath A\<close> by blast
      qed
    qed

  end

  subsection "Composite Completion of an Extensional RTS"

  locale composite_completion_of_extensional_rts =
    R: extensional_rts +
    composite_completion
  begin

    sublocale P: paths_in_weakly_extensional_rts resid ..

    notation comp (infixl "\<lbrace>\<^sup>*\<cdot>\<^sup>*\<rbrace>" 55)

    text \<open>
      When applied to an extensional RTS, the composite completion construction does not
      identify any states that are distinct in the original RTS.
    \<close>

    lemma incl_injective_on_ide:
    shows "inj_on incl (Collect R.ide)"
      using R.extensional cong_iff_eq_incl
      by (intro inj_onI) auto

    text \<open>
      When applied to an extensional RTS, the composite completion construction
      is a bijection between the states of the original RTS and the states of its completion.
    \<close>

    lemma incl_bijective_on_ide:
    shows "bij_betw incl (Collect R.ide) (Collect ide)"
      using incl_injective_on_ide img_incl_ide bij_betw_def by blast

  end

  subsection "Freeness of Composite Completion"

  text \<open>
    In this section we show that the composite completion construction is free:
    any simulation from RTS \<open>A\<close> to an extensional RTS with composites \<open>B\<close>
    extends uniquely to a simulation on the composite completion of \<open>A\<close>.
  \<close>

  locale extension_of_simulation =
    A: paths_in_rts resid\<^sub>A +
    B: extensional_rts_with_composites resid\<^sub>B +
    F: simulation resid\<^sub>A resid\<^sub>B F
  for resid\<^sub>A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and resid\<^sub>B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and F :: "'a \<Rightarrow> 'b"
  begin

    notation A.Resid    (infix "\<^sup>*\\\<^sub>A\<^sup>*" 70)
    notation A.Resid1x  (infix "\<^sup>1\\\<^sub>A\<^sup>*" 70)
    notation A.Residx1  (infix "\<^sup>*\\\<^sub>A\<^sup>1" 70)
    notation A.Con      (infix "\<^sup>*\<frown>\<^sub>A\<^sup>*" 70)
    notation B.comp     (infixl "\<cdot>\<^sub>B" 55)
    notation B.con      (infix "\<frown>\<^sub>B" 50)

    fun map
    where "map [] = B.null"
        | "map [t] = F t"
        | "map (t # T) = (if A.arr (t # T) then F t \<cdot>\<^sub>B map T else B.null)"

    lemma map_o_incl_eq:
    shows "map (A.incl t) = F t"
      by (simp add: A.null_char F.extensional)

    lemma extensional:
    shows "\<not> A.arr T \<Longrightarrow> map T = B.null"
      using F.extensional A.arr_char
      by (metis A.Arr.simps(2) map.elims)

    lemma preserves_comp:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []; A.Arr (T @ U)\<rbrakk> \<Longrightarrow> map (T @ U) = map T \<cdot>\<^sub>B map U"
    proof (induct T arbitrary: U)
      show "\<And>U. [] \<noteq> [] \<Longrightarrow> map ([] @ U) = map [] \<cdot>\<^sub>B map U"
        by simp
      fix t and T U :: "'a list"
      assume ind: "\<And>U. \<lbrakk>T \<noteq> []; U \<noteq> []; A.Arr (T @ U)\<rbrakk>
                          \<Longrightarrow> map (T @ U) = map T \<cdot>\<^sub>B map U"
      assume U: "U \<noteq> []"
      assume Arr: "A.Arr ((t # T) @ U)"
      hence 1: "A.Arr (t # (T @ U))"
        by simp
      have 2: "A.Arr (t # T)"
        by (metis A.Con_Arr_self A.Con_append(1) A.Con_implies_Arr(1) Arr U append_is_Nil_conv
            list.distinct(1))
      show "map ((t # T) @ U) = B.comp (map (t # T)) (map U)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          by (metis (full_types) "1" A.arr_char U append_Cons append_Nil list.exhaust
              map.simps(2) map.simps(3))
        assume T: "T \<noteq> []"
        have "map ((t # T) @ U) = map (t # (T @ U))"
          by simp
        also have "... = F t \<cdot>\<^sub>B map (T @ U)"
          using T 1
          by (metis A.arr_char Nil_is_append_conv list.exhaust map.simps(3))
        also have "... =  F t \<cdot>\<^sub>B (map T \<cdot>\<^sub>B map U)"
          using ind
          by (metis "1" A.Con_Arr_self A.Con_implies_Arr(1) A.Con_rec(4) T U append_is_Nil_conv)
        also have "... = F t \<cdot>\<^sub>B map T \<cdot>\<^sub>B map U"
          using B.comp_assoc\<^sub>E\<^sub>C by blast
        also have "... = map (t # T) \<cdot>\<^sub>B map U"
          using T 2
          by (metis A.arr_char list.exhaust map.simps(3))
        finally show "map ((t # T) @ U) = map (t # T) \<cdot>\<^sub>B map U" by simp
      qed
    qed

    lemma preserves_arr_ind:
    shows "\<lbrakk>A.arr T; a \<in> A.Srcs T\<rbrakk> \<Longrightarrow> B.arr (map T) \<and> B.src (map T) = F a"
    proof (induct T arbitrary: a)
      show "\<And>a. \<lbrakk>A.arr []; a \<in> A.Srcs []\<rbrakk> \<Longrightarrow> B.arr (map []) \<and> B.src (map []) = F a"
        using A.arr_char by simp
      fix a t T
      assume a: "a \<in> A.Srcs (t # T)"
      assume tT: "A.arr (t # T)"
      assume ind: "\<And>a. \<lbrakk>A.arr T; a \<in> A.Srcs T\<rbrakk> \<Longrightarrow> B.arr (map T) \<and> B.src (map T) = F a"
      have 1: "a \<in> A.R.sources t"
        using a tT A.Con_imp_eq_Srcs A.Con_initial_right A.Srcs.simps(2) A.con_char
        by blast
      show "B.arr (map (t # T)) \<and> B.src (map (t # T)) = F a"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          by (metis "1" A.Arr.simps(2) A.arr_char B.arr_has_un_source B.src_in_sources
              F.preserves_reflects_arr F.preserves_sources image_subset_iff map.simps(2) tT)
        assume T: "T \<noteq> []"
        obtain a' where a': "a' \<in> A.R.targets t"
          using tT "1" A.R.resid_source_in_targets by auto
        have 2: "a' \<in> A.Srcs T"
          using a' tT
          by (metis A.Con_Arr_self A.R.sources_resid A.Srcs.simps(2) A.arr_char T
              A.Con_imp_eq_Srcs A.Con_rec(4))
        have "B.arr (map (t # T)) \<longleftrightarrow> B.arr (F t \<cdot>\<^sub>B map T)"
          using tT T by (metis map.simps(3) neq_Nil_conv)
        also have 2: "... \<longleftrightarrow> True"
          by (metis (no_types, lifting) "2" A.arr_char B.arr_comp\<^sub>E\<^sub>C B.arr_has_un_target
              B.trg_in_targets F.preserves_reflects_arr F.preserves_targets T a'
              A.Arr.elims(2) image_subset_iff ind list.sel(1) list.sel(3) tT)
        finally have "B.arr (map (t # T))" by simp
        moreover have "B.src (map (t # T)) = F a"
        proof -
          have "B.src (map (t # T)) = B.src (F t \<cdot>\<^sub>B map T)"
            using tT T by (metis map.simps(3) neq_Nil_conv)
          also have "... = B.src (F t)"
            using "2" B.con_comp_iff by force
          also have "... = F a"
            by (meson "1" B.weakly_extensional_rts_axioms F.simulation_axioms
                simulation_to_weakly_extensional_rts.preserves_src
                simulation_to_weakly_extensional_rts_def)
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
    qed

    lemma preserves_arr:
    shows "A.arr T \<Longrightarrow> B.arr (map T)"
      using preserves_arr_ind A.arr_char A.Arr_has_Src by blast

    lemma preserves_src:
    assumes "A.arr T" and "a \<in> A.Srcs T"
    shows "B.src (map T) = F a"
      using assms preserves_arr_ind by simp

    lemma preserves_trg:
    shows "\<lbrakk>A.arr T; b \<in> A.Trgs T\<rbrakk> \<Longrightarrow> B.trg (map T) = F b"
    proof (induct T)
      show "\<lbrakk>A.arr []; b \<in> A.Trgs []\<rbrakk> \<Longrightarrow> B.trg (map []) = F b"
        by simp
      fix t T
      assume tT: "A.arr (t # T)"
      assume b: "b \<in> A.Trgs (t # T)"
      assume ind: "\<lbrakk>A.arr T; b \<in> A.Trgs T\<rbrakk> \<Longrightarrow> B.trg (map T) = F b"
      show "B.trg (map (t # T)) = F b"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT b
          by (metis A.Trgs.simps(2) B.arr_has_un_target B.trg_in_targets F.preserves_targets
              preserves_arr image_subset_iff map.simps(2))
        assume T: "T \<noteq> []"
        have 1: "B.trg (map (t # T)) = B.trg (F t \<cdot>\<^sub>B map T)"
          using tT T b
          by (metis map.simps(3) neq_Nil_conv)
        also have "... = B.trg (map T)"
          by (metis B.arr_trg_iff_arr B.composable_iff_arr_comp B.trg_comp calculation
              preserves_arr tT)
        also have "... = F b"
          using tT b ind
          by (metis A.Trgs.simps(3) T A.Arr.simps(3) A.arr_char list.exhaust)
        finally show ?thesis by simp
      qed
    qed

    lemma preserves_Resid1x_ind:
    shows "t \<^sup>1\\\<^sub>A\<^sup>* U \<noteq> A.R.null \<Longrightarrow> F t \<frown>\<^sub>B map U \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* U) = F t \\\<^sub>B map U"
    proof (induct U arbitrary: t)
      show "\<And>t. t \<^sup>1\\\<^sub>A\<^sup>* [] \<noteq> A.R.null \<Longrightarrow> F t \<frown>\<^sub>B map [] \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* []) = F t \\\<^sub>B map []"
        by simp
      fix t u U
      assume uU: "t \<^sup>1\\\<^sub>A\<^sup>* (u # U) \<noteq> A.R.null"
      assume ind: "\<And>t. t \<^sup>1\\\<^sub>A\<^sup>* U \<noteq> A.R.null
                          \<Longrightarrow> F t \<frown>\<^sub>B map U \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* U) = F t \\\<^sub>B map U"
      show "F t \<frown>\<^sub>B map (u # U) \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* (u # U)) = F t \\\<^sub>B map (u # U)"
      proof
        show 1: "F t \<frown>\<^sub>B map (u # U)"
        proof (cases "U = []")
          show "U = [] \<Longrightarrow> ?thesis"
            using A.Resid1x.simps(2) map.simps(2) F.preserves_con uU by fastforce
          assume U: "U \<noteq> []"
          have 3: "[t] \<^sup>*\\\<^sub>A\<^sup>* [u] \<noteq> [] \<and> ([t] \<^sup>*\\\<^sub>A\<^sup>* [u]) \<^sup>*\\\<^sub>A\<^sup>* U \<noteq> []"
            using A.Con_cons(2) [of "[t]" U u]
            by (meson A.Resid1x_as_Resid' U not_Cons_self2 uU)
          hence 2: "F t \<frown>\<^sub>B F u \<and> F t \\\<^sub>B F u \<frown>\<^sub>B map U"
            by (metis A.Con_rec(1) A.Con_sym A.Con_sym1 A.Residx1_as_Resid A.Resid_rec(1)
                F.preserves_con F.preserves_resid ind)
          moreover have "B.seq (F u) (map U)"
            by (metis B.coinitial_iff\<^sub>W\<^sub>E B.con_imp_coinitial B.seqI\<^sub>W\<^sub>E(1) B.src_resid calculation)
          ultimately have "F t \<frown>\<^sub>B map ([u] @ U)"
            using B.con_comp_iff\<^sub>E\<^sub>C(1) [of "F t" "F u" "map U"] B.con_sym preserves_comp
            by (metis 3 A.Con_cons(2) A.Con_implies_Arr(2)
                append.left_neutral append_Cons map.simps(2) not_Cons_self2)
          thus ?thesis by simp
        qed
        show "F (t \<^sup>1\\\<^sub>A\<^sup>* (u # U)) = F t \\\<^sub>B map (u # U)"
        proof (cases "U = []")
          show "U = [] \<Longrightarrow> ?thesis"
            using A.Resid1x.simps(2) F.preserves_resid map.simps(2) uU by fastforce
          assume U: "U \<noteq> []"
          have "F (t \<^sup>1\\\<^sub>A\<^sup>* (u # U)) = F ((t \\\<^sub>A u) \<^sup>1\\\<^sub>A\<^sup>* U)"
            using A.Resid1x_as_Resid' A.Resid_rec(3) U uU by metis
          also have "... = F (t \\\<^sub>A u) \\\<^sub>B map U"
            using uU U ind A.Con_rec(3) A.Resid1x_as_Resid [of "t \\\<^sub>A u" U] 
            by (metis A.Resid1x.simps(3) list.exhaust)
          also have "... = (F t \\\<^sub>B F u) \\\<^sub>B map U"
            using uU U
            by (metis A.Resid1x_as_Resid' F.preserves_resid A.Con_rec(3))
          also have "... = F t \\\<^sub>B (F u \<cdot>\<^sub>B map U)"
            by (metis B.comp_null(2) B.composable_iff_comp_not_null B.con_compI(2) B.conI
                B.con_sym_ax B.mediating_transition B.null_is_zero(2) B.resid_comp(1))
          also have "... = F t \\\<^sub>B map (u # U)"
            by (metis A.Resid1x_as_Resid' A.con_char U map.simps(3) neq_Nil_conv
                A.con_implies_arr(2) uU)
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma preserves_Residx1_ind:
    shows "U \<^sup>*\\\<^sub>A\<^sup>1 t \<noteq> [] \<Longrightarrow> map U \<frown>\<^sub>B F t \<and> map (U \<^sup>*\\\<^sub>A\<^sup>1 t) = map U \\\<^sub>B F t"
    proof (induct U arbitrary: t)
      show "\<And>t. [] \<^sup>*\\\<^sub>A\<^sup>1 t \<noteq> [] \<Longrightarrow> map [] \<frown>\<^sub>B F t \<and> map ([] \<^sup>*\\\<^sub>A\<^sup>1 t) = map [] \\\<^sub>B F t"
        by simp
      fix t u U
      assume ind: "\<And>t. U \<^sup>*\\\<^sub>A\<^sup>1 t \<noteq> [] \<Longrightarrow> map U \<frown>\<^sub>B F t \<and> map (U \<^sup>*\\\<^sub>A\<^sup>1 t) = map U \\\<^sub>B F t"
      assume uU: "(u # U) \<^sup>*\\\<^sub>A\<^sup>1 t \<noteq> []"
      show "map (u # U) \<frown>\<^sub>B F t \<and> map ((u # U) \<^sup>*\\\<^sub>A\<^sup>1 t) = map (u # U) \\\<^sub>B F t"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using A.Residx1.simps(2) F.preserves_con F.preserves_resid map.simps(2) uU
          by presburger
        assume U: "U \<noteq> []"
        show ?thesis
        proof
          show "map (u # U) \<frown>\<^sub>B F t"
            using uU U A.Con_sym1 B.con_sym preserves_Resid1x_ind by blast
          show "map ((u # U) \<^sup>*\\\<^sub>A\<^sup>1 t) = map (u # U) \\\<^sub>B F t"
          proof -
            have "map ((u # U) \<^sup>*\\\<^sub>A\<^sup>1 t) = map ((u \\\<^sub>A t) # U \<^sup>*\\\<^sub>A\<^sup>1 (t \\\<^sub>A u))"
              using uU U A.Residx1_as_Resid A.Resid_rec(2) by fastforce
            also have "... = F (u \\\<^sub>A t) \<cdot>\<^sub>B map (U \<^sup>*\\\<^sub>A\<^sup>1 (t \\\<^sub>A u))"
              by (metis A.Residx1_as_Resid A.arr_char U A.Con_imp_Arr_Resid
                  A.Con_rec(2) A.Resid_rec(2) list.exhaust map.simps(3) uU)
            also have "... = F (u \\\<^sub>A t) \<cdot>\<^sub>B map U \\\<^sub>B F (t \\\<^sub>A u)"
              using uU U ind A.Con_rec(2) A.Residx1_as_Resid by force
            also have "... = (F u \\\<^sub>B F t) \<cdot>\<^sub>B map U \\\<^sub>B (F t \\\<^sub>B F u)"
              using uU U
              by (metis A.Con_initial_right A.Con_rec(1) A.Con_sym1 A.Resid1x_as_Resid'
                  A.Residx1_as_Resid F.preserves_resid)
            also have "... = (F u \<cdot>\<^sub>B map U) \\\<^sub>B F t"
              by (metis B.comp_null(2) B.composable_iff_comp_not_null B.con_compI(2) B.con_sym
                  B.mediating_transition B.null_is_zero(2) B.resid_comp(2) B.con_def)
            also have "... = map (u # U) \\\<^sub>B F t"
              by (metis A.Con_implies_Arr(2) A.Con_sym A.Residx1_as_Resid U
                  A.arr_char map.simps(3) neq_Nil_conv uU)
            finally show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma preserves_resid_ind:
    shows "A.con T U \<Longrightarrow> map T \<frown>\<^sub>B map U \<and> map (T \<^sup>*\\\<^sub>A\<^sup>* U) = map T \\\<^sub>B map U"
    proof (induct T arbitrary: U)
      show "\<And>U. A.con [] U \<Longrightarrow> map [] \<frown>\<^sub>B map U \<and> map ([] \<^sup>*\\\<^sub>A\<^sup>* U) = map [] \\\<^sub>B map U"
        using A.con_char A.Resid.simps(1) by blast
      fix t T U
      assume tT: "A.con (t # T) U"
      assume ind: "\<And>U. A.con T U \<Longrightarrow>
                         map T \<frown>\<^sub>B map U \<and> map (T \<^sup>*\\\<^sub>A\<^sup>* U) = map T \\\<^sub>B map U"
      show "map (t # T) \<frown>\<^sub>B map U \<and> map ((t # T) \<^sup>*\\\<^sub>A\<^sup>* U) = map (t # T) \\\<^sub>B map U"
      proof (cases "T = []")
        assume T: "T = []"
        show ?thesis
          using T tT
          apply simp
          by (metis A.Resid1x_as_Resid A.Residx1_as_Resid A.con_char
              A.Con_sym A.Con_sym1 map.simps(2) preserves_Resid1x_ind)
        next
        assume T: "T \<noteq> []"
        have 1: "map (t # T) = F t \<cdot>\<^sub>B map T"
          using tT T
          by (metis A.con_implies_arr(1) list.exhaust map.simps(3))
        show ?thesis
        proof
          show 2: "B.con (map (t # T)) (map U)"
            using T tT
            by (metis "1" A.Con_cons(1) A.Residx1_as_Resid A.con_char A.not_arr_null
                A.null_char B.composable_iff_comp_not_null B.con_compI(2) B.con_sym
                B.not_arr_null preserves_arr ind preserves_Residx1_ind A.con_implies_arr(1-2))
          show "map ((t # T) \<^sup>*\\\<^sub>A\<^sup>* U) = map (t # T) \\\<^sub>B map U"
          proof -
            have "map ((t # T) \<^sup>*\\\<^sub>A\<^sup>* U) = map (([t] \<^sup>*\\\<^sub>A\<^sup>* U) @ (T \<^sup>*\\\<^sub>A\<^sup>* (U \<^sup>*\\\<^sub>A\<^sup>* [t])))"
              by (metis A.Resid.simps(1) A.Resid_cons(1) A.con_char A.ex_un_null tT)
            also have "... = map ([t] \<^sup>*\\\<^sub>A\<^sup>* U) \<cdot>\<^sub>B map (T \<^sup>*\\\<^sub>A\<^sup>* (U \<^sup>*\\\<^sub>A\<^sup>* [t]))"
              by (metis A.Arr.simps(1) A.Con_imp_Arr_Resid A.Con_implies_Arr(2) A.Con_sym
                  A.Resid_cons(1-2) A.con_char T preserves_comp tT)
            also have "... = (map [t] \\\<^sub>B map U) \<cdot>\<^sub>B map (T \<^sup>*\\\<^sub>A\<^sup>* (U \<^sup>*\\\<^sub>A\<^sup>* [t]))"
              by (metis A.Con_initial_right A.Con_sym A.Resid1x_as_Resid
                  A.Residx1_as_Resid A.con_char A.Con_sym1 map.simps(2)
                  preserves_Resid1x_ind tT)
            also have "... = (map [t] \\\<^sub>B map U) \<cdot>\<^sub>B (map T \\\<^sub>B map (U \<^sup>*\\\<^sub>A\<^sup>* [t]))"
              using tT T ind
              by (metis A.Con_cons(1) A.Con_sym A.Resid.simps(1) A.con_char)
            also have "... = (map [t] \\\<^sub>B map U) \<cdot>\<^sub>B (map T \\\<^sub>B (map U \\\<^sub>B map [t]))"
              using tT T
              by (metis A.Con_cons(1) A.Con_sym A.Resid.simps(2) A.Residx1_as_Resid
                        A.con_char map.simps(2) preserves_Residx1_ind)
            also have "... = (F t \\\<^sub>B map U) \<cdot>\<^sub>B (map T \\\<^sub>B (map U \\\<^sub>B F t))"
              using tT T by simp
            also have "... = map (t # T) \\\<^sub>B map U"
              using 1 2 B.resid_comp(2) by presburger
            finally show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma preserves_con:
    assumes "A.con T U"
    shows "map T \<frown>\<^sub>B map U"
      using assms preserves_resid_ind by simp

    lemma preserves_resid:
    assumes "A.con T U"
    shows "map (T \<^sup>*\\\<^sub>A\<^sup>* U) = map T \\\<^sub>B map U"
      using assms preserves_resid_ind by simp

    sublocale simulation A.Resid resid\<^sub>B map
      using A.con_char preserves_con preserves_resid extensional
      by unfold_locales auto

    sublocale simulation_to_extensional_rts A.Resid resid\<^sub>B map ..

    lemma is_universal:
    assumes "rts_with_composites resid\<^sub>B" and "simulation resid\<^sub>A resid\<^sub>B F"
    shows "\<exists>!F'. simulation A.Resid resid\<^sub>B F' \<and> F' o A.incl = F"
    proof
      interpret B: rts_with_composites resid\<^sub>B
        using assms by auto
      interpret F: simulation resid\<^sub>A resid\<^sub>B F
        using assms by auto
      show "simulation A.Resid resid\<^sub>B map \<and> map \<circ> A.incl = F"
        using map_o_incl_eq simulation_axioms by auto
      show "\<And>F'. simulation A.Resid resid\<^sub>B F' \<and> F' o A.incl = F \<Longrightarrow> F' = map"
      proof
        fix F' T
        assume F': "simulation A.Resid resid\<^sub>B F' \<and> F' o A.incl = F"
        interpret F': simulation A.Resid resid\<^sub>B F'
          using F' by simp
        show "F' T = map T"
        proof (induct T)
          show "F' [] = map []"
            by (simp add: A.arr_char F'.extensional)
          fix t T
          assume ind: "F' T = map T"
          show "F' (t # T) = map (t # T)"
          proof (cases "A.Arr (t # T)")
            show "\<not> A.Arr (t # T) \<Longrightarrow> ?thesis"
              by (simp add: A.arr_char F'.extensional extensional)
            assume tT: "A.Arr (t # T)"
            show ?thesis
            proof (cases "T = []")
              show 2: "T = [] \<Longrightarrow> ?thesis"
                using F' tT by auto
              assume T: "T \<noteq> []"
              have "F' (t # T) = F' [t] \<cdot>\<^sub>B map T"
              proof -
                have "F' (t # T) = F' ([t] @ T)"
                  by simp
                also have "... = F' [t] \<cdot>\<^sub>B F' T"
                proof -
                  have "A.composite_of [t] T ([t] @ T)"
                    using T tT
                    by (metis (full_types) A.Arr.simps(2) A.Con_Arr_self
                        A.append_is_composite_of A.Con_implies_Arr(1) A.Con_imp_eq_Srcs
                        A.Con_rec(4) A.Resid_rec(1) A.Srcs_Resid A.seq_char A.R.arrI)
                  thus ?thesis
                    using F'.preserves_composites [of "[t]" T "[t] @ T"] B.comp_is_composite_of
                    by auto
                qed
                also have "... = F' [t] \<cdot>\<^sub>B map T"
                  using T ind by simp
                finally show ?thesis by simp
              qed
              also have "... = (F' \<circ> A.incl) t \<cdot>\<^sub>B map T"
                using tT
                by (simp add: A.arr_char A.null_char F'.extensional)
              also have "... = F t \<cdot>\<^sub>B map T"
                using F' by simp
              also have "... = map (t # T)"
                using T tT
                by (metis A.arr_char list.exhaust map.simps(3))
              finally show ?thesis by simp
            qed
          qed
        qed
      qed
    qed

  end

  (*
   * TODO: Localize to context rts?
   *)
  lemma composite_completion_of_rts:
  assumes "rts A"
  shows "\<exists>(C :: 'a list resid) I. rts_with_composites C \<and> simulation A C I \<and>
          (\<forall>B (J :: 'a \<Rightarrow> 'c). extensional_rts_with_composites B \<and> simulation A B J
                                 \<longrightarrow> (\<exists>!J'. simulation C B J' \<and> J' o I = J))"
  proof (intro exI conjI)
    interpret A: rts A
      using assms by auto
    interpret P\<^sub>A: paths_in_rts A ..
    show "rts_with_composites P\<^sub>A.Resid"
      using P\<^sub>A.rts_with_composites_axioms by simp
    show "simulation A P\<^sub>A.Resid P\<^sub>A.incl"
      using P\<^sub>A.incl_is_simulation by simp
    show "\<forall>B (J :: 'a \<Rightarrow> 'c). extensional_rts_with_composites B \<and> simulation A B J
                                \<longrightarrow> (\<exists>!J'. simulation P\<^sub>A.Resid B J' \<and> J' o P\<^sub>A.incl = J)"
    proof (intro allI impI)
      fix B :: "'c resid" and J
      assume 1: "extensional_rts_with_composites B \<and> simulation A B J"
      interpret B: extensional_rts_with_composites B
        using 1 by simp
      interpret J: simulation A B J
        using 1 by simp
      interpret J: extension_of_simulation A B J
        ..
      have "simulation P\<^sub>A.Resid B J.map"
        using J.simulation_axioms by simp
      moreover have "J.map o P\<^sub>A.incl = J"
        using J.map_o_incl_eq by auto
      moreover have "\<And>J'. simulation P\<^sub>A.Resid B J' \<and> J' o P\<^sub>A.incl = J \<Longrightarrow> J' = J.map"
        using "1" B.rts_with_composites_axioms J.is_universal J.simulation_axioms
              calculation(2)
        by blast
      ultimately show "\<exists>!J'. simulation P\<^sub>A.Resid B J' \<and> J' \<circ> P\<^sub>A.incl = J" by auto
    qed
  qed

  section "Constructions on RTS's"

  subsection "Products of RTS's"

  locale product_rts =
    A: rts A +
    B: rts B
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  begin

    notation A.con     (infix "\<frown>\<^sub>A" 50)
    notation A.prfx    (infix "\<lesssim>\<^sub>A" 50)
    notation A.cong    (infix "\<sim>\<^sub>A" 50)

    notation B.con     (infix "\<frown>\<^sub>B" 50)
    notation B.prfx    (infix "\<lesssim>\<^sub>B" 50)
    notation B.cong    (infix "\<sim>\<^sub>B" 50)

    type_synonym ('c, 'd) arr = "'c * 'd"

    abbreviation (input) Null :: "('a, 'b) arr"                                 
    where "Null \<equiv> (A.null, B.null)"

    definition resid :: "('a, 'b) arr \<Rightarrow> ('a, 'b) arr \<Rightarrow> ('a, 'b) arr"
    where "resid t u = (if fst t \<frown>\<^sub>A fst u \<and> snd t \<frown>\<^sub>B snd u
                        then (fst t \\\<^sub>A fst u, snd t \\\<^sub>B snd u)
                        else Null)"

    notation resid      (infix "\\" 70)

    sublocale partial_magma resid
      by unfold_locales
        (metis A.con_implies_arr(1-2) A.not_arr_null fst_conv resid_def)

    lemma is_partial_magma:
    shows "partial_magma resid"
      ..

    lemma null_char [simp]:
    shows "null = Null"
      by (metis B.null_is_zero(1) B.residuation_axioms ex_un_null null_is_zero(1)
          resid_def residuation.conE snd_conv)

    sublocale residuation resid
    proof
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> u \\ t \<noteq> null"
        by (metis A.con_def A.con_sym null_char prod.inject resid_def B.con_sym)
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> (t \\ u) \\ (t \\ u) \<noteq> null"
        by (metis (no_types, lifting) A.arrE B.con_def B.con_imp_arr_resid fst_conv null_char
            resid_def A.arr_resid snd_conv)
      show "\<And>v t u. (v \\ t) \\ (u \\ t) \<noteq> null \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      proof -
        fix t u v
        assume 1: "(v \\ t) \\ (u \\ t) \<noteq> null"
        have "(fst v \\\<^sub>A fst t) \\\<^sub>A (fst u \\\<^sub>A fst t) \<noteq> A.null"
          by (metis 1 A.not_arr_null fst_conv null_char null_is_zero(1-2)
              resid_def A.arr_resid)
        moreover have "(snd v \\\<^sub>B snd t) \\\<^sub>B (snd u \\\<^sub>B snd t) \<noteq> B.null"
          by (metis 1 B.not_arr_null snd_conv null_char null_is_zero(1-2)
              resid_def B.arr_resid)
        ultimately show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
          using resid_def null_char A.con_def B.con_def A.cube B.cube
          apply simp
          by (metis (no_types, lifting) A.conI A.con_sym_ax A.resid_reflects_con
              B.con_sym_ax B.null_is_zero(1))
      qed
    qed

    lemma is_residuation:
    shows "residuation resid"
      ..

    notation con     (infix "\<frown>" 50)

    lemma arr_char [iff]:
    shows "arr t \<longleftrightarrow> A.arr (fst t) \<and> B.arr (snd t)"
      by (metis (no_types, lifting) A.arr_def B.arr_def B.conE null_char resid_def
          residuation.arr_def residuation.con_def residuation_axioms snd_eqD)

    lemma ide_char [iff]:
    shows "ide t \<longleftrightarrow> A.ide (fst t) \<and> B.ide (snd t)"
      by (metis (no_types, lifting) A.residuation_axioms B.residuation_axioms
          arr_char arr_def fst_conv null_char prod.collapse resid_def residuation.conE
          residuation.ide_def residuation.ide_implies_arr residuation_axioms snd_conv)

    lemma con_char [iff]:
    shows "t \<frown> u \<longleftrightarrow> fst t \<frown>\<^sub>A fst u \<and> snd t \<frown>\<^sub>B snd u"
      by (simp add: B.residuation_axioms con_def resid_def residuation.con_def)

    lemma trg_char:
    shows "trg t = (if arr t then (A.trg (fst t), B.trg (snd t)) else Null)"
      using A.trg_def B.trg_def resid_def trg_def by auto

    sublocale rts resid
    proof
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        by (simp add: trg_char)
      show 1: "\<And>a t. \<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
        by (simp add: A.resid_arr_ide B.resid_arr_ide resid_def)
      thus "\<And>a t. \<lbrakk>ide a; a \<frown> t\<rbrakk> \<Longrightarrow> ide (a \\ t)"
        using arr_resid cube
        apply (elim ideE, intro ideI)
         apply auto
        by (metis 1 conI con_sym_ax ideI null_is_zero(2))
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
      proof -
        fix t u
        assume tu: "t \<frown> u"
        obtain a1 where a1: "a1 \<in> A.sources (fst t) \<inter> A.sources (fst u)"
          by (meson A.con_imp_common_source all_not_in_conv con_char tu)
        obtain a2 where a2: "a2 \<in> B.sources (snd t) \<inter> B.sources (snd u)"
          by (meson B.con_imp_common_source all_not_in_conv con_char tu)
        have "ide (a1, a2) \<and> (a1, a2) \<frown> t \<and> (a1, a2) \<frown> u"
          using a1 a2 ide_char con_char
          by (metis A.con_imp_common_source A.in_sourcesE A.sources_eqI
              B.con_imp_common_source B.in_sourcesE B.sources_eqI con_sym
              fst_conv inf_idem snd_conv tu)
        thus "\<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u" by blast
      qed
      show "\<And>t u v. \<lbrakk>ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
      proof -
        fix t u v
        assume tu: "ide (t \\ u)"
        assume uv: "u \<frown> v"
        have "A.ide (fst t \\\<^sub>A fst u) \<and> B.ide (snd t \\\<^sub>B snd u)"
          using tu ide_char
          by (metis conI con_char fst_eqD ide_implies_arr not_arr_null resid_def snd_conv)
        moreover have "fst u \<frown>\<^sub>A fst v \<and> snd u \<frown>\<^sub>B snd v"
          using uv con_char by blast
        ultimately show "t \\ u \<frown> v \\ u"
          by (simp add: A.con_target A.con_sym A.prfx_implies_con
              B.con_target B.con_sym B.prfx_implies_con resid_def)
      qed
    qed

    lemma is_rts:
    shows "rts resid"
      ..

    notation prfx    (infix "\<lesssim>" 50)
    notation cong    (infix "\<sim>" 50)

    lemma sources_char:
    shows "sources t = A.sources (fst t) \<times> B.sources (snd t)"
      by force

    lemma targets_char:
    shows "targets t = A.targets (fst t) \<times> B.targets (snd t)"
    proof
      show "targets t \<subseteq> A.targets (fst t) \<times> B.targets (snd t)"
        using targets_def ide_char con_char resid_def trg_char trg_def by auto
      show "A.targets (fst t) \<times> B.targets (snd t) \<subseteq> targets t"
      proof
        fix a
        assume a: "a \<in> A.targets (fst t) \<times> B.targets (snd t)"
        show "a \<in> targets t"
        proof
          show "ide a"
            using a ide_char by auto
          show "trg t \<frown> a"
            using a trg_char con_char [of "trg t" a]
            by (metis (no_types, lifting) SigmaE arr_char con_char con_implies_arr(1)
                fst_conv A.in_targetsE B.in_targetsE A.arr_resid_iff_con B.arr_resid_iff_con
                A.trg_def B.trg_def snd_conv)
        qed
      qed
    qed

    lemma prfx_char:
    shows "t \<lesssim> u \<longleftrightarrow> fst t \<lesssim>\<^sub>A fst u \<and> snd t \<lesssim>\<^sub>B snd u"
      using A.prfx_implies_con B.prfx_implies_con resid_def by auto

    lemma cong_char:
    shows "t \<sim> u \<longleftrightarrow> fst t \<sim>\<^sub>A fst u \<and> snd t \<sim>\<^sub>B snd u"
      using prfx_char by auto

    lemma join_of_char:
    shows "join_of t u v \<longleftrightarrow> A.join_of (fst t) (fst u) (fst v) \<and> B.join_of (snd t) (snd u) (snd v)"
    and "joinable t u \<longleftrightarrow> A.joinable (fst t) (fst u) \<and> B.joinable (snd t) (snd u)"
    proof -
      show "\<And>v. join_of t u v \<longleftrightarrow>
                   A.join_of (fst t) (fst u) (fst v) \<and> B.join_of (snd t) (snd u) (snd v)"
      proof
        fix v
        show "join_of t u v \<Longrightarrow>
                A.join_of (fst t) (fst u) (fst v) \<and> B.join_of (snd t) (snd u) (snd v)"
        proof -
          assume 1: "join_of t u v"
          have 2: "t \<frown> u \<and> t \<frown> v \<and> u \<frown> v \<and> u \<frown> t \<and> v \<frown> t \<and> v \<frown> u"
            by (meson 1 bounded_imp_con con_prfx_composite_of(1) join_ofE con_sym)
          show "A.join_of (fst t) (fst u) (fst v) \<and> B.join_of (snd t) (snd u) (snd v)"
            using 1 2 prfx_char resid_def
            by (elim conjE join_ofE composite_ofE congE conE,
                intro conjI A.join_ofI B.join_ofI A.composite_ofI B.composite_ofI)
               auto
        qed
        show "A.join_of (fst t) (fst u) (fst v) \<and> B.join_of (snd t) (snd u) (snd v)
                \<Longrightarrow> join_of t u v"
          using cong_char resid_def
          by (elim conjE A.join_ofE B.join_ofE A.composite_ofE B.composite_ofE,
                 intro join_ofI composite_ofI)
             auto
      qed
      thus "joinable t u \<longleftrightarrow> A.joinable (fst t) (fst u) \<and> B.joinable (snd t) (snd u)"
        using joinable_def A.joinable_def B.joinable_def by simp
    qed

  end

  locale product_of_weakly_extensional_rts =
    A: weakly_extensional_rts A +
    B: weakly_extensional_rts B +
    product_rts
  begin

    sublocale weakly_extensional_rts resid
    proof
      show "\<And>t u. \<lbrakk>t \<sim> u; ide t; ide u\<rbrakk> \<Longrightarrow> t = u"
        by (metis cong_char ide_char prod.exhaust_sel A.weak_extensionality B.weak_extensionality)
    qed

    lemma is_weakly_extensional_rts:
    shows "weakly_extensional_rts resid"
      ..

    lemma src_char:
    shows "src t = (if arr t then (A.src (fst t), B.src (snd t)) else null)"
    proof (cases "arr t")
      show "\<not> arr t \<Longrightarrow> ?thesis"
        using src_def by presburger
      assume t: "arr t"
      show ?thesis
        using t con_char arr_char
        by (intro src_eqI) auto
    qed

  end

  locale product_of_extensional_rts =
    A: extensional_rts A +
    B: extensional_rts B +
    product_of_weakly_extensional_rts
  begin

    sublocale extensional_rts resid
    proof
      show "\<And>t u. t \<sim> u \<Longrightarrow> t = u"
        by (metis A.extensional B.extensional cong_char prod.collapse)
    qed

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

  end

  subsubsection "Product Simulations"

  locale product_simulation =
    A1: rts A1 +
    A0: rts A0 +
    B1: rts B1 +
    B0: rts B0 +
    A1xA0: product_rts A1 A0 +
    B1xB0: product_rts B1 B0 +
    F1: simulation A1 B1 F1 +
    F0: simulation A0 B0 F0
  for A1 :: "'a1 resid"      (infix "\\\<^sub>A\<^sub>1" 70)
  and A0 :: "'a0 resid"      (infix "\\\<^sub>A\<^sub>0" 70)
  and B1 :: "'b1 resid"      (infix "\\\<^sub>B\<^sub>1" 70)
  and B0 :: "'b0 resid"      (infix "\\\<^sub>B\<^sub>0" 70)
  and F1 :: "'a1 \<Rightarrow> 'b1"
  and F0 :: "'a0 \<Rightarrow> 'b0"
  begin

    definition map
    where "map = (\<lambda>a. if A1xA0.arr a then (F1 (fst a), F0 (snd a))
                      else (F1 A1.null, F0 A0.null))"

    lemma map_simp [simp]:
    assumes "A1.arr a1" and "A0.arr a0"
    shows "map (a1, a0) = (F1 a1, F0 a0)"
      using assms map_def by auto

    sublocale simulation A1xA0.resid B1xB0.resid map
    proof
      show "\<And>t. \<not> A1xA0.arr t \<Longrightarrow> map t = B1xB0.null"
        using map_def F1.extensional F0.extensional by auto
      show "\<And>t u. A1xA0.con t u \<Longrightarrow> B1xB0.con (map t) (map u)"
        using A1xA0.con_char B1xB0.con_char A1.con_implies_arr A0.con_implies_arr by auto
      show "\<And>t u. A1xA0.con t u \<Longrightarrow> map (A1xA0.resid t u) = B1xB0.resid (map t) (map u)"
        using A1xA0.resid_def B1xB0.resid_def A1.con_implies_arr A0.con_implies_arr
        by auto
    qed

    lemma is_simulation:
    shows "simulation A1xA0.resid B1xB0.resid map"
      ..

  end

  subsubsection "Binary Simulations"

  locale binary_simulation =
    A1: rts A1 +
    A0: rts A0 +
    A: product_rts A1 A0 +
    B: rts B +
    simulation A.resid B F
  for A1 :: "'a1 resid"    (infix "\\\<^sub>A\<^sub>1" 70)
  and A0 :: "'a0 resid"    (infix "\\\<^sub>A\<^sub>0" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and F :: "'a1 * 'a0 \<Rightarrow> 'b"
  begin

    lemma fixing_ide_gives_simulation_1:
    assumes "A1.ide a1"
    shows "simulation A0 B (\<lambda>t0. F (a1, t0))"
    proof
      show "\<And>t0. \<not> A0.arr t0 \<Longrightarrow> F (a1, t0) = B.null"
        using assms extensional A.arr_char by simp
      show "\<And>t0 u0. A0.con t0 u0 \<Longrightarrow> B.con (F (a1, t0)) (F (a1, u0))"
        using assms A.con_char preserves_con by auto
      show "\<And>t0 u0. A0.con t0 u0 \<Longrightarrow> F (a1, t0 \\\<^sub>A\<^sub>0 u0) = F (a1, t0) \\\<^sub>B F (a1, u0)"
        using assms A.con_char A.resid_def preserves_resid
        by (metis A1.ideE fst_conv snd_conv)
    qed

    lemma fixing_ide_gives_simulation_0:
    assumes "A0.ide a0"
    shows "simulation A1 B (\<lambda>t1. F (t1, a0))"
    proof
      show "\<And>t1. \<not> A1.arr t1 \<Longrightarrow> F (t1, a0) = B.null"
        using assms extensional A.arr_char by simp
      show "\<And>t1 u1. A1.con t1 u1 \<Longrightarrow> B.con (F (t1, a0)) (F (u1, a0))"
        using assms A.con_char preserves_con by auto
      show "\<And>t1 u1. A1.con t1 u1 \<Longrightarrow> F (t1 \\\<^sub>A\<^sub>1 u1, a0) = F (t1, a0) \\\<^sub>B F (u1, a0)"
        using assms A.con_char A.resid_def preserves_resid
        by (metis A0.ideE fst_conv snd_conv)
    qed

  end

  subsection "Sub-RTS's"

  locale sub_rts =
    R: rts R
  for R :: "'a resid"      (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool" +
  assumes inclusion: "Arr t \<Longrightarrow> R.arr t"
  and sources_closed: "Arr t \<Longrightarrow> R.sources t \<subseteq> Collect Arr"
  and resid_closed: "\<lbrakk>Arr t; Arr u; R.con t u\<rbrakk> \<Longrightarrow> Arr (t \\\<^sub>R u)"
  begin

    notation R.con     (infix "\<frown>\<^sub>R" 50)
    notation R.prfx    (infix "\<lesssim>\<^sub>R" 50)
    notation R.cong    (infix "\<sim>\<^sub>R" 50)

    definition resid  (infix "\\" 70)
    where "t \\ u \<equiv> (if Arr t \<and> Arr u \<and> t \<frown>\<^sub>R u then t \\\<^sub>R u else R.null)"

    sublocale partial_magma resid
      by unfold_locales
        (metis R.ex_un_null R.null_is_zero(2) resid_def)

    lemma is_partial_magma:
    shows "partial_magma resid"
      ..

    lemma null_char [simp]:
    shows "null = R.null"
      by (metis R.null_is_zero(1) ex_un_null null_is_zero(1) resid_def)

    sublocale residuation resid
    proof
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> u \\ t \<noteq> null"
        by (metis R.con_sym R.con_sym_ax null_char resid_def)
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> (t \\ u) \\ (t \\ u) \<noteq> null"
        by (metis R.arrE R.arr_resid R.not_arr_null null_char resid_closed resid_def)
      show "\<And>v t u. (v \\ t) \\ (u \\ t) \<noteq> null \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
        by (metis R.cube R.ex_un_null R.null_is_zero(1) R.residuation_axioms null_is_zero(2)
            resid_closed resid_def residuation.conE residuation.conI)
    qed

    lemma is_residuation:
    shows "residuation resid"
      ..

    notation con     (infix "\<frown>" 50)

    lemma arr_char [iff]:
    shows "arr t \<longleftrightarrow> Arr t"
    proof
      show "arr t \<Longrightarrow> Arr t"
        by (metis arrE conE null_char resid_def)
      show "Arr t \<Longrightarrow> arr t"
        by (metis R.arrE R.conE conI con_implies_arr(2) inclusion null_char resid_def)
    qed

    lemma ide_char [iff]:
    shows "ide t \<longleftrightarrow> Arr t \<and> R.ide t"
      by (metis R.ide_def arrE arr_char conE ide_def null_char resid_def)

    lemma con_char [iff]:
    shows "t \<frown> u \<longleftrightarrow> Arr t \<and> Arr u \<and> t \<frown>\<^sub>R u"
      using con_def resid_def by auto

    lemma trg_char:
    shows "trg t = (if arr t then R.trg t else null)"
      using R.trg_def arr_def resid_def trg_def by force

    sublocale rts resid
    proof
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        by (metis R.ide_trg arrE arr_char arr_resid ide_char inclusion trg_char trg_def)
      show "\<And>a t. \<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
        by (simp add: R.resid_arr_ide resid_def)
      show "\<And>a t. \<lbrakk>ide a; a \<frown> t\<rbrakk> \<Longrightarrow> ide (a \\ t)"
        by (metis R.resid_ide_arr arr_resid_iff_con arr_char con_char ide_char resid_def)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
        by (metis (full_types) R.con_imp_coinitial_ax R.con_sym R.in_sourcesI
            con_char ide_char in_mono mem_Collect_eq sources_closed)
      show "\<And>t u v. \<lbrakk>ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
        by (metis R.con_target arr_resid_iff_con con_char con_sym ide_char
            ide_implies_arr resid_closed resid_def)
    qed

    lemma is_rts:
    shows "rts resid"
      ..

    notation prfx    (infix "\<lesssim>" 50)
    notation cong    (infix "\<sim>" 50)

    lemma sources_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "sources t = {a. Arr t \<and> a \<in> R.sources t}"
      using sources_closed by auto

    lemma targets_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "targets t = {b. Arr t \<and> b \<in> R.targets t}"
    proof
      show "targets t \<subseteq> {b. Arr t \<and> b \<in> R.targets t}"
      proof
        fix b
        assume b: "b \<in> targets t"
        show "b \<in> {b. Arr t \<and> b \<in> R.targets t}"
        proof
          have "Arr t"
            using arr_iff_has_target b by force
          moreover have "Arr b"
            using b by blast
          moreover have "b \<in> R.targets t"
            by (metis R.in_targetsI b calculation(1) con_char in_targetsE
                arr_char ide_char trg_char)
          ultimately show "Arr t \<and> b \<in> R.targets t" by blast
        qed
      qed
      show "{b. Arr t \<and> b \<in> R.targets t} \<subseteq> targets t"
      proof
        fix b
        assume b: "b \<in> {b. Arr t \<and> b \<in> R.targets t}"
        show "b \<in> targets t"
        proof (intro in_targetsI)
          show "ide b"
            using b
            by (metis R.arrE ide_char inclusion mem_Collect_eq R.sources_resid
                R.target_is_ide resid_closed sources_closed subset_eq)
          show "trg t \<frown> b"
            using b
            using \<open>ide b\<close> ide_trg trg_char by auto
        qed
      qed
    qed

    lemma prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "t \<lesssim> u \<longleftrightarrow> Arr t \<and> Arr u \<and> t \<lesssim>\<^sub>R u"
      by (metis R.prfx_implies_con con_char ide_char prfx_implies_con resid_closed resid_def)

    lemma cong_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "t \<sim> u \<longleftrightarrow> Arr t \<and> Arr u \<and> t \<sim>\<^sub>R u"
      using prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S by force

    lemma inclusion_is_simulation:
    shows "simulation resid R (\<lambda>t. if arr t then t else null)"
      using resid_closed resid_def
      by unfold_locales auto

    interpretation P\<^sub>R: paths_in_rts R
      ..
    interpretation P: paths_in_rts resid
      ..

    lemma path_reflection:
    shows "\<lbrakk>P\<^sub>R.Arr T; set T \<subseteq> Collect Arr\<rbrakk> \<Longrightarrow> P.Arr T"
      apply (induct T)
       apply simp
    proof -
      fix t T
      assume ind: "\<lbrakk>P\<^sub>R.Arr T; set T \<subseteq> Collect Arr\<rbrakk> \<Longrightarrow> P.Arr T"
      assume tT: "P\<^sub>R.Arr (t # T)"
      assume set: "set (t # T) \<subseteq> Collect Arr"
      have 1: "R.arr t"
        using tT
        by (metis P\<^sub>R.Arr_imp_arr_hd list.sel(1))
      show "P.Arr (t # T)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using 1 set by simp
        assume T: "T \<noteq> []"
        show ?thesis
        proof
          show "arr t"
            using 1 arr_char set by simp
          show "P.Arr T"
            using T tT P\<^sub>R.Arr_imp_Arr_tl
            by (metis ind insert_subset list.sel(3) list.simps(15) set)
          show "targets t \<subseteq> P.Srcs T"
          proof -
            have "targets t \<subseteq> R.targets t"
              using targets_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S by blast
            also have "... \<subseteq> R.sources (hd T)"
              using T tT
              by (metis P\<^sub>R.Arr.simps(3) P\<^sub>R.Srcs_simp\<^sub>P list.collapse)
            also have "... \<subseteq> P.Srcs T"
              using P.Arr_imp_arr_hd P.Srcs_simp\<^sub>P \<open>P.Arr T\<close> sources_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S by force
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

  end

  locale sub_weakly_extensional_rts =
    sub_rts +
    R: weakly_extensional_rts R
  begin

    sublocale weakly_extensional_rts resid
      apply unfold_locales
      using R.weak_extensionality cong_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S
      by blast

    lemma is_weakly_extensional_rts:
    shows "weakly_extensional_rts resid"
      ..

    lemma src_char:
    shows "src t = (if arr t then R.src t else null)"
    proof (cases "arr t")
      show "\<not> arr t \<Longrightarrow> ?thesis"
        by (simp add: src_def)
      assume t: "arr t"
      show ?thesis
      proof (intro src_eqI)
        show "ide (if arr t then R.src t else null)"
          using t sources_closed inclusion R.src_in_sources
          by (metis (full_types) CollectD R.ide_src arr_char in_mono ide_char)
        show "con (if arr t then R.src t else null) t"
          using t con_char
          by (metis (full_types) R.con_sym R.in_sourcesE R.src_in_sources
              \<open>ide (if arr t then R.src t else null)\<close> arr_char ide_char inclusion)
      qed
    qed

  end

  text \<open>
    Here we justify the terminology ``normal sub-RTS'', which was introduced earlier,
    by showing that a normal sub-RTS really is a sub-RTS.
  \<close>

  lemma (in normal_sub_rts) is_sub_rts:
  shows "sub_rts resid (\<lambda>t. t \<in> \<NN>)"
    using elements_are_arr ide_closed
    apply unfold_locales
      apply auto[2]
    by (meson R.con_imp_coinitial R.con_sym forward_stable)

end
