(*  Title:       ResiduatedTransitionSystem
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2022
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Residuated Transition Systems"

theory ResiduatedTransitionSystem
imports Main "HOL-Library.FuncSet"
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
   * properties of residuated transition systems, but for now I don't want this theory
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
      A \emph{residuation} is a partial magma subject to three axioms.
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
  for resid :: "'a resid" (infix \<open>\\<close> 70) +
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

    definition con  (infix \<open>\<frown>\<close> 50)
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

    lemma arr_trg_iff_arr:
    shows "arr (trg t) \<longleftrightarrow> arr t"
      by (metis arrI arrE arr_resid_iff_con resid_arr_self)

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

    abbreviation prfx  (infix \<open>\<lesssim>\<close> 50)
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

    abbreviation cong  (infix \<open>\<sim>\<close> 50)
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
      by (metis assms coterminalE coinitialE cong_implies_coinitial
          cong_implies_coterminal seqE seqI(1))


    subsubsection "Chosen Sources"

    text \<open>
      In a general RTS, sources are not unique and (in contrast to the case for targets)
      there isn't even any canonical source.  However, it is useful to choose an arbitrary
      source for each transition.  Once we have at least weak extensionality, this will
      be the unique source and stronger things can be proved about it.
    \<close>

    definition src
    where "src t \<equiv> if arr t then SOME a. a \<in> sources t else null"

    lemma src_in_sources:
    assumes "arr t"
    shows "src t \<in> sources t"
      using assms someI_ex [of "\<lambda>a. a \<in> sources t"] arr_iff_has_source src_def
      by auto

    lemma coinitial_imp_eq_src:
    assumes "coinitial t t'"
    shows "src t = src t'"
      using assms
      by (simp add: coinitial_iff src_def)

    lemma src_congI:
    assumes "ide a" and "a \<frown> t"
    shows "src t \<sim> a"
      using assms src_in_sources sources_are_cong
      by (metis arr_iff_has_source con_sym emptyE in_sourcesI)

    lemma arr_src_iff_arr:
    shows "arr (src t) \<longleftrightarrow> arr t"
      by (metis arrI conE null_is_zero(2) sources_are_con arrE src_def src_in_sources)

    lemma arr_src_if_arr [simp]:
    assumes "arr t"
    shows "arr (src t)"
      using assms arr_src_iff_arr by blast

    lemma sources_char\<^sub>C\<^sub>S:
    shows "sources t = {a. arr t \<and> src t \<sim> a}"
      unfolding sources_def
      by (meson con_implies_arr(1) con_sym in_sourcesE sources_cong_closed
          src_congI src_in_sources)

    lemma targets_char':
    shows "targets t = {b. arr t \<and> trg t \<sim> b}"
      unfolding targets_def
      using targets_char targets_def trg_def by presburger

    lemma con_imp_cong_src:
    assumes "t \<frown> u"
    shows "src t \<sim> src u"
      using assms con_imp_coinitial_ax cong_transitive src_congI by blast

    lemma ide_src [simp]:
    assumes "arr t"
    shows "ide (src t)"
      using assms src_in_sources by blast

    lemma src_resid:
    assumes "t \<frown> u"
    shows "src (t \\ u) \<sim> trg u"
      using assms
      by (metis con_implies_arr(2) con_sym con_target ide_trg src_congI trg_def)

    lemma apex_arr_prfx':
    assumes "prfx t u"
    shows "trg (u \\ t) \<sim> trg u"
    and "trg (t \\ u) \<sim> trg u"
      using assms
      apply (metis (no_types, lifting) ide_def mem_Collect_eq prfx_implies_con
          sources_resid targets_resid_sym sources_def targets_char' trg_in_targets)
      by (metis assms ideE prfx_transitive arr_resid_iff_con src_resid)

    lemma seqI\<^sub>C\<^sub>S [intro, simp]:
    shows "\<lbrakk>arr t; trg t \<sim> src u\<rbrakk> \<Longrightarrow> seq t u"
    and "\<lbrakk>arr u; trg t \<sim> src u\<rbrakk> \<Longrightarrow> seq t u"
      apply (metis ide_trg in_sourcesE not_ide_null prfx_implies_con resid_arr_ide
          seqI(1) sources_resid src_def src_in_sources trg_def)
      by (metis in_sourcesE prfx_implies_con resid_arr_ide seqI(2) sources_resid
          src_in_sources trg_def)

    lemma seqE\<^sub>C\<^sub>S [elim]:
    assumes "seq t u"
    and "\<lbrakk>arr u; arr t; trg t \<sim> src u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms
      by (metis seq_def sources_are_cong src_in_sources trg_in_targets)

    lemma coinitial_iff':
    shows "coinitial t u \<longleftrightarrow> arr t \<and> arr u \<and> src t \<sim> src u"
      by (metis (full_types) arr_resid_iff_con coinitialE coinitialI ide_implies_arr
          resid_arr_ide con_imp_coinitial in_sourcesE src_in_sources)

    lemma coterminal_iff':
    shows "coterminal t u \<longleftrightarrow> arr t \<and> arr u \<and> trg t \<sim> trg u"
      by (meson coterminalE ide_imp_con_iff_cong coterminal_iff_con_trg ide_trg)

    lemma coinitialI' [intro]:
    assumes "arr t" and "src t \<sim> src u"
    shows "coinitial t u"
      by (metis assms(2) coinitial_iff' not_ide_null null_is_zero(2) src_def)

    lemma coinitialE' [elim]:
    assumes "coinitial t u"
    and "\<lbrakk>arr t; arr u; src t \<sim> src u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms coinitial_iff' by blast

    lemma coterminalI' [intro]:
    assumes "arr t" and "trg t \<sim> trg u"
    shows "coterminal t u"
      by (simp add: assms(2) prfx_implies_con coterminal_iff_con_trg)

    lemma coterminalE' [elim]:
    assumes "coterminal t u"
    and "\<lbrakk>arr t; arr u; trg t \<sim> trg u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms coterminal_iff' by blast

    lemma src_cong_ide:
    assumes "ide a"
    shows "src a \<sim> a"
      using arrI assms src_congI by blast

    lemma trg_ide [simp]:
    assumes "ide a"
    shows "trg a = a"
      using assms resid_arr_self by auto

    lemma ide_iff_src_cong_self:
    assumes "arr a"
    shows "ide a \<longleftrightarrow> src a \<sim> a"
      by (metis assms ide_backward_stable in_sourcesE src_cong_ide src_in_sources)

    lemma ide_iff_trg_cong_self:
    assumes "arr a"
    shows "ide a \<longleftrightarrow> trg a \<sim> a"
      by (metis assms ideE ide_backward_stable ide_trg trg_def)

    lemma src_src_cong_src:
    assumes "arr t"
    shows "src (src t) \<sim> src t"
      using assms src_cong_ide src_in_sources by blast

    lemma trg_trg_cong_trg:
    assumes "arr t"
    shows "trg (trg t) \<sim> trg t"
      using assms by fastforce

    lemma src_trg_cong_trg:
    assumes "arr t"
    shows "src (trg t) \<sim> trg t"
      using assms ide_trg src_cong_ide by blast

    lemma trg_src_cong_src:
    assumes "arr t"
    shows "trg (src t) \<sim> src t"
      using assms
      by (metis in_sourcesE resid_arr_self trg_ide src_in_sources)

    lemma resid_ide_cong:
    assumes "ide a" and "coinitial a t"
    shows "t \\ a \<sim> t" and "a \\ t \<sim> trg t"
      using assms
       apply (metis coinitialE cong_reflexive ideE in_sourcesE in_sourcesI resid_arr_ide)
      by (metis apex_arr_prfx'(2) assms coinitialE ideE in_sourcesI resid_arr_self
          source_is_prfx)

    lemma con_arr_src [simp]:
    assumes "arr f"
    shows "f \<frown> src f" and "src f \<frown> f"
      using assms src_in_sources con_sym by blast+

    lemma resid_src_arr_cong:
    assumes "arr f"
    shows "src f \\ f \<sim> trg f"
      using assms
      by (meson resid_source_in_targets src_in_sources trg_in_targets targets_are_cong)

    lemma resid_arr_src_cong:
    assumes "arr f"
    shows "f \\ src f \<sim> f"
      using assms
      by (metis cong_reflexive in_sourcesE resid_arr_ide src_in_sources)

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

    lemma src_eqI:
    assumes "ide a" and "a \<frown> t"
    shows "src t = a"
      using assms src_in_sources
      by (metis arr_has_un_source resid_arr_ide in_sourcesI arr_resid_iff_con con_sym)

    lemma sources_char\<^sub>W\<^sub>E:
    shows "sources t = {a. arr t \<and> src t = a}"
      using arr_iff_has_source con_sym src_eqI by auto

    lemma targets_char\<^sub>W\<^sub>E:
    shows "targets t = {b. arr t \<and> trg t = b}"
      using trg_in_targets arr_has_un_target arr_iff_has_target by auto

    lemma con_imp_eq_src:
    assumes "t \<frown> u"
    shows "src t = src u"
      using assms
      by (metis con_imp_coinitial_ax src_eqI)

    lemma src_resid\<^sub>W\<^sub>E [simp]:
    assumes "t \<frown> u"
    shows "src (t \\ u) = trg u"
      using assms
      by (metis arr_resid_iff_con con_implies_arr(2) arr_has_un_source trg_in_targets
                sources_resid src_in_sources)

    lemma apex_sym:
    shows "trg (t \\ u) = trg (u \\ t)"
      by (metis arr_has_un_target con_sym_ax arr_resid_iff_con conI targets_resid_sym
          trg_in_targets)

    lemma apex_arr_prfx\<^sub>W\<^sub>E:
    assumes "prfx t u"
    shows "trg (u \\ t) = trg u"
    and "trg (t \\ u) = trg u"
      using assms
       apply (metis apex_sym arr_resid_iff_con ideE src_resid\<^sub>W\<^sub>E)
      by (metis arr_resid_iff_con assms ideE src_resid\<^sub>W\<^sub>E)

    lemma seqI\<^sub>W\<^sub>E [intro, simp]:
    shows "\<lbrakk>arr t; trg t = src u\<rbrakk> \<Longrightarrow> seq t u"
    and "\<lbrakk>arr u; trg t = src u\<rbrakk> \<Longrightarrow> seq t u"
      by (metis arrE arr_src_iff_arr arr_trg_iff_arr in_sourcesE resid_arr_ide
          seqI(1) sources_resid src_in_sources trg_def)+

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

    lemma src_ide [simp]:
    assumes "ide a"
    shows "src a = a"
      using arrI assms src_eqI by blast

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
      by (metis con_def not_arr_null src_def src_resid\<^sub>W\<^sub>E trg_def)

    lemma trg_src [simp]:
    shows "trg (src t) = src t"
      by (metis ide_src null_is_zero(2) resid_arr_self src_def trg_ide)

    lemma resid_ide:
    assumes "ide a" and "coinitial a t"
    shows (* [simp]: *) "t \\ a = t" and "a \\ t = trg t"
      using assms resid_arr_ide apply blast
      using assms
      by (metis con_def con_sym_ax ideE in_sourcesE in_sourcesI resid_ide_arr
          coinitialE src_ide src_resid\<^sub>W\<^sub>E)

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
  assumes extensionality: "t \<sim> u \<Longrightarrow> t = u"
  begin

    sublocale weakly_extensional_rts
      using extensionality
      by unfold_locales auto

    lemma cong_char:
    shows "t \<sim> u \<longleftrightarrow> arr t \<and> t = u"
      by (metis arrI cong_reflexive prfx_implies_con extensionality)

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

    lemma composable_permute:
    shows "composable t (u \\ t) \<longleftrightarrow> composable u (t \\ u)"
      unfolding composable_def
      by (metis cube ide_backward_stable ide_imp_con_iff_cong prfx_implies_con
          composite_ofE composite_ofI)

    lemma diamond_commutes_upto_cong:
    assumes "composite_of t (u \\ t) v" and "composite_of u (t \\ u) v'"
    shows "v \<sim> v'"
      using assms cube ide_backward_stable prfx_transitive
      by (elim composite_ofE) metis

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

    lemma joinable_iff_composable:
    shows "joinable t u \<longleftrightarrow> composable t (u \\ t)"
    proof
      show "joinable t u \<Longrightarrow> composable t (u \\ t)"
        unfolding joinable_def join_of_def composable_def by auto
      show "composable t (u \\ t) \<Longrightarrow> joinable t u"
      proof -
        assume 1: "composable t (u \\ t)"
        obtain v where v: "composite_of t (u \\ t) v"
          using 1 composable_def by blast
        have "composite_of u (t \\ u) v"
        proof
          show "u \<lesssim> v"
            by (metis v composite_ofE cube ide_backward_stable)
          show "v \\ u \<sim> t \\ u"
            by (metis v \<open>u \<lesssim> v\<close> coinitial_ide_are_cong composite_ofE
                con_imp_coinitial cube prfx_implies_con)
        qed
        thus "joinable t u"
          using v joinable_def by auto
      qed
    qed

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

    lemma join_of_respects_cong_left:
    assumes "join_of t u v" and "cong t t'"
    shows "join_of t' u v"
      using assms prfx_transitive cong_subst_left(2) cong_subst_right(2)
      apply (elim join_ofE composite_ofE, intro join_ofI composite_ofI)
      by (meson con_sym con_with_join_of_iff(2) prfx_implies_con)+

    lemma join_of_respects_cong_right:
    assumes "join_of t u v" and "cong u u'"
    shows "join_of t u' v"
      using assms join_of_respects_cong_left join_of_symmetric
      by meson

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
      using assms composite_of_unq_upto_cong extensionality by fastforce

    lemma divisors_of_ide:
    assumes "composite_of t u v" and "ide v"
    shows "ide t" and "ide u"
    proof -
      show "ide t"
        using assms ide_backward_stable by blast
      show "ide u"
        by (metis assms(1-2) composite_ofE con_ide_are_eq con_prfx_composite_of(1)
            ide_backward_stable)
    qed

    text \<open>
      Here we define composition of transitions.  Note that we compose transitions
      in diagram order, rather than in the order used for function composition.
      This may eventually lead to confusion, but here (unlike in the case of a category)
      transitions are typically not functions, so we don't have the constraint of having
      to conform to the order of function application and composition, and diagram order
      seems more natural.
    \<close>

    definition comp  (infixr \<open>\<cdot>\<close> 55)
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
                      composable_imp_seq composite_of_def extensionality seqE)
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
      by (metis composable_def composable_iff_arr_comp composite_of_cancel_left extensionality
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

    definition join  (infix \<open>\<squnion>\<close> 52)
    where "t \<squnion> u \<equiv> if joinable t u then THE v. join_of t u v else null"

    lemma join_is_join_of:
    assumes "joinable t u"
    shows "join_of t u (t \<squnion> u)"
      using assms joinable_def join_def join_of_unique
            the1I2 [of "join_of t u" "join_of t u"]
      by force

    lemma joinable_iff_arr_join:
    shows "joinable t u \<longleftrightarrow> arr (t \<squnion> u)"
      by (metis cong_char join_is_join_of join_of_un_upto_cong not_arr_null join_def)

    lemma joinable_iff_join_not_null:
    shows "joinable t u \<longleftrightarrow> t \<squnion> u \<noteq> null"
      by (metis join_def joinable_iff_arr_join not_arr_null)

    lemma join_sym:
    shows "t \<squnion> u = u \<squnion> t"
      by (metis join_def join_of_unique join_is_join_of join_of_symmetric joinable_def)

    lemma src_join:
    assumes "joinable t u"
    shows "src (t \<squnion> u) = src t"
      using assms
      by (metis con_imp_eq_src con_prfx_composite_of(1) join_is_join_of join_of_def)

    lemma trg_join:
    assumes "joinable t u"
    shows "trg (t \<squnion> u) = trg (t \\ u)"
      using assms
      by (metis arr_resid_iff_con join_is_join_of joinable_iff_arr_join
          joinable_implies_con in_targetsE src_eqI targets_join_of(1) trg_in_targets)

    lemma resid_join\<^sub>E [simp]:
    assumes "joinable t u" and "v \<frown> t \<squnion> u"
    shows "v \\ (t \<squnion> u) = (v \\ u) \\ (t \\ u)"
    and "v \\ (t \<squnion> u) = (v \\ t) \\ (u \\ t)"
    and "(t \<squnion> u) \\ v = (t \\ v) \<squnion> (u \\ v)"
    proof -
      show 1: "v \\ (t \<squnion> u) = (v \\ u) \\ (t \\ u)"
        by (meson assms con_sym join_of_def resid_composite_of(3) extensionality
            join_is_join_of)
      show "v \\ (t \<squnion> u) = (v \\ t) \\ (u \\ t)"
        by (metis "1" cube)
      show "(t \<squnion> u) \\ v = (t \\ v) \<squnion> (u \\ v)"
        using assms joinable_def join_of_resid join_is_join_of extensionality
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
           src_resid\<^sub>W\<^sub>E)
      by (metis arr_resid_iff_con comp_eqI con_comp_iff con_implies_arr(1) con_sym)

    lemma join_prfx:
    assumes "t \<lesssim> u"
    shows "t \<squnion> u = u" and "u \<squnion> t = u"
    proof -
      show "t \<squnion> u = u"
        using assms
        by (metis (no_types, lifting) join_eqI ide_iff_src_self ide_implies_arr resid_arr_self
            prfx_implies_con src_resid\<^sub>W\<^sub>E)
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
            using src_resid\<^sub>W\<^sub>E trg_join
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
            by (metis tu_v tu con_sym cube joinable_implies_con src_resid\<^sub>W\<^sub>E trg_def trg_join
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
              joinable_implies_con src_resid\<^sub>W\<^sub>E)
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

    lemma join_expansion:
    assumes "joinable t u"
    shows "t \<squnion> u = t \<cdot> (u \\ t)" and "seq t (u \\ t)"
       apply (metis assms comp_is_composite_of(2) join_is_join_of join_of_def)
      using assms joinable_iff_composable by auto

    lemma join3_expansion:
    assumes "joinable (t \<squnion> u) v"
    shows "(t \<squnion> u) \<squnion> v = (t \<cdot> (u \\ t)) \<cdot> ((v \\ t) \\ (u \\ t))"
      by (metis assms con_implies_arr(1) join_expansion(1) joinable_iff_arr_join
        joinable_implies_con resid_comp(1))

    lemma join_comp:
    assumes "joinable (t \<cdot> u) v"
    shows "(t \<cdot> u) \<squnion> v = t \<cdot> (v \\ t) \<cdot> (u \\ (v \\ t))"
      by (metis assms composable_iff_comp_not_null extensional_rts.comp_assoc
        extensional_rts_axioms join_expansion(1) join_sym joinable_iff_composable
        joinable_iff_join_not_null joinable_implies_con resid_comp(1))

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
        by (metis ideE prfx_implies_con src_resid\<^sub>W\<^sub>E trg_ide)
      also have "... = trg v"
        by (metis assms(2) ide_iff_src_self ide_implies_arr join_arr_self prfx_implies_con
            src_resid\<^sub>W\<^sub>E)
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
    assumes "arr t" and "trg t = src u"
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
            resid_comp(2) con_imp_arr_resid con_sym comp_def arr_comp\<^sub>E\<^sub>C src_resid\<^sub>W\<^sub>E conI)
      moreover have "u \<lesssim> t \<cdot> (u \\ t)"
        by (metis arr_resid_iff_con calculation con cong_reflexive comp_arr_trg
            resid_arr_self resid_comp(1) apex_sym)
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
            con_sym comp_resid_prfx prfx_comp resid_comp(1) arr_compE\<^sub>E\<^sub>C arr_comp\<^sub>E\<^sub>C
            prfx_implies_con)
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
            seqI\<^sub>W\<^sub>E(2) src_resid\<^sub>W\<^sub>E conI)
      also have "... = w \\ (t \\ u)"
        by (metis (no_types, lifting) "1" arr_comp\<^sub>E\<^sub>C assms composable_imp_seq con_imp_eq_src
            con_implies_arr(2) comp_def not_arr_null conI src_resid\<^sub>W\<^sub>E)
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
        by (metis con con_implies_arr(1) con_sym diamond_commutes prfx_implies_con
            prfx_comp src_resid\<^sub>W\<^sub>E arr_comp\<^sub>E\<^sub>C)
      have "t \<squnion> u = t \<cdot> (u \\ t)"
      proof (intro join_eqI)
        show "t \<lesssim> t \<cdot> (u \\ t)"
          by (metis 1 composable_def comp_is_composite_of(2) composite_of_def
              con_comp_iff)
        moreover show 2: "u \<lesssim> t \<cdot> (u \\ t)"
          using 1 arr_resid con con_sym prfx_reflexive resid_comp(1) by metis
        moreover show "(t \<cdot> (u \\ t)) \\ u = t \\ u"
          using 1 diamond_commutes induced_arrow(2) resid_comp(2) by force
        ultimately show "(t \<cdot> (u \\ t)) \\ t = u \\ t"
          by (metis con_comp_iff\<^sub>E\<^sub>C(1) con_sym prfx_implies_con resid_comp(2)
              induced_arrow(1))
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
        using assms 1 composable_iff_seq arr_comp src_join arr_compE\<^sub>E\<^sub>C
              joinable_iff_arr_join seqI\<^sub>W\<^sub>E(1)
        by metis
      have "con (t \<cdot> u) (t \<cdot> u')"
        using 1 2 arr_comp arr_compE\<^sub>E\<^sub>C assms(2) comp_assoc\<^sub>E\<^sub>C comp_resid_prfx
              con_comp_iff joinable_implies_con comp_def not_arr_null
        by metis
      thus "t \<cdot> (u \<squnion> u') = t \<cdot> u \<squnion> t \<cdot> u'"
        using assms comp_join(2) joinable_iff_con by blast
    qed

    lemma resid_common_prefix:
    assumes "t \<cdot> u \<frown> t \<cdot> v"
    shows "(t \<cdot> u) \\ (t \<cdot> v) = u \\ v"
      using assms
      by (metis con_comp_iff con_sym con_comp_iff\<^sub>E\<^sub>C(2) con_implies_arr(2)
          induced_arrow(1) resid_comp(1-2) arr_resid_iff_con)

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
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
  and F :: "'a \<Rightarrow> 'b" +
  assumes extensionality: "\<not> A.arr t \<Longrightarrow> F t = B.null"
  and preserves_con [simp]: "A.con t u \<Longrightarrow> B.con (F t) (F u)"
  and preserves_resid [simp]: "A.con t u \<Longrightarrow> F (t \\\<^sub>A u) = F t \\\<^sub>B F u"
  begin

    notation A.con     (infix \<open>\<frown>\<^sub>A\<close> 50)
    notation A.prfx    (infix \<open>\<lesssim>\<^sub>A\<close> 50)
    notation A.cong    (infix \<open>\<sim>\<^sub>A\<close> 50)

    notation B.con     (infix \<open>\<frown>\<^sub>B\<close> 50)
    notation B.prfx    (infix \<open>\<lesssim>\<^sub>B\<close> 50)
    notation B.cong    (infix \<open>\<sim>\<^sub>B\<close> 50)

    lemma preserves_reflects_arr [iff]:
    shows "B.arr (F t) \<longleftrightarrow> A.arr t"
      by (metis A.arr_def B.con_implies_arr(2) B.not_arr_null extensionality preserves_con)

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

    lemma preserves_seq:
    shows "A.seq t u \<Longrightarrow> B.seq (F t) (F u)"
      by (metis A.in_sourcesE A.seqE B.seqI(1) B.targets_composite_of preserves_con
          preserves_reflects_arr preserves_resid B.composite_of_arr_target
          A.resid_arr_ide B.sources_resid A.trg_in_targets B.trg_in_targets
          simulation.preserves_trg simulation_axioms)

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
      using F.extensionality G.extensionality by unfold_locales auto
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

    notation B.comp  (infixr \<open>\<cdot>\<^sub>B\<close> 55)
    notation B.join  (infixr \<open>\<squnion>\<^sub>B\<close> 52)

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

  subsection "Simulations between Weakly Extensional RTS's"

  locale simulation_between_weakly_extensional_rts =
    simulation_to_weakly_extensional_rts +
    A: weakly_extensional_rts A
  begin

    lemma preserves_src [simp]:
    shows "B.src (F t) = F (A.src t)"
      by (metis A.arr_src_iff_arr A.src_in_sources extensionality image_subset_iff
          preserves_reflects_arr preserves_sources B.arr_has_un_source B.src_def
          B.src_in_sources)

    lemma preserves_trg [simp]:
    shows "B.trg (F t) = F (A.trg t)"
      by (metis A.arr_trg_iff_arr A.trg_def B.null_is_zero(2) B.trg_def
          extensionality preserves_resid A.arrE)

  end

  subsection "Simulations between Extensional RTS's"

  locale simulation_between_extensional_rts =
    simulation_to_extensional_rts +
    A: extensional_rts A
  begin

    sublocale simulation_between_weakly_extensional_rts ..

    notation A.comp  (infixr "\<cdot>\<^sub>A" 55)
    notation A.join  (infixr "\<squnion>\<^sub>A" 52)

    lemma preserves_comp:
    assumes "A.composable t u"
    shows "F (t \<cdot>\<^sub>A u) = F t \<cdot>\<^sub>B F u"
      using assms
      by (metis A.arr_comp A.comp_resid_prfx A.composableD(2) A.not_arr_null
          A.prfx_comp B.comp_eqI preserves_prfx preserves_resid A.conI)

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
    general RTS's is not yet clear to me.  However, if the codomain is
    weakly extensional, then we have unique sources and targets, so there is no problem.
    The definition below is limited to that case.  I do not make any attempt here
    to develop facts about transformations.  My main reason for including this
    definition here is so that in the subsequent application to the \<open>\<lambda>\<close>-calculus,
    I can exhibit \<open>\<beta>\<close>-reduction as an example of a transformation.
  \<close>

  locale transformation =
    A: rts A +
    B: weakly_extensional_rts B +
    F: simulation A B F +
    G: simulation A B G
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes extensionality: "\<not> A.arr f \<Longrightarrow> \<tau> f = B.null"
  and respects_cong_ide: "\<lbrakk>A.ide a; A.cong a a'\<rbrakk> \<Longrightarrow> \<tau> a = \<tau> a'"
  and preserves_src: "A.ide f \<Longrightarrow> B.src (\<tau> f) = F f"
  and preserves_trg: "A.ide f \<Longrightarrow> B.trg (\<tau> f) = G f"
  and naturality1_ax: "a \<in> A.sources f \<Longrightarrow> \<tau> a \\\<^sub>B F f = \<tau> (a \\\<^sub>A f)"
  and naturality2_ax: "a \<in> A.sources f \<Longrightarrow> F f \\\<^sub>B \<tau> a = G f"
  and naturality3: "a \<in> A.sources f \<Longrightarrow> B.join_of (\<tau> a) (F f) (\<tau> f)"
  begin

    notation A.con     (infix \<open>\<frown>\<^sub>A\<close> 50)
    notation A.prfx    (infix \<open>\<lesssim>\<^sub>A\<close> 50)

    notation B.con     (infix \<open>\<frown>\<^sub>B\<close> 50)
    notation B.prfx    (infix \<open>\<lesssim>\<^sub>B\<close> 50)

    lemma naturality1:
    shows "\<tau> (A.src f) \\\<^sub>B F f = \<tau> (A.trg f)"
      by (metis A.arr_trg_iff_arr A.ide_trg A.resid_src_arr_cong
          A.src_in_sources B.null_is_zero(2) F.extensionality extensionality
          naturality1_ax respects_cong_ide)

    lemma naturality2:
    shows "F f \\\<^sub>B \<tau> (A.src f) = G f"
      by (metis A.src_in_sources B.null_is_zero(1) F.extensionality G.extensionality
          naturality2_ax)

    lemma respects_cong:
    assumes "A.cong u u'"
    shows "B.cong (\<tau> u) (\<tau> u')"
    proof -
      obtain a where a: "a \<in> A.sources u \<inter> A.sources u'"
        using assms
        by (meson A.con_imp_common_source A.prfx_implies_con ex_in_conv)
      have "B.cong (F u) (F u')"
        using assms F.preserves_cong by blast
      thus ?thesis
        using a naturality3 B.join_of_respects_cong_right
        by (metis A.con_imp_common_source A.prfx_implies_con A.sources_eqI
            B.join_of_un_upto_cong assms inf.idem)
    qed

  end

  subsection "Identities form a Coherent Normal Sub-RTS"

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

    type_synonym 'b arr = "'b list"

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

    lemma Arr_induct:
    assumes "\<And>t. Arr [t] \<Longrightarrow> P [t]"
    and "\<And>t U. \<lbrakk>Arr (t # U); U \<noteq> []; P U\<rbrakk> \<Longrightarrow> P (t # U)"
    shows "Arr T \<Longrightarrow> P T"
    proof (induct T)
      show "Arr [] \<Longrightarrow> P []"
        using Arr.simps(1) by blast
      show "\<And>t U. \<lbrakk>Arr U \<Longrightarrow> P U; Arr (t # U)\<rbrakk> \<Longrightarrow> P (t # U)"
        by (metis assms Arr.simps(2-3) list.exhaust)
    qed

    lemma Ide_induct:
    assumes "\<And>t. R.ide t \<Longrightarrow> P [t]"
    and "\<And>t T. \<lbrakk>R.ide t; R.targets t \<subseteq> Srcs T; P T\<rbrakk> \<Longrightarrow> P (t # T)"
    shows "Ide T \<Longrightarrow> P T"
    proof (induct T)
      show "Ide [] \<Longrightarrow> P []"
        using Ide.simps(1) by blast
      show "\<And>t T. \<lbrakk>Ide T \<Longrightarrow> P T; Ide (t # T)\<rbrakk> \<Longrightarrow> P (t # T)"
        by (metis assms Ide.simps(2-3) list.exhaust)
    qed

    lemma set_Arr_subset_arr:
    assumes "Arr T"
    shows "set T \<subseteq> Collect R.arr"
      apply (induct T rule: Arr_induct)
      using assms Arr.elims(2) by auto

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
    assumes "Ide T"
    shows "set T \<subseteq> Collect R.ide"
      apply (induct T rule: Ide_induct)
      using assms by auto

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
    assumes "Ide T"
    shows "Arr T"
      apply (induct T rule: Ide_induct)
      using assms
        apply auto[3]
      by (metis Arr.elims(2) Arr.simps(3) R.ide_implies_arr)

    lemma const_ide_is_Ide:
    shows "\<lbrakk>T \<noteq> []; R.ide (hd T); set T \<subseteq> {hd T}\<rbrakk> \<Longrightarrow> Ide T"
      apply (induct T)
       apply auto[2]
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

    fun Resid1x  (infix \<open>\<^sup>1\\<^sup>*\<close> 70)
    where "t \<^sup>1\\\<^sup>* [] = R.null"
        | "t \<^sup>1\\\<^sup>* [u] = t \\ u"
        | "t \<^sup>1\\\<^sup>* (u # U) = (t \\ u) \<^sup>1\\\<^sup>* U"

    text \<open>
      Next, we have residuation of a path along a single transition, yielding a path.
    \<close>

    fun Residx1  (infix \<open>\<^sup>*\\<^sup>1\<close> 70)
    where "[] \<^sup>*\\\<^sup>1 u = []"
        | "[t] \<^sup>*\\\<^sup>1 u = (if t \<frown> u then [t \\ u] else [])"
        | "(t # T) \<^sup>*\\\<^sup>1 u =
             (if t \<frown> u \<and> T \<^sup>*\\\<^sup>1 (u \\ t) \<noteq> [] then (t \\ u) # T \<^sup>*\\\<^sup>1 (u \\ t) else [])"

    text \<open>
      Finally, residuation of a path along a path, yielding a path.
    \<close>

    function (sequential) Resid  (infix \<open>\<^sup>*\\<^sup>*\<close> 70)
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
    abbreviation Con  (infix \<open>\<^sup>*\<frown>\<^sup>*\<close> 50)
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

    lemma sources_Resid1x:
    assumes "[u] \<^sup>*\<frown>\<^sup>* T"
    shows "R.sources (u \<^sup>1\\\<^sup>* T) = Trgs T"
      by (metis Resid1x_as_Resid Srcs.simps(2) Srcs_Resid_single_Arr assms)

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

    notation cong  (infix \<open>\<^sup>*\<sim>\<^sup>*\<close> 50)
    notation prfx  (infix \<open>\<^sup>*\<lesssim>\<^sup>*\<close> 50)

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
          by (metis R.sources_resid Srcs.simps(2) Trgs.simps(2) R.ideE)
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

    lemma coinitial_char:
    shows "coinitial T U \<Longrightarrow> Arr T \<and> Arr U \<and> Srcs T = Srcs U"
    and "Arr T \<and> Arr U \<and> Srcs T \<inter> Srcs U \<noteq> {} \<Longrightarrow> coinitial T U"
    proof -
      show "coinitial T U \<Longrightarrow> Arr T \<and> Arr U \<and> Srcs T = Srcs U"
        unfolding seq_def
        by (metis Con_imp_eq_Srcs arr_char coinitial_iff
            con_char prfx_implies_con source_is_prfx src_in_sources)
      assume 1: "Arr T \<and> Arr U \<and> Srcs T \<inter> Srcs U \<noteq> {}"
      have "sources T = sources U"
      proof -
        obtain a where a: "R.ide a \<and> a \<in> Srcs T \<and> a \<in> Srcs U"
          using 1 Srcs_are_ide by blast
        have "Srcs [a] = Srcs T"
          using a 1
          by (metis Arr.simps(1) Con_imp_eq_Srcs Resid_Arr_Src)
        moreover have "Srcs [a] = Srcs U"
          using a 1 Con_single_ide_ind Con_imp_eq_Srcs by blast
        ultimately show ?thesis
          using 1 sources_char\<^sub>P targets_char\<^sub>P by auto
      qed
      thus "coinitial T U"
        using 1 by blast
    qed

    lemma coinitialI\<^sub>P [intro]:
    assumes "Arr T" and "Arr U" and "Srcs T \<inter> Srcs U \<noteq> {}"
    shows "coinitial T U"
      using assms coinitial_char(2) by auto

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

    sublocale incl: simulation resid Resid incl
      using R.con_implies_arr(1-2) con_char R.arr_resid_iff_con null_char
      by unfold_locales auto

    lemma incl_is_simulation:
    shows "simulation resid Resid incl"
      ..

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

    lemma Resid1x_append:
    assumes "U \<noteq> []" and "V \<noteq> []" and "[t] \<^sup>*\<frown>\<^sup>* U @ V"
    shows "t \<^sup>1\\\<^sup>* (U @ V) = (t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* V"
      using assms Resid1x_as_Resid Resid_append(2)
      by (metis Resid_append_ind list.distinct(1) list.inject)

    lemma Resid1x_cons:
    assumes "R.arr u" and "V \<noteq> []" and "[t] \<^sup>*\<frown>\<^sup>* u # V"
    shows "t \<^sup>1\\\<^sup>* (u # V) = (t \\ u) \<^sup>1\\\<^sup>* V"
      using assms
      by (metis Resid1x.simps(3) neq_Nil_conv)

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

  subsection "Permutation Congruence"

  text \<open>
    Here we show that \<open>\<^sup>*\<sim>\<^sup>*\<close> coincides with ``permutation congruence'':
    the least congruence respecting composition that relates \<open>[t, u \ t]\<close> and \<open>[u, t \ u]\<close>
    whenever \<open>t \<frown> u\<close> and that relates \<open>T @ [b]\<close> and \<open>T\<close> whenever \<open>b\<close> is an identity
    such that \<open>seq T [b]\<close>.
  \<close>

  context paths_in_rts
  begin

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
        using Ide PCong.intros(5) seq
         apply force
        using seq Ide PCong.intros(4)
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
          proof
            show "seq ([t] @ [u \\ t]) (U \<^sup>*\\\<^sup>* [t \\ u])"
            proof
              show "Arr ([t] @ [u \\ t])"
                by (metis Arr.simps(2) Con_rec(2) Srcs.simps(2) Trgs.simps(2)
                    U arr_append arr_char con Con_implies_Arr(1) Con_sym seq_char
                    R.arr_resid R.sources_resid)
              show "Arr (U \<^sup>*\\\<^sup>* [t \\ u])"
                by (metis Con_imp_Arr_Resid Con_sym Resid_rec(3) U con)
              show "Trgs ([t] @ [u \\ t]) \<inter> Srcs (U \<^sup>*\\\<^sup>* [t \\ u]) \<noteq> {}"
                by (metis Con_rec(2) R.targets_resid_sym Srcs_Resid Trgs.simps(2) U
                    \<open>Arr (U \<^sup>*\\<^sup>* [t \ u])\<close> \<open>Arr ([t] @ [u \ t])\<close> con conI
                    con_sym_ax not_Cons_self paths_in_rts.Trgs_append con_char
                    paths_in_rts_axioms seq_char seq_char')
            qed
            show "PCong ([t] @ [u \\ t]) ([u] @ [t \\ u])"
              using con by (simp add: Con_rec(3) PCong.intros(6) U)
            show "PCong (U \<^sup>*\\\<^sup>* [t \\ u]) (U \<^sup>*\\\<^sup>* [t \\ u])"
              by (meson PCong.intros(1) U con Arr_Resid_single Con_rec(3) Con_sym)
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
              using PCong.intros(4) by blast
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
        also have "... = [t] @ (T @ ((U \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* T))"
          using Resid_cons(2)
          by (metis T con Con_sym)
        also have "PCong ... ([t] @ ((U \<^sup>*\\\<^sup>* [t]) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))))"
        proof -
          have "T \<^sup>*\<frown>\<^sup>* U \<^sup>*\\\<^sup>* [t]"
            by (metis Con_cons(1) Resid.simps(2) T con)
          thus ?thesis
            using ind [of "U \<^sup>*\\\<^sup>* [t]"]
            by (metis PCong.intros(4) Con_imp_Arr_Resid
                Con_implies_Arr(1) Con_sym Resid_cons(2) arr_append
                T append_is_Nil_conv calculation con list.simps(3) PCong.intros(1)
                Srcs_Resid arr_append_imp_seq seq_char)
        qed
        also have "... = ([t] @ (U \<^sup>*\\\<^sup>* [t])) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
          by simp
        also have "PCong ... ((U @ ([t] \<^sup>*\\\<^sup>* U)) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])))"
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
        using PCong_permute assms con_char prfx_implies_con
        by (metis Ide.simps(1))
      also have "PCong (U @ (T \<^sup>*\\\<^sup>* U)) U"
        using assms PCong_append_Ide
        by (metis Con_imp_Arr_Resid Con_implies_Arr(1) Srcs_Resid arr_resid_iff_con
            ide_implies_arr con_char ide_char seq_char)
      finally show ?thesis by blast
    qed

    lemma PCong_imp_Cong:
    shows "PCong T U \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* U"
    proof (induct rule: PCong.induct)
      show "\<And>T. Arr T \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* T"
        using cong_reflexive by auto
      show "\<And>T U. \<lbrakk>PCong T U; T \<^sup>*\<sim>\<^sup>* U\<rbrakk> \<Longrightarrow> U \<^sup>*\<sim>\<^sup>* T"
        by blast
      show "\<And>T U V. \<lbrakk>PCong T U; T \<^sup>*\<sim>\<^sup>* U; PCong U V; U \<^sup>*\<sim>\<^sup>* V\<rbrakk> \<Longrightarrow> T \<^sup>*\<sim>\<^sup>* V"
        using cong_transitive by blast
      show "\<And>T U T' U'. \<lbrakk>seq T U; PCong T T'; T \<^sup>*\<sim>\<^sup>* T'; PCong U U'; U \<^sup>*\<sim>\<^sup>* U'\<rbrakk>
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
          ultimately show "[t, u \\ t] \<^sup>*\<lesssim>\<^sup>* [u, t \\ u]"
            using ide_char by auto
        qed
        thus "\<And>t u. t \<frown> u \<Longrightarrow> [t, u \\ t] \<^sup>*\<sim>\<^sup>* [u, t \\ u]"
          using R.con_sym by blast
      qed
    qed

    lemma Cong_iff_PCong:
    shows "T \<^sup>*\<sim>\<^sup>* U \<longleftrightarrow> PCong T U"
      using PCong_imp_Cong Cong_imp_PCong by blast

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
      by (simp add: Srcs_simp\<^sub>P R.arr_has_un_source)

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

  section "Normal Sub-RTS's and Congruence"

  text \<open>
    We now develop a general quotient construction on an RTS.
    We define a \emph{normal sub-RTS} of an RTS to be a collection of transitions \<open>\<NN>\<close> having
    certain ``local'' closure properties.  We will refer to the elements of \<open>\<NN>\<close> as
    \emph{normal transitions}.  A normal sub-RTS induces an equivalence relation \<open>\<approx>\<^sub>0\<close>,
    which we call \emph{semi-congruence}, by defining \<open>t \<approx>\<^sub>0 u\<close> to hold exactly
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

    lemma resid_along_normal_preserves_con:
    assumes "u \<in> \<NN>" and "t \<frown> t'" and "R.coinitial t u"
    shows "t \\ u \<frown> t' \\ u"
    proof -
      have "R.coinitial (t \\ t') (u \\ t')"
        by (metis assms R.arr_resid_iff_con R.coinitialI R.con_imp_common_source forward_stable
            elements_are_arr R.con_implies_arr(2) R.sources_resid R.sources_eqI)
      hence "t \\ t' \<frown> u \\ t'"
        by (metis assms(1) R.coinitial_iff R.con_imp_coinitial R.con_sym elements_are_arr
                  forward_stable R.arr_resid_iff_con)
      thus ?thesis
        using assms R.cube forward_stable by fastforce
    qed

    lemma resid_along_normal_preserves_reflects_con:
    assumes "u \<in> \<NN>" and "R.sources t = R.sources u"
    shows "t \\ u \<frown> t' \\ u \<longleftrightarrow> t \<frown> t'"
      by (metis R.arr_resid_iff_con assms R.con_implies_arr(1-2) elements_are_arr R.coinitial_iff
                R.resid_reflects_con resid_along_normal_preserves_con)

  end

  subsubsection "Normal Sub-RTS's of an Extensional RTS with Composites"

  locale normal_sub_rts_in_extensional_rts_with_composites =
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

  subsection "Normal Paths"

  context normal_sub_rts
  begin

    sublocale P: paths_in_rts resid ..

    (* TODO: Why does P.Con still have notation here, but P.cong and P.prfx do not? *)
    notation P.cong  (infix \<open>\<^sup>*\<sim>\<^sup>*\<close> 50)
    notation P.prfx  (infix \<open>\<^sup>*\<lesssim>\<^sup>*\<close> 50)

    text \<open>
      We define a ``normal path'' to be a path that consists entirely of normal transitions.
      We show that the collection of all normal paths is a normal sub-RTS of the RTS of paths.
    \<close>

    definition NPath
    where "NPath T \<equiv> (P.Arr T \<and> List.set T \<subseteq> \<NN>)"

    lemma NPath_induct:
    assumes "\<And>t. t \<in> \<NN> \<Longrightarrow> P [t]"
    and "\<And>t T. \<lbrakk>t \<in> \<NN>; NPath T; R.targets t \<subseteq> P.Srcs T; P T\<rbrakk> \<Longrightarrow> P (t # T)"
    shows "NPath T \<Longrightarrow> P T"
    proof (induct T)
      show "NPath [] \<Longrightarrow> P []"
        by (simp add: NPath_def)
      show "\<And>t T. \<lbrakk>NPath T \<Longrightarrow> P T; NPath (t # T)\<rbrakk> \<Longrightarrow> P (t # T)"
        by (metis NPath_def P.Arr.simps(3) assms(1,2) insert_subset list.exhaust
            list.simps(15))
    qed

    lemma Ide_implies_NPath:
    assumes "P.Ide T"
    shows "NPath T"
      using assms
      by (metis Ball_Collect NPath_def P.Ide_char ide_closed subsetI)

    lemma NPath_implies_Arr:
    assumes "NPath T"
    shows "P.Arr T"
      using assms NPath_def by simp

    lemma NPath_append:
    assumes "T \<noteq> []" and "U \<noteq> []"
    shows "NPath (T @ U) \<longleftrightarrow> NPath T \<and> NPath U \<and> P.Trgs T \<subseteq> P.Srcs U"
      using assms NPath_def by auto
      
    lemma NPath_appendI [intro, simp]:
    assumes "NPath T" and "NPath U" and "P.Trgs T \<subseteq> P.Srcs U"
    shows "NPath (T @ U)"
      using assms NPath_def by simp

    lemma NPath_Resid_single_Arr:
    shows "\<lbrakk>t \<in> \<NN>; P.Arr U; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> NPath (P.Resid [t] U)"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>t \<in> \<NN>; P.Arr []; R.sources t = P.Srcs []\<rbrakk> \<Longrightarrow> NPath (P.Resid [t] [])"
        by simp
      fix t u U
      assume ind: "\<And>t. \<lbrakk>t \<in> \<NN>; P.Arr U; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> NPath (P.Resid [t] U)"
      assume t: "t \<in> \<NN>"
      assume uU: "P.Arr (u # U)"
      assume src: "R.sources t = P.Srcs (u # U)"
      show "NPath (P.Resid [t] (u # U))"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using NPath_def t src
          apply simp
          by (metis R.arrE R.arr_resid_iff_con R.coinitial_def R.con_imp_common_source
              elements_are_arr forward_stable)
        assume U: "U \<noteq> []"
        show ?thesis
        proof -
          have "NPath (P.Resid [t] (u # U)) \<longleftrightarrow> NPath (P.Resid [t \\ u] U)"
            using t U uU src
            by (metis P.Arr.simps(2) P.Con_implies_Arr(1) P.Resid_rec(3) P.Con_rec(3)
                R.arr_resid_iff_con)
          also have "... \<longleftrightarrow> True"
            using t U uU src ind
            by (metis P.Arr.elims(2) P.Arr.simps(2) P.Srcs_simp\<^sub>P P.Trgs.simps(2)
                P.seq_implies_Trgs_eq_Srcs R.arr_resid_iff_con R.coinitialI R.sources_resid
                elements_are_arr list.inject list.sel(1) forward_stable)
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma NPath_Resid_Arr_single:
    shows "\<lbrakk> NPath T; R.arr u; P.Srcs T = R.sources u \<rbrakk> \<Longrightarrow> NPath (P.Resid T [u])"
    proof (induct T arbitrary: u)
      show "\<And>u. \<lbrakk>NPath []; R.arr u; P.Srcs [] = R.sources u\<rbrakk> \<Longrightarrow> NPath (P.Resid [] [u])"
        by simp
      fix t u T
      assume ind: "\<And>u. \<lbrakk>NPath T; R.arr u; P.Srcs T = R.sources u\<rbrakk> \<Longrightarrow> NPath (P.Resid T [u])"
      assume tT: "NPath (t # T)"
      assume u: "R.arr u"
      assume src: "P.Srcs (t # T) = R.sources u"
      show "NPath (P.Resid (t # T) [u])"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT u src NPath_def
          by (metis P.Arr.simps(2) NPath_Resid_single_Arr P.Srcs.simps(2)
              list.set_intros(1) subsetD)
        assume T: "T \<noteq> []"
        have con: "t \<frown> u"
        proof -
          have "R.coinitial u t"
            by (metis R.coinitialI P.Srcs.simps(3) T list.exhaust_sel src u)
          thus ?thesis
            using tT T u src R.con_sym NPath_def
            by (metis R.arr_resid_iff_con elements_are_arr forward_stable
                insert_subset list.simps(15))
        qed
        have 1: "NPath (P.Resid (t # T) [u]) \<longleftrightarrow> NPath ((t \\ u) # P.Resid T [u \\ t])"
        proof -
          have "t # T \<^sup>*\<frown>\<^sup>* [u]"
          proof -
            have 2: "[t] \<^sup>*\<frown>\<^sup>* [u]"
              by (simp add: P.Con_rec(1) con)
            moreover have "T \<^sup>*\<frown>\<^sup>* P.Resid [u] [t]"
              using tT u T src con 2 ind NPath_def
              by (metis (lifting) ext P.Arr.simps(1) P.Arr_iff_Con_self P.Con_imp_eq_Srcs
                  P.Con_implies_Arr(2) P.Con_rec(1,4) P.Resid_rec(1) P.Srcs.simps(2)
                  R.arr_resid R.con_sym R.sources_resid insert_subset list.simps(15))
            ultimately show ?thesis
              using tT T u src P.Con_cons(1) by simp
          qed
          thus ?thesis
            using tT T u src P.Resid_cons(1) P.Resid_rec(2) by presburger
        qed
        also have "... \<longleftrightarrow> True"
        proof -
          have 2: "t \\ u \<in> \<NN> \<and> R.arr (u \\ t)"
            using tT u src con NPath_def
            by (metis R.arr_resid R.con_imp_coinitial basic_trans_rules(31) forward_stable
                list.set_intros(1) R.con_sym)
          moreover have 3: "NPath (T \<^sup>*\\\<^sup>* [u \\ t])"
            using tT ind NPath_def
            by (metis 2 P.Con_Arr_self P.Con_imp_eq_Srcs P.Con_rec(4) R.arr_resid_iff_con
                R.sources_resid P.Srcs.simps(2) T insert_subset list.exhaust
                list.simps(15) P.Arr.simps(3))
          moreover have "R.targets (t \\ u) \<subseteq> P.Srcs (P.Resid T [u \\ t])"
            using tT T u src NPath_def
            by (metis 3 P.Arr.simps(1) R.targets_resid_sym P.Srcs_Resid_Arr_single
                con subset_refl)
          ultimately show ?thesis
            using NPath_def con by simp
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma NPath_Resid [simp]:
    shows "\<lbrakk>NPath T; P.Arr U; P.Srcs T = P.Srcs U\<rbrakk> \<Longrightarrow> NPath (T \<^sup>*\\\<^sup>* U)"
    proof (induct T arbitrary: U)
      show "\<And>U. \<lbrakk>NPath []; P.Arr U; P.Srcs [] = P.Srcs U\<rbrakk> \<Longrightarrow> NPath ([] \<^sup>*\\\<^sup>* U)"
        by simp
      fix t T U
      assume ind: "\<And>U. \<lbrakk>NPath T; P.Arr U; P.Srcs T = P.Srcs U\<rbrakk> \<Longrightarrow> NPath (T \<^sup>*\\\<^sup>* U)"
      assume tT: "NPath (t # T)"
      assume U: "P.Arr U"
      assume Coinitial: "P.Srcs (t # T) = P.Srcs U"
      show "NPath ((t # T) \<^sup>*\\\<^sup>* U)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT U Coinitial NPath_Resid_single_Arr NPath_def by force
        assume T: "T \<noteq> []"
        have 0: "NPath ((t # T) \<^sup>*\\\<^sup>* U) \<longleftrightarrow> NPath ([t] \<^sup>*\\\<^sup>* U @ T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
        proof -
          have "U \<noteq> []"
            using U by auto
          moreover have "(t # T) \<^sup>*\<frown>\<^sup>* U"
          proof -
            have 1: "[t] \<^sup>*\<frown>\<^sup>* U"
              using tT U NPath_Resid_single_Arr [of t U] NPath_def Coinitial P.Srcs_simp\<^sub>P
              by force
            moreover have "T \<^sup>*\<frown>\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
            proof -
              have "P.Srcs T = P.Srcs (U \<^sup>*\\\<^sup>* [t])"
                using T tT U Coinitial 1
                by (metis P.Con_Arr_self P.Con_cons(2) P.Con_imp_eq_Srcs P.Con_sym
                    P.Srcs_Resid_Arr_single list.discI NPath_implies_Arr)
              hence "NPath (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
                using T tT U Coinitial 1 P.Con_sym ind NPath_def
                by (metis P.Con_imp_Arr_Resid P.Srcs.elims insert_subset list.simps(15)
                    P.Arr.simps(3))
              thus ?thesis
                using NPath_def by auto
            qed
            ultimately show ?thesis
              using P.Con_cons(1) [of T U t] by fastforce
          qed
          ultimately show ?thesis
            using tT U T Coinitial P.Resid_cons(1) by auto
        qed
        also have "... \<longleftrightarrow> True"
        proof (intro iffI, simp_all)
          show "NPath (([t] \<^sup>*\\\<^sup>* U) @ (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])))"
          proof
            show 1: "NPath ([t] \<^sup>*\\\<^sup>* U)"
              by (metis Coinitial NPath_Resid_single_Arr P.Srcs_simp\<^sub>P U insert_subset
                  list.sel(1) list.simps(15) NPath_def tT)
            show 2: "NPath (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
              by (metis 0 1 P.Arr.simps(1) P.Con_cons(1) P.Con_imp_eq_Srcs
                  P.Con_implies_Arr(1-2) NPath_def T append_Nil2 ind
                  insert_subset list.simps(15) tT)
            show "P.Trgs ([t] \<^sup>*\\\<^sup>* U) \<subseteq> P.Srcs (T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t]))"
              by (metis 2 P.Arr.simps(1) NPath_def P.Srcs_Resid P.Trgs_Resid_sym
                  dual_order.refl)
          qed
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma Backward_stable_single:
    shows "\<lbrakk>NPath U; NPath ([t] \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath [t]"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>NPath []; NPath ([t] \<^sup>*\\\<^sup>* [])\<rbrakk> \<Longrightarrow> NPath [t]"
        using NPath_def by simp
      show "\<And>a U t. \<lbrakk>\<And>t. \<lbrakk>NPath U; NPath ([t] \<^sup>*\\\<^sup>* U)\<rbrakk> \<Longrightarrow> NPath [t];
                     NPath (a # U); NPath ([t] \<^sup>*\\\<^sup>* (a # U))\<rbrakk>
                        \<Longrightarrow> NPath [t]"
        using NPath_def P.Arr.simps(1-2) P.Con_implies_Arr(2)
            P.Resid_rec(1,3) insert_subset list.simps(15)
        by (metis P.Con_implies_Arr(1) backward_stable)
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
          by (metis P.Arr.simps(1) P.Con_cons(1) P.Resid_cons(1))
        thus ?thesis
          by (metis Backward_stable_single NPath_Resid NPath_def P.Arr.simps(1)
              P.Con_imp_eq_Srcs P.Con_implies_Arr(1) U ind insert_subset list.simps(15)
              resid)
      qed
    qed

    lemma Resid_along_NPath_preserves_reflects_Con:
    assumes "NPath U" and "P.Srcs T = P.Srcs U"
    shows "T \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* T' \<^sup>*\\\<^sup>* U \<longleftrightarrow> T \<^sup>*\<frown>\<^sup>* T'"
      using assms NPath_def NPath_Resid P.Con_implies_Arr(2) P.Cube(1)
      by (metis P.Arr.simps(1) P.Arr_iff_Con_self P.Con_imp_Arr_Resid P.Con_imp_eq_Srcs)

    lemma Resid_along_NPath_preserves_reflects_con:
    assumes "NPath U" and "R.sources t = P.Srcs U"
    shows "t \<^sup>1\\\<^sup>* U \<frown> t' \<^sup>1\\\<^sup>* U \<longleftrightarrow> t \<frown> t'"
    proof -
      have "t \<^sup>1\\\<^sup>* U \<frown> t' \<^sup>1\\\<^sup>* U \<longleftrightarrow> [t] \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* [t'] \<^sup>*\\\<^sup>* U"
        by (metis P.Con_Arr_self P.Con_implies_Arr(1) P.Resid1x_as_Resid
            P.null_is_zero(2) P.Con_rec(1) P.Resid1x_as_Resid' R.not_con_null(2))
      also have "... \<longleftrightarrow> [t] \<^sup>*\<frown>\<^sup>* [t']"
        by (simp add: Resid_along_NPath_preserves_reflects_Con assms(1,2))
      also have "... \<longleftrightarrow> t \<frown> t'"
        by auto
      finally show ?thesis by blast
    qed

    text \<open>
      A normal sub-RTS \<open>N\<close> of an RTS \<open>R\<close> lifts to a normal sub-RTS of the RTS of paths in \<open>R\<close>.
    \<close>

    interpretation NP: normal_sub_rts P.Resid \<open>Collect NPath\<close>
      using Ide_implies_NPath NPath_implies_Arr P.ide_char P.coinitial_def P.sources_char\<^sub>P
      apply unfold_locales
           apply auto
      by (meson Backward_stable)

    theorem normal_extends_to_paths:
    shows "normal_sub_rts P.Resid (Collect NPath)"
      ..

    abbreviation implode
    where "implode \<U> \<equiv> foldr (@) \<U> []"

    lemma NP_P_Srcs_eq:
    shows "NP.P.Arr \<U> \<Longrightarrow> NP.P.Srcs \<U> = P.sources (implode \<U>)"
    proof (induct \<U>)
      show "NP.P.Arr [] \<Longrightarrow> NP.P.Srcs [] = P.sources (implode [])"
        by simp
      show "\<And>U \<U>. \<lbrakk>NP.P.Arr \<U> \<Longrightarrow> NP.P.Srcs \<U> = P.sources (implode \<U>); NP.P.Arr (U # \<U>)\<rbrakk>
                     \<Longrightarrow> NP.P.Srcs (U # \<U>) = P.sources (implode (U # \<U>))"
      proof -
        fix U \<U>
        assume ind: "NP.P.Arr \<U> \<Longrightarrow> NP.P.Srcs \<U> = P.sources (implode \<U>)"
        assume U\<U>: "NP.P.Arr (U # \<U>)"
        show "NP.P.Srcs (U # \<U>) = P.sources (implode (U # \<U>))"
        proof (cases "\<U> = []")
          case True
          show ?thesis
            using True by simp
          next
          case False
          have "NP.P.Srcs (U # \<U>) = P.sources U"
            using U\<U>
            by (metis False NP.P.Srcs.simps(3) neq_Nil_conv)
          also have "... = P.sources (U @ implode \<U>)"
            by (metis (no_types, lifting) ext False NP.P.Con_Arr_self NP.P.Con_cons(2)
                NP.P.Trgs.simps(2) NP.P.paths_in_rts_axioms P.paths_in_rts_axioms
                P.seqI(1) U\<U> ind list.sel(1) list.simps(3) paths_in_rts.Arr_imp_arr_hd
                paths_in_rts.Con_imp_eq_Srcs paths_in_rts.Con_implies_Arr(2)
                paths_in_rts.Srcs_Resid paths_in_rts.sources_append)
          also have "... = P.sources (implode (U # \<U>))"
            by simp
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma P_Arr_implode:
    shows "NP.P.Arr \<U> \<Longrightarrow> P.Arr (implode \<U>)"
    proof (induct \<U>)
      show "NP.P.Arr [] \<Longrightarrow> P.Arr (implode [])"
        by simp
      show "\<And>U \<U>. \<lbrakk>NP.P.Arr \<U> \<Longrightarrow> P.Arr (implode \<U>); NP.P.Arr (U # \<U>)\<rbrakk>
                      \<Longrightarrow> P.Arr (implode (U # \<U>))"
      proof -
        fix U \<U>
        assume ind: "NP.P.Arr \<U> \<Longrightarrow> P.Arr (implode \<U>)"
        assume U\<U>: "NP.P.Arr (U # \<U>)"
        show "P.Arr (implode (U # \<U>))"
        proof (cases "\<U> = []")
          case True
          show ?thesis
            using True P.arr_char U\<U> by auto
          next
          case False
          show ?thesis
          proof -
            have "implode (U # \<U>) = U @ implode \<U>"
              by simp
            moreover have "P.Arr ..."
            proof (intro P.Arr_appendI\<^sub>P)
              show "P.Arr U"
                using NP.P.Arr_imp_arr_hd P.arr_char U\<U> by fastforce
              show "P.Arr (implode \<U>)"
                using False U\<U> ind
                by (metis NP.P.Arr_iff_Con_self NP.P.Con_implies_Arr(2) NP.P.Resid_cons(2))
              show "P.Trgs U \<subseteq> P.Srcs (implode \<U>)"
                using False U\<U> NP_P_Srcs_eq
                by (metis NP.P.Arr_has_Src P.Arr_has_Trg P.Trgs.simps(1)
                    P.arr_append_imp_seq P.arr_iff_has_source P.seq_char
                    \<open>P.Arr (implode \<U>)\<close> \<open>P.Arr U\<close> calculation set_eq_subset)
            qed
            ultimately show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma NP_P_Trgs_eq:
    shows "NP.P.Arr \<U> \<Longrightarrow> NP.P.Trgs \<U> = P.targets (implode \<U>)"
    proof (induct \<U>)
      show "NP.P.Arr [] \<Longrightarrow> NP.P.Trgs [] = P.targets (implode [])"
        by simp
      show "\<And>U \<U>. \<lbrakk>NP.P.Arr \<U> \<Longrightarrow> NP.P.Trgs \<U> = P.targets (implode \<U>); NP.P.Arr (U # \<U>)\<rbrakk>
                     \<Longrightarrow> NP.P.Trgs (U # \<U>) = P.targets (implode (U # \<U>))"
      proof -
        fix U \<U>
        assume ind: "NP.P.Arr \<U> \<Longrightarrow> NP.P.Trgs \<U> = P.targets (implode \<U>)"
        assume U\<U>: "NP.P.Arr (U # \<U>)"
        show "NP.P.Trgs (U # \<U>) = P.targets (implode (U # \<U>))"
        proof (cases "\<U> = []")
          case True
          show ?thesis
            using True by simp
          next
          case False
          have "NP.P.Trgs (U # \<U>) = NP.P.Trgs \<U>"
            by (metis False NP.P.Trgs_append append_Cons append_Nil)
          also have "... = P.targets (implode \<U>)"
            using U\<U> ind
            by (metis False NP.P.Arr_imp_Arr_tl list.sel(3))
          also have "... = P.targets (implode (U # \<U>))"
            using False U\<U>
            apply simp
            by (metis NP.P.Arr_has_Trg P.Arr.simps(1) P.arr_append_imp_seq P.arr_char
                P.arr_iff_has_target P.paths_in_rts_axioms P_Arr_implode append.left_neutral
                calculation concat.simps(2) concat_conv_foldr paths_in_rts.targets_append)
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma NP_Resid1x_eq:
    shows "NP.P.Resid1x T \<U> \<noteq> [] \<Longrightarrow> NP.P.Resid1x T \<U> = T \<^sup>*\\\<^sup>* implode \<U>"
    proof (induct \<U> arbitrary: T)
      show "\<And>T. NP.P.Resid1x T [] \<noteq> [] \<Longrightarrow> NP.P.Resid1x T [] = T \<^sup>*\\\<^sup>* implode []"
        by (simp add: P.null_char)
      show "\<And>U \<U> T. \<lbrakk>\<And>T. NP.P.Resid1x T \<U> \<noteq> [] \<Longrightarrow> NP.P.Resid1x T \<U> = T \<^sup>*\\\<^sup>* implode \<U>;
                      NP.P.Resid1x T (U # \<U>) \<noteq> []\<rbrakk>
                         \<Longrightarrow> NP.P.Resid1x T (U # \<U>) = T \<^sup>*\\\<^sup>* implode (U # \<U>)"
      proof -
        fix U \<U> T
        assume ind: "\<And>T. NP.P.Resid1x T \<U> \<noteq> [] \<Longrightarrow> NP.P.Resid1x T \<U> = T \<^sup>*\\\<^sup>* implode \<U>"
        assume U\<U>: "NP.P.Resid1x T (U # \<U>) \<noteq> []"
        show "NP.P.Resid1x T (U # \<U>) = T \<^sup>*\\\<^sup>* implode (U # \<U>)"
        proof (cases "\<U> = []")
          case True
          show ?thesis
            using True by fastforce
          next
          case False
          have "NP.P.Resid1x T (U # \<U>) = NP.P.Resid1x (T \<^sup>*\\\<^sup>* U) \<U>"
            using False
            by (metis NP.P.Resid1x.simps(3) neq_Nil_conv)
          also have "... = (T \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* implode \<U>"
            using U\<U> calculation ind by auto
          also have "... = T \<^sup>*\\\<^sup>* (U @ implode \<U>)"
            by (metis P.Con_appendI(2) P.Con_sym P.Resid.simps(1) P.Resid_append(2)
                U\<U> calculation)
          also have "... = T \<^sup>*\\\<^sup>* foldr (@) (U # \<U>) []"
            by auto
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma NP_NPath_imp:
    shows "NP.NPath \<U> \<Longrightarrow> NPath (implode \<U>)"
    proof (induct \<U>)
      show "NP.NPath [] \<Longrightarrow> NPath (implode [])"
        using NP.NPath_def NP.P.Arr.simps(1) by blast
      show "\<And>U \<U>. \<lbrakk>NP.NPath \<U> \<Longrightarrow> NPath (implode \<U>); NP.NPath (U # \<U>)\<rbrakk>
                      \<Longrightarrow> NPath (implode (U # \<U>))"
      proof -
        fix U \<U>
        assume ind: "NP.NPath \<U> \<Longrightarrow> NPath (implode \<U>)"
        assume U\<U>: "NP.NPath (U # \<U>)"
        show "NPath (implode (U # \<U>))"
        proof (cases "\<U> = []")
          case True
          show ?thesis
            using True NP.NPath_def U\<U> by fastforce
          next
          case False
          have "NPath (foldr (@) (U # \<U>) []) = NPath (U @ implode \<U>)"
            by force
          also have "... = True"
          proof -
            have "P.seq U (implode \<U>)"
            proof
              show "P.Arr U"
                using NPath_def NP.NPath_def U\<U> by force
              show "P.Arr (foldr (@) \<U> [])"
                by (metis False NPath_def NP.P.Arr_imp_Arr_tl U\<U> ind insert_subset list.sel(3)
                    list.simps(15) normal_extends_to_paths normal_sub_rts.NPath_def)
              show "P.Trgs U \<inter> P.Srcs (implode \<U>) \<noteq> {}"
              proof -
                have "P.Srcs (implode \<U>) = P.Srcs (hd \<U> @ implode (tl \<U>))"
                  using False
                  by (metis concat.simps(2) concat_conv_foldr hd_Cons_tl)
                also have "... = P.Srcs (hd \<U>)"
                  using False
                  by (metis NP.NPath_implies_Arr NP.P.Arr_imp_arr_hd P.null_char
                      U\<U> list.sel(3) NP.P.Arr_imp_Arr_tl P.Srcs_append P.not_arr_null)
                also have "... = P.Trgs U"
                proof -
                  have "NP.P.Srcs \<U> = P.targets U"
                    using False U\<U>
                    by (metis NP.P.Arr.simps(2) NP.P.Trgs.simps(2) list.exhaust_sel
                        normal_extends_to_paths normal_sub_rts.NPath_def NP.P.Arr.simps(3)
                        NP.P.seq_implies_Trgs_eq_Srcs)
                  thus ?thesis
                    using False
                    by (metis NP.NPath_implies_Arr NP.P.Arr_imp_Arr_tl NP.P.Srcs_simp\<^sub>P
                        P.arr_char P.seqI(1) P.seq_char U\<U> \<open>P.Arr U\<close> list.sel(3))
                qed
                finally have "P.Srcs (implode \<U>) = P.Trgs U" by blast
                moreover have "... \<noteq> {}"
                  using U\<U> by (simp add: P.Arr_has_Trg \<open>P.Arr U\<close>)
                ultimately show ?thesis by blast
              qed
            qed
            thus ?thesis
              using False U\<U> ind
              by (metis CollectD NPath_appendI NP.P.Arr_iff_Con_self NP.P.Con_cons(1)
                  insert_subset list.discI list.simps(15) NP.NPath_def order_refl
                  NP.P.Con_implies_Arr(2) NP.P.Con_rec(3) P.seq_char)
          qed
          finally show ?thesis by blast
        qed
      qed
    qed

  end

  subsection "Semi-Congruence"

    text \<open>
      Generalizing identity transitions to normal transitions in the definition of congruence,
      we obtain the notion of \emph{semi-congruence} of transitions with respect to a
      normal sub-RTS.
    \<close>

  context normal_sub_rts
  begin

    abbreviation Cong\<^sub>0  (infix \<open>\<approx>\<^sub>0\<close> 50)
    where "t \<approx>\<^sub>0 t' \<equiv> t \\ t' \<in> \<NN> \<and> t' \\ t \<in> \<NN>"

    lemma cong_implies_Cong\<^sub>0:
    assumes "t \<sim> t'"
    shows "t \<approx>\<^sub>0 t'"
      using assms ide_closed by blast

    lemma Cong\<^sub>0_iff:
    shows "t \<approx>\<^sub>0 t' \<longleftrightarrow> (\<exists>V V'. NPath V \<and> NPath V' \<and> [t] @ V \<^sup>*\<sim>\<^sup>* [t'] @ V')"
    proof
      show "t \<approx>\<^sub>0 t' \<Longrightarrow> \<exists>V V'. NPath V \<and> NPath V' \<and> [t] @ V \<^sup>*\<sim>\<^sup>* [t'] @ V'"
      proof (intro exI conjI)
        assume 1: "t \<approx>\<^sub>0 t'"
        show "NPath [t' \\ t]" and "NPath [t \\ t']"
          using "1" NPath_def elements_are_arr by force+
        have 2: "[t] @ [t' \\ t] \<^sup>*\<sim>\<^sup>* [t'] @ [t \\ t']"
          using 1 P.diamond_commutes_upto_cong P.append_is_composite_of
          by (metis (no_types, lifting) ext R.sources_resid P.Arr.simps(2)
              P.Con_implies_Arr(2) P.Resid.simps(3) P.Srcs.simps(2) P.Trgs.simps(2)
              elements_are_arr not_Cons_self2 P.seq_char R.arr_resid_iff_con)
        show "[t] @ [t' \\ t] \<^sup>*\<lesssim>\<^sup>* [t'] @ [t \\ t']"
          using 2 by blast
        show "[t'] @ [t \\ t'] \<^sup>*\<lesssim>\<^sup>* [t] @ [t' \\ t]"
          using 2 by blast
      qed
      show "\<exists>V V'. NPath V \<and> NPath V' \<and> [t] @ V \<^sup>*\<sim>\<^sup>* [t'] @ V' \<Longrightarrow> t \<approx>\<^sub>0 t'"
      proof
        assume 1: "\<exists>V V'. NPath V \<and> NPath V' \<and> [t] @ V \<^sup>*\<sim>\<^sup>* [t'] @ V'"
        obtain V V' where VV': "NPath V \<and> NPath V' \<and> [t] @ V \<^sup>*\<sim>\<^sup>* [t'] @ V'"
          using 1 by blast
        show "t \\ t' \<in> \<NN>"
        proof -
          have "[t \\ t'] \<^sup>*\<lesssim>\<^sup>* V'"
          proof -
            have "[t \\ t'] = [t] \<^sup>*\\\<^sup>* [t']"
              by (metis Cons_eq_append_conv P.Con_initial_left P.Con_initial_right
                  P.Resid_rec(1) P.not_ide_null P.null_char VV')
            moreover have "P.Ide ((([t] \<^sup>*\\\<^sup>* [t']) @ (V \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* [t]))) \<^sup>*\\\<^sup>* V')"
              by (metis NPath_implies_Arr P.Ide.simps(1) P.Resid.simps(1) P.Resid_append(1,2)
                  P.ide_char VV' not_Cons_self P.Con_Arr_self)
            ultimately show ?thesis
              using P.Resid_append(1) [of "[t] \<^sup>*\\\<^sup>* [t']" "V \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* [t])" V']
                    P.Con_sym P.Ide_append_iff\<^sub>P P.con_char P.ide_char P.null_char
                    P.prfx_implies_con append.right_neutral P.null_is_zero(2)
              by metis
          qed
          hence "NPath [t \\ t']"
            using Backward_stable Ide_implies_NPath P.ide_char VV' by blast
          thus ?thesis
            using NPath_def by auto
        qed
        show "t' \\ t \<in> \<NN>"
        proof -
          have "[t' \\ t] \<^sup>*\<lesssim>\<^sup>* V"
          proof -
            have "[t' \\ t] = [t'] \<^sup>*\\\<^sup>* [t]"
              by (metis Cons_eq_append_conv P.Con_initial_left P.Con_initial_right
                  P.Resid_rec(1) P.not_ide_null P.null_char VV')
            moreover have "P.Ide ((([t'] \<^sup>*\\\<^sup>* [t]) @ (V' \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t']))) \<^sup>*\\\<^sup>* V)"
              by (metis NPath_implies_Arr P.Ide.simps(1) P.Resid.simps(1) P.Resid_append(1,2)
                  P.ide_char P.paths_in_rts_axioms VV' not_Cons_self paths_in_rts.Con_Arr_self)
            ultimately show ?thesis
              using P.Resid_append(1) [of "[t'] \<^sup>*\\\<^sup>* [t]" "V' \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* [t'])" V]
                    P.Con_sym P.Ide_append_iff\<^sub>P P.con_char P.ide_char P.null_char
                    P.prfx_implies_con append.right_neutral P.null_is_zero(2)
              by metis
          qed
          hence "NPath [t' \\ t]"
            using Backward_stable Ide_implies_NPath P.ide_char VV' by blast
          thus ?thesis
            using NPath_def by auto
        qed
      qed
    qed

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
      Semi-congruence is preserved and reflected by residuation along normal transitions,
      hence along normal paths.
    \<close>

    lemma Resid_along_normal_preserves_Cong\<^sub>0:
    assumes "t \<approx>\<^sub>0 t'" and "u \<in> \<NN>" and "R.sources t = R.sources u" 
    shows "t \\ u \<approx>\<^sub>0 t' \\ u"
      by (metis Cong\<^sub>0_imp_coinitial R.arr_resid_iff_con R.coinitialI R.coinitial_def
          R.cube R.sources_resid assms elements_are_arr forward_stable)

    lemma Resid_along_NPath_preserves_Cong\<^sub>0:
    assumes "t \<approx>\<^sub>0 t'" and "NPath U" and "R.sources t = P.Srcs U" 
    shows "\<lbrakk>t \<approx>\<^sub>0 t'; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U"
    proof (induct U arbitrary: t t' rule: NPath_induct)
      show "NPath U" by fact
      show "\<And>t t' u. \<lbrakk>u \<in> \<NN>; t \<approx>\<^sub>0 t'; R.sources t = P.Srcs [u]\<rbrakk> \<Longrightarrow> t \<^sup>1\\\<^sup>* [u] \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* [u]"
        using Resid_along_normal_preserves_Cong\<^sub>0 by auto
      show "\<And>t t' u U. \<lbrakk>u \<in> \<NN>; NPath U; R.targets u \<subseteq> P.Srcs U;
                        \<And>t t'. \<lbrakk>t \<approx>\<^sub>0 t'; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U;
                        t \<approx>\<^sub>0 t'; R.sources t = P.Srcs (u # U)\<rbrakk>
                           \<Longrightarrow> t \<^sup>1\\\<^sup>* (u # U) \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* (u # U)"
      proof -
        fix t t' u U
        assume u: "u \<in> \<NN>" and U: "NPath U" and uU: "R.targets u \<subseteq> P.Srcs U"
        assume tt': "t \<approx>\<^sub>0 t'" and tuU: "R.sources t = P.Srcs (u # U)"
        assume ind: "\<And>t t'. \<lbrakk>t \<approx>\<^sub>0 t'; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U"
        show "t \<^sup>1\\\<^sup>* (u # U) \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* (u # U)"
        proof -
          have "t \\ u \<approx>\<^sub>0 t' \\ u"
            by (metis Resid_along_normal_preserves_Cong\<^sub>0 P.Srcs.simps(2,3) neq_Nil_conv
                tt' tuU u)
          moreover have "(t \\ u) \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 (t' \\ u) \<^sup>1\\\<^sup>* U"
            by (metis NPath_implies_Arr R.conE R.conI R.null_is_zero(2) R.sources_resid
                P.Arr.simps(2) P.Trgs.simps(2) U calculation elements_are_arr ind
                Cong\<^sub>0_imp_con P.seq_implies_Trgs_eq_Srcs u uU)
          moreover have "(t \\ u) \<^sup>1\\\<^sup>* U = t \<^sup>1\\\<^sup>* (u # U) \<and> (t' \\ u) \<^sup>1\\\<^sup>* U = t' \<^sup>1\\\<^sup>* (u # U)"
            by (metis NPath_implies_Arr P.Resid1x.simps(3) P.arrI\<^sub>P P.not_arr_null
                P.null_char U neq_Nil_conv)
          ultimately show ?thesis by argo
        qed
      qed
    qed

    lemma Resid_along_normal_reflects_Cong\<^sub>0:
    assumes "t \\ u \<approx>\<^sub>0 t' \\ u" and "u \<in> \<NN>"
    shows "t \<approx>\<^sub>0 t'"
      using assms
      by (metis backward_stable R.con_imp_coinitial R.cube R.null_is_zero(2)
                forward_stable R.conI)

    lemma Resid_along_NPath_reflects_Cong\<^sub>0:
    assumes "t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U" and "NPath U"
    shows "t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U \<Longrightarrow> t \<approx>\<^sub>0 t'"
    proof (induct U arbitrary: t t' rule: NPath_induct)
      show "NPath U" by fact
      show "\<And>t t' u. \<lbrakk>u \<in> \<NN>; t \<^sup>1\\\<^sup>* [u] \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* [u]\<rbrakk> \<Longrightarrow> t \<approx>\<^sub>0 t'"
        by (metis Resid_along_normal_reflects_Cong\<^sub>0 P.Resid1x.simps(2))
      show "\<And>t t' u U. \<lbrakk>u \<in> \<NN>; NPath U; R.targets u \<subseteq> P.Srcs U;
                        \<And>t t'. t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U \<Longrightarrow> t \<approx>\<^sub>0 t';
                        t \<^sup>1\\\<^sup>* (u # U) \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* (u # U)\<rbrakk>
                          \<Longrightarrow> t \<approx>\<^sub>0 t'"
      proof -
        fix t t' u U
        assume u: "u \<in> \<NN>" and U: "NPath U" and uU: "R.targets u \<subseteq> P.Srcs U"
        assume tt': "t \<^sup>1\\\<^sup>* (u # U) \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* (u # U)"
        assume ind: "\<And>t t'. t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U \<Longrightarrow> t \<approx>\<^sub>0 t'"
        show "t \<approx>\<^sub>0 t'"
        proof -
          have "t \\ u \<approx>\<^sub>0 t' \\ u"
          proof -
            have "t \<^sup>1\\\<^sup>* (u # U) = (t \\ u) \<^sup>1\\\<^sup>* U \<and> t' \<^sup>1\\\<^sup>* (u # U) = (t' \\ u) \<^sup>1\\\<^sup>* U"
              by (metis NPath_implies_Arr P.Arr.simps(1) P.Resid1x.simps(3) U list.exhaust)
            thus ?thesis
              using tt' ind by presburger
          qed
          thus ?thesis
            using Resid_along_normal_reflects_Cong\<^sub>0 u by blast
        qed
      qed
    qed

    text \<open>
      Semi-congruence is substitutive for the left-hand argument of residuation.
    \<close>

    lemma Cong\<^sub>0_subst_left:
    assumes "t \<approx>\<^sub>0 t'" and "t \<frown> u"
    shows "t' \<frown> u" and "t \\ u \<approx>\<^sub>0 t' \\ u"
    proof -
      have 1: "t \<frown> u \<and> t \<frown> t' \<and> u \\ t \<frown> t' \\ t"
        using assms
        by (metis Resid_along_normal_preserves_Cong\<^sub>0 Cong\<^sub>0_imp_con Cong\<^sub>0_reflexive
                  R.con_sym R.null_is_zero(2) R.arr_resid_iff_con R.sources_resid R.conI)
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
      using assms Cong\<^sub>0_subst_left(1) R.con_sym
       apply meson
      using assms R.sources_resid Cong\<^sub>0_imp_con Cong\<^sub>0_reflexive
        Resid_along_normal_preserves_Cong\<^sub>0 R.arr_resid_iff_con residuation.cube
        R.residuation_axioms
      by metis

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
        by (meson assms(1,3) Cong\<^sub>0_subst_left(2) R.composite_of_def R.con_sym
            R.prfx_implies_con)
      also have "v' \\ t \<approx>\<^sub>0 u'"
        using assms(2) ide_closed by blast
      finally show ?thesis by auto
    qed

    lemma diamond_commutes_upto_Cong\<^sub>0:
    assumes "R.composite_of t (u \\ t) v" and "R.composite_of u (t \\ u) v'"
    shows "v \<approx>\<^sub>0 v'"
    proof -
      have "v \\ v \<approx>\<^sub>0 v' \\ v \<and> v' \\ v' \<approx>\<^sub>0 v \\ v'"
        using R.arr_composite_of R.cong_subst_left(2) R.diamond_commutes_upto_cong
          assms ide_closed
        by auto
      thus ?thesis
        by (metis assms R.composite_of_unq_upto_cong R.resid_arr_ide Cong\<^sub>0_imp_con)
    qed

  end

  subsection "Congruence"

  text \<open>
    We use semi-congruence to define a coarser relation as follows.
  \<close>

  context normal_sub_rts
  begin

    definition Cong  (infix \<open>\<approx>\<close> 50)
    where "Cong t t' \<equiv> \<exists>U U'. NPath U \<and> NPath U' \<and> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"

    lemma CongI [intro]:
    assumes "NPath U" and "NPath U'" and "t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"
    shows "Cong t t'"
      using assms Cong_def by auto

    lemma CongE [elim]:
    assumes "t \<approx> t'"
    obtains U U'
    where "NPath U" and "NPath U'" and "t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"
      using assms Cong_def by auto

    lemma Cong_imp_arr:
    assumes "t \<approx> t'"
    shows "R.arr t" and "R.arr t'"
      using assms Cong_def Cong\<^sub>0_imp_con R.arr_resid_iff_con R.con_implies_arr(1)
       apply (metis R.conI P.Resid1x.elims P.Resid1x_null)
      by (metis Cong\<^sub>0_imp_con Cong_def R.conI R.con_implies_arr(1) R.residuation_axioms
          P.Resid1x.elims P.Resid1x_null assms residuation.not_con_null(2))

    lemma Cong_reflexive:
    assumes "R.arr t"
    shows "t \<approx> t"
      unfolding Cong_def
      using assms Cong\<^sub>0_reflexive
      by (metis R.arr_resid R.con_imp_coinitial_ax R.con_sym R.residuation_axioms
          P.Ide.simps(2) P.Resid1x.simps(2) normal_sub_rts.Ide_implies_NPath
          normal_sub_rts_axioms residuation.arrE)

    lemma Cong_symmetric:
    assumes "t \<approx> t'"
    shows "t' \<approx> t"
      using assms Cong_def Cong\<^sub>0_symmetric by blast

    text \<open>
      The existence of composites of normal paths is used in the following.
    \<close>

    lemma Cong_transitive [trans]:
    assumes "t \<approx> t''" and "t'' \<approx> t'"
    shows "t \<approx> t'"
    proof -
      obtain U U'' where UU'': "NPath U \<and> NPath U'' \<and> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t'' \<^sup>1\\\<^sup>* U''"
        using assms Cong_def by blast
      obtain V' V'' where V'V'': "NPath V' \<and> NPath V'' \<and> t'' \<^sup>1\\\<^sup>* V'' \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'"
        using assms Cong_def by blast
      have U''V'': "P.coinitial U'' V''"
      proof
        show "P.Arr U''"
          using UU'' NPath_def by blast
        show "P.Arr V''"
          using V'V'' NPath_def by blast
        show "P.Srcs U'' \<inter> P.Srcs V'' \<noteq> {}"
        proof -
          have "R.sources t'' \<subseteq> P.Srcs U'' \<inter> P.Srcs V''"
            using UU'' V'V'' P.Resid1x_as_Resid
            by (metis P.Con_imp_eq_Srcs P.Con_rec(1) P.Con_sym1 P.Resid1x_null
                P.Residx1_as_Resid P.Srcs.simps(2) inf.idem
                normal_sub_rts.Cong\<^sub>0_imp_con normal_sub_rts_axioms subset_refl)
          moreover have "R.sources t'' \<noteq> {}"
            using UU'' Cong_imp_arr(1) R.arr_iff_has_source by blast
          ultimately show ?thesis by blast
        qed
      qed
      hence V''U'': "P.coinitial V'' U''"
        by blast
      have 1: "NPath (U @ (V'' \<^sup>*\\\<^sup>* U'')) \<and> NPath (V' @ (U'' \<^sup>*\\\<^sup>* V'')) \<and>
               NPath (U'' @ (V'' \<^sup>*\\\<^sup>* U''))"
      proof (intro NPath_appendI conjI)
        show "NPath U" and "NPath U''"
          using UU'' by blast+
        show "NPath V'"
          using V'V'' by blast
        show "NPath (V'' \<^sup>*\\\<^sup>* U'')" and "NPath (V'' \<^sup>*\\\<^sup>* U'')" and "NPath (U'' \<^sup>*\\\<^sup>* V'')"
          using P.coinitial_char(1) V''U'' V'V'' UU'' by force+
        have "P.Trgs U = P.Trgs U''" and "P.Trgs V' = P.Trgs V''"
          using Cong\<^sub>0_imp_coinitial UU'' V'V''
          by (metis Cong\<^sub>0_imp_con R.residuation_axioms P.Resid1x.simps(2) P.Resid1x_as_Resid'
              P.Srcs.simps(2) P.Resid1x_as_Resid P.Resid1x_null P.Srcs_Resid residuation.conE)+
        show "P.Trgs U \<subseteq> P.Srcs (V'' \<^sup>*\\\<^sup>* U'')"
          by (metis NPath_def P.Arr.simps(1) P.Srcs_Resid \<open>NPath (V'' \<^sup>*\\<^sup>* U'')\<close>
              \<open>P.Trgs U = P.Trgs U''\<close> subset_refl)
        show "P.Trgs U'' \<subseteq> P.Srcs (V'' \<^sup>*\\\<^sup>* U'')"
          using \<open>P.Trgs U = P.Trgs U''\<close> \<open>P.Trgs U \<subseteq> P.Srcs (V'' \<^sup>*\\<^sup>* U'')\<close> by order
        show "P.Trgs V' \<subseteq> P.Srcs (U'' \<^sup>*\\\<^sup>* V'')"
          by (metis NPath_def P.Arr.simps(1) P.Srcs_Resid \<open>NPath (U'' \<^sup>*\\<^sup>* V'')\<close>
              \<open>P.Trgs V' = P.Trgs V''\<close> set_eq_subset)
      qed
      have 2: "(t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'') \<frown> (t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')"
      proof -
        have "t \<^sup>1\\\<^sup>* U \<frown> t'' \<^sup>1\\\<^sup>* U''"
          using Cong\<^sub>0_imp_con UU'' by blast
        hence "[t] \<^sup>*\\\<^sup>* U \<^sup>*\<frown>\<^sup>* [t''] \<^sup>*\\\<^sup>* U''"
          by (metis R.not_con_null(1) P.Con_rec(1) P.Con_sym P.Con_sym1
              P.Resid1x_as_Resid P.Residx1_as_Resid)
        hence "([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\<frown>\<^sup>* ([t''] \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')"
          by (metis NPath_Resid Resid_along_NPath_preserves_reflects_Con P.arrI\<^sub>P
              V''U'' V'V'' NPath_implies_Arr P.Con_imp_eq_Srcs P.Con_implies_Arr(2)
              P.Srcs_Resid P.coinitial_char(1) P.con_char P.arr_resid_iff_con)
        thus ?thesis
          by (metis P.Con_sym P.Resid.simps(1,3) P.Resid1x_as_Resid)
      qed
      have 3: "(t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'') \<frown> (t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')"
      proof -
        have "t' \<^sup>1\\\<^sup>* V' \<frown> t'' \<^sup>1\\\<^sup>* V''"
          using Cong\<^sub>0_imp_con V'V'' by blast
        hence "[t'] \<^sup>*\\\<^sup>* V' \<^sup>*\<frown>\<^sup>* [t''] \<^sup>*\\\<^sup>* V''"
          by (metis R.not_con_null(1) P.Con_rec(1) P.Con_sym P.Con_sym1
              P.Resid1x_as_Resid P.Residx1_as_Resid)
        hence "([t'] \<^sup>*\\\<^sup>* V') \<^sup>*\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\<frown>\<^sup>* ([t''] \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')"
          by (metis NPath_Resid Resid_along_NPath_preserves_reflects_Con P.Con_imp_eq_Srcs
              P.Resid.simps(1,2) P.coinitial_char(1) U''V'' UU'' V'V'')
        thus ?thesis
          by (metis P.Con_sym P.Resid.simps(1,3) P.Resid1x_as_Resid)
      qed
      have "t \<^sup>1\\\<^sup>* (U @ (V'' \<^sup>*\\\<^sup>* U'')) \<approx>\<^sub>0 t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))"
      proof -
        have "t \<^sup>1\\\<^sup>* (U @ (V'' \<^sup>*\\\<^sup>* U'')) = (t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')"
        proof -
          have "[t] \<^sup>*\<frown>\<^sup>* U @ (V'' \<^sup>*\\\<^sup>* U'')"
            by (metis "2" P.Con_appendI(2) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                P.Resid1x_null R.not_con_null(1))
          thus ?thesis
            using UU'' V''U'' V'V'' 1 P.Resid1x_as_Resid P.Resid_append(2)
            by (metis "2" NPath_def P.Arr.simps(1) P.Con_append(2) P.Resid.simps(2)
                P.Resid1x_as_Resid' R.con_def not_Cons_self2 R.null_is_zero(2))
        qed
        also have "... \<approx>\<^sub>0 (t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')"
        proof
          show "((t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \\ ((t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \<in> \<NN>"
          proof -
            have "[((t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \\ ((t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U''))] =
                  [((t \<^sup>1\\\<^sup>* U) \\ (t'' \<^sup>1\\\<^sup>* U'')) \<^sup>1\\\<^sup>* ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t''] \<^sup>*\\\<^sup>* U''))]"
            proof -
              have "[((t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \\ ((t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U''))] =
                    [(t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')] \<^sup>*\\\<^sup>* [(t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')]"
                using UU'' V'V'' V''U'' 2 by auto
              also have "... = ([t \<^sup>1\\\<^sup>* U] \<^sup>*\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \<^sup>*\\\<^sup>*
                                 ([t'' \<^sup>1\\\<^sup>* U''] \<^sup>*\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U''))"
                by (metis "2" R.residuation_axioms P.Resid1x_as_Resid P.Con_rec(1)
                    P.Con_sym P.Resid1x_as_Resid' residuation.not_con_null(2))
              also have "... = ([t \<^sup>1\\\<^sup>* U] \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* U'']) \<^sup>*\\\<^sup>* 
                                 ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t''] \<^sup>*\\\<^sup>* U''))"
                by (metis "2" R.not_con_null(2) P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                    P.Resid1x_null P.Residx1_as_Resid P.cube)
              also have "... = [(t \<^sup>1\\\<^sup>* U) \\ (t'' \<^sup>1\\\<^sup>* U'')] \<^sup>*\\\<^sup>*
                                 ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t''] \<^sup>*\\\<^sup>* U''))"
                using calculation by auto
              also have "... = [((t \<^sup>1\\\<^sup>* U) \\ (t'' \<^sup>1\\\<^sup>* U'')) \<^sup>1\\\<^sup>*
                                  ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t''] \<^sup>*\\\<^sup>* U''))]"
                using P.Resid1x_as_Resid calculation by force
              finally show ?thesis by blast
            qed
            moreover have "NPath ..."
            proof -
              have "((t \<^sup>1\\\<^sup>* U) \\ (t'' \<^sup>1\\\<^sup>* U'')) \<^sup>1\\\<^sup>* ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t''] \<^sup>*\\\<^sup>* U'')) \<in> \<NN>"
                by (metis (lifting) ext "2" UU'' NPath_Resid P.Resid.simps(1) P.coinitial_char(1)
                    P.ex_un_null R.arr_resid_iff_con R.not_arr_null
                    Resid_along_NPath_preserves_Cong\<^sub>0 UU'' V''U'' V'V'' calculation list.sel(1)
                    P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Srcs.simps(2) P.Srcs_Resid)
              thus ?thesis
                by (metis NPath_def P.Arr.simps(2) empty_subsetI insert_subset list.simps(15)
                    elements_are_arr set_empty)
            qed
            thus ?thesis
              using NPath_def calculation by force
          qed
          show "((t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \\ ((t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \<in> \<NN>"
          proof -
            have "[((t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \\ ((t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U''))] =
                  [((t'' \<^sup>1\\\<^sup>* U'') \\ (t \<^sup>1\\\<^sup>* U)) \<^sup>1\\\<^sup>* ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))]"
            proof -
              have "[((t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \\ ((t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U''))] =
                    [(t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')] \<^sup>*\\\<^sup>* [(t \<^sup>1\\\<^sup>* U) \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')]"
                using UU'' V'V'' V''U'' 2
                by (metis P.Con_rec(1) P.Con_sym P.Resid_rec(1))
              also have "... = ([t'' \<^sup>1\\\<^sup>* U''] \<^sup>*\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'')) \<^sup>*\\\<^sup>*
                                  ([t \<^sup>1\\\<^sup>* U] \<^sup>*\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U''))"
                by (metis "2" R.residuation_axioms P.Resid1x_as_Resid P.Con_rec(1) P.Con_sym
                    P.Resid1x_as_Resid' residuation.not_con_null(2))
              also have "... = ([t'' \<^sup>1\\\<^sup>* U''] \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* U]) \<^sup>*\\\<^sup>*
                                  ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
                by (metis "2" R.not_con_null(1) P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                    P.Resid1x_null P.Residx1_as_Resid P.cube)
              also have "... = [(t'' \<^sup>1\\\<^sup>* U'') \\ (t \<^sup>1\\\<^sup>* U)] \<^sup>*\\\<^sup>*
                                  ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
                using calculation by auto
              also have "... = [((t'' \<^sup>1\\\<^sup>* U'') \\ (t \<^sup>1\\\<^sup>* U)) \<^sup>1\\\<^sup>*
                                  ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))]"
                using P.Resid1x_as_Resid calculation by force
              finally show ?thesis by blast
            qed
            moreover have "NPath ..."
            proof -
              have "((t'' \<^sup>1\\\<^sup>* U'') \\ (t \<^sup>1\\\<^sup>* U)) \<^sup>1\\\<^sup>* ((V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) \<in> \<NN>"
                using "2" UU'' NPath_Resid P.Resid.simps(1) P.coinitial_char(1)
                      P.ex_un_null R.arr_resid_iff_con R.not_arr_null
                      Resid_along_NPath_preserves_Cong\<^sub>0 UU'' V''U'' V'V'' calculation list.sel(1)
                      P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Srcs.simps(2) P.Srcs_Resid
                by (metis (no_types, lifting) ext R.null_is_zero(2) elements_are_arr)
              thus ?thesis
                by (metis Cong\<^sub>0_imp_con NPath_def P.Arr.simps(2) R.arr_resid_iff_con
                    \<open>((t \<^sup>1\\<^sup>* U) \<^sup>1\\<^sup>* (V'' \<^sup>*\\<^sup>* U'')) \ ((t'' \<^sup>1\\<^sup>* U'') \<^sup>1\\<^sup>* (V'' \<^sup>*\\<^sup>* U'')) \<in> \<NN>\<close>
                    calculation empty_subsetI insert_subset list.simps(15) set_empty)
            qed
            thus ?thesis
              using NPath_def calculation by force
          qed
        qed
        also have "(t'' \<^sup>1\\\<^sup>* U'') \<^sup>1\\\<^sup>* (V'' \<^sup>*\\\<^sup>* U'') = t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))"
          using UU'' 1 P.Resid1x_as_Resid [of t'' "U'' @ (V'' \<^sup>*\\\<^sup>* U'')"]
                P.Resid1x_as_Resid [of "t'' \<^sup>1\\\<^sup>* U''" "V'' \<^sup>*\\\<^sup>* U''"]
                P.Resid_append(2) [of U'' "V'' \<^sup>*\\\<^sup>* U''" "[t'']"]
          by (metis "2" P.Con_appendI(2) P.Resid1x_as_Resid R.not_con_null(2)
              Cong\<^sub>0_imp_con P.Resid1x.simps(1) P.Resid1x_as_Resid')
        finally show ?thesis by blast
      qed
      also have "t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U'')) \<approx>\<^sub>0 t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V''))"
      proof -
        have "[t''] \<^sup>*\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U'')) \<^sup>*\<sim>\<^sup>* [t''] \<^sup>*\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V''))"
        proof -
          have "U'' @ (V'' \<^sup>*\\\<^sup>* U'') \<^sup>*\<sim>\<^sup>* V'' @ (U'' \<^sup>*\\\<^sup>* V'')"
            using U''V'' UU'' P.append_is_composite_of
                  P.diamond_commutes_upto_cong
                    [of U'' V'' "U'' @ (V'' \<^sup>*\\\<^sup>* U'')" "V'' @ (U'' \<^sup>*\\\<^sup>* V'')"]
            by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.Con_imp_Arr_Resid
                P.Srcs_Resid P.coinitial_char(1) P.paths_in_rts_axioms paths_in_rts.Con_sym
                paths_in_rts.seq_char)
          thus ?thesis
            by (metis P.Resid1x_as_Resid' P.cong_subst_right(2) R.not_arr_null
                R.null_is_zero(2) calculation elements_are_arr P.con_char)
        qed
        hence "[t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))] \<^sup>*\<sim>\<^sup>* [t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V''))]"
          by (metis P.Resid1x_as_Resid P.ex_un_null P.ide_backward_stable P.Resid.simps(1))
        hence "P.Ide ([t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))] \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V''))]) \<and>
               P.Ide ([t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V''))] \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))])"
          using P.ide_char by blast
        hence "R.ide ((t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))) \\ (t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V'')))) \<and>
               R.ide ((t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V''))) \\ (t'' \<^sup>1\\\<^sup>* (U'' @ (V'' \<^sup>*\\\<^sup>* U''))))"
          by (metis P.Ide.simps(1) P.Ide_imp_Ide_last P.Resid_rec(1) last_ConsL)
        thus ?thesis
          using ide_closed by blast
      qed
      also have "t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V'')) \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* (V' @ (U'' \<^sup>*\\\<^sup>* V''))"
      proof -
        have "t'' \<^sup>1\\\<^sup>* (V'' @ (U'' \<^sup>*\\\<^sup>* V'')) = (t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')"
          by (metis "3" Cong\<^sub>0_imp_con P.Resid1x_append P.null_char P.null_is_zero(2)
              R.not_con_null(2) calculation P.Resid1x_as_Resid')
        also have "... \<approx>\<^sub>0 (t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')"
        proof
          show "((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \<in> \<NN>"
          proof -
            have "NPath [((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))]"
            proof -
              have "[((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))] =
                    [((t'' \<^sup>1\\\<^sup>* V'') \\ (t' \<^sup>1\\\<^sup>* V')) \<^sup>1\\\<^sup>* ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* V'])]"
              proof -
                have "[((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))] =
                      [(t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')] \<^sup>*\\\<^sup>* [(t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')]"
                  using UU'' V'V'' V''U'' 3
                  by (metis P.Con_rec(1) P.Con_sym P.Resid_rec(1))
                also have "... = ([t'' \<^sup>1\\\<^sup>* V''] \<^sup>*\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \<^sup>*\\\<^sup>*
                                    ([t' \<^sup>1\\\<^sup>* V'] \<^sup>*\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))"
                  by (metis "3" R.not_con_null(1,2) P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                      P.Residx1_as_Resid)
                also have "... = ([t'' \<^sup>1\\\<^sup>* V''] \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* V']) \<^sup>*\\\<^sup>*
                                    ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* V'])"
                  using P.cube by blast
                also have "... = [(t'' \<^sup>1\\\<^sup>* V'') \\ (t' \<^sup>1\\\<^sup>* V')] \<^sup>*\\\<^sup>*
                                    ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* V'])"
                  using calculation by auto
                also have "... = [((t'' \<^sup>1\\\<^sup>* V'') \\ (t' \<^sup>1\\\<^sup>* V')) \<^sup>1\\\<^sup>*
                                     ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* V'])]"
                  using P.Resid1x_as_Resid calculation by force
                finally show ?thesis by blast
              qed
              moreover have "NPath ..."
              proof -
                have "(t'' \<^sup>1\\\<^sup>* V'') \\ (t' \<^sup>1\\\<^sup>* V') \<in> \<NN>"
                  using V'V'' by blast
                hence "NPath ([(t'' \<^sup>1\\\<^sup>* V'') \\ (t' \<^sup>1\\\<^sup>* V')] \<^sup>*\\\<^sup>*
                                 ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* V']))"
                  using NPath_Resid_single_Arr
                  by (metis (full_types) "3" Cong\<^sub>0_imp_con P.Con_imp_Arr_Resid
                      P.Resid1x_as_Resid' P.null_char R.con_def R.not_con_null(1)
                      R.sources_resid P.Srcs_Resid_Arr_single P.con_sym_ax)
                thus ?thesis
                  by (metis Backward_stable P.Resid.simps(1) P.Resid1x_as_Resid P.ex_un_null)
              qed
              ultimately show ?thesis
                by argo
            qed
            thus ?thesis
              by (simp add: NPath_def)
          qed
          show "((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \<in> \<NN>"
          proof -
            have "NPath [((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))]"
            proof -
              have "[((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))] =
                    [((t' \<^sup>1\\\<^sup>* V') \\ (t'' \<^sup>1\\\<^sup>* V'')) \<^sup>1\\\<^sup>* ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* V''])]"
              proof -
                have "[((t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \\ ((t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))] =
                      [(t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')] \<^sup>*\\\<^sup>* [(t'' \<^sup>1\\\<^sup>* V'') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')]"
                  using UU'' V'V'' V''U'' 3
                  by (metis P.Con_rec(1) P.Resid_rec(1))
                also have "... = ([t' \<^sup>1\\\<^sup>* V'] \<^sup>*\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'')) \<^sup>*\\\<^sup>*
                                    ([t'' \<^sup>1\\\<^sup>* V''] \<^sup>*\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V''))"
                  by (metis "3" R.not_con_null(1,2) P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                      P.Residx1_as_Resid)
                also have "... = ([t' \<^sup>1\\\<^sup>* V'] \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* V'']) \<^sup>*\\\<^sup>*
                                     ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* V''])"
                  using P.cube by blast
                also have "... = [(t' \<^sup>1\\\<^sup>* V') \\ (t'' \<^sup>1\\\<^sup>* V'')] \<^sup>*\\\<^sup>*
                                    ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* V''])"
                  using calculation by auto
                also have "... = [((t' \<^sup>1\\\<^sup>* V') \\ (t'' \<^sup>1\\\<^sup>* V'')) \<^sup>1\\\<^sup>*
                                     ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* V''])]"
                  using P.Resid1x_as_Resid calculation by force
                finally show ?thesis by blast
              qed
              moreover have "NPath ..."
              proof -
                have "(t' \<^sup>1\\\<^sup>* V') \\ (t'' \<^sup>1\\\<^sup>* V'') \<in> \<NN>"
                  using V'V'' by blast
                hence "NPath ([(t' \<^sup>1\\\<^sup>* V') \\ (t'' \<^sup>1\\\<^sup>* V'')] \<^sup>*\\\<^sup>*
                                 ((U'' \<^sup>*\\\<^sup>* V'') \<^sup>*\\\<^sup>* [t'' \<^sup>1\\\<^sup>* V'']))"
                  using NPath_Resid_single_Arr
                  by (metis "3" P.Con_imp_eq_Srcs P.Con_implies_Arr(2) P.Resid1x_as_Resid'
                      P.Srcs.simps(2) R.conE calculation list.inject)
                thus ?thesis
                  by (metis Backward_stable P.Resid.simps(1) P.Resid1x_as_Resid P.ex_un_null)
              qed
              ultimately show ?thesis
                by argo
            qed
            thus ?thesis
              by (simp add: NPath_def)
          qed
        qed
        also have "(t' \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (U'' \<^sup>*\\\<^sup>* V'') = t' \<^sup>1\\\<^sup>* (V' @ (U'' \<^sup>*\\\<^sup>* V''))"
          using UU'' 1 P.Resid1x_append [of V' "U'' \<^sup>*\\\<^sup>* V''" t']
          by (metis "3" P.Con_appendI(1) P.Con_sym P.Con_sym1 P.Resid1x.simps(1)
              P.Resid1x_as_Resid P.Resid1x_null P.Residx1_as_Resid R.con_implies_arr(1)
              R.not_arr_null)
        finally show ?thesis by blast
      qed
      finally have "Cong\<^sub>0 (t \<^sup>1\\\<^sup>* (U @ (V'' \<^sup>*\\\<^sup>* U''))) (t' \<^sup>1\\\<^sup>* (V' @ (U'' \<^sup>*\\\<^sup>* V'')))"
        by blast
      thus ?thesis
        unfolding Cong_def
        using \<open>NPath (U @ V'' \<^sup>*\\<^sup>* U'') \<and> NPath (V' @ U'' \<^sup>*\\<^sup>* V'') \<and> NPath (U'' @ V'' \<^sup>*\\<^sup>* U'')\<close>
        by blast
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
        by (metis Cong\<^sub>0_imp_con Cong\<^sub>0_subst_left(2) R.con_imp_coinitial_ax R.con_sym P.Ide.simps(2) P.Resid1x.simps(2)
            normal_sub_rts.Cong_def normal_sub_rts.Ide_implies_NPath normal_sub_rts_axioms)
      show "\<lbrakk>u \<in> \<NN>; R.sources t = R.sources u\<rbrakk> \<Longrightarrow> t \<approx> t \\ u"
      proof -
        assume u: "u \<in> \<NN>" and coinitial: "R.sources t = R.sources u"
        obtain a where a: "a \<in> R.targets u"
          by (meson elements_are_arr empty_subsetI R.arr_iff_has_target subsetI subset_antisym u)
        have 1: "t \\ u \<approx>\<^sub>0 (t \\ u) \\ a"
          by (metis (lifting) ext R.composite_of_arr_target a coinitial cong_implies_Cong\<^sub>0
              elements_are_arr forward_stable R.arr_resid_iff_con R.coinitialE R.coinitialI
              R.resid_composite_of(3) u)
        hence "t \<^sup>1\\\<^sup>* [u] \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* ([u] @ [a])"
          by auto
        moreover have "NPath [u]"
          using u NPath_def normal_sub_rts.elements_are_arr normal_sub_rts_axioms by force
        moreover have "NPath ([u] @ [a])"
          using u a
          by (metis Ide_implies_NPath NPath_append P.Arr_append_iff\<^sub>P P.Con_implies_Arr(2)
              P.Ide.simps(2) R.conE R.in_targetsE  calculation(1,2) elements_are_arr
              not_Cons_self R.null_is_zero(2) P.Resid1x_as_Resid' R.arr_resid_iff_con)
        ultimately show ?thesis
          by (metis 1 CongI NPath_def P.Arr.simps(2) P.Resid1x.simps(2) append.left_neutral
              append_Cons elements_are_arr insert_subset list.simps(15))
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
      obtain U U' where UU': "NPath U \<and> NPath U' \<and> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"
        using assms Cong_def by blast
      show "a \<approx> a'"
      proof
        show "NPath U"
          using UU' by simp
        show "NPath U'"
          using UU' by simp
        show "a \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 a' \<^sup>1\\\<^sup>* U'"
        proof -
          have "P.con [a] U" and "P.con [a'] U'"
            by (metis R.con_implies_arr(1-2) R.not_arr_null P.Con_single_ideI(1) UU'
                assms(2-3) Cong\<^sub>0_imp_con NPath_def P.Con_imp_eq_Srcs P.Resid1x_as_Resid'
                P.Srcs.simps(2) P.conI\<^sub>P R.in_sourcesE)+
          moreover have "a \<^sup>1\\\<^sup>* U \<in> P.Trgs U" and "a' \<^sup>1\\\<^sup>* U' \<in> P.Trgs U'"
            by (metis R.ideE R.in_sourcesI R.source_is_ide P.Resid1x_as_Resid
                P.residuation_axioms assms(2-3) calculation(1-2) P.Con_sym1 P.Resid1x_ide
                P.Residx1_as_Resid P.Srcs.simps(2) P.Srcs_Resid P.con_char residuation.con_sym)+
          moreover have "P.Trgs U = P.Trgs U'"
          proof -
            have "P.Trgs U = R.sources (t \<^sup>1\\\<^sup>* U)"
              by (metis P.Resid1x_as_Resid R.arr_resid_iff_con R.conE R.null_is_zero(2)
                  UU' elements_are_arr P.Resid1x_as_Resid' P.Srcs.simps(2)
                  P.Srcs_Resid_single_Arr)
            also have "... = R.sources (t' \<^sup>1\\\<^sup>* U')"
              using UU'
              by (simp add: Cong\<^sub>0_imp_coinitial)
            also have "... = P.Trgs U'"
              by (metis P.Resid1x_as_Resid R.arr_resid_iff_con R.conE R.null_is_zero(2)
                  UU' elements_are_arr P.Resid1x_as_Resid' P.Srcs.simps(2)
                  P.Srcs_Resid_single_Arr)
            finally show ?thesis by blast
          qed
          ultimately have "a \<^sup>1\\\<^sup>* U \<sim> a' \<^sup>1\\\<^sup>* U'"
            using R.targets_are_cong
            by (metis R.in_sourcesE R.not_con_null(1) R.resid_ide_arr P.Resid1x_ide
                P.Trgs_are_con assms(2,3))
          thus ?thesis
            using ide_closed by blast
        qed
      qed
    qed

    lemma in_targets_respects_Cong:
    assumes "t \<approx> t'" and "b \<in> R.targets t" and "b' \<in> R.targets t'"
    shows "b \<approx> b'"
    proof -
      obtain U U' where UU': "NPath U \<and> NPath U' \<and> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"
        using assms Cong_def by blast

      have seq: "P.seq (U \<^sup>*\\\<^sup>* [t]) (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) \<and>
                 P.seq (U' \<^sup>*\\\<^sup>* [t']) (([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* U'))"
      proof
        show "P.seq (U \<^sup>*\\\<^sup>* [t]) (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
        proof
          show "P.Arr (U \<^sup>*\\\<^sup>* [t])"
            using UU' Cong\<^sub>0_imp_con P.con_implies_arr
            by (metis P.Con_imp_Arr_Resid P.Con_sym1 P.Residx1_as_Resid R.null_is_zero(2)
                elements_are_arr R.not_arr_null)
          show "P.Arr (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            by (metis P.Arr.simps(2) P.Resid1x_as_Resid P.Resid1x_as_Resid' R.not_con_null(2)
                UU' Cong\<^sub>0_imp_con elements_are_arr P.Resid.simps(3))
          show "P.Trgs (U \<^sup>*\\\<^sup>* [t]) \<inter> P.Srcs (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) \<noteq> {}"
            by (metis Int_absorb P.Arr.simps(1) P.Srcs_Resid P.Trgs_Resid_sym
                \<open>P.Arr (([t'] \<^sup>*\\<^sup>* U') \<^sup>*\\<^sup>* ([t] \<^sup>*\\<^sup>* U))\<close> \<open>P.Arr (U \<^sup>*\\<^sup>* [t])\<close> P.Arr_has_Trg)
        qed
        show "P.seq (U' \<^sup>*\\\<^sup>* [t']) (([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* U'))"
          by (metis P.arr_resid_iff_con P.conI P.con_sym_ax P.seqE\<^sub>C\<^sub>S P.seqI(2)
              P.sources_resid P.targets_resid_sym
              \<open>P.seq (U \<^sup>*\\<^sup>* [t]) (([t'] \<^sup>*\\<^sup>* U') \<^sup>*\\<^sup>* ([t] \<^sup>*\\<^sup>* U))\<close>)
      qed
      let ?V = "(U \<^sup>*\\\<^sup>* [t]) @ (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
      let ?V' = "(U' \<^sup>*\\\<^sup>* [t']) @ (([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* U'))"
      show "b \<approx> b'"
      proof
        show NPath_V: "NPath ?V"
        proof
          show "NPath (U \<^sup>*\\\<^sup>* [t])"
            by (meson NPath_Resid P.arr_resid_iff_con P.coinitial_char(1)
                P.seq_def UU' P.con_imp_coinitial seq)
          show "NPath (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            by (metis NPath_def P.Arr.simps(1) P.Resid.simps(1,3) P.Resid1x_as_Resid
                P.seq_char UU' bot.extremum empty_set insert_subset list.simps(15) seq)
          show "P.Trgs (U \<^sup>*\\\<^sup>* [t]) \<subseteq> P.Srcs (([t'] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            using P.seq_char seq by blast
        qed
        show NPath_V': "NPath ?V'"
        proof
          show "NPath (U' \<^sup>*\\\<^sup>* [t'])"
            by (meson NPath_Resid P.arr_resid_iff_con P.coinitial_char(1)
                P.seq_def UU' P.con_imp_coinitial seq)
          show "NPath (([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* U'))"
            by (metis NPath_def P.Arr.simps(1) P.Resid.simps(1,3) P.Resid1x_as_Resid
                P.seq_char UU' bot.extremum empty_set insert_subset list.simps(15) seq)
          show "P.Trgs (U' \<^sup>*\\\<^sup>* [t']) \<subseteq> P.Srcs (([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* U'))"
            using P.seq_char seq by blast
        qed
        show "b \<^sup>1\\\<^sup>* ?V \<approx>\<^sub>0 b' \<^sup>1\\\<^sup>* ?V'"
        proof -
          have 1: "[b] \<^sup>*\\\<^sup>* ?V \<in> P.targets ?V"
            by (metis NPath_V P.Con_single_ideI(2) P.Ide.simps(2) P.Srcs_append
                P.ide_char P.in_sourcesI P.resid_source_in_targets P.seqE\<^sub>C\<^sub>S assms(2)
                NPath_implies_Arr P.Srcs_Resid_Arr_single P.con_char P.arr_resid_iff_con
                R.target_is_ide seq)
          have 2: "[b'] \<^sup>*\\\<^sup>* ?V' \<in> P.targets ?V'"
            by (metis NPath_V' R.target_is_ide P.Con_single_ideI(2) P.Ide.simps(2)
                P.Srcs_append P.Trgs.simps(2) P.ide_char P.in_sourcesI
                P.resid_source_in_targets  P.seqE\<^sub>C\<^sub>S assms(3) NPath_implies_Arr
                P.Srcs_Resid P.con_char P.arr_resid_iff_con seq)
          have 3: "P.targets ?V = P.targets ?V'"
            by (metis P.conI\<^sub>P P.targets_append P.targets_resid_sym seq)
          have "b \<^sup>1\\\<^sup>* ?V \<sim> b' \<^sup>1\\\<^sup>* ?V'"
            using 1 2 3 P.Resid1x_as_Resid [of b ?V] P.Resid1x_as_Resid [of b' ?V']
            by (metis (full_types) 1 2 R.conE R.in_targetsE R.resid_ide_arr
                P.Con_rec(1) P.Resid1x_ide P.in_targetsE P.not_ide_null P.null_char
                assms(2,3) R.null_is_zero(2) P.targets_are_cong)
          thus ?thesis
            using ide_closed by blast
        qed
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

    lemma Cong'_arr_resid_NPath:
    assumes "NPath U"
    shows "\<lbrakk>R.arr t; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> Cong' t (t \<^sup>1\\\<^sup>* U)"
    proof (induct U arbitrary: t rule: NPath_induct)
      show "NPath U" by fact
      show "\<And>t u. \<lbrakk>u \<in> \<NN>; R.arr t; R.sources t = P.Srcs [u]\<rbrakk> \<Longrightarrow> Cong' t (t \<^sup>1\\\<^sup>* [u])"
        by (simp add: Cong'.intros(4))
      show "\<And>t u U. \<lbrakk>u \<in> \<NN>; NPath U; R.targets u \<subseteq> P.Srcs U;
                     \<And>t. \<lbrakk>R.arr t; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> Cong' t (t \<^sup>1\\\<^sup>* U);
                     R.arr t; R.sources t = P.Srcs (u # U)\<rbrakk>
                       \<Longrightarrow> Cong' t (t \<^sup>1\\\<^sup>* (u # U))"
      proof -
        fix t u U
        assume u: "u \<in> \<NN>" and U: "NPath U" and uU: "R.targets u \<subseteq> P.Srcs U"
        assume t: "R.arr t" and tuU: "R.sources t = P.Srcs (u # U)"
        assume ind: "\<And>t. \<lbrakk>R.arr t; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> Cong' t (t \<^sup>1\\\<^sup>* U)"
        show "Cong' t (t \<^sup>1\\\<^sup>* (u # U))"
        proof -
          have "Cong' t (t \\ u)"
            by (metis Cong'.intros(4) P.Srcs.simps(2,3) list.exhaust t tuU u)
          moreover have "Cong' (t \\ u) ((t \\ u) \<^sup>1\\\<^sup>* U)"
            by (metis NPath_implies_Arr R.sources_resid P.Arr.simps(2) P.Arr_consI\<^sub>P
                P.Srcs_simp\<^sub>P P.Trgs.simps(2) P.seq_implies_Trgs_eq_Srcs U elements_are_arr
                ind list.sel(1) resid_along_normal_preserves_reflects_con R.arrI
                R.arr_resid_iff_con R.con_arr_self t tuU u uU)
          moreover have "(t \\ u) \<^sup>1\\\<^sup>* U = t \<^sup>1\\\<^sup>* (u # U)"
            by (metis NPath_def P.Arr.simps(1) P.Resid1x.simps(3) U neq_Nil_conv)
          ultimately show ?thesis
            by (metis Cong'.intros(2))
        qed
      qed
    qed

    lemma Cong'_if:
    shows "\<lbrakk>NPath U; NPath U'; t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'\<rbrakk> \<Longrightarrow> Cong' t t'"
    proof -
      assume u: "NPath U" and u': "NPath U'" and 1: "t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"
      have "Cong' t (t \<^sup>1\\\<^sup>* U)"
        by (metis "1" CongI Cong\<^sub>0_imp_con R.conE R.null_is_zero(2) P.Con_imp_eq_Srcs
            P.Resid1x_as_Resid' P.Srcs.simps(2) Cong'_arr_resid_NPath Cong_imp_arr(1) u u')
      moreover have "Cong' (t \<^sup>1\\\<^sup>* U) (t' \<^sup>1\\\<^sup>* U')"
        using "1" Cong'.intros(3) by blast
      moreover have "Cong' (t' \<^sup>1\\\<^sup>* U') t'"
        by (metis "1" Cong'_arr_resid_NPath CongI Cong\<^sub>0_imp_con R.conE R.null_is_zero(2)
            P.Con_imp_eq_Srcs P.Resid1x_as_Resid' P.Srcs.simps(2) Cong'.intros(1)
            Cong_imp_arr(2) u u')
      ultimately show ?thesis
        using Cong'.intros(2) by blast
    qed

    lemma Cong_char:
    shows "Cong t t' \<longleftrightarrow> Cong' t t'"
    proof -
      have "Cong t t' \<Longrightarrow> Cong' t t'"
        using Cong_def Cong'_if by blast
      moreover have "Cong' t t' \<Longrightarrow> Cong t t'"
        apply (induction rule: Cong'.induct)
        using Cong_closure_props(3-4) Cong_def
           apply auto
        by (metis (full_types) Cong_transitive)
      ultimately show ?thesis
        using Cong_def by blast
    qed

    lemma Cong_arr_resid_NPath:
    assumes "NPath U"
    shows "\<lbrakk>R.arr t; R.sources t = P.Srcs U\<rbrakk> \<Longrightarrow> Cong t (t \<^sup>1\\\<^sup>* U)"
      using assms Cong_char Cong'_arr_resid_NPath by presburger

    lemma normal_is_Cong_closed:
    assumes "t \<in> \<NN>" and "t \<approx> t'"
    shows "t' \<in> \<NN>"
    proof -
      obtain U U' where UU': "NPath U \<and> NPath U' \<and> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* U'"
        using assms Cong_def by blast
      have "NPath ([t] \<^sup>*\\\<^sup>* U)"
        by (metis Cong\<^sub>0_imp_con NPath_Resid_single_Arr NPath_implies_Arr
            P.Con_imp_eq_Srcs P.Srcs.simps(2) UU' assms(1) R.null_is_zero(2)
            P.Resid1x_as_Resid' R.conE)
      hence "NPath [t \<^sup>1\\\<^sup>* U]"
        by (metis NPath_def P.Arr.simps(1) P.Resid1x_as_Resid)
      hence "NPath [t' \<^sup>1\\\<^sup>* U']"
        by (metis NPath_def P.Arr.simps(2) R.con_implies_arr(2) UU' backward_stable
            insert_subset list.simps(15) Cong\<^sub>0_imp_con)
      hence "NPath ([t'] \<^sup>*\\\<^sup>* U')"
        by (metis NPath_def P.Arr.simps(2) P.Resid1x_as_Resid P.Resid1x_as_Resid'
            R.not_arr_null)
      hence "NPath [t']"
        using Backward_stable UU' by blast
      thus ?thesis
        by (simp add: NPath_def)
    qed

    lemma composite_of_normal_arr:
    shows "\<lbrakk> u \<in> \<NN>; R.composite_of u t t' \<rbrakk> \<Longrightarrow> t' \<approx> t"
      by (meson Cong'.intros(3) Cong_char R.composite_of_def R.con_implies_arr(2)
                ide_closed R.prfx_implies_con Cong_closure_props(2,4) R.sources_composite_of)

    lemma composite_of_arr_normal:
    shows "\<lbrakk> u \<in> \<NN>; R.composite_of t u t' \<rbrakk> \<Longrightarrow> t' \<approx>\<^sub>0 t"
      by (meson Cong_closure_props(3) R.composite_of_def ide_closed prfx_closed)

  end

  context normal_sub_rts
  begin

    interpretation NP: normal_sub_rts P.Resid \<open>Collect NPath\<close>
      using normal_extends_to_paths by blast

    notation NP.Cong\<^sub>0  (infix \<open>\<approx>\<^sup>*\<^sub>0\<close> 50)
    notation NP.Cong   (infix \<open>\<approx>\<^sup>*\<close> 50)

    lemma NP_Cong\<^sub>0_char:
    shows "T \<approx>\<^sup>*\<^sub>0 T' \<longleftrightarrow> NPath (T \<^sup>*\\\<^sup>* T') \<and> NPath (T' \<^sup>*\\\<^sup>* T)"
      by blast

    lemma NP_Cong_char:
    shows "T \<approx>\<^sup>* T' \<longleftrightarrow> (\<exists>U U'. NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U')"
    proof
      show "\<exists>U U'. NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U' \<Longrightarrow> T \<approx>\<^sup>* T'"
      proof -
        assume 1: "\<exists>U U'. NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U'"
        obtain U U' where UU': "NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U'"
          using 1 by blast
        show "T \<approx>\<^sup>* T'"
          apply (intro NP.CongI [of "[U]" "[U']"])
            apply (auto simp add: NP.NPath_def NP.elements_are_arr UU')
          using UU' by auto
      qed
      show "T \<approx>\<^sup>* T' \<Longrightarrow> \<exists>U U'. NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U'"
        using NP_Resid1x_eq
        by (metis NP.CongE NP_NPath_imp P.Arr.simps(1) P.Con_implies_Arr(2) mem_Collect_eq)
    qed

    theorem extends_to_paths:
    shows "normal_sub_rts P.Resid (Collect NPath)"
      ..

    lemma Cong\<^sub>0_append_Arr_NPath:
    assumes "T \<noteq> []" and "P.Arr (T @ U)" and "NPath U"
    shows "NP.Cong\<^sub>0 (T @ U) T"
      using assms
      by (metis NP.composite_of_arr_normal NPath_def P.Arr.simps(1) P.append_is_composite_of
          P.arr_char P.paths_in_rts_axioms mem_Collect_eq paths_in_rts.arr_append_imp_seq)

    lemma Cong_append_NPath_Arr:
    assumes "T \<noteq> []" and "P.Arr (U @ T)" and "NPath U"
    shows "U @ T \<approx>\<^sup>* T"
      using assms
      by (metis NP.composite_of_normal_arr NP.elements_are_arr P.Arr.simps(1)
          P.append_is_composite_of P.arr_append_imp_seq P.arr_char mem_Collect_eq)

    (*
     * TODO: Leave these for now -- they still seem a little difficult to prove
     * in this context, but are probably useful.
     *)
    lemma Cong\<^sub>0_cancel_left\<^sub>C\<^sub>S:
    assumes "T @ U \<approx>\<^sup>*\<^sub>0 T @ U'" and "T \<noteq> []" and "U \<noteq> []" and "U' \<noteq> []"
    shows "U \<approx>\<^sup>*\<^sub>0 U'"
      using assms NP.Cong\<^sub>0_cancel_left [of T U "T @ U" U' "T @ U'"] NP.Cong\<^sub>0_reflexive
            P.append_is_composite_of
      by (metis NP.Cong\<^sub>0_implies_Cong NP.Cong_imp_arr(1) P.arr_append_imp_seq)

    lemma Srcs_respects_Cong:
    assumes "T \<approx>\<^sup>* T'" and "a \<in> P.Srcs T" and "a' \<in> P.Srcs T'"
    shows "[a] \<approx>\<^sup>* [a']"
    proof -
      obtain U U' where UU': "NPath U \<and> NPath U' \<and> T \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 T' \<^sup>*\\\<^sup>* U'"
        using assms(1) NP_Cong_char by blast
      have "[a] \<^sup>*\\\<^sup>* U \<approx>\<^sup>*\<^sub>0 [a'] \<^sup>*\\\<^sup>* U'"
      proof -
        have "NPath ([a] \<^sup>*\\\<^sup>* U) \<and> NPath ([a'] \<^sup>*\\\<^sup>* U')"
          by (metis NPath_Resid_single_Arr NPath_implies_Arr NP.elements_are_arr
              R.in_sourcesE P.Con_imp_eq_Srcs P.Resid.simps(1) P.Srcs.simps(2)
              P.not_arr_null P.null_char UU' assms(2,3) ide_closed P.Resid_Arr_Src)
        thus ?thesis
          using UU'
          by (metis (full_types) P.Arr.simps(1) P.paths_in_rts_axioms mem_Collect_eq
              NPath_Resid NPath_def P.Con_imp_eq_Srcs P.Con_implies_Arr(2)
              paths_in_rts.Srcs_Resid)
      qed
      thus ?thesis
        using NP_Cong_char
        by (meson UU')
    qed

    lemma Trgs_respects_Cong:
    assumes "T \<approx>\<^sup>* T'" and "b \<in> P.Trgs T" and "b' \<in> P.Trgs T'"
    shows "[b] \<approx>\<^sup>* [b']"
    proof -
      have "[b] \<in> P.targets T \<and> [b'] \<in> P.targets T'"
      proof -
        have 1: "P.Ide [b] \<and> P.Ide [b']"
          using assms
          by (metis Ball_Collect P.Trgs_are_ide P.Ide.simps(2))
        moreover have "P.Srcs [b] = P.Trgs T"
          using assms
          by (metis NP.Cong_imp_arr(1) P.Resid_Arr_Src P.Con_Arr_self P.Con_imp_Arr_Resid
              P.Con_imp_eq_Srcs P.Srcs_Resid P.arr_char)
        moreover have "P.Srcs [b'] = P.Trgs T'"
          using assms
          by (metis NP.Cong_imp_arr(2) P.Arr_iff_Con_self P.Con_imp_eq_Srcs P.Ide_implies_Arr
              P.Resid_Arr_Src P.Resid_Arr_self P.Srcs_Resid P.arr_char)
        ultimately show ?thesis
          unfolding P.targets_char\<^sub>P
          using assms NP.Cong_imp_arr(2) P.arr_char by blast
      qed
      thus ?thesis
        using assms P.targets_char
        by (meson NP.in_targets_respects_Cong)
    qed

    (* TODO: Where is this used? *)
    lemma Cong\<^sub>0_append_resid_NPath:
    assumes "NPath (T \<^sup>*\\\<^sup>* U)"
    shows "NP.Cong\<^sub>0 (T @ (U \<^sup>*\\\<^sup>* T)) U"
    proof (intro conjI)
      show 0: "(T @ (U \<^sup>*\\\<^sup>* T)) \<^sup>*\\\<^sup>* U \<in> Collect NPath"
      proof -
        have 1: "(T @ (U \<^sup>*\\\<^sup>* T)) \<^sup>*\\\<^sup>* U = (T \<^sup>*\\\<^sup>* U) @ ((U \<^sup>*\\\<^sup>* T) \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* T))"
          by (metis P.Arr.simps(1) P.Con_Arr_self P.Con_appendI(1) P.Con_imp_Arr_Resid
              assms NPath_implies_Arr P.Con_implies_Arr(2) P.Con_sym P.Resid_append(1))
        moreover have "NPath ..."
          using assms
          by (metis Ide_implies_NPath NPath_appendI P.Arr_iff_Con_self P.Resid_Arr_self
              P.Srcs_Resid P.Trgs_Resid_sym append_self_conv subset_refl)
        ultimately show ?thesis by simp
      qed
      show "U \<^sup>*\\\<^sup>* (T @ (U \<^sup>*\\\<^sup>* T)) \<in> Collect NPath"
        using assms 0
        by (metis NP.ide_closed P.arr_resid P.conE P.con_char P.con_sym_ax P.null_is_zero(2)
            P.prfx_reflexive append.right_neutral P.Resid_append(2))
    qed

  end

  subsection "Congruence Classes"

  text \<open>
    Here we develop some notions relating to the congruence classes of \<open>\<approx>\<close>.
  \<close>

  context normal_sub_rts
  begin

    definition Cong_class (\<open>\<lbrace>_\<rbrace>\<close>)
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
      using assms Cong_class_def Cong_class_is_nonempty Cong_class_membs_are_Cong
      by (metis Cong_class_eqI Cong_imp_arr(1) is_Cong_class_def arr_in_Cong_class)

    lemma Cong_class_rep [simp]:
    assumes "is_Cong_class \<T>"
    shows "\<lbrace>Cong_class_rep \<T>\<rbrace> = \<T>"
      by (metis Cong_class_membs_are_Cong Cong_class_eqI assms is_Cong_class_def
          rep_in_Cong_class)

    lemma Cong_class_memb_Cong_rep:
    assumes "is_Cong_class \<T>" and "t \<in> \<T>"
    shows "Cong t (Cong_class_rep \<T>)"
      using assms Cong_class_membs_are_Cong rep_in_Cong_class by simp

  end

  subsection "Coherent Normal Sub-RTS's"

  text \<open>
    A \emph{coherent} normal sub-RTS is one that satisfies a parallel moves property with respect
    to arbitrary normal paths.  The congruence \<open>\<approx>\<close> induced by a coherent normal sub-RTS is
    fully substitutive with respect to consistency and residuation,
    and in fact coherence is equivalent to substitutivity in this context.
  \<close>

  locale coherent_normal_sub_rts = normal_sub_rts +
    assumes coherent: "\<lbrakk> R.arr t; NPath U; NPath U'; P.Srcs U = P.Srcs U';
                         P.Trgs U = P.Trgs U'; R.sources t = P.Srcs U \<rbrakk>
                            \<Longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* U'"

  context normal_sub_rts
  begin

    text \<open>
      The above ``parallel moves'' formulation of coherence is equivalent to the following
      formulation, which involves ``opposing spans''.
    \<close>

    lemma coherent_iff:
    shows "(\<forall>t U U'. R.arr t \<and> NPath U \<and> NPath U' \<and> R.sources t = P.Srcs U \<and>
                     P.Srcs U = P.Srcs U' \<and> P.Trgs U = P.Trgs U'
                            \<longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* U')
           \<longleftrightarrow>
           (\<forall>t t' V V' W W'. NPath V \<and> NPath V' \<and> NPath W \<and> NPath W' \<and>
                             P.Srcs V = P.Srcs W \<and> P.Srcs V' = P.Srcs W' \<and>
                             P.Trgs W = P.Trgs W' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'
                                \<longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W')"
    proof
      assume 1: "\<forall>t t' V V' W W'. NPath V \<and> NPath V' \<and> NPath W \<and> NPath W' \<and>
                                  P.Srcs V = P.Srcs W \<and> P.Srcs V' = P.Srcs W' \<and>
                                  P.Trgs W = P.Trgs W' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'
                                     \<longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
      show "\<forall>t U U'. R.arr t \<and> NPath U \<and> NPath U' \<and> R.sources t = P.Srcs U \<and>
                     P.Srcs U = P.Srcs U' \<and> P.Trgs U = P.Trgs U'
                            \<longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* U'"
      proof (intro allI impI, elim conjE)
        fix t U U'
        assume t: "R.arr t" and U: "NPath U" and U': "NPath U'"
        and tU: "R.sources t = P.Srcs U" and sources: "P.Srcs U = P.Srcs U'"
        and targets: "P.Trgs U = P.Trgs U'"
        show "t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* U'"
          using t U U' tU 1 sources targets Cong\<^sub>0_reflexive Resid_along_NPath_preserves_Cong\<^sub>0
          by metis
      qed
      next
      assume 1: "\<forall>t U U'. R.arr t \<and> NPath U \<and> NPath U' \<and> R.sources t = P.Srcs U \<and>
                          P.Srcs U = P.Srcs U' \<and> P.Trgs U = P.Trgs U'
                             \<longrightarrow> t \<^sup>1\\\<^sup>* U \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* U'"
      show "\<forall>t t' V V' W W'. NPath V \<and> NPath V' \<and> NPath W \<and> NPath W' \<and>
                             P.Srcs V = P.Srcs W \<and> P.Srcs V' = P.Srcs W' \<and>
                             P.Trgs W = P.Trgs W' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'
                                \<longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
      proof (intro allI impI, elim conjE)
        fix t t' V V' W W'
        assume V: "NPath V" and V': "NPath V'" and W: "NPath W" and W': "NPath W'"
        and VW: "P.Srcs V = P.Srcs W" and V'W': "P.Srcs V' = P.Srcs W'"
        and WW': "P.Trgs W = P.Trgs W'"
        and tt'VV': "(t \<^sup>1\\\<^sup>* V) \\ (t' \<^sup>1\\\<^sup>* V') \<in> \<NN>" and t'tV'V:"(t' \<^sup>1\\\<^sup>* V') \\ (t \<^sup>1\\\<^sup>* V) \<in> \<NN>"
        show "t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
        proof -
          have 3: "R.sources t = P.Srcs V \<and> R.sources t' = P.Srcs V'"
            using R.con_imp_coinitial
            by (metis R.ex_un_null R.not_arr_null P.Con_imp_eq_Srcs P.Con_sym1
                P.Resid1x.simps(2) P.Resid1x_null P.Residx1_as_Resid P.Srcs.simps(2)
                elements_are_arr t'tV'V)
          have 2: "t \<^sup>1\\\<^sup>* W \<approx> t' \<^sup>1\\\<^sup>* W'"
            using V V' W W' VW V'W' WW' tt'VV' t'tV'V 3 Cong_arr_resid_NPath
            by (metis Cong_closure_props(2) Cong_imp_arr(1) Cong_symmetric
                normal_sub_rts.CongI normal_sub_rts_axioms)
          obtain Z Z' where ZZ': "NPath Z \<and> NPath Z' \<and> (t \<^sup>1\\\<^sup>* W) \<^sup>1\\\<^sup>* Z \<approx>\<^sub>0 (t' \<^sup>1\\\<^sup>* W') \<^sup>1\\\<^sup>* Z'"
            using 2 by auto
          have "(t \<^sup>1\\\<^sup>* W) \<^sup>1\\\<^sup>* Z \<approx>\<^sub>0 (t \<^sup>1\\\<^sup>* W) \<^sup>1\\\<^sup>* Z'"
          proof -
            have "R.arr (t \<^sup>1\\\<^sup>* W)"
              using "2" Cong_imp_arr(1) by blast
            moreover have "R.sources (t \<^sup>1\\\<^sup>* W) = P.Srcs Z"
              by (metis R.null_is_zero(2) P.Con_imp_eq_Srcs P.Con_sym1 P.Residx1_as_Resid
                  P.Srcs.simps(2) ZZ' elements_are_arr R.not_arr_null)
            moreover have "P.Srcs Z = P.Srcs Z'"
              by (metis R.null_is_zero(2) R.residuation_axioms P.Con_imp_eq_Srcs
                  P.Resid1x_as_Resid' P.Resid1x_null P.Srcs_Resid ZZ' elements_are_arr
                  P.Resid1x_as_Resid residuation.not_arr_null WW')
            moreover have "P.Trgs Z = P.Trgs Z'"
              by (metis R.null_is_zero(2) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                  P.Srcs.simps(2) P.Srcs_Resid_single_Arr ZZ' elements_are_arr
                  R.not_arr_null Cong\<^sub>0_imp_coinitial)
            ultimately show ?thesis
              using ZZ' 1 by blast
          qed
          hence "(t \<^sup>1\\\<^sup>* W) \<^sup>1\\\<^sup>* Z' \<approx>\<^sub>0 (t' \<^sup>1\\\<^sup>* W') \<^sup>1\\\<^sup>* Z'"
            using ZZ' Cong\<^sub>0_transitive Cong\<^sub>0_symmetric by blast
          thus ?thesis
            using ZZ' Resid_along_NPath_reflects_Cong\<^sub>0 by metis
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
    assumes "NPath V" and "NPath V'" and "NPath W" and "NPath W'"
    and "P.Srcs V = P.Srcs W" and "P.Srcs V' = P.Srcs W'"
    and "P.Trgs W = P.Trgs W'" and "t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'"
    shows "t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
    proof
      show "(t \<^sup>1\\\<^sup>* W) \\ (t' \<^sup>1\\\<^sup>* W') \<in> \<NN>"
        using assms coherent coherent_iff by meson
      show "(t' \<^sup>1\\\<^sup>* W') \\ (t \<^sup>1\\\<^sup>* W) \<in> \<NN>"
        using assms coherent coherent_iff by meson
    qed

    text \<open>
      The relation \<open>\<approx>\<close> is substitutive with respect to both arguments of residuation.
    \<close>

    lemma Cong_subst:
    assumes "t \<approx> t'" and "u \<approx> u'" and "t \<frown> u" and "R.sources t' = R.sources u'"
    shows "t' \<frown> u'" and "t \\ u \<approx> t' \\ u'"
    proof -
      obtain V V' where VV': "NPath V \<and> NPath V' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'"
        using assms by auto
      obtain W W' where WW': "NPath W \<and> NPath W' \<and> u \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 u' \<^sup>1\\\<^sup>* W'"
        using assms by auto
      let ?x = "t \<^sup>1\\\<^sup>* V" and ?x' = "t' \<^sup>1\\\<^sup>* V'"
      let ?y = "u \<^sup>1\\\<^sup>* W" and ?y' = "u' \<^sup>1\\\<^sup>* W'"
      have xx': "?x \<approx>\<^sub>0 ?x'"
        using assms VV' by blast
      have yy': "?y \<approx>\<^sub>0 ?y'"
        using assms WW' by blast
      have 1: "t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
      proof (intro coherent' [of V V' W W' t])
        show "NPath V" and "NPath V'" and "NPath W" and "NPath W'" and "t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'"
          using VV' WW' by auto
        show "P.Srcs V = P.Srcs W"
          using WW' xx'
          by (metis (no_types, lifting) ext R.coinitialE R.con_imp_coinitial
              R.null_is_zero(2) P.Con_imp_eq_Srcs P.Con_sym1 P.Residx1_as_Resid
              P.Srcs.simps(2) assms(3) elements_are_arr R.not_arr_null)
        show "P.Srcs V' = P.Srcs W'"
          using WW' xx'
          by (metis (full_types) R.null_is_zero(2) P.Con_imp_eq_Srcs P.Con_sym1
              P.Residx1_as_Resid P.Srcs.simps(2) assms(4) elements_are_arr R.not_arr_null)
        show "P.Trgs W = P.Trgs W'"
          using yy' R.conE R.partial_magma_axioms P.Resid1x_as_Resid
                P.Srcs_Resid_single_Arr Cong\<^sub>0_imp_con R.null_is_zero(2) P.Con_imp_eq_Srcs
                P.Con_rec(1) P.Resid1x_as_Resid'
          by (metis (no_types, lifting) ext)
      qed
      have 2: "t' \<^sup>1\\\<^sup>* W' \<frown> u' \<^sup>1\\\<^sup>* W'"
        using Resid_along_NPath_preserves_reflects_con
        by (metis "1" Cong\<^sub>0_imp_con Cong\<^sub>0_subst_Con P.Srcs.simps(2) R.not_con_null(1)
            WW' assms(3) P.Con_imp_eq_Srcs P.Resid1x_as_Resid')
      thus 3: "t' \<frown> u'"
        using WW' Resid_along_NPath_preserves_reflects_con
        by (metis P.Con_imp_eq_Srcs P.Resid1x_as_Resid' P.Srcs.simps(2) R.not_con_null(2)
            assms(4))
      have "t \\ u \<approx> ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ (?y' \\ ?y)"
      proof -
        have "t \\ u \<approx> (t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"
          by (metis (no_types, lifting) ext Cong_arr_resid_NPath Cong_imp_arr(1)
              R.arr_resid R.conE R.null_is_zero(2) P.Arr.simps(2) P.Con_imp_eq_Srcs
              P.Con_sym P.Srcs_Resid_Arr_single WW' assms(2,3) Cong\<^sub>0_imp_con NPath_Resid
              P.Resid1x_as_Resid' R.sources_resid)
        also have "... \<approx> ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ (?y' \\ ?y)"
        proof -
          have "R.sources ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) = R.sources ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))"
          proof -
            have "R.sources ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) = P.Trgs (W \<^sup>*\\\<^sup>* [u])"
              by (metis Cong_imp_arr(2) R.not_arr_null P.Con_sym P.Con_sym1
                  P.Resid1x_as_Resid P.Residx1_as_Resid P.Srcs.simps(2) P.Srcs_Resid
                  calculation)
            also have "... = R.targets (u \<^sup>1\\\<^sup>* W)"
              by (metis Cong_imp_arr(2) R.not_arr_null P.Con_sym P.Con_sym1
                  P.Resid.simps(1) P.Resid1x_as_Resid P.Residx1_as_Resid P.Trgs.simps(2)
                  P.Trgs_Resid_sym \<open>t \ u \<approx> (t \ u) \<^sup>1\\<^sup>* (W \<^sup>*\\<^sup>* [u])\<close>)
            also have "... = R.sources ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))"
              using R.arr_resid_iff_con R.sources_resid WW' elements_are_arr by blast
            finally show ?thesis by blast
          qed
          thus ?thesis
            using yy' Cong_closure_props(4) [of "?y' \\ ?y" "(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"]
            by blast
        qed
        finally show ?thesis by simp
      qed
      also have "... \<approx> (((t \<^sup>1\\\<^sup>* W) \\ ?y) \\ (?y' \\ ?y))"
      proof -
        have "[(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])] = [(t \<^sup>1\\\<^sup>* W) \\ ?y]"
        proof -
          have "[(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])] = ([t] \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"
            by (metis R.not_arr_null R.null_is_zero(1) P.Resid.simps(3)
                P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Resid1x_null assms(3)
                calculation Cong_def elements_are_arr)
          also have "... = ([t] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W)"
            using P.cube by blast
          also have "... = [(t \<^sup>1\\\<^sup>* W) \\ ?y]"
            by (metis P.Resid.simps(1) P.Resid1x.simps(2) P.Resid1x_as_Resid
                P.ex_un_null calculation not_Cons_self2)
          finally show ?thesis by blast
        qed
        thus ?thesis
          using Cong_imp_arr(2) Cong_reflexive calculation by force
      qed
      also have "... \<approx> (((t' \<^sup>1\\\<^sup>* W') \\ ?y) \\ (?y' \\ ?y))"
        using 1 Cong\<^sub>0_subst_left(2) [of "t \<^sup>1\\\<^sup>* W" "(t' \<^sup>1\\\<^sup>* W')" ?y]
              Cong\<^sub>0_subst_left(2) [of "(t \<^sup>1\\\<^sup>* W) \\ ?y" "(t' \<^sup>1\\\<^sup>* W') \\ ?y" "?y' \\ ?y"]
        by (meson Cong\<^sub>0_implies_Cong Cong_imp_arr(2) R.arr_resid_iff_con
            R.con_implies_arr(1) calculation)
      also have "... \<approx> ((t' \<^sup>1\\\<^sup>* W') \\ ?y') \\ (?y \\ ?y')"
        using 2 Cong\<^sub>0_implies_Cong Cong\<^sub>0_subst_right(2) WW' by presburger
      also have 4: "... \<approx> (t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
      proof -
        have "((t' \<^sup>1\\\<^sup>* W') \\ ?y') \\ (?y \\ ?y') \<approx> (t' \<^sup>1\\\<^sup>* W') \\ (u' \<^sup>1\\\<^sup>* W')"
          by (simp add: "2" Cong\<^sub>0_imp_con Cong_closure_props(4) Cong_symmetric WW')
        moreover have "... = (t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
        proof -
          have "[(t' \<^sup>1\\\<^sup>* W') \\ (u' \<^sup>1\\\<^sup>* W')] = [(t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])]"
          proof - 
            have "[(t' \<^sup>1\\\<^sup>* W') \\ (u' \<^sup>1\\\<^sup>* W')] = [t' \<^sup>1\\\<^sup>* W'] \<^sup>*\\\<^sup>* [u' \<^sup>1\\\<^sup>* W']"
              using "2" by auto
            also have "... = ([t'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W')"
              by (metis "2" R.not_con_null(1,2) P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                  P.Residx1_as_Resid)
            also have "... = ([t'] \<^sup>*\\\<^sup>* [u']) \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
              using P.cube by blast
            also have "... = [t' \\ u'] \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
              using "3" by auto
            also have "... = [(t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])]"
              using P.Resid1x_as_Resid calculation by force
            finally show ?thesis by blast
          qed
          thus ?thesis by blast
        qed
        ultimately show ?thesis by argo
      qed
      also have "... \<approx> t' \\ u'"
         using WW' 3 4
         by (metis (lifting) ext "2" Cong'.intros(1) Cong'_arr_resid_NPath Cong_char
             NPath_Resid_Arr_single R.con_implies_arr(1) R.con_sym R.not_con_null(2)
             R.sources_resid P.Con_imp_eq_Srcs P.Con_sym P.Resid1x_as_Resid'
             P.Srcs.simps(2) P.Srcs_Resid_Arr_single R.arr_resid_iff_con)
      finally show "t \\ u \<approx> t' \\ u'" by simp
    qed

    lemma Cong_subst_con:
    assumes "R.sources t = R.sources u" and "R.sources t' = R.sources u'"
    and "t \<approx> t'" and "u \<approx> u'"
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
           (\<forall>t t' V V' W W'. NPath V \<and> NPath V' \<and> NPath W \<and> NPath W' \<and>
                             P.Srcs V = P.Srcs W \<and> P.Srcs V' = P.Srcs W' \<and>
                             P.Trgs W = P.Trgs W' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'
                                \<longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W')"
    proof
      assume 1: "\<forall>t t' u u'. t \<approx> t' \<and> u \<approx> u' \<and> t \<frown> u \<and> R.sources t' = R.sources u'
                               \<longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u'"
      show "\<forall>t t' V V' W W'. NPath V \<and> NPath V' \<and> NPath W \<and> NPath W' \<and>
                             P.Srcs V = P.Srcs W \<and> P.Srcs V' = P.Srcs W' \<and>
                             P.Trgs W = P.Trgs W' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'
                                \<longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
      proof (intro allI impI, elim conjE)
        fix t t' V V' W W'
        assume v: "NPath V" and v': "NPath V'" and w: "NPath W" and w': "NPath W'"
        and VW: "P.Srcs V = P.Srcs W"
        and V'W': "P.Srcs V' = P.Srcs W'"
        and WW': "P.Trgs W = P.Trgs W'"
        and tt': "(t \<^sup>1\\\<^sup>* V) \\ (t' \<^sup>1\\\<^sup>* V') \<in> \<NN>" and t't: "(t' \<^sup>1\\\<^sup>* V') \\ (t \<^sup>1\\\<^sup>* V) \<in> \<NN>"
        show "t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
        proof -
          have 2: "\<And>t t' u u'. \<lbrakk>t \<approx> t'; u \<approx> u'; t \<frown> u; R.sources t' = R.sources u'\<rbrakk>
                                   \<Longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u'"
            using 1 by blast
          have 3: "t \<^sup>1\\\<^sup>* W \<approx> t \<^sup>1\\\<^sup>* V \<and> t' \<^sup>1\\\<^sup>* W' \<approx> t' \<^sup>1\\\<^sup>* V'"
          proof
            show "t \<^sup>1\\\<^sup>* W \<approx> t \<^sup>1\\\<^sup>* V"
              by (metis CongI Cong_arr_resid_NPath Cong_imp_arr(2) Cong_symmetric
                  Cong_transitive R.arr_def R.conE R.null_is_zero(2) P.Con_imp_eq_Srcs
                  P.Resid1x_as_Resid' P.Srcs.simps(2) elements_are_arr VW t't tt' v v' w)
            show "t' \<^sup>1\\\<^sup>* W' \<approx> t' \<^sup>1\\\<^sup>* V'"
              by (metis CongI Cong_arr_resid_NPath Cong_imp_arr(2) Cong_symmetric
                  Cong_transitive R.not_arr_null R.null_is_zero(2) P.Con_imp_eq_Srcs
                  P.Resid1x_as_Resid' P.Srcs.simps(2) elements_are_arr V'W' t't tt' v v' w')
          qed
          have 4: "R.sources (t \<^sup>1\\\<^sup>* W) = R.sources (t' \<^sup>1\\\<^sup>* W')"
          proof -
            have "R.sources (t \<^sup>1\\\<^sup>* W) = P.Trgs W"
              by (metis "3" P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Srcs.simps(2)
                  P.Srcs_Resid R.arr_def R.null_is_zero(2) Cong_imp_arr(1) R.conE)
            also have "... = P.Trgs W'"
              using WW' by blast
            also have "... = R.sources (t' \<^sup>1\\\<^sup>* W')"
              by (metis "3" Cong_imp_arr(1) P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                  P.Residx1_as_Resid P.Srcs.simps(2) P.Srcs_Resid R.arr_def
                  R.not_con_null(1))
            finally show ?thesis by blast
          qed
          have "(t \<^sup>1\\\<^sup>* W) \\ (t' \<^sup>1\\\<^sup>* W') \<approx> (t \<^sup>1\\\<^sup>* V) \\ (t' \<^sup>1\\\<^sup>* V')"
            using 2 [of "t \<^sup>1\\\<^sup>* V" "t \<^sup>1\\\<^sup>* W" "t' \<^sup>1\\\<^sup>* V'" "t' \<^sup>1\\\<^sup>* W'"] 3 4
            by (metis Cong\<^sub>0_imp_con Cong_symmetric R.conI R.con_sym t't)
          moreover have "(t' \<^sup>1\\\<^sup>* W') \\ (t \<^sup>1\\\<^sup>* W) \<approx> (t' \<^sup>1\\\<^sup>* V') \\ (t \<^sup>1\\\<^sup>* V)"
            using 2 [of "t' \<^sup>1\\\<^sup>* V'" "t' \<^sup>1\\\<^sup>* W'" "t \<^sup>1\\\<^sup>* V" "t \<^sup>1\\\<^sup>* W"] 3 4
            by (metis Cong\<^sub>0_imp_con Cong_symmetric R.conI R.con_sym t't)
          ultimately show ?thesis
            by (meson tt' t't normal_is_Cong_closed Cong_symmetric)
        qed
      qed
      next
      assume 0: "\<forall>t t' V V' W W'.
                   NPath V \<and> NPath V' \<and> NPath W \<and> NPath W' \<and>
                   P.Srcs V = P.Srcs W \<and> P.Srcs V' = P.Srcs W' \<and>
                   P.Trgs W = P.Trgs W' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'
                      \<longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
      show "\<forall>t t' u u'. t \<approx> t' \<and> u \<approx> u' \<and> t \<frown> u \<and> R.sources t' = R.sources u'
                           \<longrightarrow> t' \<frown> u' \<and> t \\ u \<approx> t' \\ u'"
      proof (intro allI impI, elim conjE, intro conjI)
        have *: "\<And>t t' V V' W W'.
                    \<lbrakk>NPath V; NPath V'; NPath W; NPath W';
                     P.Srcs V = P.Srcs W; P.Srcs V' = P.Srcs W'; P.Trgs W = P.Trgs W';
                     t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'\<rbrakk>
                        \<Longrightarrow> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
          using 0 by metis
        fix t t' u u'
        assume tt': "t \<approx> t'" and uu': "u \<approx> u'" and con: "t \<frown> u"
        and t'u': "R.sources t' = R.sources u'"
        obtain V V' where VV': "NPath V \<and> NPath V' \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'"
          using tt' by auto
        obtain W W' where WW': "NPath W \<and> NPath W' \<and> u \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 u' \<^sup>1\\\<^sup>* W'"
          using uu' by auto
        let ?x = "t \<^sup>1\\\<^sup>* V" and ?x' = "t' \<^sup>1\\\<^sup>* V'"
        let ?y = "u \<^sup>1\\\<^sup>* W" and ?y' = "u' \<^sup>1\\\<^sup>* W'"
        have XX': "?x \<approx>\<^sub>0 ?x'"
          using tt' VV' by blast
        have yy': "?y \<approx>\<^sub>0 ?y'"
          using uu' WW' by blast
        have 1: "t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
        proof (intro * [of V V' W W' t t'])
          show "NPath V" and "NPath V'" and "NPath W" and "NPath W'" and "t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* V'"
            using VV' WW' by auto
          show "P.Srcs V' = P.Srcs W'"
            using t'u' VV' WW'
            by (metis Cong\<^sub>0_imp_con R.not_con_null(1) P.Con_imp_eq_Srcs P.Resid1x_as_Resid'
                P.Srcs.simps(2))
          show "P.Srcs V = P.Srcs W"
            using VV' WW'
            by (metis (no_types, lifting) ext R.coinitial_iff R.con_imp_coinitial
                R.null_is_zero(2) P.Con_imp_eq_Srcs P.Con_sym1 P.Residx1_as_Resid
                P.Srcs.simps(2) con elements_are_arr R.not_arr_null)
          show "P.Trgs W = P.Trgs W'"
          proof -
            have "P.Trgs W = R.sources (u \<^sup>1\\\<^sup>* W)"
              by (metis Cong\<^sub>0_imp_con R.not_con_null(1) P.Con_sym P.Con_sym1
                  P.Resid1x_as_Resid P.Residx1_as_Resid P.Srcs.simps(2) P.Srcs_Resid WW')
            also have "... = R.sources (u' \<^sup>1\\\<^sup>* W')"
              by (simp add: Cong\<^sub>0_imp_coinitial yy')
            also have "... = P.Trgs W'"
              by (metis NPath_def R.arr_def R.arr_iff_has_source R.con_def R.null_is_zero(2)
                  P.Arr_has_Trg P.Resid1x_as_Resid P.Srcs.simps(2) WW' calculation
                  P.Resid1x_as_Resid' P.Srcs_Resid)
            finally show ?thesis by blast
          qed
        qed
        have 2: "t' \<^sup>1\\\<^sup>* W' \<frown> u' \<^sup>1\\\<^sup>* W'"
          using 1 yy' con WW'
                Cong\<^sub>0_subst_Con [of "t' \<^sup>1\\\<^sup>* W'" "t \<^sup>1\\\<^sup>* W" "u' \<^sup>1\\\<^sup>* W'" "u \<^sup>1\\\<^sup>* W"]
                Resid_along_NPath_preserves_reflects_con [of W t u]
          by (metis P.Con_imp_eq_Srcs P.Resid1x_as_Resid' P.Srcs.simps(2) R.con_sym_ax
              R.null_is_zero(2) Cong\<^sub>0_imp_con)
        thus 3: "t' \<frown> u'"
          using WW' Resid_along_NPath_preserves_reflects_con [of W' t' u']
          by (metis P.Con_imp_eq_Srcs P.Resid1x_as_Resid' P.Srcs.simps(2) R.conE
              R.ex_un_null R.null_is_zero(2))
        have "t \\ u \<approx> (t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"
          using Cong_arr_resid_NPath [of "W \<^sup>*\\\<^sup>* [u]" "t \\ u"]
          by (metis NPath_Resid P.Arr.simps(2) P.Con_imp_eq_Srcs P.Con_sym P.Resid1x_as_Resid'
              P.Srcs_Resid_Arr_single R.conE R.null_is_zero(2) WW' con Cong\<^sub>0_imp_con
              R.arr_resid R.con_implies_arr(2) R.sources_resid)
        also have "(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u]) \<approx> ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ (?y' \\ ?y)"
        proof -
          have "R.sources ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) = R.sources ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))"
          proof -
            have "R.sources ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) = P.Srcs (([t] \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u]))"
              by (metis R.arr_iff_has_source R.not_arr_null P.Resid.simps(3)
                  P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Srcs.simps(1,2) con)
            also have "... = P.Trgs (W \<^sup>*\\\<^sup>* [u])"
              by (metis P.Srcs.simps(1) P.Srcs_Resid \<open>t \ u \<approx> (t \ u) \<^sup>1\\<^sup>* (W \<^sup>*\\<^sup>* [u])\<close>
                  calculation Cong_imp_arr(2) R.arr_iff_has_source)
            also have "... = P.Trgs ([u] \<^sup>*\\\<^sup>* W)"
              by (metis P.Trgs_Resid_sym)
            also have "... = P.Srcs (([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W))"
              by (metis Cong\<^sub>0_imp_con R.con_implies_arr(2) R.not_arr_null
                  P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Srcs_Resid P.Con_rec(1) yy')
            also have "... = R.sources ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))"
              by (metis Cong\<^sub>0_imp_con R.not_arr_null R.sources_resid P.Con_sym P.Con_sym1
                  P.Resid1x_as_Resid P.Residx1_as_Resid P.Trgs.simps(2)
                  \<open>P.Trgs ([u] \<^sup>*\\<^sup>* W) = P.Srcs (([u'] \<^sup>*\\<^sup>* W') \<^sup>*\\<^sup>* ([u] \<^sup>*\\<^sup>* W))\<close>
                  R.con_implies_arr(2) yy')
            finally show ?thesis by blast
          qed
          thus ?thesis
            using yy' Cong_closure_props(4) [of "?y' \\ ?y" "(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"]
            by fastforce
        qed
        also have "... \<approx> (((t \<^sup>1\\\<^sup>* W) \\ ?y) \\ (?y' \\ ?y))"
        proof -
          have "[(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])] = [(t \<^sup>1\\\<^sup>* W) \\ ?y]"
          proof -
            have "[(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])] = ([t] \<^sup>*\\\<^sup>* [u]) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"
              using P.Resid1x_as_Resid
              by (metis R.not_arr_null P.Resid.simps(3) P.Resid1x_as_Resid'
                  \<open>t \ u \<approx> (t \ u) \<^sup>1\\<^sup>* (W \<^sup>*\\<^sup>* [u])\<close> con Cong_imp_arr(2))
            also have "... = ([t] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W)"
              using P.cube by blast
            also have "... = [(t \<^sup>1\\\<^sup>* W) \\ ?y]"
              using P.Resid1x_as_Resid
              by (metis P.Resid.simps(1) P.Resid_rec(1) P.ex_un_null calculation
                  list.distinct(1))
            finally show ?thesis by blast
          qed
          thus ?thesis
            using Cong_imp_arr(2) Cong_reflexive calculation by force
        qed
        also have "... \<approx> (((t' \<^sup>1\\\<^sup>* W') \\ ?y) \\ (?y' \\ ?y))"
        proof -
          have "((t \<^sup>1\\\<^sup>* W) \\ ?y) \\ (?y' \\ ?y) \<approx>\<^sub>0 ((t' \<^sup>1\\\<^sup>* W') \\ ?y) \\ (?y' \\ ?y)"
            using 1 2 Cong\<^sub>0_subst_left(2)
            by (metis Cong\<^sub>0_subst_right(2) R.conI R.not_con_null(1) WW')
          thus ?thesis
            using Cong\<^sub>0_implies_Cong by presburger
        qed
        also have "... \<approx> ((t' \<^sup>1\\\<^sup>* W') \\ ?y') \\ (?y \\ ?y')"
          using Cong_imp_arr(2) Cong_reflexive R.cube calculation by presburger
        also have "... \<approx> (t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
        proof -
          have "((t' \<^sup>1\\\<^sup>* W') \\ ?y') = (t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
          proof -
            have "[((t' \<^sup>1\\\<^sup>* W') \\ ?y')] = ([t'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W')"
              using P.Resid1x_as_Resid
              by (metis "2" R.not_con_null(1,2) P.Resid.simps(3) P.Resid1x_as_Resid')
            also have "... = ([t'] \<^sup>*\\\<^sup>* [u']) \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])"
              using P.cube by blast
            also have "... = [(t' \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])]"
              by (metis "3" P.Resid.simps(3) P.Resid1x_as_Resid calculation list.distinct(1))
            finally show ?thesis by blast
          qed
          thus ?thesis
            by (metis "2" Cong\<^sub>0_imp_con R.rts_axioms normal_sub_rts.Cong_closure_props(1,4)
                normal_sub_rts_axioms rts.sources_resid yy')
        qed
        also have "... \<approx> t' \\ u'"
          by (metis (lifting) ext "2" "3" Cong_arr_resid_NPath Cong_symmetric
              R.con_def R.con_implies_arr(1) R.con_sym_ax R.not_con_null(2)
              P.Con_sym P.Resid1x_as_Resid' P.Srcs.simps(2) P.Srcs_Resid_Arr_single
              P.paths_in_rts_axioms WW' NPath_Resid_Arr_single paths_in_rts.Con_imp_eq_Srcs
              R.arr_resid_iff_con R.sources_resid)
        finally show "t \\ u \<approx> t' \\ u'" by simp
      qed
    qed

  end

  context coherent_normal_sub_rts
  begin

    text \<open>
      Coherence for single transitions extends inductively to paths.
    \<close>

    lemma Coherent_single:
    assumes "R.arr t" and "NPath U" and "NPath U'"
    and "R.sources t = P.Srcs U" and "P.Srcs U = P.Srcs U'" and "P.Trgs U = P.Trgs U'"
    shows "NPath (([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
    proof -
      have "(t \<^sup>1\\\<^sup>* U) \\ (t \<^sup>1\\\<^sup>* U') \<in> \<NN>"
        using assms coherent [of t U U'] by auto
      hence "NPath [(t \<^sup>1\\\<^sup>* U) \\ (t \<^sup>1\\\<^sup>* U')]"
        by (simp add: NPath_def elements_are_arr)
      thus ?thesis
        using P.Resid1x_as_Resid
        by (metis NPath_def P.Arr.simps(2) P.Resid.simps(1) P.Resid1x.simps(2)
            P.Resid1x_as_Resid' P.Srcs.simps(2) R.not_arr_null
            Resid_along_NPath_preserves_reflects_Con assms(1,2,3,4,5) P.Con_Arr_self)
    qed

    lemma Coherent:
    shows "\<lbrakk> P.Arr T; NPath U; NPath U'; P.Srcs T = P.Srcs U;
             P.Srcs U = P.Srcs U'; P.Trgs U = P.Trgs U' \<rbrakk>
                \<Longrightarrow> NPath ((T \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U'))"
    proof (induct T arbitrary: U U')
      show "\<And>U U'. \<lbrakk> P.Arr []; NPath U; NPath U'; P.Srcs [] = P.Srcs U;
                     P.Srcs U = P.Srcs U'; P.Trgs U = P.Trgs U' \<rbrakk>
                      \<Longrightarrow> NPath (([] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([] \<^sup>*\\\<^sup>* U'))"
        using P.Arr.simps(1) by blast
      fix t T U U'
      assume tT: "P.Arr (t # T)" and U: "NPath U" and U': "NPath U'"
      and Srcs1: "P.Srcs (t # T) = P.Srcs U" and Srcs2: "P.Srcs U = P.Srcs U'"
      and Trgs: "P.Trgs U = P.Trgs U'"
      and ind: "\<And>U U'. \<lbrakk> P.Arr T; NPath U; NPath U'; P.Srcs T = P.Srcs U;
                         P.Srcs U = P.Srcs U'; P.Trgs U = P.Trgs U' \<rbrakk>
                            \<Longrightarrow> NPath ((T \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* (T \<^sup>*\\\<^sup>* U'))"
      have t: "R.arr t"
        using tT
        by (metis P.Arr_imp_arr_hd list.sel(1))
      show "NPath (((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U'))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT U U' Coherent_single P.Srcs.simps(2) Srcs1 Srcs2 Trgs t by presburger
        assume T: "T \<noteq> []"
        let ?t = "[t] \<^sup>*\\\<^sup>* U" and ?t' = "[t] \<^sup>*\\\<^sup>* U'"
        let ?T = "T \<^sup>*\\\<^sup>* (U \<^sup>*\\\<^sup>* [t])"
        let ?T' = "T \<^sup>*\\\<^sup>* (U' \<^sup>*\\\<^sup>* [t])"
        have 0: "(t # T) \<^sup>*\\\<^sup>* U = ?t @ ?T"
          using tT U U' Srcs1 Srcs2
          by (metis NPath_Resid NPath_def P.Arr.simps(1) P.Con_sym P.Resid_cons(1))
        have 1: "NPath (?t \<^sup>*\\\<^sup>* ?t') \<and> NPath (?t' \<^sup>*\\\<^sup>* ?t)"
          by (metis Coherent_single P.Srcs.simps(3) Srcs1 Srcs2 T Trgs U U' neq_Nil_conv t)
        have A: "?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t) = T \<^sup>*\\\<^sup>* ((U \<^sup>*\\\<^sup>* [t]) @ (?t' \<^sup>*\\\<^sup>* ?t))"
          using 1 P.Arr.simps(1) P.Con_append(2) P.Con_sym P.Resid_append(2) P.Con_implies_Arr(1)
                NPath_def
          by metis
        have B: "?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t') = T \<^sup>*\\\<^sup>* ((U' \<^sup>*\\\<^sup>* [t]) @ (?t \<^sup>*\\\<^sup>* ?t'))"
          by (metis "1" NPath_implies_Arr P.Con_appendI(2) P.Con_sym P.Resid.simps(1)
              P.Resid_append(2) P.Arr.simps(1))
        have C: "NPath ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
        proof -
          have "P.Arr T"
            using P.Arr.elims(1) T tT by blast
          moreover have "NPath (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            using 1 U t tT Srcs1 P.Srcs_simp\<^sub>P
            apply (intro NPath_appendI)
              apply auto
            by (metis P.Arr.simps(1) NPath_def P.Srcs_Resid P.Trgs_Resid_sym)
          moreover have "NPath (U' \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
            using t U' 1 P.Con_imp_eq_Srcs P.Trgs_Resid_sym
            apply (intro NPath_appendI)
              apply auto
             apply (metis P.Arr.simps(2) NPath_Resid P.Resid.simps(1))
            by (metis P.Arr.simps(1) NPath_def P.Srcs_Resid)
          moreover have "P.Srcs T = P.Srcs (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U))"
            using A B
            by (metis "0" "1" NPath_implies_Arr P.Arr.simps(1) P.Con_cons(1)
                P.Con_imp_eq_Srcs P.Srcs_append P.ex_un_null T append_is_Nil_conv)
          moreover have "P.Srcs (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) =
                         P.Srcs (U' \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
            by (metis "1" NPath_implies_Arr P.Arr.simps(1) P.Con_sym P.Resid.simps(1)
                P.Srcs_Resid P.Srcs_append)
          moreover have "P.Trgs (U \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U)) =
                         P.Trgs (U' \<^sup>*\\\<^sup>* [t] @ ([t] \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* U'))"
            using "1" Cong\<^sub>0_imp_con P.con_char
            by (metis NPath_implies_Arr P.Arr.simps(1) P.Trgs_Resid_sym P.Trgs_append)
          ultimately show ?thesis
            using A B ind [of "(U \<^sup>*\\\<^sup>* [t]) @ (?t' \<^sup>*\\\<^sup>* ?t)" "(U' \<^sup>*\\\<^sup>* [t]) @ (?t \<^sup>*\\\<^sup>* ?t')"]
            by simp
        qed
        show ?thesis
        proof -
          have 2: "((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U') =
                   ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T') @ ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
          proof -
            have "((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U') = (?t @ ?T) \<^sup>*\\\<^sup>* (?t' @ ?T')"
              using 0
              by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.Resid_cons(1)
                  P.paths_in_rts_axioms Srcs1 Srcs2 U' paths_in_rts.Con_sym tT)
            also have "... = ((?t @ ?T) \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T'"
              using tT T U U' Srcs1 Srcs2 0
              by (metis C NPath_implies_Arr P.Con_appendI(2) P.Con_sym P.Resid.simps(1)
                  P.Resid_append(2) P.paths_in_rts_axioms paths_in_rts.Arr.simps(1))
            also have "... = ((?t \<^sup>*\\\<^sup>* ?t') @ (?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t))) \<^sup>*\\\<^sup>* ?T'"
            proof -
              have "?t @ ?T \<^sup>*\<frown>\<^sup>* ?t'"
                using 1 P.Con_appendI(1) [of ?t ?t' ?T] C NPath_implies_Arr by fastforce
              thus ?thesis
                using P.Resid_append(1) [of ?t ?T ?t']
                by (metis P.Con_sym P.Resid.simps(1) append_Nil2)
            qed
            also have "... = ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T') @
                               ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
            proof -
              have "?t \<^sup>*\\\<^sup>* ?t' @ ?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t) \<^sup>*\<frown>\<^sup>* ?T'"
                by (metis C NPath_def P.Arr.simps(1) P.Con_appendI(1) P.Con_sym P.Resid.simps(1))
              thus ?thesis
                by (metis "1" NPath_implies_Arr P.Arr.simps(1) P.Resid_append(1))
            qed
            finally show ?thesis by simp
          qed
          moreover have 3: "NPath ..."
          proof -
            have "NPath ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T')"
              by (metis "1" C NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.Con_imp_eq_Srcs
                  P.Con_implies_Arr(1,2))
            moreover have "P.Trgs ((?t \<^sup>*\\\<^sup>* ?t') \<^sup>*\\\<^sup>* ?T') =
                           P.Srcs ((?T \<^sup>*\\\<^sup>* (?t' \<^sup>*\\\<^sup>* ?t)) \<^sup>*\\\<^sup>* (?T' \<^sup>*\\\<^sup>* (?t \<^sup>*\\\<^sup>* ?t')))"
              using C
              by (metis NPath_implies_Arr P.Srcs.simps(1) P.Srcs_Resid
                  P.Trgs_Resid_sym P.Arr_has_Src)
            ultimately show ?thesis
              using C by blast
          qed
          ultimately show "NPath (((t # T) \<^sup>*\\\<^sup>* U) \<^sup>*\\\<^sup>* ((t # T) \<^sup>*\\\<^sup>* U'))"
            by simp
        qed
      qed
    qed

    interpretation NP: normal_sub_rts P.Resid \<open>Collect NPath\<close>
      using Ide_implies_NPath NPath_implies_Arr P.ide_char P.coinitial_def P.sources_char\<^sub>P
      apply unfold_locales
           apply auto
      by (meson Backward_stable)

    interpretation NP: coherent_normal_sub_rts P.Resid \<open>Collect NPath\<close>
    proof
      fix T \<U> \<U>'
      assume T: "P.arr T" and \<U>: "NP.NPath \<U>" and \<U>': "NP.NPath \<U>'"
      assume Srcs: "NP.P.Srcs \<U> = NP.P.Srcs \<U>'" and Trgs: "NP.P.Trgs \<U> = NP.P.Trgs \<U>'"
      assume T\<U>: "P.sources T = NP.P.Srcs \<U>"
      have "NP.P.Resid1x T \<U> = T \<^sup>*\\\<^sup>* implode \<U>"
        by (metis NP.Resid_along_NPath_preserves_reflects_con NP_Resid1x_eq
            P.con_arr_src(1) P.not_con_null(1) P.null_char T T\<U> \<U>)
      also have "T \<^sup>*\\\<^sup>* implode \<U> \<approx>\<^sup>*\<^sub>0 T \<^sup>*\\\<^sup>* implode \<U>'"
      proof -
        have "P.Srcs T = P.Srcs (implode \<U>)"
          by (metis NP.Resid_along_NPath_preserves_reflects_con P.Arr.simps(1)
              P.Con_imp_eq_Srcs P.arrI P.arr_char P.con_arr_self T T\<U> \<U> calculation)
        moreover have "NPath (implode \<U>)"
          by (simp add: NP_NPath_imp \<U>)
        moreover have "NPath (implode \<U>')"
          by (simp add: NP_NPath_imp \<U>')
        moreover have "P.Srcs (implode \<U>) = P.Srcs (implode \<U>')"
          by (metis NP.Resid_along_NPath_preserves_reflects_con NP_Resid1x_eq
              P.Con_imp_eq_Srcs P.arrI P.congE P.cong_reflexive P.not_arr_null
              P.null_char Srcs T T\<U> \<U>' calculation(1))
        moreover have "P.Trgs (implode \<U>) = P.Trgs (implode \<U>')"
        proof
          have 1: "P.targets (implode \<U>) = P.targets (implode \<U>')"
            using \<U> \<U>' Trgs NP_P_Trgs_eq
            by (simp add: NP.NPath_implies_Arr)
          show "P.Trgs (implode \<U>) \<subseteq> P.Trgs (implode \<U>')"
          proof
            fix B
            assume B: "B \<in> P.Trgs (implode \<U>)"
            have 2: "R.sources B = P.Trgs (implode \<U>)"
              using B
              by (metis (full_types) NP.Cong_arr_resid_NPath P.Arr.simps(1)
                  P.Resid_Arr_Src P.Srcs.simps(2) P.Srcs_Resid P.arr_char
                  T T\<U> \<U> \<open>NP.P.Resid1x T \<U> = T \<^sup>*\\<^sup>* foldr (@) \<U> []\<close>
                  NP.Cong_imp_arr(2) P.Con_imp_eq_Srcs)
            have "[B] \<in> P.targets (implode \<U>)"
              using B 2
              unfolding P.targets_char\<^sub>P [of "implode \<U>"]
              apply (simp, intro conjI)
              using P.Trgs_are_ide NPath_def calculation(2) by blast+
            hence "[B] \<in> P.targets (implode \<U>')"
              using B 1 by blast
            thus "B \<in> P.Trgs (implode \<U>')"
              by (metis (full_types, lifting) NP.NPath_implies_Arr NP_P_Trgs_eq
                  Trgs \<U> \<U>' mem_Collect_eq P.targets_char\<^sub>P B)
          qed
          show "P.Trgs (foldr (@) \<U>' []) \<subseteq> P.Trgs (foldr (@) \<U> [])"
          proof
            fix B
            assume B: "B \<in> P.Trgs (implode \<U>')"
            have "NP.P.Resid1x T \<U>' = T \<^sup>*\\\<^sup>* implode \<U>'"
              by (metis NP.Resid_along_NPath_preserves_reflects_con NP_Resid1x_eq
                  P.con_arr_src(1) P.not_con_null(1) P.null_char Srcs T T\<U> \<U>')
            hence 2: "R.sources B = P.Trgs (implode \<U>')"
              using B
              by (metis (full_types) CollectD NP.Cong_arr_resid_NPath P.Con_single_ide_iff
                  P.Srcs.simps(2) P.Trgs_are_ide Srcs T T\<U> \<U>' NP.Cong_imp_arr(2)
                  P.Con_imp_eq_Srcs P.Srcs_Resid P.arr_char P.con_char P.arr_resid_iff_con
                  subsetD)
            have "[B] \<in> P.targets (implode \<U>')"
              using B 2
              unfolding P.targets_char\<^sub>P [of "implode \<U>'"]
              apply (simp, intro conjI)
              using P.Trgs_are_ide NPath_def calculation(3) by blast+
            hence "[B] \<in> P.targets (implode \<U>')"
              using B 1 by blast
            thus "B \<in> P.Trgs (implode \<U>)"
              by (metis (full_types, lifting) NP.NPath_implies_Arr NP_P_Trgs_eq
                  Trgs \<U> \<U>' mem_Collect_eq P.targets_char\<^sub>P B)
          qed
        qed
        ultimately show ?thesis
          using T Coherent NP_NPath_imp
          by (simp add: P.arr_char)
      qed
      also have "T \<^sup>*\\\<^sup>* foldr (@) \<U>' [] = NP.P.Resid1x T \<U>'"
        by (metis NP.Resid_along_NPath_preserves_reflects_con NP_Resid1x_eq
            P.con_arr_src(1) P.not_con_null(1) P.null_char T T\<U> \<U>' Srcs)
      finally show "NP.P.Resid1x T \<U> \<approx>\<^sup>*\<^sub>0 NP.P.Resid1x T \<U>'" by blast
    qed

    theorem extends_to_paths:
    shows "coherent_normal_sub_rts P.Resid (Collect NPath)"
      ..

  end

  subsection "Quotient by Coherent Normal Sub-RTS"

  text \<open>
    We now define the quotient of an RTS by a coherent normal sub-RTS and show that it is
    an extensional RTS.
  \<close>

  locale quotient_by_coherent_normal =
    R: rts +
    coherent_normal_sub_rts
  begin

    definition Resid  (infix \<open>\<lbrace>\\<rbrace>\<close> 70)
    where "\<T> \<lbrace>\\\<rbrace> \<U> \<equiv>
           if is_Cong_class \<T> \<and> is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)
           then Cong_class
                  (fst (SOME tu. fst tu \<in> \<T> \<and> snd tu \<in> \<U> \<and> fst tu \<frown> snd tu) \\
                   snd (SOME tu. fst tu \<in> \<T> \<and> snd tu \<in> \<U> \<and> fst tu \<frown> snd tu))
           else {}"

    sublocale partial_magma Resid
      using Cong_class_is_nonempty Resid_def
      by unfold_locales metis

    lemma is_partial_magma:
    shows "partial_magma Resid"
      ..

    lemma null_char:
    shows "null = {}"
      using Cong_class_is_nonempty Resid_def
      by (metis null_is_zero(2))

    lemma Resid_by_members:
    assumes "is_Cong_class \<T>" and "is_Cong_class \<U>" and "t \<in> \<T>" and "u \<in> \<U>" and "t \<frown> u"
    shows "\<T> \<lbrace>\\\<rbrace> \<U> = \<lbrace>t \\ u\<rbrace>"
      using assms Resid_def someI_ex [of "\<lambda>tu. fst tu \<in> \<T> \<and> snd tu \<in> \<U> \<and> fst tu \<frown> snd tu"]
      apply simp
      by (meson Cong_class_membs_are_Cong Cong_class_eqI Cong_subst(2)
          R.coinitial_iff R.con_imp_coinitial)

    abbreviation Con  (infix \<open>\<lbrace>\<frown>\<rbrace>\<close> 50)
    where "\<T> \<lbrace>\<frown>\<rbrace> \<U> \<equiv> \<T> \<lbrace>\\\<rbrace> \<U> \<noteq> {}"

    lemma Con_char:
    shows "\<T> \<lbrace>\<frown>\<rbrace> \<U> \<longleftrightarrow>
           is_Cong_class \<T> \<and> is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)"
      by (metis (no_types, opaque_lifting) Cong_class_is_nonempty is_Cong_classI
          Resid_def Resid_by_members R.arr_resid_iff_con)

    lemma Con_sym:
    assumes "Con \<T> \<U>"
    shows "Con \<U> \<T>"
      using assms Con_char R.con_sym by meson

    lemma is_Cong_class_Resid:
    assumes "\<T> \<lbrace>\<frown>\<rbrace> \<U>"
    shows "is_Cong_class (\<T> \<lbrace>\\\<rbrace> \<U>)"
      using assms Con_char Resid_by_members R.arr_resid_iff_con is_Cong_classI by auto

    lemma Con_witnesses:
    assumes "\<T> \<lbrace>\<frown>\<rbrace> \<U>" and "t \<in> \<T>" and "u \<in> \<U>"
    shows "\<exists>V W. NPath V \<and> NPath W \<and> t \<^sup>1\\\<^sup>* V \<frown> u \<^sup>1\\\<^sup>* W"
    proof -
      obtain t' u' where t'u': "t' \<in> \<T> \<and> u' \<in> \<U> \<and> t' \<frown> u'"
        using assms Con_char by auto
      have 1: "t' \<approx> t \<and> u' \<approx> u"
        using assms Con_char t'u' Cong_class_membs_are_Cong by auto
      obtain V V' where VV': "NPath V \<and> NPath V' \<and> t' \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* V'"
        using 1 by auto
      obtain W W' where WW': "NPath W \<and> NPath W' \<and> u' \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 u \<^sup>1\\\<^sup>* W'"
        using 1 by auto
      have Trgs_VV': "P.Trgs V = P.Trgs V'"
      proof -
        have "P.Trgs V = R.sources (t' \<^sup>1\\\<^sup>* V)"
          by (metis P.Resid1x_as_Resid P.Srcs.simps(2) P.Srcs_Resid elements_are_arr
              R.null_is_zero(2) VV' P.Resid1x_as_Resid' R.not_arr_null)
        also have "... = R.sources (t \<^sup>1\\\<^sup>* V')"
          using VV' Cong\<^sub>0_imp_coinitial by presburger
        also have "... = P.Trgs V'"
          by (metis P.Resid1x_as_Resid P.Srcs.simps(2) elements_are_arr
              R.arr_resid_iff_con R.not_arr_null VV' P.Resid1x_as_Resid' P.Srcs_Resid
              R.con_implies_arr(1))
        finally show ?thesis by blast
      qed
      have Trgs_WW': "P.Trgs W = P.Trgs W'"
      proof -
        have "P.Trgs W = R.sources (u' \<^sup>1\\\<^sup>* W)"
          by (metis P.Resid1x_as_Resid P.Srcs.simps(2) P.Srcs_Resid elements_are_arr
              R.null_is_zero(2) WW' P.Resid1x_as_Resid' R.not_arr_null)
        also have "... = R.sources (u \<^sup>1\\\<^sup>* W')"
          using WW' Cong\<^sub>0_imp_coinitial by presburger
        also have "... = P.Trgs W'"
          by (metis P.Resid1x_as_Resid P.Srcs.simps(2) elements_are_arr
              R.arr_resid_iff_con R.not_arr_null WW' P.Resid1x_as_Resid' P.Srcs_Resid
              R.con_implies_arr(1))
        finally show ?thesis by blast
      qed
      have con_WV: "W \<^sup>*\<frown>\<^sup>* V"
      proof -
        have "P.coinitial W V"
        proof
          show "P.Arr W" and "P.Arr V"
            using VV' WW' NPath_def by blast+
          show "P.Srcs W \<inter> P.Srcs V \<noteq> {}"
          proof -
            have "R.sources t' \<inter> R.sources u' \<subseteq> P.Srcs W \<inter> P.Srcs V"
              using VV' WW'
              by (metis (full_types) R.con_def R.null_is_zero(2) R.sources_eqI
                  Cong\<^sub>0_imp_con P.Con_imp_eq_Srcs P.Resid1x_as_Resid'
                  P.Srcs.simps(2) subsetI)
            thus ?thesis
              using t'u' R.con_imp_common_source by force
          qed
        qed
        thus ?thesis
          by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.coinitial_char(1) WW')
      qed
      have seq_V_WV: "P.seq V (W \<^sup>*\\\<^sup>* V)"
        using P.arr_resid_iff_con P.conI\<^sub>P P.seqI(2) P.sources_resid con_WV
        by presburger
      have seq_V'_WV: "P.seq V' (W \<^sup>*\\\<^sup>* V)"
        using NPath_implies_Arr P.seq_char VV' Trgs_VV' seq_V_WV by presburger
      let ?X = "V @ (W \<^sup>*\\\<^sup>* V)" and ?X' = "V' @ (W \<^sup>*\\\<^sup>* V)"
      have X: "P.composite_of V (W \<^sup>*\\\<^sup>* V) ?X"
        by (simp add: P.append_is_composite_of seq_V_WV)
      have X': "P.composite_of V' (W \<^sup>*\\\<^sup>* V) ?X'"
        by (simp add: P.append_is_composite_of seq_V'_WV)
      have con_t'X: "[t'] \<^sup>*\<frown>\<^sup>* ?X"
        using con_WV VV' WW' P.Con_appendI(2)
        by (metis Resid_along_NPath_preserves_reflects_Con P.Con_imp_eq_Srcs
            P.Resid.simps(1) P.Resid1x_as_Resid' elements_are_arr R.not_arr_null
            R.null_is_zero(1))
      have *: "t' \<^sup>1\\\<^sup>* ?X \<approx>\<^sub>0 t \<^sup>1\\\<^sup>* ?X'"
      proof
        have t'X_ne_null: "t' \<^sup>1\\\<^sup>* ?X \<noteq> R.null"
          by (metis P.Con_rec(1) P.Resid1x_as_Resid P.con_imp_arr_resid P.null_char
              R.not_con_null(2) con_t'X)
        have tX'_ne_null: "t \<^sup>1\\\<^sup>* ?X' \<noteq> R.null"
        proof -
          have "[t] \<^sup>*\<frown>\<^sup>* ?X'"
            using con_WV VV' WW' P.Con_appendI(2) [of "[t]" V' "W \<^sup>*\\\<^sup>* V"]
            by (metis (lifting) ext NPath_Resid NPath_implies_Arr P.Con_imp_eq_Srcs
                P.Con_sym P.seq_char R.not_arr_null R.null_is_zero(1) seq_V'_WV
                elements_are_arr P.Arr.simps(1) P.Con_imp_Arr_Resid P.Resid1x_as_Resid'
                P.Srcs_Resid)
          thus ?thesis
            by (metis P.Resid1x_as_Resid R.not_arr_null P.Arr.simps(2) P.Con_imp_Arr_Resid)
        qed
        have t'X_eq_t'V_WV: "t' \<^sup>1\\\<^sup>* ?X = (t' \<^sup>1\\\<^sup>* V) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* V)"
          using con_WV P.Con_append(2) P.Con_sym P.Resid.simps(1)
               P.Resid1x_as_Resid P.Resid1x_as_Resid' P.Resid1x_null P.Resid_append(2)
          by (metis P.Resid1x_append con_t'X)
        have tX_eq_tV'_WV: "t \<^sup>1\\\<^sup>* ?X' = (t \<^sup>1\\\<^sup>* V') \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* V)"
          by (metis NPath_implies_Arr P.Arr.simps(1) P.Resid1x_as_Resid'
              P.paths_in_rts_axioms VV' con_WV paths_in_rts.Resid1x_append tX'_ne_null)
        have con_t'X_tX': "t' \<^sup>1\\\<^sup>* ?X \<frown> t \<^sup>1\\\<^sup>* ?X'"
          by (metis Cong\<^sub>0_imp_con NPath_Resid NPath_implies_Arr P.Resid1x_as_Resid'
              P.Srcs.simps(2) Resid_along_NPath_preserves_reflects_con VV' WW' con_WV
              P.Con_imp_eq_Srcs t'X_eq_t'V_WV t'X_ne_null tX_eq_tV'_WV)
        show "(t' \<^sup>1\\\<^sup>* ?X) \\ (t \<^sup>1\\\<^sup>* ?X') \<in> \<NN>"
        proof -
          have "(t' \<^sup>1\\\<^sup>* ?X) \\ (t \<^sup>1\\\<^sup>* ?X') =
                ((t' \<^sup>1\\\<^sup>* V) \\ (t \<^sup>1\\\<^sup>* V')) \<^sup>1\\\<^sup>* ((W \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* V'))"
          proof -
            have "[(t' \<^sup>1\\\<^sup>* ?X) \\ (t \<^sup>1\\\<^sup>* ?X')] =
                  (([t'] \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* V)) \<^sup>*\\\<^sup>* (([t] \<^sup>*\\\<^sup>* V') \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* V))"
              by (metis P.Resid.simps(3) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                  P.Resid1x_null tX_eq_tV'_WV tX'_ne_null t'X_eq_t'V_WV con_t'X_tX'
                  t'X_ne_null)
            also have "... = (([t'] \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* V')) \<^sup>*\\\<^sup>* ((W \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* V'))"
              using P.cube by blast
            also have "... = [((t' \<^sup>1\\\<^sup>* V) \\ (t \<^sup>1\\\<^sup>* V')) \<^sup>1\\\<^sup>* ((W \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* V'))]"
              by (metis P.Resid.simps(1) P.Resid1x_as_Resid P.Resid_rec(1) P.ex_un_null
                  calculation not_Cons_self)
            finally show ?thesis by blast
          qed
          moreover have "... \<in> \<NN>"
            by (metis con_WV NPath_Resid NPath_implies_Arr
                Resid_along_NPath_preserves_Cong\<^sub>0 P.Con_imp_eq_Srcs P.Resid1x_as_Resid'
                P.Srcs.simps(2) VV' WW' tX_eq_tV'_WV t'X_eq_t'V_WV t'X_ne_null calculation)
          ultimately show ?thesis by auto
        qed
        show "(t \<^sup>1\\\<^sup>* ?X') \\ (t' \<^sup>1\\\<^sup>* ?X) \<in> \<NN>"
        proof -
          have "(t \<^sup>1\\\<^sup>* ?X') \\ (t' \<^sup>1\\\<^sup>* ?X) =
                ((t \<^sup>1\\\<^sup>* V') \\ (t' \<^sup>1\\\<^sup>* V)) \<^sup>1\\\<^sup>* ((W \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* V))"
          proof -
            have "[(t \<^sup>1\\\<^sup>* ?X') \\ (t' \<^sup>1\\\<^sup>* ?X)] =
                  (([t] \<^sup>*\\\<^sup>* V') \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* V)) \<^sup>*\\\<^sup>* (([t'] \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* V))"
              by (metis P.Resid.simps(3) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                  P.Resid1x_null R.con_sym tX_eq_tV'_WV
                  tX'_ne_null t'X_eq_t'V_WV
                  con_t'X_tX' t'X_ne_null)
            also have "... = (([t] \<^sup>*\\\<^sup>* V') \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* V)) \<^sup>*\\\<^sup>* ((W \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* V))"
              using P.cube by blast
            also have "... = [((t \<^sup>1\\\<^sup>* V') \\ (t' \<^sup>1\\\<^sup>* V)) \<^sup>1\\\<^sup>* ((W \<^sup>*\\\<^sup>* V) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* V))]"
              by (metis P.Resid.simps(1) P.Resid1x_as_Resid P.Resid_rec(1) P.ex_un_null
                  calculation not_Cons_self)
            finally show ?thesis by blast
          qed
          moreover have "... \<in> \<NN>"
            by (metis con_WV NPath_Resid NPath_implies_Arr
                Resid_along_NPath_preserves_Cong\<^sub>0 P.Con_imp_eq_Srcs P.Resid1x_as_Resid'
                P.Srcs.simps(2) VV' WW' tX_eq_tV'_WV t'X_eq_t'V_WV t'X_ne_null calculation)
          ultimately show ?thesis by auto
        qed
      qed
      let ?Y = "W @ (V \<^sup>*\\\<^sup>* W)" and ?Y' = "W' @ (V \<^sup>*\\\<^sup>* W)"
      have Y: "P.composite_of W (V \<^sup>*\\\<^sup>* W) ?Y"
        by (simp add: P.append_is_composite_of P.composable_imp_seq P.composable_permute
            P.has_composites seq_V_WV)
      have Y': "P.composite_of W' (V \<^sup>*\\\<^sup>* W) ?Y'"
        by (metis NPath_implies_Arr P.append_is_composite_of P.composable_def
            P.seq_char WW' Y Trgs_WW' P.composableE)
      have **: "u' \<^sup>1\\\<^sup>* ?Y \<approx>\<^sub>0 u \<^sup>1\\\<^sup>* ?Y'"
      proof
        have con_u'Y: "[u'] \<^sup>*\<frown>\<^sup>* ?Y"
          using con_WV VV' WW' P.Con_appendI(2) [of "[u']" W "V \<^sup>*\\\<^sup>* W"]
          by (metis Resid_along_NPath_preserves_reflects_Con P.Con_imp_eq_Srcs
              P.Resid.simps(1) P.Resid1x_as_Resid' elements_are_arr R.not_arr_null
              R.null_is_zero(1))
        have con_uY': "[u] \<^sup>*\<frown>\<^sup>* ?Y'"
        proof -
          have seq_W'_VW: "P.seq W' (V \<^sup>*\\\<^sup>* W)"
            by (metis P.Arr_has_Trg P.Trgs.simps(1) P.arr_composite_of P.conI
                P.con_char P.con_sym_ax WW' Y' con_WV NPath_def P.arr_append_imp_seq)
          thus ?thesis
            using con_WV VV' WW' P.Con_appendI(2) [of "[u]" W' "V \<^sup>*\\\<^sup>* W"]
            by (metis (lifting) ext NPath_Resid NPath_implies_Arr P.Con_imp_eq_Srcs
                P.Con_sym P.seq_char R.not_arr_null R.null_is_zero(1)
                seq_W'_VW elements_are_arr P.Arr.simps(1) P.Con_imp_Arr_Resid
                P.Resid1x_as_Resid' P.Srcs_Resid)
        qed
        have u'Y_ne_null: "u' \<^sup>1\\\<^sup>* ?Y \<noteq> R.null"
          by (metis P.Con_rec(1) P.Resid1x_as_Resid P.con_imp_arr_resid P.null_char
              R.not_con_null(2) con_u'Y)
        have u'Y_eq_u'W_VW: "u' \<^sup>1\\\<^sup>* ?Y = (u' \<^sup>1\\\<^sup>* W) \<^sup>1\\\<^sup>* (V \<^sup>*\\\<^sup>* W)"
          using con_WV P.Con_append(2) P.Con_sym P.Resid.simps(1) P.Resid1x_as_Resid
            P.Resid1x_as_Resid' P.Resid1x_null P.Resid_append(2)
          by (metis P.Resid1x_append con_u'Y)
        have uY'_eq_uW'_VW: "u \<^sup>1\\\<^sup>* ?Y' = (u \<^sup>1\\\<^sup>* W') \<^sup>1\\\<^sup>* (V \<^sup>*\\\<^sup>* W)"
          using P.Resid_append(2) [of W' "V \<^sup>*\\\<^sup>* W" "[u]"]
          by (metis con_WV Cong\<^sub>0_imp_con P.Con_append(2) P.Con_sym P.Resid1x.simps(1)
              P.Resid1x_as_Resid R.not_con_null(2) WW' con_uY' list.inject neq_Nil_conv)
        have con_u'Y_uY': "u' \<^sup>1\\\<^sup>* ?Y \<frown> u \<^sup>1\\\<^sup>* ?Y'"
          by (metis con_WV NPath_Resid NPath_implies_Arr Resid_along_NPath_preserves_Cong\<^sub>0
              P.Resid1x_as_Resid' P.Srcs.simps(2) elements_are_arr R.arr_resid_iff_con
              VV' WW' uY'_eq_uW'_VW u'Y_eq_u'W_VW u'Y_ne_null P.Con_imp_eq_Srcs)
        show "(u' \<^sup>1\\\<^sup>* ?Y) \\ (u \<^sup>1\\\<^sup>* ?Y') \<in> \<NN>"
        proof -
          have "(u' \<^sup>1\\\<^sup>* ?Y) \\ (u \<^sup>1\\\<^sup>* ?Y') =
                ((u' \<^sup>1\\\<^sup>* W) \\ (u \<^sup>1\\\<^sup>* W')) \<^sup>1\\\<^sup>* ((V \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W'))"
          proof -
            have "[(u' \<^sup>1\\\<^sup>* ?Y) \\ (u \<^sup>1\\\<^sup>* ?Y')] =
                  (([u'] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W)) \<^sup>*\\\<^sup>* (([u] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W))"
            proof -
              have "[(u' \<^sup>1\\\<^sup>* ?Y) \\ (u \<^sup>1\\\<^sup>* ?Y')] = [u' \<^sup>1\\\<^sup>* ?Y] \<^sup>*\\\<^sup>* [u \<^sup>1\\\<^sup>* ?Y']"
                using con_u'Y_uY' by auto
              also have "... = (([u'] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W)) \<^sup>*\\\<^sup>* (([u] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W))"
                by (metis P.Resid1x_as_Resid P.Resid_append(2) P.composite_of_def P.con_char
                    P.not_con_null(2) P.null_char P.prfx_implies_con Y' con_u'Y con_uY')
              finally show ?thesis by blast
            qed
            also have "... = (([u'] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W')) \<^sup>*\\\<^sup>* ((V \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W'))"
              using P.cube by blast
            also have "... = [((u' \<^sup>1\\\<^sup>* W) \\ (u \<^sup>1\\\<^sup>* W')) \<^sup>1\\\<^sup>* ((V \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W'))]"
              by (metis P.Resid.simps(1) P.Resid1x_as_Resid P.Resid_rec(1) P.ex_un_null
                  calculation not_Cons_self)
            finally show ?thesis by blast
          qed
          moreover have "... \<in> \<NN>"
            by (metis con_WV NPath_Resid NPath_implies_Arr Resid_along_NPath_preserves_Cong\<^sub>0
                P.Con_imp_eq_Srcs P.Resid1x_as_Resid' P.Srcs.simps(2) VV' WW'
                uY'_eq_uW'_VW u'Y_eq_u'W_VW u'Y_ne_null calculation)
          ultimately show ?thesis by auto
        qed
        show "(u \<^sup>1\\\<^sup>* ?Y') \\ (u' \<^sup>1\\\<^sup>* ?Y) \<in> \<NN>"
        proof -
          have "(u \<^sup>1\\\<^sup>* ?Y') \\ (u' \<^sup>1\\\<^sup>* ?Y) =
                ((u \<^sup>1\\\<^sup>* W') \\ (u' \<^sup>1\\\<^sup>* W)) \<^sup>1\\\<^sup>* ((V \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W))"
          proof -
            have "[(u \<^sup>1\\\<^sup>* ?Y') \\ (u' \<^sup>1\\\<^sup>* ?Y)] =
                  (([u] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W)) \<^sup>*\\\<^sup>* (([u'] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W))"
            proof -
              have "[(u \<^sup>1\\\<^sup>* ?Y') \\ (u' \<^sup>1\\\<^sup>* ?Y)] = [u \<^sup>1\\\<^sup>* ?Y'] \<^sup>*\\\<^sup>* [u' \<^sup>1\\\<^sup>* ?Y]"
                by (simp add: R.con_sym con_u'Y_uY')
              also have "... = (([u] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W)) \<^sup>*\\\<^sup>* (([u'] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* W))"
                by (metis Cong\<^sub>0_imp_con P.Resid1x.simps(1) P.Resid1x_as_Resid
                    P.Resid_append(2) P.paths_in_rts_axioms R.not_con_null(2) WW'
                    con_WV con_u'Y con_uY' paths_in_rts.Con_sym)
              finally show ?thesis by blast
            qed
            also have "... = (([u] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W)) \<^sup>*\\\<^sup>* ((V \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W))"
              using P.cube by blast
            also have "... = [((u \<^sup>1\\\<^sup>* W') \\ (u' \<^sup>1\\\<^sup>* W)) \<^sup>1\\\<^sup>* ((V \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W))]"
              by (metis P.Resid.simps(1) P.Resid1x_as_Resid P.Resid_rec(1) P.ex_un_null
                  calculation not_Cons_self)
            finally show ?thesis by blast
          qed
          moreover have "... \<in> \<NN>"
            by (metis con_WV NPath_Resid NPath_implies_Arr Resid_along_NPath_preserves_Cong\<^sub>0
                P.Con_imp_eq_Srcs P.Resid1x_as_Resid' P.Srcs.simps(2) VV' WW'
                uY'_eq_uW'_VW u'Y_eq_u'W_VW u'Y_ne_null calculation)
          ultimately show ?thesis by auto
        qed
      qed
      have 2: "NPath ?X \<and> NPath ?Y"
        by (metis (full_types) con_WV P.Con_imp_eq_Srcs P.Srcs_Resid
            VV' WW' inf.absorb_iff2 inf.idem coherent_normal_sub_rts_def NPath_Resid
            NPath_appendI NPath_implies_Arr self_append_conv)
      have "t \<^sup>1\\\<^sup>* ?X' \<frown> u \<^sup>1\\\<^sup>* ?Y'"
      proof -
        have "t \<^sup>1\\\<^sup>* ?X' \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* ?X"
          using * by simp
        moreover have "t' \<^sup>1\\\<^sup>* ?X \<frown> u' \<^sup>1\\\<^sup>* ?Y"
        proof -
          have "t' \<^sup>1\\\<^sup>* ?X \<frown> u' \<^sup>1\\\<^sup>* ?X"
            using t'u' Resid_along_NPath_preserves_reflects_Con
            by (metis 2 P.Con_imp_eq_Srcs P.Srcs.simps(2)
                Resid_along_NPath_preserves_reflects_con con_t'X)
          moreover have "u' \<^sup>1\\\<^sup>* ?X \<approx>\<^sub>0 u' \<^sup>1\\\<^sup>* ?Y"
            using WW' X Y coherent' [of _ _ ?X ?Y u' u']
            by (metis (no_types, lifting) "**" con_WV 2 Cong\<^sub>0_transitive
                P.Con_imp_eq_Srcs P.Con_sym P.Trgs_Resid_sym P.Trgs_append
                P.con_char P.diamond_commutes_upto_cong P.prfx_implies_con)
          ultimately show ?thesis
            using Cong\<^sub>0_subst_right by blast
        qed
        moreover have "u' \<^sup>1\\\<^sup>* ?Y \<approx>\<^sub>0 u \<^sup>1\\\<^sup>* ?Y'"
          using ** R.con_sym by simp
        ultimately show ?thesis
          using Cong\<^sub>0_subst_Con by auto
      qed
      moreover have "NPath ?X' \<and> NPath ?Y'"
        using X' Y' VV' WW' Trgs_VV' Trgs_WW'
        by (metis con_WV 2 NPath_append NPath_appendI P.Con_sym P.Resid.simps(1))
      ultimately show ?thesis by auto
    qed

    abbreviation Arr
    where "Arr \<T> \<equiv> Con \<T> \<T>"

    lemma Arr_Resid:
    assumes "Con \<T> \<U>"
    shows "Arr (\<T> \<lbrace>\\\<rbrace> \<U>)"
      by (metis Con_char Cong_class_memb_is_arr R.arrE rep_in_Cong_class
          assms is_Cong_class_Resid)

    lemma Cube:
    assumes "Con (\<V> \<lbrace>\\\<rbrace> \<T>) (\<U> \<lbrace>\\\<rbrace> \<T>)"
    shows "(\<V> \<lbrace>\\\<rbrace> \<T>) \<lbrace>\\\<rbrace> (\<U> \<lbrace>\\\<rbrace> \<T>) = (\<V> \<lbrace>\\\<rbrace> \<U>) \<lbrace>\\\<rbrace> (\<T> \<lbrace>\\\<rbrace> \<U>)"
    proof -
      obtain t u where tu: "t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u \<and> \<T> \<lbrace>\\\<rbrace> \<U> = \<lbrace>t \\ u\<rbrace>"
        using assms
        by (metis Con_char Cong_class_is_nonempty R.con_sym Resid_by_members)
      obtain t' v where t'v: "t' \<in> \<T> \<and> v \<in> \<V> \<and> t' \<frown> v \<and> \<T> \<lbrace>\\\<rbrace> \<V> = \<lbrace>t' \\ v\<rbrace>"
        using assms
        by (metis Con_char Cong_class_is_nonempty Resid_by_members Con_sym)
      have tt': "t \<approx> t'"
        using assms
        by (metis Cong_class_membs_are_Cong Cong_class_is_nonempty Resid_def t'v tu)
      have \<U>\<T>: "\<U> \<lbrace>\\\<rbrace> \<T> = \<lbrace>u \\ t\<rbrace>" and \<V>\<T>: "\<V> \<lbrace>\\\<rbrace> \<T> = \<lbrace>v \\ t'\<rbrace>"
        by (metis Con_char Cong_class_is_nonempty R.con_sym Resid_by_members assms t'v tu)+
      obtain W W' where WW': "NPath W \<and> NPath W' \<and> t \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 t' \<^sup>1\\\<^sup>* W'"
        using tu t'v tt' by auto
      obtain X X' where XX': "NPath X \<and> NPath X' \<and> (u \\ t) \<^sup>1\\\<^sup>* X \<frown> (v \\ t') \<^sup>1\\\<^sup>* X'"
        using \<U>\<T> \<V>\<T> Con_witnesses [of "\<U> \<lbrace>\\\<rbrace> \<T>" "\<V> \<lbrace>\\\<rbrace> \<T>" "u \\ t" "v \\ t'"]
        by (metis arr_in_Cong_class R.con_sym t'v tu assms Con_sym R.arr_resid_iff_con)

      have Con_tW: "P.Con [t] W"
        by (metis Cong\<^sub>0_imp_con P.Resid1x_as_Resid' R.not_con_null(1) WW')
      have Con_t'W': "P.Con [t'] W'"
        by (metis Cong\<^sub>0_imp_con P.Resid1x_as_Resid' R.not_con_null(1) WW')
      have Con_uW: "P.Con [u] W"
        by (metis NPath_Resid_Arr_single NPath_implies_Arr P.Arr.simps(1)
            P.Con_imp_eq_Srcs P.Con_sym P.Srcs.simps(2) R.coinitial_iff
            R.con_imp_coinitial WW' Con_tW tu)
      have Con_vW': "P.Con [v] W'"
        by (metis Cong_arr_resid_NPath P.Con_imp_eq_Srcs P.Con_rec(1)
            P.Resid1x_as_Resid' P.Srcs.simps(2) R.con_implies_arr(2) R.not_arr_null
            WW' Con_t'W' Cong_imp_arr(2) t'v)
      have Con_tX_W: "P.Con ([t] @ X) W"
        by (metis (lifting) ext NPath_implies_Arr P.Arr.simps(1) P.Con_appendI(1)
            P.Con_imp_eq_Srcs P.Con_sym P.Srcs.simps(2) R.con_sym R.not_arr_null
            XX' Con_tW NPath_Resid  P.Con_imp_Arr_Resid P.Resid1x_as_Resid'
            P.Srcs_Resid_Arr_single R.con_implies_arr(1) R.sources_resid tu)
      have Con_X_Wt: "X \<^sup>*\<frown>\<^sup>* W \<^sup>*\\\<^sup>* [t]"
        by (metis NPath_implies_Arr P.Arr.simps(1) P.Con_cons(1) P.null_char
            P.null_is_zero(2) XX' Con_tX_W append_Cons append_Nil)
      have Con_X'_W't': "X' \<^sup>*\<frown>\<^sup>* W' \<^sup>*\\\<^sup>* [t']"
        by (metis (lifting) ext NPath_implies_Arr P.Arr.simps(1) P.Con_imp_eq_Srcs
            P.Con_sym P.Srcs.simps(2) R.con_sym XX' Con_t'W' NPath_Resid
            R.null_is_zero(2) P.Con_imp_Arr_Resid P.Resid1x_as_Resid'
            P.Srcs_Resid_Arr_single R.conE R.sources_resid t'v)
      have Con_t'X'_W': "P.Con ([t'] @ X') W'"
        using P.Con_append(1)
        by (metis P.Resid.simps(1) P.ex_un_null Con_X'_W't' Con_t'W')
      have seq_tX: "P.seq [t] X"
        by (metis P.arr_append_imp_seq P.con_implies_arr(1) Con_X_Wt Con_tX_W
            not_Cons_self P.Resid.simps(1) P.con_char)
      have seq_t'X': "P.seq [t'] X'"
        by (metis P.Con_sym P.arr_append_imp_seq Con_X'_W't' Con_t'X'_W'
            P.Con_implies_Arr(2) P.Resid.simps(1) P.arrI\<^sub>P)

      let ?t_W = "t \<^sup>1\\\<^sup>* W" and ?t'_W' = "t' \<^sup>1\\\<^sup>* W'" and ?u_W = "u \<^sup>1\\\<^sup>* W" and ?v_W' = "v \<^sup>1\\\<^sup>* W'"
      let ?tX = "[t] @ X" and ?t'X' = "[t'] @ X'"
      let ?tX_W = "?tX \<^sup>*\\\<^sup>* W" and ?t'X'_W' = "?t'X' \<^sup>*\\\<^sup>* W'"
      let ?W_tX = "(W \<^sup>*\\\<^sup>* [t]) \<^sup>*\\\<^sup>* X" and ?W'_t'X' = "(W' \<^sup>*\\\<^sup>* [t']) \<^sup>*\\\<^sup>* X'"
      let ?u_tX = "(u \\ t) \<^sup>1\\\<^sup>* X" and ?v_t'X' = "(v \\ t') \<^sup>1\\\<^sup>* X'"
      let ?u_W = "u \<^sup>1\\\<^sup>* W" and ?v_W' = "v \<^sup>1\\\<^sup>* W'"
      let ?W_u = "W \<^sup>*\\\<^sup>* [u]" and ?W'_v = "W' \<^sup>*\\\<^sup>* [v]"

      have tX: "P.composite_of [t] X ?tX"
        using P.append_is_composite_of seq_tX by blast
      have t'X': "P.composite_of [t'] X' ?t'X'"
        using P.append_is_composite_of seq_t'X' by blast
      have NPath_W_tX: "NPath ?W_tX"
        by (metis NPath_Resid P.Arr.simps(1) P.Con_imp_eq_Srcs P.Con_implies_Arr(2)
            P.seq_char WW' seq_tX Con_X_Wt)
      have NPath_W'_t'X': "NPath ?W'_t'X'"
        by (metis NPath_Resid P.Con_imp_eq_Srcs P.Con_implies_Arr(1) WW'
            Con_X'_W't' Con_t'W')
      have tX_W_eq: "?tX_W = [?t_W] @ (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))"
        by (metis P.Resid.simps(1) P.Resid_cons' Con_X_Wt Con_tX_W
            append.left_neutral append_Cons)
      have t'X'_W'_eq: "?t'X'_W' = [?t'_W'] @ (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']))"
        by (metis P.Resid.simps(1) P.Resid_cons' Con_X'_W't' Con_t'X'_W'
            append.left_neutral append_Cons)

      have Con_tX_W__t'X'_W': "?tX_W \<^sup>*\<frown>\<^sup>* ?t'X'_W'"
      proof -
        have "[?t_W] @ (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) \<^sup>*\<frown>\<^sup>* [?t'_W'] @ (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']))"
        proof (intro P.Con_appendI)
          show 1: "[t \<^sup>1\\\<^sup>* W] \<^sup>*\<frown>\<^sup>* [t' \<^sup>1\\\<^sup>* W']"
            using Cong\<^sub>0_imp_con WW' by auto
          show 2: "[t \<^sup>1\\\<^sup>* W] \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* W'] \<^sup>*\<frown>\<^sup>* X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])"
            by (metis (lifting) ext "1" Con_X'_W't' Con_t'W' NPath_Resid NPath_implies_Arr
                P.Arr.simps(1) P.Resid1x_as_Resid XX' P.Con_imp_Arr_Resid
                P.Con_imp_eq_Srcs P.Con_sym P.Srcs_Resid P.Trgs_Resid_sym)
          show "X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* ([t' \<^sup>1\\\<^sup>* W'] @ X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W]"
          proof -
            have "NPath (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))"
              by (metis Backward_stable NPath_Resid NPath_implies_Arr P.Con_imp_eq_Srcs
                  NPath_W_tX XX')
            moreover have "P.coinitial
                             (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))
                             (([t' \<^sup>1\\\<^sup>* W'] @ X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W])"
              by (metis P.arr_resid P.coinitialI P.sources_resid P.targets_resid_sym
                  Con_X_Wt 1 2 Con_tW P.Con_appendI(2) P.Con_sym P.Resid1x_as_Resid
                  P.conI\<^sub>P)
            ultimately show ?thesis
              by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.coinitial_char(1))
          qed
        qed
        thus ?thesis
          using t'X'_W'_eq tX_W_eq by argo
      qed
      have NPath_tX_W__t'X'_W': "NPath (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W')"
      proof -
        have "?tX_W \<^sup>*\\\<^sup>* ?t'X'_W' =
              (([?t_W] \<^sup>*\\\<^sup>* [?t'_W']) \<^sup>*\\\<^sup>* (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']))) @
                 ((X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* [?t_W]))"
          by (metis P.Con_initial_left P.Resid.simps(1) P.Resid_cons' P.Resid_cons(1,2)
              Con_tX_W__t'X'_W' Con_X'_W't' Con_t'X'_W' append.left_neutral append_Cons tX_W_eq)
        moreover have "NPath (([?t_W] \<^sup>*\\\<^sup>* [?t'_W']) \<^sup>*\\\<^sup>* (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])))"
          by (metis P.Con_rec(1) P.Resid.simps(3) P.Resid1x_as_Resid WW'
              Con_X'_W't' Con_t'W' Cong\<^sub>0_imp_con NPath_Resid_single_Arr
              P.Con_imp_Arr_Resid P.Srcs_Resid P.Srcs_Resid_Arr_single
              P.Trgs_Resid_sym R.sources_resid)
        moreover have "NPath ((X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* [?t_W]))"
          using NPath_Resid P.Con_append(1) P.Con_imp_Arr_Resid P.Con_imp_eq_Srcs
                P.Con_sym P.Resid.simps(1) XX' Con_tX_W__t'X'_W' list.discI tX_W_eq
          by (metis (lifting) ext Con_X_Wt Con_t'X'_W')
        ultimately show ?thesis
          by (metis NPath_appendI NPath_implies_Arr P.Arr_append_iff\<^sub>P
              P.Con_imp_Arr_Resid P.arrI\<^sub>P P.arr_resid_iff_con P.con_char
              Con_tX_W__t'X'_W')
      qed
      have NPath_t'X'_W'__tX_W: "NPath (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
      proof -
        have "?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W =
              (([?t'_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) @
                 ((X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* (?tX_W \<^sup>*\\\<^sup>* [?t'_W']))"
        proof -
          have "?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W =
                (([t'] \<^sup>*\\\<^sup>* W') @ (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']))) \<^sup>*\\\<^sup>* (([t] @ X) \<^sup>*\\\<^sup>* W)"
            by (metis Con_t'X'_W' P.Resid_append(1) not_Cons_self2)
          also have "... = (([t'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* (([t] \<^sup>*\\\<^sup>* W) @ (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])))) @
                              ((X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* ((([t] @ X) \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* W')))"
            by (metis Con_t'W' Con_tX_W Con_tX_W__t'X'_W' P.Con_sym P.Resid_append(1)
                calculation not_Cons_self2)
          also have "... = ((([t'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([t] \<^sup>*\\\<^sup>* W)) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) @
                              ((X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* ((([t] @ X) \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([t'] \<^sup>*\\\<^sup>* W')))"
            using Con_X_Wt Con_tW P.Arr.simps(1) P.Con_implies_Arr(1)
                  P.Resid_append(2) [of "[t] \<^sup>*\\\<^sup>* W" "X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])" "[t'] \<^sup>*\\\<^sup>* W'"]
            by (metis P.Con_appendI(2))
          also have "... = (([?t'_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) @
                             ((X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* (?tX_W \<^sup>*\\\<^sup>* [?t'_W']))"
            using Con_t'W' Con_tW P.Resid1x_as_Resid by fastforce
          finally show ?thesis by blast
        qed
        moreover have "NPath (([?t'_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])))"
          by (metis P.Con_rec(1) P.Resid.simps(3) P.Resid1x_as_Resid
              WW' Con_X_Wt Con_tW Cong\<^sub>0_imp_con NPath_Resid_single_Arr
              P.Con_imp_Arr_Resid P.Srcs_Resid P.Srcs_Resid_Arr_single
              P.Trgs_Resid_sym R.sources_resid)
        moreover have "NPath ((X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) \<^sup>*\\\<^sup>* (?tX_W \<^sup>*\\\<^sup>* [?t'_W']))"
          by (metis NPath_Resid P.Con_append(2) XX' Con_tX_W__t'X'_W' Con_X'_W't' Con_tX_W
              list.distinct(1) P.Con_imp_Arr_Resid P.Con_imp_eq_Srcs P.Con_implies_Arr(2)
              t'X'_W'_eq)
        ultimately show ?thesis
          by (metis NPath_appendI NPath_implies_Arr P.Arr_append_iff\<^sub>P
              P.Con_imp_Arr_Resid P.Con_sym P.arrI\<^sub>P P.arr_resid_iff_con P.con_char
              Con_tX_W__t'X'_W')
      qed

      let ?Z = "?tX_W @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
      let ?Z' = "?t'X'_W' @ (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W')"
      have Z: "P.Arr ?Z" and Z': "P.Arr ?Z'"
        by (metis P.Con_appendI(2) P.Con_implies_Arr(2) P.con_imp_arr_resid
            P.null_char Con_tX_W Con_t'X'_W' append_Nil2)+
      have Z_eq: "?Z = [?t_W] @ ((X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W))"
        using tX_W_eq by force
      have Z'_eq: "?Z' = [?t'_W'] @ ((X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) @ (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W'))"
        using t'X'_W'_eq by force

      have Con_Z_tW: "?Z \<^sup>*\<frown>\<^sup>* [?t_W]"
      proof -
        have "?Z = [?t_W] @ ((X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W))"
          using Z_eq by fastforce
        moreover have "P.Ide ([t \<^sup>1\\\<^sup>* W] \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W])"
          using P.Con_imp_Arr_Resid P.Resid1x_as_Resid P.Resid_Arr_self Con_tW
          by presburger
        moreover have "X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W) \<^sup>*\<frown>\<^sup>* [t \<^sup>1\\\<^sup>* W] \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W]"
        proof -
          have "[t \<^sup>1\\\<^sup>* W] \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W] \<in> P.targets (W \<^sup>*\\\<^sup>* [t])"
            using P.trg_in_targets
            by (metis P.Resid1x_as_Resid P.arr_resid P.conI\<^sub>P P.targets_resid_sym
                P.trg_def Con_tW)
          moreover have "P.sources (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)) =
                         P.targets (W \<^sup>*\\\<^sup>* [t])"
          proof -
            have "P.sources (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)) =
                  P.sources (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))"
              by (metis NPath_implies_Arr P.arr_append_imp_seq P.sources_append
                  NPath_W_tX Z Z_eq append_is_Nil_conv append_self_conv list.simps(3)
                  P.Arr_appendE\<^sub>P P.Con_sym P.arrI\<^sub>P P.con_char P.arr_resid_iff_con)
            thus ?thesis
              by (metis NPath_implies_Arr NPath_W_tX P.arrI\<^sub>P P.arr_resid_iff_con
                  P.con_sym P.sources_resid)
          qed
          ultimately show ?thesis
            by (metis P.Con_sym P.ide_char P.source_is_prfx P.Ide.simps(1))
        qed
        ultimately show ?thesis
          using P.Con_append(1)
          by (metis P.Ide.simps(1) P.null_char P.null_is_zero(1))
      qed
      have Con_Z_uW: "?Z \<^sup>*\<frown>\<^sup>* [?u_W]"
      proof (intro P.Con_appendI(1))
        show 1: "([t] @ X) \<^sup>*\\\<^sup>* W \<^sup>*\<frown>\<^sup>* [u \<^sup>1\\\<^sup>* W]"
        proof -
          have "[t \<^sup>1\\\<^sup>* W] @ X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* [u \<^sup>1\\\<^sup>* W]"
          proof (intro P.Con_appendI(1))
            show 1: "[t \<^sup>1\\\<^sup>* W] \<^sup>*\<frown>\<^sup>* [u \<^sup>1\\\<^sup>* W]"
              by (metis (no_types, lifting) P.Con_rec(1) P.Resid1x_as_Resid WW'
                  Con_tW Con_uW Resid_along_NPath_preserves_reflects_Con
                  P.Con_imp_eq_Srcs tu)
            show "X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]) \<^sup>*\<frown>\<^sup>* [u \<^sup>1\\\<^sup>* W] \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W]"
            proof -
              have "NPath (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))"
                by (metis Backward_stable NPath_Resid NPath_W_tX NPath_implies_Arr
                    P.Con_imp_eq_Srcs XX')
              moreover have "P.coinitial (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) ([u \<^sup>1\\\<^sup>* W] \<^sup>*\\\<^sup>* [t \<^sup>1\\\<^sup>* W])"
                by (metis (full_types) "1" Con_X_Wt Con_tW P.arr_resid P.coinitialI
                    P.paths_in_rts_axioms P.sources_resid P.targets_resid_sym
                    paths_in_rts.Con_sym paths_in_rts.Resid1x_as_Resid paths_in_rts.conI\<^sub>P)
              ultimately show ?thesis
                by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.coinitial_char(1))
            qed
          qed
          thus ?thesis
            using tX_W_eq by argo
        qed
        show "?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W \<^sup>*\<frown>\<^sup>* [?u_W] \<^sup>*\\\<^sup>* ?tX_W"
          using NPath_t'X'_W'__tX_W
          by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.Con_imp_Arr_Resid
              P.Con_sym P.Srcs_Resid 1)
      qed
      have Con_Z'_vW': "?Z' \<^sup>*\<frown>\<^sup>* [?v_W']"
      proof (intro P.Con_appendI(1))
        show 1: "([t'] @ X') \<^sup>*\\\<^sup>* W' \<^sup>*\<frown>\<^sup>* [v \<^sup>1\\\<^sup>* W']"
        proof -
          have "[t' \<^sup>1\\\<^sup>* W'] @ X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']) \<^sup>*\<frown>\<^sup>* [v \<^sup>1\\\<^sup>* W']"
          proof (intro P.Con_appendI(1))
            show 2: "[t' \<^sup>1\\\<^sup>* W'] \<^sup>*\<frown>\<^sup>* [v \<^sup>1\\\<^sup>* W']"
              by (metis (no_types, lifting) P.Con_rec(1) P.Resid1x_as_Resid
                  WW' Con_t'W' Con_vW' Resid_along_NPath_preserves_reflects_Con
                  P.Con_imp_eq_Srcs t'v)
            show "X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']) \<^sup>*\<frown>\<^sup>* [v \<^sup>1\\\<^sup>* W'] \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* W']"
            proof -
              have "NPath (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t']))"
                by (metis Backward_stable NPath_Resid NPath_W'_t'X' NPath_implies_Arr
                    P.Con_imp_eq_Srcs XX')
              moreover have "P.coinitial (X' \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* [t'])) ([v \<^sup>1\\\<^sup>* W'] \<^sup>*\\\<^sup>* [t' \<^sup>1\\\<^sup>* W'])"
                by (metis (no_types, lifting) "2" Con_X'_W't' Con_t'W' P.Con_sym
                    P.arr_resid P.coinitialI P.conI\<^sub>P P.paths_in_rts_axioms
                    P.sources_resid P.targets_resid_sym paths_in_rts.Resid1x_as_Resid)
              ultimately show ?thesis
                by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.coinitial_char(1))
            qed
          qed
          thus ?thesis
            using t'X'_W'_eq by argo
        qed
        show "?tX_W \<^sup>*\\\<^sup>* ?t'X'_W' \<^sup>*\<frown>\<^sup>* [?v_W'] \<^sup>*\\\<^sup>* ?t'X'_W'"
          by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) 1
              NPath_tX_W__t'X'_W' P.Con_imp_Arr_Resid P.Con_sym P.Srcs_Resid)
      qed

      have *: "?u_W \\ ?t_W \<frown> ?v_W' \\ ?t_W"
      proof -
        have 2: "NPath (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))"
          using P.Con_imp_eq_Srcs P.Con_implies_Arr(2) XX' Con_X_Wt by auto
        have "?u_W \<^sup>1\\\<^sup>* ?Z \<frown> ?v_W' \<^sup>1\\\<^sup>* ?Z"
        proof -
          have "?u_W \<^sup>1\\\<^sup>* ?Z \<frown> ?v_W' \<^sup>1\\\<^sup>* ?Z'"
          proof -
            let ?Y = "(W \<^sup>*\\\<^sup>* ?tX) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
            let ?Y' = "(W' \<^sup>*\\\<^sup>* ?t'X') @ (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W')"
            have Y: "P.composite_of (W \<^sup>*\\\<^sup>* ?tX) (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W) ?Y"
              using P.append_is_composite_of
              by (metis (no_types, lifting) ext P.seq_char Con_tX_W__t'X'_W' Con_tX_W
                  P.Con_imp_Arr_Resid P.Con_sym P.Srcs_Resid P.Trgs_Resid_sym)
            have Y': "P.composite_of (W' \<^sup>*\\\<^sup>* ?t'X') (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W') ?Y'"
              using P.append_is_composite_of
              by (metis P.Arr_append_iff\<^sub>P P.arrI\<^sub>P P.arr_append_imp_seq Z' Con_tX_W__t'X'_W'
                  Con_t'X'_W' P.Con_imp_Arr_Resid P.Con_sym P.Trgs_Resid_sym)
            have NPath_Y: "NPath ?Y"
              by (metis NPath_Resid NPath_appendI P.Arr_append_iff\<^sub>P P.Con_imp_eq_Srcs
                  P.Con_implies_Arr(1) P.Con_sym P.Trgs_Resid_sym WW' Z Con_tX_W__t'X'_W'
                  NPath_t'X'_W'__tX_W Con_tX_W)
            have NPath_Y': "NPath ?Y'"
              by (metis NPath_Resid P.Arr_append_iff\<^sub>P P.Con_implies_Arr(1)
                  WW' Z' Con_tX_W__t'X'_W' NPath_tX_W__t'X'_W' Con_t'X'_W' NPath_appendI
                  P.Con_imp_eq_Srcs P.Trgs_Resid_sym)
            have Y_coinitial: "P.coinitial ?Y [u \<^sup>1\\\<^sup>* ?tX]"
            proof
              show "P.Arr ?Y"
                using \<open>NPath ?Y\<close> NPath_implies_Arr by blast
              show 3: "P.Arr [u \<^sup>1\\\<^sup>* ?tX]"
                by (metis P.Arr.simps(2) P.Resid.simps(1) P.Resid1x.simps(3)
                    P.ex_un_null R.con_implies_arr(1) R.not_arr_null XX' append_Cons
                    append_Nil neq_Nil_conv P.Resid1x_as_Resid')
              show "P.Srcs ?Y \<inter> P.Srcs [u \<^sup>1\\\<^sup>* ?tX] \<noteq> {}"
              proof -
                have "P.Srcs ?Y = P.Trgs ?tX"
                  using P.Con_sym Con_tX_W by auto
                also have "... = P.Srcs [u \<^sup>1\\\<^sup>* ?tX]"
                  by (metis P.Arr.simps(2) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                      P.Srcs_Resid R.not_arr_null 3)
                finally show ?thesis
                by (metis P.Arr_has_Src 3 inf_idem)
              qed
            qed
            have Y'_coinitial: "P.coinitial ?Y' [v \<^sup>1\\\<^sup>* ?t'X']"
            proof
              show "P.Arr ?Y'"
                using NPath_Y' NPath_implies_Arr by blast
              show 3: "P.Arr [v \<^sup>1\\\<^sup>* ?t'X']"
                by (metis NPath_implies_Arr P.Arr.simps(1) P.Con_implies_Arr(2)
                    P.Resid1x.simps(3) XX' append.left_neutral append_Cons list.exhaust
                    P.Con_rec(1))
              show "P.Srcs ?Y' \<inter> P.Srcs [v \<^sup>1\\\<^sup>* ?t'X'] \<noteq> {}"
              proof -
                have "P.Srcs ?Y' = P.Trgs ?t'X'"
                  using P.Con_sym Con_t'X'_W' by auto
                also have "... = P.Srcs [v \<^sup>1\\\<^sup>* ?t'X']"
                  by (metis P.Arr.simps(2) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                      P.Srcs_Resid R.not_arr_null 3)
                finally show ?thesis
                  by (metis P.Arr_has_Src 3 inf_idem)
              qed
            qed
            have Con_Y: "P.Con ?Y [u \<^sup>1\\\<^sup>* ?tX]"
              by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.coinitial_char(1)
                  NPath_Y Y_coinitial)
            have Con_Y': "P.Con ?Y' [v \<^sup>1\\\<^sup>* ?t'X']"
              by (metis NPath_Resid NPath_implies_Arr P.Arr.simps(1) P.coinitial_char(1)
                  NPath_Y' Y'_coinitial)
            have A: "?u_W \<^sup>1\\\<^sup>* ?Z \<sim> (u \<^sup>1\\\<^sup>* ?tX) \<^sup>1\\\<^sup>* ?Y"
            proof -
              have "[(u \<^sup>1\\\<^sup>* ?tX) \<^sup>1\\\<^sup>* ?Y] \<^sup>*\<sim>\<^sup>* [?u_W \<^sup>1\\\<^sup>* ?Z]"
              proof -
                have "[(u \<^sup>1\\\<^sup>* ?tX) \<^sup>1\\\<^sup>* ?Y] = ([u] \<^sup>*\\\<^sup>* ?tX) \<^sup>*\\\<^sup>* ?Y"
                  using P.Resid1x_as_Resid
                  by (metis (no_types, opaque_lifting) Con_Y Con_Z_uW Con_tX_W__t'X'_W'
                      Con_uW P.Con_append(1) P.Con_sym P.Resid.simps(1) P.cube)
                also have "([u] \<^sup>*\\\<^sup>* ?tX) \<^sup>*\\\<^sup>* ?Y \<^sup>*\<sim>\<^sup>*
                           (([u] \<^sup>*\\\<^sup>* ?tX) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* ?tX)) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
                  using Y Con_Y
                        P.resid_composite_of(3)
                          [of "W \<^sup>*\\\<^sup>* ?tX" "?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W" ?Y "[u \<^sup>1\\\<^sup>* ?tX]"]
                  by (metis P.Resid.simps(1) P.Resid1x_as_Resid P.con_char calculation)
                also have "(([u] \<^sup>*\\\<^sup>* ?tX) \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* ?tX)) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W) =
                           [?u_W] \<^sup>*\\\<^sup>* ?Z"
                  by (metis Con_Z_uW Con_tX_W Con_tX_W__t'X'_W' Con_uW P.Con_sym
                      P.Resid1x_as_Resid P.Resid_append(2) P.cube)
                also have "... = [?u_W \<^sup>1\\\<^sup>* ?Z]"
                  using Con_Z_uW P.Con_sym P.Resid1x_as_Resid by blast
                finally show ?thesis by blast
              qed
              thus ?thesis
                using P.Resid_rec(1) P.paths_in_rts_axioms P.prfx_implies_con
                      paths_in_rts.con_char P.ide_char
                by (metis P.Ide.simps(2))
            qed
            have B: "?v_W' \<^sup>1\\\<^sup>* ?Z' \<sim> (v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y'"
            proof -
              have "[(v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y'] \<^sup>*\<sim>\<^sup>* [?v_W' \<^sup>1\\\<^sup>* ?Z']"
              proof -
                have "[(v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y'] = ([v] \<^sup>*\\\<^sup>* ?t'X') \<^sup>*\\\<^sup>* ?Y'"
                  using P.Resid1x_as_Resid [of v ?t'X'] P.Resid1x_as_Resid [of "v \<^sup>1\\\<^sup>* ?t'X'" ?Y']
                  by (metis Con_Y' P.Con_sym P.Con_sym1 P.Resid1x_null P.Residx1_as_Resid)
                also have "... \<^sup>*\<sim>\<^sup>*
                           (([v] \<^sup>*\\\<^sup>* ?t'X') \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* ?t'X')) \<^sup>*\\\<^sup>* (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W')"
                  using Y Con_Y
                        P.resid_composite_of(3)
                          [of "W' \<^sup>*\\\<^sup>* ?t'X'" "?tX_W \<^sup>*\\\<^sup>* ?t'X'_W'" ?Y' "[v \<^sup>1\\\<^sup>* ?t'X']"]
                  by (metis P.conI\<^sub>P P.con_sym P.resid_composite_of(3) Y' calculation list.discI)
                also have "(([v] \<^sup>*\\\<^sup>* ?t'X') \<^sup>*\\\<^sup>* (W' \<^sup>*\\\<^sup>* ?t'X')) \<^sup>*\\\<^sup>* (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W') =
                           [?v_W'] \<^sup>*\\\<^sup>* ?Z'"
                  by (metis (no_types, opaque_lifting) Con_Z'_vW' Con_t'X'_W' Con_tX_W__t'X'_W'
                      Con_vW' P.Con_sym P.Resid1x_as_Resid P.Resid_append(2) P.cube)
                also have "[?v_W'] \<^sup>*\\\<^sup>* ?Z' = [?v_W' \<^sup>1\\\<^sup>* ?Z']"
                  using Con_Z'_vW' P.Con_sym P.Resid1x_as_Resid by blast
                finally show ?thesis by blast
              qed
              thus ?thesis
                using P.Resid_rec(1) P.paths_in_rts_axioms P.prfx_implies_con
                      paths_in_rts.con_char P.ide_char
                by (metis P.Ide.simps(2))
            qed
            have C: "u \<^sup>1\\\<^sup>* ?tX \<frown> v \<^sup>1\\\<^sup>* ?t'X'"
              by (metis NPath_implies_Arr P.Arr.simps(1) P.Resid1x.simps(3) XX'
                  append_Cons append_Nil list.exhaust)
            have par_Y_Y': "P.Srcs ?Y = P.Srcs ?Y' \<and> P.Trgs ?Y = P.Trgs ?Y'"
            proof
              show "P.Srcs ?Y = P.Srcs ?Y'"
              proof -
                have 1: "NPath (?Y \<^sup>*\\\<^sup>* ?Y') \<and> NPath (?Y' \<^sup>*\\\<^sup>* ?Y)"
                proof -
                  have "P.coinitial ?Y ?Y'"
                    using C Con_Y Con_Y' P.Con_imp_eq_Srcs P.Con_implies_Arr(1)
                          P.coinitialI\<^sub>P R.con_imp_common_source
                    by auto
                  thus ?thesis
                    using NPath_Resid P.coinitial_char(1) NPath_Y NPath_Y'
                    by presburger
                qed
                have "P.Srcs ?Y = P.Trgs ?tX"
                  using P.Con_sym Con_tX_W by auto
                also have "... = P.Srcs ?Y'"
                  by (metis (full_types) 1 NPath_implies_Arr P.Con_imp_eq_Srcs
                      P.paths_in_rts_axioms calculation paths_in_rts.Arr.simps(1))
                finally show ?thesis by blast
              qed
              show "P.Trgs ?Y = P.Trgs ?Y'"
                using Con_tX_W__t'X'_W' P.Con_sym by force
            qed
            have "(u \<^sup>1\\\<^sup>* ?tX) \<^sup>1\\\<^sup>* ?Y \<frown> (v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y'"
            proof -
              have "(u \<^sup>1\\\<^sup>* ?tX) \<^sup>1\\\<^sup>* ?Y \<frown> (v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y"
                by (metis C Con_Y NPath_Y P.Srcs.simps(2) P.Con_imp_eq_Srcs
                    Resid_along_NPath_preserves_reflects_con)
              moreover have "(v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y \<approx>\<^sub>0 (v \<^sup>1\\\<^sup>* ?t'X') \<^sup>1\\\<^sup>* ?Y'"
                using par_Y_Y' coherent R.coinitial_iff Y'_coinitial NPath_Y NPath_Y'
                      C P.Srcs.simps(2) P.coinitial_char(1) R.con_implies_arr(2)
                by presburger
              ultimately show ?thesis
                using Cong\<^sub>0_subst_right(1) by blast
            qed
            thus ?thesis
              by (meson A B Cong\<^sub>0_subst_Con ide_closed)
          qed
          moreover have 1: "?v_W' \<^sup>1\\\<^sup>* ?Z' \<approx> ?v_W' \<^sup>1\\\<^sup>* ?Z"
          proof -
            have 2: "NPath (?Z \<^sup>*\\\<^sup>* ?Z') \<and> NPath (?Z' \<^sup>*\\\<^sup>* ?Z)"
            proof -
              have "P.seq ?tX_W (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W) \<and> P.seq ?t'X'_W' (?tX_W \<^sup>*\\\<^sup>* ?t'X'_W')"
                using P.Con_sym P.arr_append_imp_seq P.arr_char Z Z' Con_tX_W__t'X'_W'
                      Con_t'X'_W' Con_tX_W
                by presburger
              hence "P.cong ?Z ?Z'"
                using P.append_is_composite_of
                by (metis P.diamond_commutes_upto_cong)
              thus ?thesis
                using Ide_implies_NPath P.ide_char by blast
            qed
            have "(?v_W' \<^sup>1\\\<^sup>* ?Z') \<approx> (?v_W' \<^sup>1\\\<^sup>* ?Z') \<^sup>1\\\<^sup>* (?Z \<^sup>*\\\<^sup>* ?Z')"
              using 2 Cong_arr_resid_NPath
              by (metis P.Arr.simps(1) P.Resid1x_as_Resid P.Resid1x_as_Resid'
                  P.Srcs.simps(2) P.Srcs_Resid R.con_implies_arr(1) R.con_sym
                  R.not_arr_null calculation NPath_implies_Arr)
            also have 3: "(?v_W' \<^sup>1\\\<^sup>* ?Z') \<^sup>1\\\<^sup>* (?Z \<^sup>*\\\<^sup>* ?Z') = (?v_W' \<^sup>1\\\<^sup>* ?Z) \<^sup>1\\\<^sup>* (?Z' \<^sup>*\\\<^sup>* ?Z)"
            proof -
              have "[(?v_W' \<^sup>1\\\<^sup>* ?Z') \<^sup>1\\\<^sup>* (?Z \<^sup>*\\\<^sup>* ?Z')] = ([?v_W'] \<^sup>*\\\<^sup>* ?Z') \<^sup>*\\\<^sup>* (?Z \<^sup>*\\\<^sup>* ?Z')"
                using P.Resid1x_as_Resid
                by (metis Con_Z'_vW' R.not_arr_null calculation Cong_imp_arr(2) P.Con_sym
                    P.Resid1x_as_Resid')
              also have "... = ([?v_W'] \<^sup>*\\\<^sup>* ?Z) \<^sup>*\\\<^sup>* (?Z' \<^sup>*\\\<^sup>* ?Z)"
                using P.cube by blast
              also have "... = [(?v_W' \<^sup>1\\\<^sup>* ?Z) \<^sup>1\\\<^sup>* (?Z' \<^sup>*\\\<^sup>* ?Z)]"
                using P.Resid1x_as_Resid
                by (metis P.Resid.simps(1) calculation P.Resid1x_as_Resid')
              finally show ?thesis by blast
            qed
            also have "(?v_W' \<^sup>1\\\<^sup>* ?Z) \<^sup>1\\\<^sup>* (?Z' \<^sup>*\\\<^sup>* ?Z) \<approx> ?v_W' \<^sup>1\\\<^sup>* ?Z"
            proof -
              have "R.sources (?v_W' \<^sup>1\\\<^sup>* ?Z) = P.Srcs (?Z' \<^sup>*\\\<^sup>* ?Z)"
                by (metis (no_types, lifting) Cong_imp_arr(2) P.Srcs.simps(2)
                    R.not_arr_null calculation P.Con_imp_eq_Srcs P.Resid1x_as_Resid')
              thus ?thesis
                using 2 3 Cong\<^sub>0_reflexive Cong_imp_arr(2) calculation
                      Cong_arr_resid_NPath [of "?Z' \<^sup>*\\\<^sup>* ?Z" "?v_W' \<^sup>1\\\<^sup>* ?Z"]
                by blast
            qed
            finally show ?thesis by blast
          qed
          moreover have "R.sources (?v_W' \<^sup>1\\\<^sup>* ?Z) = R.sources (?u_W \<^sup>1\\\<^sup>* ?Z)"
          proof -
            have "R.sources ((v \<^sup>1\\\<^sup>* W') \<^sup>1\\\<^sup>* ?Z) = P.Srcs (([v] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ?Z)"
              using P.Resid1x_as_Resid
              by (metis P.Resid1x_as_Resid' P.Srcs.simps(2) R.not_arr_null
                  Con_vW' calculation(2) Cong_imp_arr(2))
            also have "... = P.Trgs ?Z"
              by (metis R.not_arr_null 1 Con_vW' Cong_imp_arr(2) P.Resid1x_as_Resid
                  P.Resid1x_as_Resid' P.Srcs_Resid)
            also have "... = P.Srcs (([u] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ?Z)"
              by (metis Con_Z_uW P.Con_sym P.Resid1x_as_Resid P.Srcs_Resid Con_uW)
            also have "... = R.sources ((u \<^sup>1\\\<^sup>* W) \<^sup>1\\\<^sup>* ?Z)"
              by (metis Con_Z_uW P.Con_sym P.Resid1x_as_Resid P.Srcs.simps(2) Con_uW)
            finally show ?thesis by blast
          qed
          ultimately show ?thesis
            using Cong_reflexive R.con_implies_arr(1)
                  Cong_subst(1)
                    [of "?u_W \<^sup>1\\\<^sup>* ?Z" "?u_W \<^sup>1\\\<^sup>* ?Z" "?v_W' \<^sup>1\\\<^sup>* ?Z'" "?v_W' \<^sup>1\\\<^sup>* ?Z"]
            by blast
        qed
        hence 1: "[?u_W] \<^sup>*\\\<^sup>* ?Z \<^sup>*\<frown>\<^sup>* [?v_W'] \<^sup>*\\\<^sup>* ?Z"
          using P.Con_rec(1) P.Resid1x_as_Resid' R.null_is_zero(2)
                P.Con_sym P.Resid1x_as_Resid R.conE
          by (metis Con_Z_uW)
        moreover have "[?u_W] \<^sup>*\\\<^sup>* ?Z =
                       (([?u_W] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
          using Z_eq
                P.Resid_append(2)
                  [of "[?t_W]" "(X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)" "[?u_W]"]
          by (metis (no_types, lifting) Con_X_Wt Con_Z_uW Con_tX_W Con_tX_W__t'X'_W'
              P.Con_append(2) P.Con_sym P.Resid_append(2) not_Cons_self2 tX_W_eq)
        moreover have "[?v_W'] \<^sup>*\\\<^sup>* ?Z =
                       (([?v_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
        proof -
          have "[?v_W'] \<^sup>*\\\<^sup>* ?Z = [?v_W'] \<^sup>*\\\<^sup>* ([?t_W] @ ((X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)))"
            using Z_eq by simp
          also have "... = ([?v_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* ((X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W))"
            using P.Resid_append(2)
                    [of "[?t_W]" "(X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t])) @ (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)" "[?v_W']"]
            by (metis 1 Con_X_Wt P.null_char P.null_is_zero(2) Z_eq
                append_is_Nil_conv neq_Nil_conv)
          also have "... = (([?v_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
            by (metis Con_X_Wt Con_tX_W__t'X'_W' P.Con_appendI(2) P.Con_sym P.Resid.simps(1)
                P.Resid_append(2))
          finally show ?thesis by blast
        qed
        ultimately
        have "(([?u_W] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W) \<^sup>*\<frown>\<^sup>*
              (([?v_W'] \<^sup>*\\\<^sup>* [?t_W]) \<^sup>*\\\<^sup>* (X \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [t]))) \<^sup>*\\\<^sup>* (?t'X'_W' \<^sup>*\\\<^sup>* ?tX_W)"
          by simp
        hence "[?u_W] \<^sup>*\\\<^sup>* [?t_W] \<^sup>*\<frown>\<^sup>* [?v_W'] \<^sup>*\\\<^sup>* [?t_W]"
          by (metis P.Resid.simps(1) P.cube)
        thus ?thesis
          by (metis P.Con_sym P.Resid.simps(1,3))
      qed

      have \<T>: "is_Cong_class \<T> \<and> ?t_W \<in> \<T>"
      proof -
        have "t \<approx> ?t_W"
          by (metis (lifting) ext Cong_arr_resid_NPath Cong_imp_arr(1)
              P.Con_imp_eq_Srcs P.Srcs.simps(2) P.Srcs_append
              P.ex_un_null WW' Z_eq append_Cons append_is_Nil_conv neq_Nil_conv tt')
        thus ?thesis
          by (metis Con_char Cong_closure_props(1) is_Cong_classE assms tu)
      qed
      have \<U>: "is_Cong_class \<U> \<and> ?u_W \<in> \<U>"
      proof -
        have "u \<approx> ?u_W"
          by (metis Con_Z_uW P.Arr_has_Src P.Con_imp_eq_Srcs P.Con_implies_Arr(1)
              P.Resid1x_as_Resid' P.Srcs.simps(2) R.arr_iff_has_source
              WW' Cong_arr_resid_NPath R.not_arr_null)
        thus ?thesis
          by (metis Con_char Cong_closure_props(1) is_Cong_classE assms tu)
      qed
      have \<V>: "is_Cong_class \<V> \<and> ?v_W' \<in> \<V>"
      proof -
        have "v \<approx> ?v_W'"
          by (metis Cong_arr_resid_NPath P.Con_imp_eq_Srcs P.Srcs.simps(2)
              R.con_implies_arr(2) WW' Con_vW' t'v)
        thus ?thesis
          by (metis Con_char Cong_symmetric is_Cong_classE assms t'v)
      qed
      show "(\<V> \<lbrace>\\\<rbrace> \<T>) \<lbrace>\\\<rbrace> (\<U> \<lbrace>\\\<rbrace> \<T>) = (\<V> \<lbrace>\\\<rbrace> \<U>) \<lbrace>\\\<rbrace> (\<T> \<lbrace>\\\<rbrace> \<U>)"
      proof -
        have 1: "?v_W' \\ ?t_W \<frown> ?u_W \\ ?t_W \<and>
                 (?v_W' \\ ?t_W) \\ (?u_W \\ ?t_W) = (?v_W' \\ ?u_W) \\ (?t_W \\ ?u_W)"
          by (simp add: "*" R.con_sym R.cube)
        have "(\<V> \<lbrace>\\\<rbrace> \<T>) \<lbrace>\\\<rbrace> (\<U> \<lbrace>\\\<rbrace> \<T>) = \<lbrace>(?v_W' \\ ?t_W) \\ (?u_W \\ ?t_W)\<rbrace>"
          by (metis (lifting) ext "1" Con_char arr_in_Cong_class R.arr_resid_iff_con
              R.con_implies_arr(1,2) Resid_by_members \<T> \<U> \<V> assms)
        moreover have "(\<V> \<lbrace>\\\<rbrace> \<U>) \<lbrace>\\\<rbrace> (\<T> \<lbrace>\\\<rbrace> \<U>) = \<lbrace>(?v_W' \\ ?u_W) \\ (?t_W \\ ?u_W)\<rbrace>"
          using \<T> \<U> \<V> Resid_by_members [of \<T> \<U> ?t_W ?u_W] Resid_by_members [of \<V> \<U> ?v_W' ?u_W]
                Resid_by_members [of "\<V> \<lbrace>\\\<rbrace> \<U>" "\<T> \<lbrace>\\\<rbrace> \<U>" "?v_W' \\ ?u_W" "?t_W \\ ?u_W"]
          by (metis "1" R.arr_resid_iff_con R.con_implies_arr(1,2) arr_in_Cong_class is_Cong_classI)
        ultimately show ?thesis
          using 1 by simp
      qed
    qed

    sublocale residuation Resid
      using null_char Con_sym Arr_Resid Cube
      by unfold_locales metis+

    lemma is_residuation:
    shows "residuation Resid"
      ..

    lemma arr_char:
    shows "arr \<T> \<longleftrightarrow> is_Cong_class \<T>"
      by (metis is_Cong_class_def arrI not_arr_null null_char Cong_class_memb_is_arr
          Con_char R.arrE arrE arr_resid conI)

    lemma ide_char:
    shows "ide \<U> \<longleftrightarrow> arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {}"
    proof
      show "ide \<U> \<Longrightarrow> arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {}"
        by (metis Cong\<^sub>0_reflexive Cong_class_memb_is_arr arr_in_Cong_class
            rep_in_Cong_class R.arrE Resid_by_members arr_char disjoint_iff ideE
            ide_implies_arr elements_are_arr)
      show "arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {} \<Longrightarrow> ide \<U>"
      proof -
        assume \<U>: "arr \<U> \<and> \<U> \<inter> \<NN> \<noteq> {}"
        obtain u where u: "R.arr u \<and> u \<in> \<U> \<inter> \<NN>"
          using \<U> arr_char
          by (metis IntI Cong_class_memb_is_arr disjoint_iff)
        show ?thesis
          by (metis IntD1 IntD2 Cong_class_eqI Cong_closure_props(4) arr_in_Cong_class
              is_Cong_classI Resid_by_members \<U> arrE arr_char disjoint_iff ideI
              Cong_class_eqI' R.arrE u)
      qed
    qed

    lemma ide_char':
    shows "ide \<A> \<longleftrightarrow> arr \<A> \<and> \<A> \<subseteq> \<NN>"
      by (metis Int_absorb2 Int_emptyI Cong_class_memb_Cong_rep Cong_closure_props(1)
          ide_char not_arr_null null_char normal_is_Cong_closed arr_char subsetI)

    lemma con_char\<^sub>Q\<^sub>C\<^sub>N:
    shows "con \<T> \<U> \<longleftrightarrow>
           is_Cong_class \<T> \<and> is_Cong_class \<U> \<and> (\<exists>t u. t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u)"
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
      by (meson assms Cong_subst(1) is_Cong_classE con_char\<^sub>Q\<^sub>C\<^sub>N)

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
          by (meson Cong_closure_props(4) Cong_symmetric R.coinitialE R.con_imp_coinitial
              ta)
        thus "\<T> \<lbrace>\\\<rbrace> \<A> = \<T>"
          using ta
          by (metis Cong_class_eqI Cong_class_memb_Cong_rep Cong_class_rep con con_char\<^sub>Q\<^sub>C\<^sub>N)
      qed
      show "\<And>\<T>. arr \<T> \<Longrightarrow> ide (trg \<T>)"
        by (metis Cong\<^sub>0_reflexive Resid_by_members disjoint_iff ide_char Cong_class_memb_is_arr
            arr_in_Cong_class is_Cong_class_def arr_char R.arrE R.arr_resid resid_arr_self)
      show "\<And>\<A> \<T>. \<lbrakk>ide \<A>; con \<A> \<T>\<rbrakk> \<Longrightarrow> ide (\<A> \<lbrace>\\\<rbrace> \<T>)"
        by (metis 1 arrE arr_resid con_sym ideE ideI cube)
      show "\<And>\<T> \<U>. con \<T> \<U> \<Longrightarrow> \<exists>\<A>. ide \<A> \<and> con \<A> \<T> \<and> con \<A> \<U>"
      proof -
        fix \<T> \<U>
        assume \<T>\<U>: "con \<T> \<U>"
        obtain t u where tu: "\<T> = \<lbrace>t\<rbrace> \<and> \<U> = \<lbrace>u\<rbrace> \<and> t \<frown> u"
          using \<T>\<U> con_char\<^sub>Q\<^sub>C\<^sub>N arr_char
          by (metis Cong_class_memb_Cong_rep Cong_class_eqI Cong_class_rep)
        obtain a where a: "a \<in> R.sources t"
          using \<T>\<U> tu R.con_implies_arr(1) R.arr_iff_has_source by blast
        have "ide \<lbrace>a\<rbrace> \<and> con \<lbrace>a\<rbrace> \<T> \<and> con \<lbrace>a\<rbrace> \<U>"
        proof (intro conjI)
          have 2: "a \<in> \<NN>"
            using \<T>\<U> tu a arr_char ide_closed R.sources_def by force
          show 3: "ide \<lbrace>a\<rbrace>"
            using \<T>\<U> tu 2 a ide_char arr_char con_char\<^sub>Q\<^sub>C\<^sub>N
            by (metis IntI arr_in_Cong_class is_Cong_classI empty_iff elements_are_arr)
          show "con \<lbrace>a\<rbrace> \<T>"
            using \<T>\<U> tu 2 3 a ide_char arr_char con_char\<^sub>Q\<^sub>C\<^sub>N
            by (metis arr_in_Cong_class R.composite_of_source_arr
                R.composite_of_def R.prfx_implies_con R.con_implies_arr(1))
          show "con \<lbrace>a\<rbrace> \<U>"
            using \<T>\<U> tu a ide_char arr_char con_char\<^sub>Q\<^sub>C\<^sub>N
            by (metis arr_in_Cong_class R.composite_of_source_arr R.con_prfx_composite_of
                is_Cong_classI R.con_implies_arr(1) R.con_implies_arr(2))
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
          by (meson Resid_by_members ide_implies_arr con_char\<^sub>Q\<^sub>C\<^sub>N arr_resid_iff_con)
        obtain v u' where vu': "v \<in> \<V> \<and> u' \<in> \<U> \<and> v \<frown> u' \<and> \<V> \<lbrace>\\\<rbrace> \<U> = \<lbrace>v \\ u'\<rbrace>"
          by (meson R.con_sym Resid_by_members \<U>\<V> con_char\<^sub>Q\<^sub>C\<^sub>N)
        have 1: "u \<approx> u'"
          using \<U>\<V> tu vu'
          by (meson Cong_class_membs_are_Cong con_char\<^sub>Q\<^sub>C\<^sub>N)
        obtain W W' where WW': "NPath W \<and> NPath W' \<and> u \<^sup>1\\\<^sup>* W \<approx>\<^sub>0 u' \<^sup>1\\\<^sup>* W'"
          using 1 by auto
        have 2: "((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W)) \<frown>
                 ((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) \\ ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W'))"
        proof -
          have "((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W)) \<in> \<NN>"
          proof -
            have "t \\ u \<in> \<NN>"
              using tu arr_in_Cong_class R.arr_resid_iff_con \<T>\<U> ide_char' by blast
            hence "NPath ([t \\ u] \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u]))"
              by (metis Cong\<^sub>0_imp_con NPath_Resid_single_Arr P.null_char
                  R.null_is_zero(2)  WW' P.Con_imp_Arr_Resid P.Resid1x_as_Resid'
                  P.Srcs_Resid_Arr_single R.conE P.con_sym_ax R.sources_resid tu)
            moreover have "P.Srcs ([t \\ u] \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) =
                           P.Srcs (([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W))"
            proof -
              have "P.Srcs ([t \\ u] \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) = P.Trgs (W \<^sup>*\\\<^sup>* [u])"
                by (metis NPath_implies_Arr P.Arr.simps(1) P.Srcs_Resid calculation)
              also have "... = P.Trgs ([u] \<^sup>*\\\<^sup>* W)"
                by (metis P.Trgs_Resid_sym)
              also have "... = P.Srcs (([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W))"
                by (metis Cong\<^sub>0_imp_con P.Resid1x.simps(2) P.Resid1x_as_Resid'
                    P.Srcs_Resid P.paths_in_rts_axioms R.not_con_null(2)
                    R.null_is_zero(1) WW' paths_in_rts.Resid1x_as_Resid)
              finally show ?thesis by blast
            qed
            ultimately
            have "NPath (([t \\ u] \<^sup>*\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \<^sup>*\\\<^sup>* (([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W)))"
              by (metis NPath_Resid NPath_implies_Arr P.Arr_has_Src P.Con_imp_Arr_Resid
                  P.Srcs.simps(1))
            hence "NPath [((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))]"
              using P.Resid1x_as_Resid
              by (metis P.Arr.simps(1) P.Resid.simps(1) P.Resid1x.simps(2) P.ex_un_null
                  NPath_def)
            thus ?thesis
              by (simp add: NPath_def)
          qed
          moreover have "R.sources (((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))) =
                         R.sources (((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) \\ ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W')))"
          proof -
            have "R.sources (((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))) =
                  R.targets ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))"
              using R.arr_resid_iff_con elements_are_arr R.sources_resid calculation by blast
            also have "... = R.targets ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W'))"
              by (metis R.targets_resid_sym R.conI)
            also have "... = R.sources (((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) \\ ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W')))"
            proof -
              have "R.con ((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W'))"
              proof -
                have "(u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W') \<in> \<NN>"
                  using WW' by fastforce
                moreover have "R.sources ((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) =
                               R.sources ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W'))"
                proof -
                  have "R.sources ((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) = P.Trgs (W' \<^sup>*\\\<^sup>* [u'])"
                    by (metis (no_types, lifting) ext Cong_imp_arr(2) NPath_Resid
                        P.Arr.simps(2) P.Con_imp_eq_Srcs P.Trgs.simps(1)
                        R.arr_iff_has_source R.arr_resid R.con_implies_arr(2) R.not_arr_null
                        R.sources_resid WW' Cong_arr_resid_NPath P.Resid1x_as_Resid'
                        P.Srcs_Resid_Arr_single P.sources_Resid1x vu')
                  also have "... = R.targets (u' \<^sup>1\\\<^sup>* W')"
                    by (metis Cong\<^sub>0_imp_con P.Con_sym P.Con_sym1 P.Resid1x_as_Resid
                        P.Residx1_as_Resid P.Trgs_Resid_sym P.paths_in_rts_axioms
                        R.not_con_null(2) WW' paths_in_rts.Trgs.simps(2))
                  also have "... = R.sources ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W'))"
                    by (simp add: Cong\<^sub>0_imp_con WW')
                  finally show ?thesis by blast
                qed
                ultimately show ?thesis
                  by (metis Cong_closure_props(4) Cong_imp_arr(2) R.conI R.not_arr_null)

              qed
              thus ?thesis
                using R.arr_resid_iff_con elements_are_arr R.sources_resid
                by presburger
            qed
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            by (metis Cong_closure_props(4) P.Con_rec(1) P.Con_sym1 P.Resid1x.simps(2)
                P.Residx1_as_Resid R.arr_def R.not_con_null(1) Cong_imp_arr(2))
        qed
        moreover have "t \\ u \<approx> ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) \\ ((u' \<^sup>1\\\<^sup>* W') \\ (u \<^sup>1\\\<^sup>* W))"
        proof -
          have "NPath (W \<^sup>*\\\<^sup>* [u])"
            by (metis Cong\<^sub>0_imp_con P.Arr.simps(2) P.Con_imp_eq_Srcs R.null_is_zero(2)
                WW' NPath_Resid P.Resid1x_as_Resid' R.conE R.con_implies_arr(2) tu)
          moreover have 1: "NPath (([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W))"
            by (metis WW' NPath_def P.Arr.simps(2) P.Resid.simps(3) elements_are_arr
                R.conE R.null_is_zero(2) empty_set empty_subsetI insert_subset list.simps(15)
                Cong\<^sub>0_imp_con P.Resid1x_as_Resid P.Resid1x_as_Resid')
          moreover have "R.sources (t \\ u) = P.Srcs (W \<^sup>*\\\<^sup>* [u])"
            by (metis NPath_def P.Arr.simps(1) P.Srcs_Resid_Arr_single R.sources_resid
                calculation(1) tu)
          moreover have "R.sources ((t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])) =
                         P.Srcs (([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W))"
            by (metis "2" P.Con_imp_eq_Srcs P.Resid1x.simps(2) P.Resid1x_as_Resid
                P.Resid1x_as_Resid' P.Srcs.simps(2) R.conE R.ex_un_null R.null_is_zero(2))
          ultimately show ?thesis
            using Cong_arr_resid_NPath [of "W \<^sup>*\\\<^sup>* [u]" "t \\ u"]
                  Cong_arr_resid_NPath
                    [of "([u'] \<^sup>*\\\<^sup>* W') \<^sup>*\\\<^sup>* ([u] \<^sup>*\\\<^sup>* W)" "(t \\ u) \<^sup>1\\\<^sup>* (W \<^sup>*\\\<^sup>* [u])"]
            by (metis (full_types, lifting) ext Backward_stable Cong_closure_props(4)
                NPath_implies_Arr P.Arr.simps(2) P.Resid.simps(1) P.Resid1x.simps(2)
                P.Resid1x_as_Resid P.Resid1x_null P.Srcs.simps(2) P.ex_un_null
                R.arr_resid_iff_con R.con_def WW' Cong_closure_props(2))
        qed
        moreover have "v \\ u' \<approx> ((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) \\ ((u \<^sup>1\\\<^sup>* W) \\ (u' \<^sup>1\\\<^sup>* W'))"
        proof -
          have "NPath (W' \<^sup>*\\\<^sup>* [u'])"
            by (metis "1" Cong\<^sub>0_imp_con Cong_imp_arr(2) P.Arr.simps(2) P.Con_imp_eq_Srcs
                R.null_is_zero(2) WW' NPath_Resid P.Resid1x_as_Resid' R.conE)
          moreover have 1: "NPath (([u] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W'))"
            using WW'
            by (metis NPath_def P.Arr.simps(2) P.Resid.simps(3) elements_are_arr
                R.conE R.null_is_zero(2) empty_set empty_subsetI insert_subset list.simps(15)
                Cong\<^sub>0_imp_con P.Resid1x_as_Resid P.Resid1x_as_Resid')
          moreover have "R.sources (v \\ u') = P.Srcs (W' \<^sup>*\\\<^sup>* [u'])"
            by (metis NPath_implies_Arr P.Arr.simps(1) R.sources_resid calculation(1)
                P.Srcs_Resid_Arr_single vu')
          moreover have "R.sources ((v \\ u') \<^sup>1\\\<^sup>* (W' \<^sup>*\\\<^sup>* [u'])) =
                         P.Srcs (([u] \<^sup>*\\\<^sup>* W) \<^sup>*\\\<^sup>* ([u'] \<^sup>*\\\<^sup>* W'))"
            by (metis "2" P.Con_imp_eq_Srcs P.Resid1x.simps(2) P.Resid1x_as_Resid
                P.Resid1x_as_Resid' P.Srcs.simps(2) R.conE R.ex_un_null R.null_is_zero(2))
          ultimately show ?thesis
            using Cong_arr_resid_NPath
            by (metis (no_types, lifting) ext "2" Cong\<^sub>0_reflexive Cong_closure_props(4)
                Cong_transitive P.Con_imp_eq_Srcs P.Srcs.simps(2)
                R.arr_resid_iff_con R.con_implies_arr(2) WW' CongI Cong_imp_arr(1)
                P.Con_rec(1))
        qed
        ultimately show "con (\<T> \<lbrace>\\\<rbrace> \<U>) (\<V> \<lbrace>\\\<rbrace> \<U>)"
          using tu vu' con_char\<^sub>Q\<^sub>C\<^sub>N is_Cong_classI Cong_class_def by auto
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
          by (metis Con_char Cong_class_eqI Cong_class_memb_Cong_rep Cong_class_rep
              \<T>\<U> ide_char not_arr_null null_char)
        have "t \<approx>\<^sub>0 u"
          using tu \<T>\<U> Resid_by_members [of \<T> \<U> t u] Resid_by_members [of \<U> \<T> u t] R.con_sym
          by (metis (full_types) arr_in_Cong_class R.con_implies_arr(1-2)
              is_Cong_classI ide_char' R.arr_resid_iff_con subset_iff)+
        hence "t \<approx> u"
          using Cong\<^sub>0_implies_Cong by simp
        thus "\<T> = \<U>"
          by (simp add: Cong_class_eqI tu)
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
          using ide_closed normal_is_Cong_closed by blast
        show "arr ?\<A>"
        proof -
          have "is_Cong_class ?\<A>"
          proof
            show "?\<A> \<noteq> {}"
              by (metis (mono_tags, lifting) Collect_empty_eq Cong_class_def Cong_imp_arr(1)
                  is_Cong_class_def sources_are_Cong R.arr_iff_has_source R.sources_def
                  \<T> arr_char mem_Collect_eq)
            show "\<And>a a'. \<lbrakk>a \<in> ?\<A>; a' \<approx> a\<rbrakk> \<Longrightarrow> a' \<in> ?\<A>"
              using Cong_transitive by blast
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
                by (meson IntD1 Cong_class_membs_are_Cong in_sources_respects_Cong)
              thus "a \<approx> a'"
                by (meson Cong_symmetric Cong_transitive b b')
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
          by (metis Cong_class_is_nonempty R.arr_iff_has_source empty_subsetI
                    Cong_class_memb_is_arr subsetI subset_antisym)
        have "t \<in> \<T> \<and> a \<in> {a. \<exists>t a'. t \<in> \<T> \<and> a' \<in> R.sources t \<and> a' \<approx> a} \<and> t \<frown> a"
          using a Cong_reflexive R.sources_def R.con_implies_arr(2) by fast
        thus ?thesis
          using \<T> 1 arr_char con_char\<^sub>Q\<^sub>C\<^sub>N [of \<T> ?\<A>] by auto
      qed
      ultimately have "arr \<T> \<Longrightarrow> ?\<A> \<in> sources \<T>"
        using sources_def by blast
      thus ?thesis
        using "1" ide_char sources_char\<^sub>W\<^sub>E by auto
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
            by (meson Cong_closure_props(3) forward_stable elements_are_arr
                \<B> arr_char R.con_imp_coinitial is_Cong_classE ide_char' R.arrE
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
           apply (metis IntI Cong_class_eqI' R.arr_resid_iff_con is_Cong_classI empty_iff
                        set_eq_subset)
          by (meson arr_in_Cong_class R.arr_resid_iff_con subsetD)
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

    sublocale quot: simulation_to_extensional_rts resid Resid quot
    proof
      show "\<And>t. \<not> R.arr t \<Longrightarrow> \<lbrace>t\<rbrace> = null"
        using Cong_class_def Cong_imp_arr(1) null_char by force
      show "\<And>t u. t \<frown> u \<Longrightarrow> con \<lbrace>t\<rbrace> \<lbrace>u\<rbrace>"
        by (meson arr_in_Cong_class is_Cong_classI R.con_implies_arr(1-2) con_char\<^sub>Q\<^sub>C\<^sub>N)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<lbrace>t \\ u\<rbrace> = \<lbrace>t\<rbrace> \<lbrace>\\\<rbrace> \<lbrace>u\<rbrace>"
        by (metis arr_in_Cong_class is_Cong_classI R.con_implies_arr(1-2) Resid_by_members)
    qed

    lemma quotient_is_simulation:
    shows "simulation resid Resid quot"
      ..

    lemma ide_quot_normal:
    assumes "t \<in> \<NN>"
    shows "ide (quot t)"
      using assms
      by (metis IntI arr_in_Cong_class elements_are_arr empty_iff
          quot.preserves_reflects_arr ide_char)

    lemma quotient_reflects_con:
    assumes "con \<lbrace>t\<rbrace> \<lbrace>u\<rbrace>" and "R.coinitial t u"
    shows "R.con t u"
      using assms
      by (meson R.coinitialE arr_in_Cong_class con_imp_coinitial_members_are_con)

    text\<open>
      If a simulation \<open>F\<close> from \<open>R\<close> to an extensional RTS \<open>B\<close> maps every element of \<open>\<NN>\<close>
      to an identity, then it has a unique extension along the quotient map.
    \<close>

    lemma is_couniversal:
    assumes "extensional_rts B"
    and "simulation resid B F"
    and "\<And>t. t \<in> \<NN> \<Longrightarrow> residuation.ide B (F t)"
    shows "\<exists>!F'. simulation Resid B F' \<and> F' \<circ> quot = F"
    proof -
      interpret B: extensional_rts B
        using assms(1) simulation.axioms(2) by blast
      interpret Bp: paths_in_rts B ..
      interpret F: simulation resid B F
        using assms by blast
      have *: "\<And>V. NPath V \<Longrightarrow> \<forall>t. P.coinitial [t] V \<longrightarrow> F (t \<^sup>1\\\<^sup>* V) = F t"
      proof -
        fix V
        assume V: "NPath V"
        show "\<forall>t. P.coinitial [t] V \<longrightarrow> F (t \<^sup>1\\\<^sup>* V) = F t"
        proof (induct V rule: NPath_induct)
          show "NPath V" by fact
          show "\<And>v. v \<in> \<NN> \<Longrightarrow> \<forall>t. P.coinitial [t] [v] \<longrightarrow> F (t \<^sup>1\\\<^sup>* [v]) = F t"
          proof (intro allI impI)
            fix t v
            assume v: "v \<in> \<NN>" and tv: "P.coinitial [t] [v]"
            have "F (t \<^sup>1\\\<^sup>* [v]) = F (t \\ v)"
              by auto
            also have "... = B (F t) (F v)"
              by (metis F.preserves_resid Cong_closure_props(4) Cong_imp_arr(2)
                  P.Srcs.simps(2) P.coinitial_char(1) R.conI R.not_arr_null tv v)
            also have "... = F t"
              using v assms(3)
              by (metis B.resid_arr_ide F.preserves_reflects_arr Cong_closure_props(4)
                  P.Srcs.simps(2) P.coinitial_char(1) \<open>F (t \ v) = B (F t) (F v)\<close>
                  Cong_imp_arr(2) B.arr_resid_iff_con tv)
            finally show "F (t \<^sup>1\\\<^sup>* [v]) = F t" by blast
          qed
          show "\<And>v V. \<lbrakk>v \<in> \<NN>; NPath V; R.targets v \<subseteq> P.Srcs V;
                        \<forall>t. P.coinitial [t] V \<longrightarrow> F (t \<^sup>1\\\<^sup>* V) = F t\<rbrakk>
                           \<Longrightarrow> \<forall>t. P.coinitial [t] (v # V) \<longrightarrow> F (t \<^sup>1\\\<^sup>* (v # V)) = F t"
          proof (intro allI impI)
            fix v V t
            assume v: "v \<in> \<NN>" and V: "NPath V" and vV: "R.targets v \<subseteq> P.Srcs V"
            assume ind: "\<forall>t. P.coinitial [t] V \<longrightarrow> F (t \<^sup>1\\\<^sup>* V) = F t"
            assume t: "P.coinitial [t] (v # V)"
            show "F (t \<^sup>1\\\<^sup>* (v # V)) = F t"
            proof -
              have "F (t \<^sup>1\\\<^sup>* (v # V)) = F ((t \\ v) \<^sup>1\\\<^sup>* V)"
                by (metis P.Arr.simps(1) P.Resid1x.simps(3) V neq_Nil_conv
                    NPath_implies_Arr)
              also have "... = F (t \\ v)"
                using ind
                by (metis F.extensionality P.Arr.simps(2) P.Resid1x_as_Resid'
                    P.Trgs.simps(2) P.conI\<^sub>P coherent elements_are_arr R.not_arr_null
                    V NPath_implies_Arr P.seq_implies_Trgs_eq_Srcs R.arrI R.conI
                    P.con_imp_coinitial R.sources_resid v vV)
              also have "... = F t"
                by (metis B.resid_arr_ide F.preserves_con F.preserves_resid
                    resid_along_normal_preserves_reflects_con P.Arr.simps(2)
                    P.Srcs_simp\<^sub>P R.arr_def assms(3) list.sel(1) P.coinitial_char(1)
                    R.arr_resid_iff_con t v)
              finally show ?thesis by blast
            qed
          qed
        qed
      qed
      have 1: "\<And>t u. t \<approx> u \<Longrightarrow> F t = F u"
      proof -
        fix t u
        assume Cong: "t \<approx> u"
        obtain V W where VW: "NPath V \<and> NPath W \<and> t \<^sup>1\\\<^sup>* V \<approx>\<^sub>0 u \<^sup>1\\\<^sup>* W"
          using Cong by blast
        have "B.cong (F t) (F u)"
          using assms(3) VW * B.not_ide_null F.extensionality P.Resid1x_as_Resid'
                P.conI\<^sub>P P.con_imp_coinitial R.con_def R.not_arr_null R.not_con_null(2)
                Cong\<^sub>0_imp_con F.preserves_resid
          by (metis (no_types, lifting) ext)
        thus "F t = F u"
          using B.extensionality by blast
      qed
      let ?F' = "\<lambda>\<T>. if arr \<T> then F (Cong_class_rep \<T>) else B.null"
      interpret F': simulation Resid B ?F'
      proof
        show "\<And>\<T>. \<not> arr \<T> \<Longrightarrow> ?F' \<T> = B.null"
          by argo
        fix \<T> \<U>
        assume con: "con \<T> \<U>"
        show "B.con (?F' \<T>) (?F' \<U>)"
          using con
          by (metis (full_types) 1 F.preserves_con Cong_class_memb_Cong_rep arr_char
              con_char\<^sub>Q\<^sub>C\<^sub>N)
        show "?F' (\<T> \<lbrace>\\\<rbrace> \<U>) = B (?F' \<T>) (?F' \<U>)"
        proof -
          have 2: "is_Cong_class \<T> \<and> is_Cong_class \<U>"
            using con con_char\<^sub>Q\<^sub>C\<^sub>N by auto
          obtain t u where tu: "t \<in> \<T> \<and> u \<in> \<U> \<and> t \<frown> u"
            using con con_char\<^sub>Q\<^sub>C\<^sub>N by force
          have "?F' (\<T> \<lbrace>\\\<rbrace> \<U>) = ?F' \<lbrace>t \\ u\<rbrace>"
            using tu 2 Resid_by_members by force
          also have "... = F (t \\ u)"
            by (metis tu Cong_class_memb_Cong_rep arr_in_Cong_class is_Cong_classI
                R.arr_resid \<open>\<And>y x. x \<approx> y \<Longrightarrow> F x = F y\<close> quot.preserves_reflects_arr)
          also have "... = B (F t) (F u)"
            by (simp add: tu)
          also have "... = B (?F' \<T>) (?F' \<U>)"
            by (metis (full_types) tu 1 2 Cong_class_memb_Cong_rep con
                con_implies_arr(1-2))
          finally show ?thesis by blast
        qed
      qed
      have "simulation Resid B ?F' \<and> ?F' \<circ> quot = F"
        using 1 F'.simulation_axioms F.extensionality Cong_class_memb_Cong_rep
              arr_in_Cong_class arr_char quot.preserves_reflects_arr
        by fastforce
      moreover have "\<And>F''. \<lbrakk>simulation Resid B F''; F'' \<circ> quot = F\<rbrakk> \<Longrightarrow> F'' = ?F'"
        using simulation.extensionality arr_char by force
      ultimately show ?thesis by blast
    qed

    definition ext_to_quotient
    where "ext_to_quotient B F \<equiv> THE F'. simulation Resid B F' \<and> F' \<circ> quot = F"

    lemma ext_to_quotient_props:
    assumes "extensional_rts B"
    and "simulation resid B F"
    and "\<And>t. t \<in> \<NN> \<Longrightarrow> residuation.ide B (F t)"
    shows "simulation Resid B (ext_to_quotient B F)" and "ext_to_quotient B F \<circ> quot = F"
    proof -
      have "simulation Resid B (ext_to_quotient B F) \<and> ext_to_quotient B F \<circ> quot = F"
        unfolding ext_to_quotient_def
        using assms is_couniversal [of B F]
              theI' [of "\<lambda>F'. simulation (\<lbrace>\\\<rbrace>) B F' \<and> F' \<circ> quot = F"]
        by fastforce
      thus "simulation Resid B (ext_to_quotient B F)" and "ext_to_quotient B F \<circ> quot = F"
        by auto
    qed

  end

  subsection "Identities form a Coherent Normal Sub-RTS"

  text \<open>
    We now show that the collection of identities of an RTS form a coherent normal sub-RTS,
    and that the associated congruence \<open>\<approx>\<close> coincides with \<open>\<sim>\<close>.
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
    qed

    lemma identities_form_normal_sub_rts:
    shows "normal_sub_rts resid (Collect ide)"
      ..

    interpretation coherent_normal_sub_rts resid \<open>Collect ide\<close>
    proof
      fix t U U'
      assume t: "arr t" and U: "NPath U" and U': "NPath U'"
      assume Srcs: "P.Srcs U = P.Srcs U'" and Trgs: "P.Trgs U = P.Trgs U'"
      assume sources: "sources t = P.Srcs U"
      have "P.Ide U \<and> P.Ide U'"
        using NPath_def U U' by auto
      hence "[t] \<^sup>*\\\<^sup>* U = [t] \<and> [t] \<^sup>*\\\<^sup>* U' = [t]"
        using P.Resid_Ide(1) P.Arr.simps(2) P.Con_IdeI(2) P.Resid_Arr_Ide_ind
          P.Srcs.simps(2) Srcs sources t
        by presburger
      thus "Cong\<^sub>0 (t \<^sup>1\\\<^sup>* U) (t \<^sup>1\\\<^sup>* U')"
        by (metis P.Resid1x_as_Resid last_ConsL mem_Collect_eq not_Cons_self2 prfx_reflexive t)
    qed

    lemma identities_form_coherent_normal_sub_rts:
    shows "coherent_normal_sub_rts resid (Collect ide)"
      ..
 
    (* TODO: There is undesirable notation \<^sup>*\<sim>\<^sup>*, etc. in this context. *)

    lemma Cong_iff_cong:
    shows "Cong t u \<longleftrightarrow> t \<sim> u"
    proof
      show "t \<sim> u \<Longrightarrow> Cong t u"
        by (simp add: Cong\<^sub>0_implies_Cong)
      show "Cong t u \<Longrightarrow> t \<sim> u"
      proof -
        assume 1: "Cong t u"
        obtain V W where VW: "NPath V \<and> NPath W \<and> Cong\<^sub>0 (t \<^sup>1\\\<^sup>* V) (u \<^sup>1\\\<^sup>* W)"
          using 1 by blast
        have "t \<^sup>1\\\<^sup>* V = t \<and> u \<^sup>1\\\<^sup>* W = u"
        proof -
          have "P.Ide V \<and> P.Ide W"
            using VW NPath_def by auto
          thus ?thesis
            using VW P.Resid_Ide(1)
            by (metis Cong\<^sub>0_imp_con P.Resid1x_as_Resid' P.Resid_Arr_Ide_ind conE
                list.sel(1) null_is_zero(2))
        qed
        thus "t \<sim> u"
          using VW by auto
      qed
    qed

  end

  subsection "Kernels of Consistency-Reflecting Simulations"

  text\<open>
    We may regard the set of transitions that are mapped to identities by a simulation
    as a kind of kernel of the simulation.  Here we show that if \<open>F\<close> is a
    consistency-reflecting simulation, then its kernel is a coherent normal sub-RTS of
    its domain.
  \<close>

  lemma (in simulation) kernel_is_coherent_normal_sub_rts:
  assumes "\<And>t u. \<lbrakk>A.coinitial t u; B.con (F t) (F u)\<rbrakk> \<Longrightarrow> A.con t u"
  shows "coherent_normal_sub_rts A {t. B.ide (F t)}"
  proof -
    interpret P\<^sub>A: paths_in_rts A ..
    interpret P\<^sub>B: paths_in_rts B ..
    interpret N\<^sub>A: normal_sub_rts A \<open>{t. B.ide (F t)}\<close>
    proof
      show "\<And>t. t \<in> {t. B.ide (F t)} \<Longrightarrow> A.arr t"
        using B.ide_implies_arr by blast
      show "\<And>a. A.ide a \<Longrightarrow> a \<in> {t. B.ide (F t)}"
        by fastforce
      show "\<And>u t. \<lbrakk>u \<in> {t. B.ide (F t)}; A.coinitial t u\<rbrakk> \<Longrightarrow> u \\\<^sub>A t \<in> {t. B.ide (F t)}"
      proof -
        fix u t
        assume u: "u \<in> {t. B.ide (F t)}"
        assume t: "A.coinitial t u"
        have "F u \<in> B.sources (F t)"
          using t u
          by (metis (mono_tags, lifting) A.in_sourcesE A.residuation_axioms A.rts_axioms
              B.in_sourcesI B.rts_axioms CollectD preserves_con preserves_resid
              residuation.arrE rts.coinitial_iff rts.resid_arr_ide rts.sources_resid
              rts.src_in_sources)
        hence "F u \\\<^sub>B F t \<in> B.targets (F t)"
          using B.resid_source_in_targets by blast
        thus "u \\\<^sub>A t \<in> {t. B.ide (F t)}"
          by (metis A.conI A.not_arr_null A.residuation_axioms B.conE B.in_sourcesE
              B.in_targetsE CollectI \<open>F u \<in> B.sources (F t)\<close> assms extensionality
              preserves_resid residuation.con_sym_ax t)
      qed
      show "\<And>u t. \<lbrakk>u \<in> {t. B.ide (F t)}; t \\\<^sub>A u \<in> {t. B.ide (F t)}\<rbrakk> \<Longrightarrow> t \<in> {t. B.ide (F t)}"
        by (metis A.arr_resid_iff_con B.resid_arr_ide CollectD CollectI
            \<open>\<And>t. t \<in> {t. B.ide (F t)} \<Longrightarrow> A.arr t\<close> preserves_con preserves_resid)
    qed
    interpret N\<^sub>B: normal_sub_rts B \<open>{t. B.ide t}\<close>
      by (simp add: B.identities_form_normal_sub_rts)
    let ?Fx = "\<lambda>T. if P\<^sub>A.Arr T then map F T else []"
    interpret Fx: simulation P\<^sub>A.Resid P\<^sub>B.Resid ?Fx
      using simulation_axioms lifts_to_paths by fastforce
    have *: "\<And>T. N\<^sub>A.NPath T \<Longrightarrow> N\<^sub>B.NPath (?Fx T)"
      unfolding N\<^sub>A.NPath_def N\<^sub>B.NPath_def
      apply auto
      using preserves_paths by blast
    show ?thesis
    proof
      show "\<And>t U U'. \<lbrakk>A.arr t; N\<^sub>A.NPath U; N\<^sub>A.NPath U';
                       P\<^sub>A.Srcs U = P\<^sub>A.Srcs U'; P\<^sub>A.Trgs U = P\<^sub>A.Trgs U';
                       A.sources t = P\<^sub>A.Srcs U\<rbrakk>
                         \<Longrightarrow> N\<^sub>A.Cong\<^sub>0 (P\<^sub>A.Resid1x t U) (P\<^sub>A.Resid1x t U')"
      proof
        fix t U U'
        assume t: "A.arr t" and U: "N\<^sub>A.NPath U" and U': "N\<^sub>A.NPath U'"
        assume Srcs: "P\<^sub>A.Srcs U = P\<^sub>A.Srcs U'" and Trgs: "P\<^sub>A.Trgs U = P\<^sub>A.Trgs U'"
        assume tU: "A.sources t = P\<^sub>A.Srcs U"
        have tU': "A.sources t = P\<^sub>A.Srcs U'"
          by (simp add: Srcs tU)
        have Ft: "F (P\<^sub>A.Resid1x t U) = F t"
        proof -
          have "[F (P\<^sub>A.Resid1x t U)] = ?Fx [P\<^sub>A.Resid1x t U]"
            by (simp add: N\<^sub>A.Resid_along_NPath_preserves_reflects_con P\<^sub>A.Arr_iff_Con_self U t tU)
          also have "... = ?Fx (P\<^sub>A.Resid [t] U)"
            by (metis A.arr_iff_has_target A.not_arr_null P\<^sub>A.Arr_has_Trg P\<^sub>A.Resid1x_as_Resid
                P\<^sub>A.Resid1x_as_Resid' P\<^sub>A.Trgs.simps(2) list.simps(8))
          also have "... = P\<^sub>B.Resid (?Fx [t]) (?Fx U)"
            by (meson Fx.preserves_resid P\<^sub>A.arr_char P\<^sub>A.arr_resid_iff_con calculation
                not_Cons_self2)
          also have "... = P\<^sub>B.Resid [F t] (?Fx U)"
            using calculation by auto
          also have "... = [P\<^sub>B.Resid1x (F t) (?Fx U)]"
            by (metis P\<^sub>B.Resid1x_as_Resid calculation not_Cons_self2)
          also have "... = [F t]"
          proof -
            have "P\<^sub>B.Ide (?Fx U)"
              using "*" N\<^sub>B.NPath_def U by blast
            thus ?thesis
              by (metis A.not_arr_null B.rts_axioms P\<^sub>B.Resid_Arr_Ide_ind
                  \<open>[F (P\<^sub>A.Resid1x t U)] = (if P\<^sub>A.Arr [P\<^sub>A.Resid1x t U] then map F [P\<^sub>A.Resid1x t U] else [])\<close>
                  calculation extensionality list.sel(1) list.simps(3) P\<^sub>A.Arr.simps(2)
                  paths_in_rts.Resid1x_as_Resid' paths_in_rts.intro preserves_reflects_arr)
          qed
          finally show ?thesis by blast
        qed
        have Ft': "F (P\<^sub>A.Resid1x t U') = F t"
        proof -
          have 1: "[F (P\<^sub>A.Resid1x t U')] = ?Fx [P\<^sub>A.Resid1x t U']"
            using N\<^sub>A.Resid_along_NPath_preserves_reflects_con P\<^sub>A.Arr_iff_Con_self U' t tU'
            by simp
          also have "... = ?Fx (P\<^sub>A.Resid [t] U')"
            by (metis A.arr_iff_has_target A.not_arr_null P\<^sub>A.Arr_has_Trg P\<^sub>A.Resid1x_as_Resid
                P\<^sub>A.Resid1x_as_Resid' P\<^sub>A.Trgs.simps(2) list.simps(8))
          also have "... = P\<^sub>B.Resid (?Fx [t]) (?Fx U')"
            by (meson Fx.preserves_resid P\<^sub>A.arr_char P\<^sub>A.arr_resid_iff_con calculation
                not_Cons_self2)
          also have "... = P\<^sub>B.Resid [F t] (?Fx U')"
            using calculation by auto
          also have "... = [P\<^sub>B.Resid1x (F t) (?Fx U')]"
            by (metis P\<^sub>B.Resid1x_as_Resid calculation not_Cons_self2)
          also have "... = [F t]"
          proof -
            have "P\<^sub>B.Ide (?Fx U')"
              using "*" N\<^sub>B.NPath_def U' by blast
            thus ?thesis
              by (metis 1 A.not_arr_null B.rts_axioms P\<^sub>A.paths_in_rts_axioms
                  P\<^sub>B.Resid_Arr_Ide_ind calculation extensionality list.sel(1) list.simps(3)
                  paths_in_rts.Arr.simps(2) paths_in_rts.Resid1x_as_Resid' paths_in_rts.intro
                  preserves_reflects_arr)
          qed
          finally show ?thesis by blast
        qed
        have "A.con (P\<^sub>A.Resid1x t U) (P\<^sub>A.Resid1x t U')"
          using assms t Ft Ft'
          by (metis A.coinitial_iff A.not_arr_null P\<^sub>A.Resid1x_as_Resid'
              P\<^sub>A.sources_Resid1x Trgs preserves_reflects_arr A.arrE
              simulation.preserves_con simulation_axioms)
        show "P\<^sub>A.Resid1x t U \\\<^sub>A P\<^sub>A.Resid1x t U' \<in> {t. B.ide (F t)}"
          by (simp add: B.prfx_reflexive Ft Ft' \<open>P\<^sub>A.Resid1x t U \<frown>\<^sub>A P\<^sub>A.Resid1x t U'\<close> t)
        show "P\<^sub>A.Resid1x t U' \\\<^sub>A P\<^sub>A.Resid1x t U \<in> {t. B.ide (F t)}"
          by (simp add: A.con_sym B.prfx_reflexive Ft Ft' \<open>P\<^sub>A.Resid1x t U \<frown>\<^sub>A P\<^sub>A.Resid1x t U'\<close> t)
      qed
    qed
  qed

  section "Composite Completion"

  text \<open>
    The RTS of paths in an RTS factors via the coherent normal sub-RTS of identity
    paths into an extensional RTS with composites, which can be regarded as a
    ``composite completion'' of the original RTS.
    Although we could have shown this fact much earlier, we have delayed proving it so that
    we could simply obtain it as a special case of our general quotient result without
    redundant work.
  \<close>

  locale composite_completion =
    R: rts R
  for R :: "'a resid"
  begin

    type_synonym 'b arr = "'b list set"

    sublocale P: paths_in_rts R ..
    sublocale N: coherent_normal_sub_rts P.Resid \<open>Collect P.ide\<close>
      using P.identities_form_coherent_normal_sub_rts by blast
    sublocale Q: quotient_by_coherent_normal P.Resid \<open>Collect P.ide\<close> ..

    notation N.Cong_class (\<open>\<lbrace>_\<rbrace>\<close>)

    definition resid    (infix \<open>\<lbrace>\<^sup>*\\<^sup>*\<rbrace>\<close> 70)
    where "resid \<equiv> Q.Resid"

    sublocale extensional_rts resid
      unfolding resid_def
      using Q.extensional_rts_axioms by simp

    notation con      (infix \<open>\<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace>\<close> 50)
    notation prfx     (infix \<open>\<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace>\<close> 50)

    notation P.Resid  (infix \<open>\<^sup>*\\<^sup>*\<close> 70)
    notation P.Con    (infix \<open>\<^sup>*\<frown>\<^sup>*\<close> 50)
    notation N.Cong   (infix \<open>\<^sup>*\<approx>\<^sup>*\<close> 50)
    notation N.Cong\<^sub>0  (infix \<open>\<^sup>*\<approx>\<^sub>0\<^sup>*\<close> 50)
    notation N.Cong_class (\<open>\<lbrace>_\<rbrace>\<close>)

    (* TODO: Delete? *)
    lemma P_ide_iff_NPath:
    shows "N.P.ide T \<longleftrightarrow> N.NPath T"
      using N.NPath_def N.P.ide_char N.ide_closed N.Ide_implies_NPath by auto

    lemma Cong_eq_Cong\<^sub>0:
    shows "T \<^sup>*\<approx>\<^sup>* T' \<longleftrightarrow> T \<^sup>*\<approx>\<^sub>0\<^sup>* T'"
      by (simp add: P.Cong_iff_cong)

    lemma Srcs_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.Srcs T = P.Srcs T'"
      using assms
      using Cong_eq_Cong\<^sub>0 P.Con_imp_eq_Srcs P.con_char by auto

    lemma sources_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.sources T = P.sources T'"
      using assms Cong_eq_Cong\<^sub>0 N.Cong\<^sub>0_imp_coinitial by force

    lemma Trgs_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.Trgs T = P.Trgs T'"
      by (metis P.Cong_iff_cong P.Srcs_Resid P.Trgs_Resid_sym
          P.con_char P.ide_def assms)

    lemma targets_respects_Cong:
    assumes "T \<^sup>*\<approx>\<^sup>* T'"
    shows "P.targets T = P.targets T'"
      by (meson P.Cong_iff_cong P.cong_implies_coterminal P.coterminalE assms)

    lemma ide_char\<^sub>C\<^sub>C:
    shows "ide \<T> \<longleftrightarrow> arr \<T> \<and> (\<forall>T. T \<in> \<T> \<longrightarrow> P.Ide T)"
      by (metis Ball_Collect P.ide_char Q.ide_char' resid_def)

    lemma con_char\<^sub>C\<^sub>C:
    shows "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<longleftrightarrow> arr \<T> \<and> arr \<U> \<and> N.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* N.Cong_class_rep \<U>"
    proof
      show "arr \<T> \<and> arr \<U> \<and> N.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* N.Cong_class_rep \<U> \<Longrightarrow> \<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        by (metis N.Cong_class_rep P.conI\<^sub>P Q.arr_char Q.quot.preserves_con resid_def)
      show "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<Longrightarrow> arr \<T> \<and> arr \<U> \<and> N.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* N.Cong_class_rep \<U>"
      proof -
        assume con: "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        have 1: "arr \<T> \<and> arr \<U>"
          using con coinitial_iff con_imp_coinitial by blast
        moreover have "N.Cong_class_rep \<T> \<^sup>*\<frown>\<^sup>* N.Cong_class_rep \<U>"
        proof -
          obtain T U where TU: "T \<in> \<T> \<and> U \<in> \<U> \<and> P.Con T U"
            using P.con_char Q.con_char\<^sub>Q\<^sub>C\<^sub>N con resid_def by auto
          have "T \<^sup>*\<approx>\<^sup>* N.Cong_class_rep \<T> \<and> U \<^sup>*\<approx>\<^sup>* N.Cong_class_rep \<U>"
            using TU 1 N.Cong_class_memb_Cong_rep Q.arr_char resid_def by simp
          thus ?thesis
            using TU N.Cong_subst(1) [of T "N.Cong_class_rep \<T>" U "N.Cong_class_rep \<U>"]
            by (metis P.coinitial_iff P.con_char P.con_imp_coinitial sources_respects_Cong)
        qed
        ultimately show ?thesis by simp
      qed
    qed

    lemma con_char\<^sub>C\<^sub>C':
    shows "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> \<longleftrightarrow> arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> T \<^sup>*\<frown>\<^sup>* U)"
    proof
      show "arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> T \<^sup>*\<frown>\<^sup>* U) \<Longrightarrow> \<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>"
        using con_char\<^sub>C\<^sub>C N.rep_in_Cong_class Q.arr_char resid_def by simp
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
        proof -
          have "N.Cong T (N.Cong_class_rep \<T>)"
            using \<open>arr \<T>\<close>
            by (simp add: "2" N.Cong_class_memb_Cong_rep Q.arr_char resid_def)
          moreover have "P.con (N.Cong_class_rep \<T>) (N.Cong_class_rep \<U>)"
            using 1 con_char\<^sub>C\<^sub>C by blast
          moreover have "N.Cong (N.Cong_class_rep \<U>) U"
            using \<open>arr \<U>\<close>
            by (simp add: "2" N.Cong_class_membs_are_Cong N.rep_in_Cong_class
                Q.arr_char resid_def)
          ultimately show ?thesis
            by (meson Cong_eq_Cong\<^sub>0 N.Cong\<^sub>0_subst_Con P.con_char)
        qed
      qed
    qed

    lemma resid_char:
    shows "\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U> =
           (if \<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U> then \<lbrace>N.Cong_class_rep \<T> \<^sup>*\\\<^sup>* N.Cong_class_rep \<U>\<rbrace> else {})"
      by (metis P.con_char N.rep_in_Cong_class Q.Resid_by_members Q.arr_char arr_resid_iff_con
          con_char\<^sub>C\<^sub>C Q.is_Cong_class_Resid resid_def)

    lemma resid_simp:
    assumes "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<U>" and "T \<in> \<T>" and "U \<in> \<U>"
    shows "\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<U> = \<lbrace>P.Resid T U\<rbrace>"
      using assms resid_char
      by (metis (no_types, lifting) P.con_char con_char\<^sub>C\<^sub>C' Q.Resid_by_members
          Q.con_char\<^sub>Q\<^sub>C\<^sub>N resid_def)

    lemma src_char':
    shows "src \<T> = {A. arr \<T> \<and> P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        by (simp add: Q.null_char Q.src_def resid_def)
      assume \<T>: "arr \<T>"
      have 1: "\<exists>A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A"
        by (metis P.Con_imp_eq_Srcs P.con_char P.con_imp_coinitial_ax P.ide_char
            \<T> con_char\<^sub>C\<^sub>C arrE)
      let ?A = "SOME A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A"
      have A: "P.Ide ?A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs ?A"
        using 1 someI_ex [of "\<lambda>A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A"] by simp
      have a: "arr \<lbrace>?A\<rbrace>"
        using A P.ide_char N.is_Cong_classI Q.arr_char resid_def by auto
      have ide_a: "ide \<lbrace>?A\<rbrace>"
        using a A N.Cong_class_def N.normal_is_Cong_closed P_ide_iff_NPath P.ide_char ide_char\<^sub>C\<^sub>C
        by auto
      have "sources \<T> = {\<lbrace>?A\<rbrace>}"
      proof -
        have "\<T> \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> \<lbrace>?A\<rbrace>"
          by (metis (no_types, lifting) A N.Cong_class_rep P.conI\<^sub>P Q.quot.preserves_con
              \<T> con_arr_self con_char\<^sub>C\<^sub>C P.Arr_iff_Con_self P.Con_IdeI(2) Q.arr_char resid_def)
        hence "\<lbrace>?A\<rbrace> \<in> sources \<T>"
          using ide_a in_sourcesI by simp
        thus ?thesis
          using sources_char\<^sub>W\<^sub>E by auto
      qed
      moreover have "\<lbrace>?A\<rbrace> = {A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A}"
      proof
        show "{A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A} \<subseteq> \<lbrace>?A\<rbrace>"
        proof
          fix A'
          assume A': "A' \<in> {A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A}"
          show "A' \<in> \<lbrace>?A\<rbrace>"
            using A'
            by (metis (mono_tags, lifting) A N.Cong_class_def P.Con_IdeI(2) P.Cong_iff_cong
                P.Ide_implies_Arr P.Resid_Arr_Ide_ind P.ide_char mem_Collect_eq)
        qed
        show "\<lbrace>?A\<rbrace> \<subseteq> {A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A}"
          using a A N.Cong_class_def Srcs_respects_Cong ide_a ide_char\<^sub>C\<^sub>C by blast
      qed
      ultimately show ?thesis
        using \<T> src_in_sources sources_char\<^sub>W\<^sub>E by auto
    qed

    lemma src_char:
    shows "src \<T> = {A. arr \<T> \<and> P.Ide A \<and> (\<forall>T. T \<in> \<T> \<longrightarrow> P.Srcs T = P.Srcs A)}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        using src_char' by simp
      assume \<T>: "arr \<T>"
      have "\<And>T. T \<in> \<T> \<Longrightarrow> P.Srcs T = P.Srcs (N.Cong_class_rep \<T>)"
        using \<T> N.Cong_class_memb_Cong_rep Srcs_respects_Cong Q.arr_char resid_def by auto
      thus ?thesis
        using \<T> src_char' N.is_Cong_class_def Q.arr_char resid_def by force
    qed

    lemma trg_char':
    shows "trg \<T> = {B. arr \<T> \<and> P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B}"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        using resid_char resid_def Q.trg_char\<^sub>Q\<^sub>C\<^sub>N by auto
      assume \<T>: "arr \<T>"
      have 1: "\<exists>B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B"
        by (metis P.Con_implies_Arr(2) P.Resid_Arr_self P.Srcs_Resid \<T> con_char\<^sub>C\<^sub>C arrE)
      define B where "B = (SOME B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B)"
      have B: "P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B"
        unfolding B_def
        using 1 someI_ex [of "\<lambda>B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B"] by simp
      hence 2: "P.Ide B \<and> P.Con (P.Resid (N.Cong_class_rep \<T>) (N.Cong_class_rep \<T>)) B"
        using \<T>
        by (metis (no_types, lifting) P.Con_Ide_iff P.Ide_implies_Arr P.Resid_Arr_self
            P.Srcs_Resid arrE P.Con_implies_Arr(2) con_char\<^sub>C\<^sub>C)
      have b: "arr \<lbrace>B\<rbrace>"
        by (simp add: "2" P.ide_char N.is_Cong_classI Q.arr_char resid_def)
      have ide_b: "ide \<lbrace>B\<rbrace>"
        by (simp add: "2" P.ide_char resid_def)
      have "targets \<T> = {\<lbrace>B\<rbrace>}"
      proof -
        have "cong (\<T> \<lbrace>\<^sup>*\\\<^sup>*\<rbrace> \<T>) \<lbrace>B\<rbrace>"
          by (metis "2" P.con_char Q.ide_imp_con_iff_cong Q.quot.preserves_con
              \<T> composite_completion.resid_char composite_completion_axioms
              cong_reflexive ide_b resid_def)
        thus ?thesis
          using \<T> Q.targets_char\<^sub>Q\<^sub>C\<^sub>N [of \<T>] cong_char resid_def by auto
      qed 
      moreover have "\<lbrace>B\<rbrace> = {B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B}"
      proof
        show "{B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B} \<subseteq> \<lbrace>B\<rbrace>"
          using B N.Cong_class_def N.Cong_closure_props(3) P.Ide_implies_Arr
                P.ide_char P.Con_IdeI(2) P.Resid_Ide(1)
          by auto
        show "\<lbrace>B\<rbrace> \<subseteq> {B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B}"
        proof -
          have "\<And>B'. N.Cong B' B \<Longrightarrow> P.Ide B' \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B'"
            using B P_ide_iff_NPath N.normal_is_Cong_closed Srcs_respects_Cong
            by (metis N.Cong_closure_props(1) P.ide_char mem_Collect_eq)
          thus ?thesis
            using N.Cong_class_def by blast
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
      have "\<And>T. T \<in> \<T> \<Longrightarrow> P.Trgs T = P.Trgs (N.Cong_class_rep \<T>)"
        using \<T>
        by (metis N.Cong_class_memb_Cong_rep Trgs_respects_Cong Q.arr_char resid_def)
      thus ?thesis
        using \<T> trg_char' N.is_Cong_class_def Q.arr_char resid_def by force
    qed

    lemma prfx_char:
    shows "\<T> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<U> \<longleftrightarrow> arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> P.prfx T U)"
    proof
      show "\<T> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<U> \<Longrightarrow> arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> P.prfx T U)"
        by (metis (mono_tags, lifting) Ball_Collect N.arr_in_Cong_class
            P.arr_resid_iff_con P.conI\<^sub>P P_ide_iff_NPath Q.ide_char'
            con_char\<^sub>C\<^sub>C' prfx_implies_con resid_def resid_simp)
      show "arr \<T> \<and> arr \<U> \<and> (\<forall>T U. T \<in> \<T> \<and> U \<in> \<U> \<longrightarrow> P.prfx T U) \<Longrightarrow> \<T> \<lbrace>\<^sup>*\<lesssim>\<^sup>*\<rbrace> \<U>"
        by (metis N.Cong_class_rep N.rep_in_Cong_class Q.arr_char Q.quot.preserves_prfx
            resid_def)
    qed

    lemma quotient_reflects_con:
    assumes "con (Q.quot t) (Q.quot u)"
    shows "P.con t u"
      using assms N.arr_in_Cong_class P.con_char con_char\<^sub>C\<^sub>C' resid_def by force

    lemma is_extensional_rts_with_composites:
    shows "extensional_rts_with_composites resid"
    proof
      fix \<T> \<U>
      assume seq: "seq \<T> \<U>"
      obtain T where T: "\<T> = \<lbrace>T\<rbrace>"
        by (metis N.Cong_class_rep Q.arr_char Q.seqE\<^sub>W\<^sub>E resid_def seq)
      obtain U where U: "\<U> = \<lbrace>U\<rbrace>"
        by (metis N.Cong_class_rep Q.arr_char Q.seqE\<^sub>W\<^sub>E resid_def seq)
      have 1: "P.Arr T \<and> P.Arr U"
        using P.arr_char T U resid_def seq by auto
      have 2: "P.Trgs T = P.Srcs U"
      proof -
        have "P.Trgs (N.Cong_class_rep \<T>) = P.Srcs (N.Cong_class_rep \<U>)"
          by (metis (mono_tags, lifting) P.Con_imp_eq_Srcs N.rep_in_Cong_class
              Q.arr_char con_arr_src(2) con_char\<^sub>C\<^sub>C' mem_Collect_eq resid_def
              seq seqE\<^sub>W\<^sub>E trg_char')
        thus ?thesis
          by (metis "1" N.Cong_class_memb_Cong_rep P.arrI\<^sub>P N.arr_in_Cong_class
              N.is_Cong_classI Srcs_respects_Cong T Trgs_respects_Cong U)
      qed
      have "P.Arr (T @ U)"
        using 1 2 by simp
      moreover have "P.Ide (T \<^sup>*\\\<^sup>* (T @ U))"
        by (metis "1" P.Con_append(2) P.Con_sym P.Resid_Arr_self P.Resid_Ide_Arr_ind
            P.Resid_append(2) P.Trgs.simps(1) calculation P.Arr_has_Trg)
      moreover have "(T @ U) \<^sup>*\\\<^sup>* T \<^sup>*\<approx>\<^sup>* U"
        by (metis "1" P.Arr.simps(1) P.Cong_iff_cong P.Ide.simps(1) P.append_is_composite_of
            P.arr_append_imp_seq P.composite_ofE P.con_implies_arr(1) P.con_sym P.null_char
            P.residuation_axioms calculation(2) residuation.conI)
      ultimately have "composite_of \<T> \<U> \<lbrace>T @ U\<rbrace>"
        by (metis "1" P.Arr.simps(1) P.append_is_composite_of P.arrI\<^sub>P P.arr_append_imp_seq
            Q.quot.preserves_composites T U resid_def)
      thus "composable \<T> \<U>"
        using composable_def by auto
    qed

    sublocale extensional_rts_with_composites resid
      using is_extensional_rts_with_composites by simp

    notation comp (infixr "\<lbrace>\<^sup>*\<cdot>\<^sup>*\<rbrace>" 55)

    subsection "Inclusion Map"

    definition incl
    where "incl \<equiv> Q.quot \<circ> P.incl"

    sublocale incl: simulation R resid incl
      unfolding incl_def resid_def
      using P.incl_is_simulation Q.quotient_is_simulation composite_simulation.intro
      by blast
    sublocale incl: simulation_to_extensional_rts R resid incl ..

    lemma incl_is_simulation:
    shows "simulation R resid incl"
      ..

    lemma incl_simp [simp]:
    shows "incl t = \<lbrace>[t]\<rbrace>"
      by (metis (mono_tags, lifting) P.Arr.simps(2) P.Arr_iff_Con_self P.Ide.simps(1)
          P.cong_reflexive P.ide_char Q.quot.extensionality incl.extensionality incl_def
          o_apply resid_def)

    lemma incl_reflects_con:
    assumes "incl t \<lbrace>\<^sup>*\<frown>\<^sup>*\<rbrace> incl u"
    shows "R.con t u"
      by (metis P.Con_rec(1) N.arr_in_Cong_class assms con_char\<^sub>C\<^sub>C' incl_simp  
          Q.quot.preserves_reflects_arr resid_def)

    lemma cong_iff_eq_incl:
    assumes "R.arr t" and "R.arr u"
    shows "incl t = incl u \<longleftrightarrow> R.cong t u"
      by (metis P.Ide.simps(2) N.arr_in_Cong_class assms(1) incl_reflects_con
          conE cong_char ide_char\<^sub>C\<^sub>C incl.preserves_prfx incl.preserves_reflects_arr
          incl.preserves_resid incl_simp prfx_implies_con Q.quot.extensionality resid_def)

    lemma incl_cancel_left:
    assumes "transformation X R F G T" and "transformation X R F' G' T'"
    and "extensional_rts R"
    and "incl \<circ> T = incl \<circ> T'"
    shows "T = T'"
    proof -
      interpret R: extensional_rts R
        using assms(3) by blast
      interpret T: transformation X R F G T
        using assms(1) by blast
      interpret T': transformation X R F' G' T'
        using assms(2) by blast
      show "T = T'"
      proof
        fix x
        show "T x = T' x"
        by (metis R.cong_char T'.extensionality T.A.cong_reflexive T.extensionality
          T.respects_cong assms(4) comp_apply cong_iff_eq_incl incl.preserves_reflects_arr)
      qed
    qed

    text \<open>
      The inclusion is surjective on identities.
    \<close>

    lemma img_incl_ide:
    shows "incl ` (Collect R.ide) = Collect ide"
    proof
      show "incl ` Collect R.ide \<subseteq> Collect ide"
        using incl.preserves_ide by force
      show "Collect ide \<subseteq> incl ` Collect R.ide"
      proof
        fix \<A>
        assume \<A>: "\<A> \<in> Collect ide"
        obtain A where A: "A \<in> \<A>"
          using \<A> Q.ide_char resid_def by auto
        obtain a where a: "a \<in> P.Srcs A"
          by (metis A CollectD P.Arr_has_Src P.Ide_implies_Arr \<A> equals0I ide_char\<^sub>C\<^sub>C)
        have "\<A> = \<lbrace>[a]\<rbrace>"
        proof -
          have "A \<^sup>*\<approx>\<^sub>0\<^sup>* [a]"
            by (metis (no_types, lifting) A P.Ide.simps(2) P.Resid_Arr_Src P.Srcs_Resid_Arr_single P.ide_char P.ide_imp_con_iff_cong
                P.paths_in_rts_axioms P.prfx_implies_con \<A> a composite_completion_axioms composite_completion_def ide_char\<^sub>C\<^sub>C
                mem_Collect_eq paths_in_rts.Con_sym paths_in_rts.Ide_implies_Arr rts.in_targetsE)
          thus ?thesis
            by (metis A CollectD N.Cong\<^sub>0_implies_Cong N.Cong_class_eqI N.elements_are_arr P.Con_implies_Arr(1) P.arrE P.con_char
                P.paths_in_rts_axioms P.resid_arr_ide Q.ideE \<A> a paths_in_rts.Resid_Arr_Src resid_def resid_simp)
        qed
        thus "\<A> \<in> incl ` Collect R.ide"
          using P.Srcs_are_ide a by auto
      qed
    qed

  end

  subsection "Composite Completion of a Weakly Extensional RTS"

  locale composite_completion_of_weakly_extensional_rts =
    R: weakly_extensional_rts R +
    composite_completion
  begin

    sublocale P: paths_in_weakly_extensional_rts R ..
    sublocale incl: simulation_between_weakly_extensional_rts R resid incl ..

    notation comp (infixr "\<lbrace>\<^sup>*\<cdot>\<^sup>*\<rbrace>" 55)

    lemma src_char\<^sub>C\<^sub>C\<^sub>W\<^sub>E:
    shows "src \<T> = (if arr \<T> then incl (P.Src (N.Cong_class_rep \<T>)) else null)"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        using src_def by auto
      assume \<T>: "arr \<T>"
      have "src \<T> = {A. P.Ide A \<and> P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A}"
        using \<T> src_char' [of \<T>] by simp
      moreover have 1: "\<And>A. P.Ide A \<Longrightarrow>
                              P.Srcs (N.Cong_class_rep \<T>) = P.Srcs A \<longleftrightarrow>
                              P.Src (N.Cong_class_rep \<T>) = P.Src A"
        by (metis \<T> P.Con_implies_Arr(2) P.Ide_implies_Arr con_arr_self con_char\<^sub>C\<^sub>C
            insertCI P.Srcs_simp\<^sub>P\<^sub>W\<^sub>E singletonD)
      ultimately have 2: "src \<T> = {A. P.Ide A \<and> P.Src (N.Cong_class_rep \<T>) = P.Src A}"
        by blast
      also have "... = incl (P.Src (N.Cong_class_rep \<T>))"
      proof -
        have "incl (P.Src (N.Cong_class_rep \<T>)) = Q.quot [R.src (hd (N.Cong_class_rep \<T>))]"
          by auto
        also have "... = {A. P.Ide A \<and> P.Src (N.Cong_class_rep \<T>) = P.Src A}"
          apply auto[1]
            apply (metis Q.null_char R.ide_iff_src_self R.src_src empty_iff ide_char\<^sub>C\<^sub>C
                incl.extensionality incl.preserves_ide incl_simp resid_def)
           apply (metis "1" CollectD N.Cong_class_def P.Ide.simps(2)
               P.paths_in_weakly_extensional_rts_axioms Q.null_char R.rts_axioms R.src_trg
               R.trg_src Srcs_respects_Cong calculation composite_completion.ide_char\<^sub>C\<^sub>C
               composite_completion_axioms empty_iff incl.extensionality incl.preserves_ide
               list.sel(1) paths_in_weakly_extensional_rts.Src.elims resid_def rts.ide_src)
          by (metis (mono_tags, lifting) 2 N.Cong_class_def P.Ide.simps(2)
              P.Ide_imp_Ide_hd P.Src.elims N.is_Cong_classE Q.arr_char Q.src_src R.src_ide
              list.sel(1) mem_Collect_eq resid_def src_char')
        finally show ?thesis by blast
      qed
      finally show ?thesis
        using \<T> by auto
    qed

    lemma trg_char\<^sub>C\<^sub>C\<^sub>W\<^sub>E:
    shows "trg \<T> = (if arr \<T> then incl (P.Trg (N.Cong_class_rep \<T>)) else null)"
    proof (cases "arr \<T>")
      show "\<not> arr \<T> \<Longrightarrow> ?thesis"
        using trg_def by auto
      assume \<T>: "arr \<T>"
      have "trg \<T> = {A. P.Ide A \<and> P.Trg (N.Cong_class_rep \<T>) = P.Src A}"
      proof -
        have "trg \<T> = {B. P.Ide B \<and> P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B}"
          using \<T> trg_char' [of \<T>] by simp
        moreover have "\<And>B. P.Ide B \<Longrightarrow>
                             P.Trgs (N.Cong_class_rep \<T>) = P.Srcs B \<longleftrightarrow>
                             P.Trg (N.Cong_class_rep \<T>) = P.Src B"
          by (metis P.Con_implies_Arr(1) P.Ide_implies_Arr \<T> con_arr_self con_char\<^sub>C\<^sub>C
              P.Srcs_simp\<^sub>P\<^sub>W\<^sub>E P.Trgs_simp\<^sub>P\<^sub>W\<^sub>E singleton_inject)
        ultimately show ?thesis by blast
      qed
      also have "... = incl (P.Trg (N.Cong_class_rep \<T>))"
        using incl.preserves_trg
        by (metis (mono_tags, lifting) N.rep_in_Cong_class \<T> arr_trg_iff_arr
            calculation mem_Collect_eq Q.arr_char resid_def src_char\<^sub>C\<^sub>C\<^sub>W\<^sub>E src_trg)
      finally show ?thesis
        using \<T> by auto
    qed

    text \<open>
      When applied to a weakly extensional RTS, the composite completion construction
      does not identify any states that are distinct in the original RTS.
    \<close>

    lemma incl_injective_on_ide:
    shows "inj_on incl (Collect R.ide)"
      by (metis R.con_ide_are_eq ideE incl.preserves_ide incl_reflects_con inj_onCI
          mem_Collect_eq)

    text \<open>
      When applied to a weakly extensional RTS, the composite completion construction
      is a bijection between the states of the original RTS and the states of its
      completion.
    \<close>

    lemma incl_bijective_on_ide:
    shows "incl \<in> Collect R.ide \<rightarrow> Collect ide"
    and "(\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) \<in> Collect ide \<rightarrow> Collect R.ide"
    and "\<And>a. R.ide a \<Longrightarrow> (\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) (incl a) = a"
    and "\<And>\<A>. ide \<A> \<Longrightarrow> incl ((\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) \<A>) = \<A>"
    and "bij_betw incl (Collect R.ide) (Collect ide)"
    and "bij_betw (\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) (Collect ide) (Collect R.ide)"
    proof -
      show 1: "incl \<in> Collect R.ide \<rightarrow> Collect ide"
        using img_incl_ide by auto
      show 2: "(\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) \<in> Collect ide \<rightarrow> Collect R.ide"
        by (metis (no_types, lifting) P.Src.elims Pi_I' R.ide_iff_trg_self
            R.trg_src ide_implies_arr incl.preserves_reflects_arr mem_Collect_eq
            src_char\<^sub>C\<^sub>C\<^sub>W\<^sub>E src_ide)
      show 3: "\<And>a. R.ide a \<Longrightarrow> (\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) (incl a) = a"
        by (metis R.ide_backward_stable R.weak_extensionality cong_iff_eq_incl
            incl.preserves_ide incl.preserves_reflects_arr ide_implies_arr
            src_char\<^sub>C\<^sub>C\<^sub>W\<^sub>E src_ide)
      show 4: "\<And>\<A>. ide \<A> \<Longrightarrow> incl ((\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) \<A>) = \<A>"
        using src_char\<^sub>C\<^sub>C\<^sub>W\<^sub>E src_ide by auto
      show "bij_betw incl (Collect R.ide) (Collect ide)"
        using incl_injective_on_ide img_incl_ide bij_betw_def by blast
      show "bij_betw (\<lambda>\<A>. P.Src (N.Cong_class_rep \<A>)) (Collect ide) (Collect R.ide)"
        using 1 2 3 4 bij_betwI by force
    qed

  end

  subsection "Composite Completion of an Extensional RTS"

  locale composite_completion_of_extensional_rts =
    R: extensional_rts R +
    composite_completion
  begin

    sublocale composite_completion_of_weakly_extensional_rts ..
    sublocale incl: simulation_between_extensional_rts R resid incl ..

  end

  subsection "Freeness of Composite Completion"

  text \<open>
    In this section we show that the composite completion construction is free:
    any simulation from RTS \<open>A\<close> to an extensional RTS with composites \<open>B\<close>
    extends uniquely to a simulation on the composite completion of \<open>A\<close>.
  \<close>

  type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  locale rts_with_chosen_composites =
    rts +
  fixes comp :: "'a comp" (infixr "\<cdot>" 55)
  assumes comp_extensionality_ax: "\<And>t u :: 'a. \<not> seq t u \<Longrightarrow> t \<cdot> u = null"
  and composite_of_comp_ax: "\<And>t u v :: 'a. seq t u \<Longrightarrow> composite_of t u (t \<cdot> u)"
  and comp_assoc_ax: "\<And>t u v :: 'a. \<lbrakk>seq t u; seq u v\<rbrakk> \<Longrightarrow> (t \<cdot> u) \<cdot> v = t \<cdot> (u \<cdot> v)"
  and resid_comp_right_ax: "t \<cdot> u \<frown> w \<Longrightarrow> w \\ (t \<cdot> u) = (w \\ t) \\ u"
  and resid_comp_left_ax: "(t \<cdot> u) \\ w = (t \\ w) \<cdot> (u \\ (w \\ t))"
  begin

    lemma comp_assoc\<^sub>C\<^sub>C:
    shows "t \<cdot> u \<cdot> v = (t \<cdot> u) \<cdot> v"
      using comp_extensionality_ax comp_assoc_ax
      by (metis (mono_tags, lifting) composite_of_comp_ax not_arr_null seq_def
          sources_composite_of targets_composite_of)

    lemma comp_null\<^sub>C\<^sub>C:
    shows "t \<cdot> null = null" and "null \<cdot> t = null"
      using comp_extensionality_ax not_arr_null apply blast
      by (simp add: comp_extensionality_ax seq_def)

    lemma composable_iff_arr_comp\<^sub>C\<^sub>C:
    shows "composable t u \<longleftrightarrow> arr (t \<cdot> u)"
      by (metis arr_composite_of comp_extensionality_ax composable_def
          composable_imp_seq composite_of_comp_ax not_arr_null)

    lemma composable_iff_comp_not_null\<^sub>C\<^sub>C:
    shows "composable t u \<longleftrightarrow> t \<cdot> u \<noteq> null"
      by (metis comp_extensionality_ax composable_def composable_iff_arr_comp\<^sub>C\<^sub>C
          composite_of_comp_ax not_arr_null)

    lemma con_comp_iff\<^sub>C\<^sub>C:
    shows "w \<frown> t \<cdot> u \<longleftrightarrow> composable t u \<and> w \\ t \<frown> u"
      by (metis composable_iff_comp_not_null\<^sub>C\<^sub>C composable_imp_seq composite_of_comp_ax
          con_composite_of_iff not_con_null(2))

    lemma con_compI\<^sub>C\<^sub>C [intro]:
    assumes "composable t u" and "w \\ t \<frown> u"
    shows "w \<frown> t \<cdot> u" and "t \<cdot> u \<frown> w"
      using assms con_comp_iff\<^sub>C\<^sub>C con_sym by blast+

    sublocale rts_with_composites resid
      using composite_of_comp_ax composable_def
      by unfold_locales auto

  end

  context paths_in_weakly_extensional_rts
  begin

    abbreviation Comp
    where "Comp T U \<equiv> if seq T U then T @ U else null"

    sublocale rts_with_chosen_composites Resid Comp
    proof
      show "\<And>T U. \<not> seq T U \<Longrightarrow> Comp T U = null"
        by argo
      show "\<And>t u v. seq t u \<Longrightarrow> composite_of t u (Comp t u)"
        by (simp add: append_is_composite_of)
      show "\<And>t u v. \<lbrakk>seq t u; seq u v\<rbrakk> \<Longrightarrow> Comp (Comp t u) v = Comp t (Comp u v)"
        by (simp add: seq_def)
      show "\<And>t u w. con (Comp t u) w \<Longrightarrow> w \<^sup>*\\\<^sup>* Comp t u = (w \<^sup>*\\\<^sup>* t) \<^sup>*\\\<^sup>* u"
        by (metis (full_types) Arr.simps(1) Con_append(2) con_implies_arr(1)
            not_arr_null Resid.simps(1) Resid_append(2) paths_in_rts.seq_char
            paths_in_rts_axioms)
      show "\<And>t u w. Comp t u \<^sup>*\\\<^sup>* w = Comp (t \<^sup>*\\\<^sup>* w) (u \<^sup>*\\\<^sup>* (w \<^sup>*\\\<^sup>* t))"
      proof -
        fix t u w
        have "\<lbrakk>Arr t; Arr u; {Trg t} = Srcs u; (t @ u) \<^sup>*\\\<^sup>* w \<noteq> []\<rbrakk>
                 \<Longrightarrow> Trg (t \<^sup>*\\\<^sup>* w) \<in> Srcs (u \<^sup>*\\\<^sup>* (w \<^sup>*\\\<^sup>* t))"
          by (metis Arr.simps(1) Con_imp_Arr_Resid Con_implies_Arr(2) Resid_append_ind
              Srcs_Resid Trgs_Resid_sym Trgs_simp\<^sub>P\<^sub>W\<^sub>E insertI1)
        thus "Comp t u \<^sup>*\\\<^sup>* w = Comp (t \<^sup>*\\\<^sup>* w) (u \<^sup>*\\\<^sup>* (w \<^sup>*\\\<^sup>* t))"
          using seq_char con_char null_char Con_implies_Arr
          apply auto[1]
          by (metis Arr_has_Src Con_append(1) Resid_append(1) Src_resid Srcs.simps(1)
              Srcs_simp\<^sub>P\<^sub>W\<^sub>E Trg_resid_sym con_imp_arr_resid singleton_iff Con_imp_eq_Srcs)+
            (* 8 sec, 12 subgoals *)
      qed
    qed

    lemma extends_to_rts_with_chosen_composites:
    shows "rts_with_chosen_composites Resid Comp"
      ..

  end

  context extensional_rts_with_composites
  begin

    lemma extends_to_rts_with_chosen_composites:
    shows "rts_with_chosen_composites resid comp"
    using composable_iff_comp_not_null comp_is_composite_of(1) comp_assoc\<^sub>E\<^sub>C
          resid_comp(1-2) comp_null(2) conI con_comp_iff\<^sub>E\<^sub>C(2) mediating_transition
      apply unfold_locales
          apply auto[4]
      by (metis comp_null(2) composable_imp_seq resid_comp(2))

    sublocale rts_with_chosen_composites resid comp
      using extends_to_rts_with_chosen_composites by blast

  end

  locale simulation_ext_to_paths =
    A: rts A +
    B: rts_with_chosen_composites B comp\<^sub>B +
    F: simulation A B F +
    paths_in_rts A
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
  and comp\<^sub>B :: "'b comp"   (infixr \<open>\<cdot>\<^sub>B\<close> 55)
  and F :: "'a \<Rightarrow> 'b"
  begin

    notation Resid    (infix \<open>\<^sup>*\\<^sub>A\<^sup>*\<close> 70)
    notation Resid1x  (infix \<open>\<^sup>1\\<^sub>A\<^sup>*\<close> 70)
    notation Residx1  (infix \<open>\<^sup>*\\<^sub>A\<^sup>1\<close> 70)
    notation Con      (infix \<open>\<^sup>*\<frown>\<^sub>A\<^sup>*\<close> 70)
    notation B.con    (infix \<open>\<frown>\<^sub>B\<close> 50)

    fun map
    where "map [] = B.null"
        | "map [t] = F t"
        | "map (t # T) = (if arr (t # T) then F t \<cdot>\<^sub>B map T else B.null)"

    lemma map_o_incl_eq:
    shows "map (incl t) = F t"
      by (simp add: null_char F.extensionality)

    lemma extensionality:
    shows "\<not> arr T \<Longrightarrow> map T = B.null"
      using F.extensionality arr_char
      by (metis Arr.simps(2) map.elims)

    lemma preserves_comp:
    shows "\<lbrakk>T \<noteq> []; U \<noteq> []; Arr (T @ U)\<rbrakk> \<Longrightarrow> map (T @ U) = map T \<cdot>\<^sub>B map U"
    proof (induct T arbitrary: U)
      show "\<And>U. [] \<noteq> [] \<Longrightarrow> map ([] @ U) = map [] \<cdot>\<^sub>B map U"
        by simp
      fix t and T U :: "'a list"
      assume ind: "\<And>U. \<lbrakk>T \<noteq> []; U \<noteq> []; Arr (T @ U)\<rbrakk>
                          \<Longrightarrow> map (T @ U) = map T \<cdot>\<^sub>B map U"
      assume U: "U \<noteq> []"
      assume Arr: "Arr ((t # T) @ U)"
      hence 1: "Arr (t # (T @ U))"
        by simp
      have 2: "Arr (t # T)"
        by (metis Con_Arr_self Con_append(1) Con_implies_Arr(1) Arr U append_is_Nil_conv
            list.distinct(1))
      show "map ((t # T) @ U) = comp\<^sub>B (map (t # T)) (map U)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          by (metis (full_types) "1" arr_char U append_Cons append_Nil list.exhaust
              map.simps(2) map.simps(3))
        assume T: "T \<noteq> []"
        have "map ((t # T) @ U) = map (t # (T @ U))"
          by simp
        also have "... = F t \<cdot>\<^sub>B map (T @ U)"
          using T 1
          by (metis arr_char Nil_is_append_conv list.exhaust map.simps(3))
        also have "... =  F t \<cdot>\<^sub>B (map T \<cdot>\<^sub>B map U)"
          using ind
          by (metis "1" Con_Arr_self Con_implies_Arr(1) Con_rec(4) T U append_is_Nil_conv)
        also have "... = (F t \<cdot>\<^sub>B map T) \<cdot>\<^sub>B map U"
          using B.comp_assoc\<^sub>C\<^sub>C by blast
        also have "... = map (t # T) \<cdot>\<^sub>B map U"
          using T 2
          by (metis arr_char list.exhaust map.simps(3))
        finally show "map ((t # T) @ U) = map (t # T) \<cdot>\<^sub>B map U" by simp
      qed
    qed

    lemma preserves_arr_ind:
    shows "\<lbrakk>arr T; a \<in> Srcs T\<rbrakk> \<Longrightarrow> B.arr (map T) \<and> F a \<in> B.sources (map T)"
    proof (induct T arbitrary: a)
      show "\<And>a. \<lbrakk>arr []; a \<in> Srcs []\<rbrakk> \<Longrightarrow> B.arr (map []) \<and> F a \<in> B.sources (map [])"
        using arr_char by simp
      fix a t T
      assume a: "a \<in> Srcs (t # T)"
      assume tT: "arr (t # T)"
      assume ind: "\<And>a. \<lbrakk>arr T; a \<in> Srcs T\<rbrakk> \<Longrightarrow> B.arr (map T) \<and> F a \<in> B.sources (map T)"
      have 1: "a \<in> A.sources t"
        using a tT Con_imp_eq_Srcs Con_initial_right Srcs.simps(2) con_char
        by blast
      show "B.arr (map (t # T)) \<and> F a \<in> B.sources (map (t # T))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using 1arr_char tT by auto
        assume T: "T \<noteq> []"
        obtain a' where a': "a' \<in> A.targets t"
          using tT "1" A.resid_source_in_targets by auto
        have 2: "a' \<in> Srcs T"
          using a' tT
          by (metis Con_Arr_self A.sources_resid Srcs.simps(2) arr_char T
              Con_imp_eq_Srcs Con_rec(4))
        have "B.arr (map (t # T)) \<longleftrightarrow> B.arr (F t \<cdot>\<^sub>B map T)"
          using tT T by (metis map.simps(3) neq_Nil_conv)
        also have "... \<longleftrightarrow> True"
        proof -
          have "B.arr (F t \<cdot>\<^sub>B map T)"
          proof -
            have "B.seq (F t) (map T)"
            proof
              show "B.arr (map T)"
                by (metis "2" A.rts_axioms Con_implies_Arr(2) Resid_cons(2)
                    T arrE arr_resid ind not_arr_null null_char
                    paths_in_rts.arr_char paths_in_rts.intro tT)
              show "B.trg (F t) \<sim>\<^sub>B B.src (map T)"
              proof (intro B.coinitial_ide_are_cong)
                show "B.ide (B.trg (F t))"
                  by (meson "1" A.in_sourcesE A.residuation_axioms B.ide_trg
                      F.preserves_reflects_arr residuation.con_implies_arr(1))
                show "B.ide (B.src (map T))"
                  by (simp add: \<open>B.arr (map T)\<close>)
                show "B.coinitial (B.trg (F t)) (B.src (map T))"
                  using a' ind extensionality
                  by (metis "1" "2" A.con_implies_arr(1) A.in_sourcesE A.in_targetsE
                      B.con_sym B.cong_implies_coinitial B.in_sourcesE B.not_arr_null
                      B.sources_con_closed B.src_congI F.preserves_con F.preserves_trg
                      \<open>B.arr (map T)\<close> \<open>B.ide (B.trg (F t))\<close>)
              qed
            qed
            thus ?thesis
              using B.composable_iff_arr_comp\<^sub>C\<^sub>C by blast
          qed
          thus ?thesis by blast
        qed
        finally have "B.arr (map (t # T))" by blast
        moreover have "F a \<in> B.sources (map (t # T))"
        proof -
          have "F a \<in> B.sources (F t)"
            using 1 tT F.preserves_sources by blast
          moreover have "B.sources (F t) = B.sources (map (t # T))"
          proof -
            have "B.sources (F t) = B.sources (F t \<cdot>\<^sub>B map T)"
              by (metis B.comp_extensionality_ax B.composite_of_comp_ax
                  B.not_arr_null B.sources_composite_of \<open>B.arr (F t \<cdot>\<^sub>B map T) = True\<close>)
            also have "... = B.sources (map (t # T))"
              by (metis T list.exhaust map.simps(3) tT)
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by blast
        qed
        ultimately show ?thesis by blast
      qed
    qed

    lemma preserves_arr:
    shows "arr T \<Longrightarrow> B.arr (map T)"
      using preserves_arr_ind arr_char Arr_has_Src by blast

    lemma preserves_sources:
    assumes "arr T" and "a \<in> Srcs T"
    shows "F a \<in> B.sources (map T)"
      using assms preserves_arr_ind by simp

    lemma preserves_targets:
    shows "\<lbrakk>arr T; b \<in> Trgs T\<rbrakk> \<Longrightarrow> F b \<in> B.targets (map T)"
    proof (induct T)
      show "\<lbrakk>arr []; b \<in> Trgs []\<rbrakk> \<Longrightarrow> F b \<in> B.targets (map [])"
        by simp
      fix t T
      assume tT: "arr (t # T)"
      assume b: "b \<in> Trgs (t # T)"
      assume ind: "\<lbrakk>arr T; b \<in> Trgs T\<rbrakk> \<Longrightarrow> F b \<in> B.targets (map T)"
      show "F b \<in> B.targets (map (t # T))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT b arr_char by auto
        assume T: "T \<noteq> []"
        show ?thesis
        proof -
          have "F b \<in> B.targets (map T)"
            by (metis Resid_cons(2) T Trgs.simps(3) arrE b con_char
                con_implies_arr(2) ind neq_Nil_conv tT)
          moreover have "B.targets (map T) = B.targets (map (t # T))"
          proof -
            have "B.targets (map T) = B.targets (F t \<cdot>\<^sub>B map T)"
              by (metis B.comp_extensionality_ax B.composite_of_comp_ax
                  B.not_arr_null B.targets_composite_of T append_Cons append_Nil
                  arr_char preserves_arr list.distinct(1) map.simps(2)
                  preserves_comp tT)
            also have "... = B.targets (map (t # T))"
              by (metis T list.exhaust map.simps(3) tT)
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by blast
        qed
      qed
    qed

    lemma preserves_Resid1x_ind:
    shows "t \<^sup>1\\\<^sub>A\<^sup>* U \<noteq> A.null \<Longrightarrow> F t \<frown>\<^sub>B map U \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* U) = F t \\\<^sub>B map U"
    proof (induct U arbitrary: t)
      show "\<And>t. t \<^sup>1\\\<^sub>A\<^sup>* [] \<noteq> A.null \<Longrightarrow> F t \<frown>\<^sub>B map [] \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* []) = F t \\\<^sub>B map []"
        by simp
      fix t u U
      assume uU: "t \<^sup>1\\\<^sub>A\<^sup>* (u # U) \<noteq> A.null"
      assume ind: "\<And>t. t \<^sup>1\\\<^sub>A\<^sup>* U \<noteq> A.null
                          \<Longrightarrow> F t \<frown>\<^sub>B map U \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* U) = F t \\\<^sub>B map U"
      show "F t \<frown>\<^sub>B map (u # U) \<and> F (t \<^sup>1\\\<^sub>A\<^sup>* (u # U)) = F t \\\<^sub>B map (u # U)"
      proof
        show 1: "F t \<frown>\<^sub>B map (u # U)"
        proof (cases "U = []")
          show "U = [] \<Longrightarrow> ?thesis"
            using Resid1x.simps(2) map.simps(2) F.preserves_con uU by fastforce
          assume U: "U \<noteq> []"
          have 3: "[t] \<^sup>*\\\<^sub>A\<^sup>* [u] \<noteq> [] \<and> ([t] \<^sup>*\\\<^sub>A\<^sup>* [u]) \<^sup>*\\\<^sub>A\<^sup>* U \<noteq> []"
            using Con_cons(2) [of "[t]" U u]
            by (meson Resid1x_as_Resid' U not_Cons_self2 uU)
          hence 2: "F t \<frown>\<^sub>B F u \<and> F t \\\<^sub>B F u \<frown>\<^sub>B map U"
            by (metis Con_rec(1) Con_sym Con_sym1 Residx1_as_Resid Resid_rec(1)
                F.preserves_con F.preserves_resid ind)
          moreover have "B.seq (F u) (map U)"
            by (metis B.coinitialE B.con_imp_coinitial calculation B.seqI(1)
                B.sources_resid)
          ultimately have "F t \<frown>\<^sub>B map ([u] @ U)"
            by (metis "3" B.composite_of_comp_ax B.con_composite_of_iff Con_consI(2)
                Con_implies_Arr(2) append_Cons list.simps(3) map.simps(2) preserves_comp
                self_append_conv2)
          thus ?thesis by simp
        qed
        show "F (t \<^sup>1\\\<^sub>A\<^sup>* (u # U)) = F t \\\<^sub>B map (u # U)"
        proof (cases "U = []")
          show "U = [] \<Longrightarrow> ?thesis"
            using Resid1x.simps(2) F.preserves_resid map.simps(2) uU by fastforce
          assume U: "U \<noteq> []"
          have "F (t \<^sup>1\\\<^sub>A\<^sup>* (u # U)) = F ((t \\\<^sub>A u) \<^sup>1\\\<^sub>A\<^sup>* U)"
            using Resid1x_as_Resid' Resid_rec(3) U uU by metis
          also have "... = F (t \\\<^sub>A u) \\\<^sub>B map U"
            using uU U ind Con_rec(3) Resid1x_as_Resid [of "t \\\<^sub>A u" U] 
            by (metis Resid1x.simps(3) list.exhaust)
          also have "... = (F t \\\<^sub>B F u) \\\<^sub>B map U"
            using uU U
            by (metis Resid1x_as_Resid' F.preserves_resid Con_rec(3))
          also have "... = F t \\\<^sub>B (F u \<cdot>\<^sub>B map U)"
          proof -
            have "F u \<cdot>\<^sub>B map U \<frown>\<^sub>B F t"
            proof
              show "B.composable (F u) (map U)"
                by (metis "1" B.composable_iff_comp_not_null\<^sub>C\<^sub>C B.not_con_null(2)
                    U append.left_neutral append_Cons arr_char extensionality
                    map.simps(2) not_Cons_self preserves_comp)
              show "F t \\\<^sub>B F u \<frown>\<^sub>B map U"
                by (metis B.arr_resid_iff_con Resid1x.simps(3) U calculation
                    ind list.exhaust uU)
            qed
            thus ?thesis
              using B.resid_comp_right_ax [of "F u" "map U" "F t"] by argo
          qed
          also have "... = F t \\\<^sub>B map (u # U)"
            by (metis Resid1x_as_Resid' con_char U map.simps(3) neq_Nil_conv
                con_implies_arr(2) uU)
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
          using Residx1.simps(2) F.preserves_con F.preserves_resid map.simps(2) uU
          by presburger
        assume U: "U \<noteq> []"
        show ?thesis
        proof
          show "map (u # U) \<frown>\<^sub>B F t"
            using uU U Con_sym1 B.con_sym preserves_Resid1x_ind by blast
          show "map ((u # U) \<^sup>*\\\<^sub>A\<^sup>1 t) = map (u # U) \\\<^sub>B F t"
          proof -
            have "map ((u # U) \<^sup>*\\\<^sub>A\<^sup>1 t) = map ((u \\\<^sub>A t) # U \<^sup>*\\\<^sub>A\<^sup>1 (t \\\<^sub>A u))"
              using uU U Residx1_as_Resid Resid_rec(2) by fastforce
            also have "... = F (u \\\<^sub>A t) \<cdot>\<^sub>B map (U \<^sup>*\\\<^sub>A\<^sup>1 (t \\\<^sub>A u))"
              by (metis Residx1_as_Resid arr_char U Con_imp_Arr_Resid
                  Con_rec(2) Resid_rec(2) list.exhaust map.simps(3) uU)
            also have "... = F (u \\\<^sub>A t) \<cdot>\<^sub>B map U \\\<^sub>B F (t \\\<^sub>A u)"
              using uU U ind Con_rec(2) Residx1_as_Resid by force
            also have "... = (F u \\\<^sub>B F t) \<cdot>\<^sub>B map U \\\<^sub>B (F t \\\<^sub>B F u)"
              using uU U
              by (metis Con_initial_right Con_rec(1) Con_sym1 Resid1x_as_Resid'
                  Residx1_as_Resid F.preserves_resid)
            also have "... = (F u \<cdot>\<^sub>B map U) \\\<^sub>B F t"
              using B.resid_comp_left_ax by auto
            also have "... = map (u # U) \\\<^sub>B F t"
              by (metis Con_implies_Arr(2) Con_sym Residx1_as_Resid U
                  arr_char map.simps(3) neq_Nil_conv uU)
            finally show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma preserves_resid_ind:
    shows "con T U \<Longrightarrow> map T \<frown>\<^sub>B map U \<and> map (T \<^sup>*\\\<^sub>A\<^sup>* U) = map T \\\<^sub>B map U"
    proof (induct T arbitrary: U)
      show "\<And>U. con [] U \<Longrightarrow> map [] \<frown>\<^sub>B map U \<and> map ([] \<^sup>*\\\<^sub>A\<^sup>* U) = map [] \\\<^sub>B map U"
        using con_char Resid.simps(1) by blast
      fix t T U
      assume tT: "con (t # T) U"
      assume ind: "\<And>U. con T U \<Longrightarrow>
                         map T \<frown>\<^sub>B map U \<and> map (T \<^sup>*\\\<^sub>A\<^sup>* U) = map T \\\<^sub>B map U"
      show "map (t # T) \<frown>\<^sub>B map U \<and> map ((t # T) \<^sup>*\\\<^sub>A\<^sup>* U) = map (t # T) \\\<^sub>B map U"
      proof (cases "T = []")
        assume T: "T = []"
        show ?thesis
          using T tT
          apply simp
          by (metis Resid1x_as_Resid Residx1_as_Resid con_char
              Con_sym Con_sym1 map.simps(2) preserves_Resid1x_ind)
        next
        assume T: "T \<noteq> []"
        have 1: "map (t # T) = F t \<cdot>\<^sub>B map T"
          using tT T
          by (metis con_implies_arr(1) list.exhaust map.simps(3))
        show ?thesis
        proof
          show 2: "B.con (map (t # T)) (map U)"
            using T tT
            by (metis "1" B.composable_iff_comp_not_null\<^sub>C\<^sub>C B.con_compI\<^sub>C\<^sub>C(2) B.con_sym
                B.not_arr_null Con_cons(1) Residx1_as_Resid con_char con_implies_arr(1-2)
                preserves_arr ind not_arr_null null_char preserves_Residx1_ind)
          show "map ((t # T) \<^sup>*\\\<^sub>A\<^sup>* U) = map (t # T) \\\<^sub>B map U"
          proof -
            have "map ((t # T) \<^sup>*\\\<^sub>A\<^sup>* U) = map (([t] \<^sup>*\\\<^sub>A\<^sup>* U) @ (T \<^sup>*\\\<^sub>A\<^sup>* (U \<^sup>*\\\<^sub>A\<^sup>* [t])))"
              by (metis Resid.simps(1) Resid_cons(1) con_char ex_un_null tT)
            also have "... = map ([t] \<^sup>*\\\<^sub>A\<^sup>* U) \<cdot>\<^sub>B map (T \<^sup>*\\\<^sub>A\<^sup>* (U \<^sup>*\\\<^sub>A\<^sup>* [t]))"
              by (metis Arr.simps(1) Con_imp_Arr_Resid Con_implies_Arr(2) Con_sym
                  Resid_cons(1-2) con_char T preserves_comp tT)
            also have "... = (map [t] \\\<^sub>B map U) \<cdot>\<^sub>B map (T \<^sup>*\\\<^sub>A\<^sup>* (U \<^sup>*\\\<^sub>A\<^sup>* [t]))"
              by (metis Con_initial_right Con_sym Resid1x_as_Resid
                  Residx1_as_Resid con_char Con_sym1 map.simps(2)
                  preserves_Resid1x_ind tT)
            also have "... = (map [t] \\\<^sub>B map U) \<cdot>\<^sub>B (map T \\\<^sub>B map (U \<^sup>*\\\<^sub>A\<^sup>* [t]))"
              using tT T ind
              by (metis Con_cons(1) Con_sym Resid.simps(1) con_char)
            also have "... = (map [t] \\\<^sub>B map U) \<cdot>\<^sub>B (map T \\\<^sub>B (map U \\\<^sub>B map [t]))"
              using tT T
              by (metis Con_cons(1) Con_sym Resid.simps(2) Residx1_as_Resid
                        con_char map.simps(2) preserves_Residx1_ind)
            also have "... = (F t \\\<^sub>B map U) \<cdot>\<^sub>B (map T \\\<^sub>B (map U \\\<^sub>B F t))"
              using tT T by simp
            also have "... = map (t # T) \\\<^sub>B map U"
              using 1 B.resid_comp_left_ax by auto
            finally show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma preserves_con:
    assumes "con T U"
    shows "map T \<frown>\<^sub>B map U"
      using assms preserves_resid_ind by simp

    lemma preserves_resid:
    assumes "con T U"
    shows "map (T \<^sup>*\\\<^sub>A\<^sup>* U) = map T \\\<^sub>B map U"
      using assms preserves_resid_ind by simp

    sublocale simulation Resid B map
      using con_char preserves_con preserves_resid extensionality
      by unfold_locales auto

    lemma is_simulation:
    shows "simulation Resid B map"
      ..

    lemma is_extension:
    shows "map \<circ> incl = F"
      using map_o_incl_eq by auto

    lemma is_universal:
    shows "simulation Resid B map" and "map \<circ> incl = F"
    and "\<And>F'. \<lbrakk>simulation Resid B F'; F' o incl = F\<rbrakk>
                 \<Longrightarrow> \<forall>T. arr T \<longrightarrow> B.cong (F' T) (map T)"
    proof -
      show "simulation Resid B map" and "map \<circ> incl = F"
        using map_o_incl_eq simulation_axioms by auto
      show "\<And>F'. \<lbrakk>simulation Resid B F'; F' o incl = F\<rbrakk> \<Longrightarrow> \<forall>T. arr T \<longrightarrow> F' T \<sim>\<^sub>B map T"
      proof (intro allI impI)
        fix F' T
        assume F': "simulation Resid B F'"
        assume 1: "F' o incl = F"
        interpret F': simulation Resid B F'
          using F' by simp
        show "arr T \<Longrightarrow> B.cong (F' T) (map T)"
        proof (induct T)
          show "arr [] \<Longrightarrow> F' [] \<sim>\<^sub>B map []"
            by (simp add: arr_char F'.extensionality)
          fix t T
          assume ind: "arr T \<Longrightarrow> F' T \<sim>\<^sub>B map T"
          assume arr: "arr (t # T)"
          show "F' (t # T) \<sim>\<^sub>B map (t # T)"
          proof (cases "Arr (t # T)")
            show "\<not> Arr (t # T) \<Longrightarrow> ?thesis"
              using arr arr_char by blast
            assume tT: "Arr (t # T)"
            show ?thesis
            proof (cases "T = []")
              show 2: "T = [] \<Longrightarrow> ?thesis"
                using F' 1 tT B.prfx_reflexive arr map.simps(2) by force
              assume T: "T \<noteq> []"
              have "F' (t # T) \<sim>\<^sub>B F' [t] \<cdot>\<^sub>B map T"
              proof -
                have "F' (t # T) = F' ([t] @ T)"
                  by simp
                also have "... \<sim>\<^sub>B F' [t] \<cdot>\<^sub>B F' T"
                proof -
                  have "composite_of [t] T ([t] @ T)"
                    using T tT
                    by (metis (full_types) Arr.simps(2) Con_Arr_self
                        append_is_composite_of Con_implies_Arr(1) Con_imp_eq_Srcs
                        Con_rec(4) Resid_rec(1) Srcs_Resid seq_char A.arrI)
                  thus ?thesis
                    using F'.preserves_composites B.composite_of_comp_ax
                    by (meson B.comp_extensionality_ax B.composable_def
                        B.composite_of_unq_upto_cong B.composable_iff_comp_not_null\<^sub>C\<^sub>C)
                qed
                also have "F' [t] \<cdot>\<^sub>B F' T \<sim>\<^sub>B F' [t] \<cdot>\<^sub>B map T"
                proof
                  show 0: "F' [t] \<cdot>\<^sub>B F' T \<lesssim>\<^sub>B F' [t] \<cdot>\<^sub>B map T"
                  proof -
                    have "F' [t] \<cdot>\<^sub>B F' T \<frown>\<^sub>B F' [t] \<cdot>\<^sub>B map T"
                    proof
                      show 1: "B.composable (F' [t]) (F' T)"
                        using B.composable_iff_comp_not_null\<^sub>C\<^sub>C calculation by force
                      show "(F' [t] \<cdot>\<^sub>B map T) \\\<^sub>B F' [t] \<frown>\<^sub>B F' T"
                        by (meson 1 B.composableD(1-2) B.composableE B.composable_def
                            B.con_compI\<^sub>C\<^sub>C(1) B.cong_respects_seq B.cong_subst_left(1)
                            B.has_composites B.prfx_implies_con B.prfx_reflexive
                            B.resid_composite_of(2) B.rts_axioms F'.preserves_reflects_arr
                            ind rts.composite_ofE)
                    qed
                    thus ?thesis
                      by (metis B.con_implies_arr(2) B.con_sym B.not_arr_null
                          B.prfx_implies_con B.prfx_transitive B.resid_comp_right_ax
                          F'.extensionality calculation ind)
                  qed
                  show "F' [t] \<cdot>\<^sub>B map T \<lesssim>\<^sub>B F' [t] \<cdot>\<^sub>B F' T"
                  proof -
                    have 1: "F' [t] \<cdot>\<^sub>B map T \<frown>\<^sub>B F' [t] \<cdot>\<^sub>B F' T"
                    proof
                      show "B.composable (F' [t]) (map T)"
                        using 0 B.composable_iff_comp_not_null\<^sub>C\<^sub>C
                        by force
                      show "(F' [t] \<cdot>\<^sub>B F' T) \\\<^sub>B F' [t] \<frown>\<^sub>B map T"
                        by (meson B.con_comp_iff\<^sub>C\<^sub>C B.prfx_implies_con
                            \<open>F' [t] \<cdot>\<^sub>B F' T \<lesssim>\<^sub>B F' [t] \<cdot>\<^sub>B map T\<close>)
                    qed
                    hence "(F' [t] \<cdot>\<^sub>B map T) \\\<^sub>B (F' [t] \<cdot>\<^sub>B F' T) =
                           ((F' [t] \<cdot>\<^sub>B map T) \\\<^sub>B F' [t]) \\\<^sub>B F' T"
                      using B.resid_comp_right_ax B.con_sym by blast
                    thus ?thesis
                      by (metis 1 B.con_arr_self B.con_implies_arr(1) B.cong_reflexive
                          B.not_ide_null B.null_is_zero(2) B.prfx_transitive
                          B.resid_comp_right_ax extensionality ind)
                  qed
                qed
                finally show ?thesis by blast
              qed
              also have "F' [t] \<cdot>\<^sub>B map T = (F' \<circ> incl) t \<cdot>\<^sub>B map T"
                using tT
                by (simp add: arr_char null_char F'.extensionality)
              also have "... = F t \<cdot>\<^sub>B map T"
                using F' 1 by simp
              also have "... = map (t # T)"
                using T tT
                by (metis arr_char list.exhaust map.simps(3))
              finally show ?thesis by simp
            qed
          qed
        qed
      qed
    qed

  end

  lemma simulation_ext_to_paths_comp:
  assumes "rts_with_chosen_composites B comp\<^sub>B"
  and "rts_with_chosen_composites C comp\<^sub>C"
  and "simulation A B F" and "simulation B C G"
  and "\<And>t u. rts.composable B t u \<Longrightarrow> G (comp\<^sub>B t u) = comp\<^sub>C (G t) (G u)"
  shows "simulation_ext_to_paths.map A C comp\<^sub>C (G \<circ> F) = G \<circ> simulation_ext_to_paths.map A B comp\<^sub>B F"
  proof -
    interpret A: rts A
      using assms(3) simulation_def simulation_axioms_def by blast
    interpret B: rts_with_chosen_composites B comp\<^sub>B
      using assms(1) by blast
    interpret C: rts_with_chosen_composites C comp\<^sub>C
      using assms(2) by blast
    interpret F: simulation A B F
      using assms(3) by blast
    interpret G: simulation B C G
      using assms(4) by blast
    interpret GoF: composite_simulation A B C F G ..
    interpret Ap: paths_in_rts A ..
    interpret Fx: simulation_ext_to_paths A B comp\<^sub>B F ..
    interpret G_o_Fx: composite_simulation Ap.Resid B C Fx.map G ..
    interpret GoF_x: simulation_ext_to_paths A C comp\<^sub>C \<open>G \<circ> F\<close> ..
    show "GoF_x.map = G_o_Fx.map"
    proof
      fix T
      show "GoF_x.map T = G_o_Fx.map T"
      proof (cases "Ap.arr T")
        show "\<not> Ap.arr T \<Longrightarrow> ?thesis"
          using G_o_Fx.extensionality GoF_x.extensionality by presburger
        assume T: "Ap.arr T"
        show ?thesis
        proof (induct T rule: Ap.Arr_induct)
          show "Ap.Arr T"
            using T Ap.arr_char by simp
          show "\<And>t. Ap.Arr [t] \<Longrightarrow> GoF_x.map [t] = G_o_Fx.map [t]"
            by auto
          show "\<And>t U. \<lbrakk>Ap.Arr (t # U); U \<noteq> []; GoF_x.map U = G_o_Fx.map U\<rbrakk>
                         \<Longrightarrow> GoF_x.map (t # U) = G_o_Fx.map (t # U)"
          proof -
            fix t U
            assume t: "Ap.Arr (t # U)" and U: "U \<noteq> []"
            assume ind: "GoF_x.map U = G_o_Fx.map U"
            show "GoF_x.map (t # U) = G_o_Fx.map (t # U)"
            proof -
              have "GoF_x.map (t # U) = comp\<^sub>C (GoF_x.map [t]) (GoF_x.map U)"
                by (metis GoF_x.preserves_comp U append_Cons append_Nil
                    list.distinct(1) t)
              also have "... = comp\<^sub>C (G (Fx.map [t])) (G (Fx.map U))"
                using ind by simp
              also have "... = G (comp\<^sub>B (Fx.map [t]) (Fx.map U))"
                by (metis B.composable_iff_comp_not_null\<^sub>C\<^sub>C B.not_arr_null
                    Fx.simulation_ext_to_paths_axioms Fx.preserves_comp U append_Cons
                    append_Nil assms(5) simulation_ext_to_paths.preserves_arr
                    simulation_ext_to_paths_def not_Cons_self2 paths_in_rts.arr_char t)
              also have "... = G (Fx.map ([t] @ U))"
                by (metis Fx.preserves_comp U append.left_neutral append_Cons
                    not_Cons_self2 t)
              also have "... = G_o_Fx.map (t # U)"
                by simp
              finally show ?thesis by blast
            qed
          qed
        qed
      qed
    qed
  qed

  locale simulation_ext_to_composite_completion =
    A: rts A +
    B: extensional_rts_with_composites B +
    F: simulation A B F
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
  and F :: "'a \<Rightarrow> 'b"
  begin

    interpretation Ac: composite_completion A ..

    notation Ac.P.Resid    (infix \<open>\<^sup>*\\<^sub>A\<^sup>*\<close> 70)
    notation Ac.P.Resid1x  (infix \<open>\<^sup>1\\<^sub>A\<^sup>*\<close> 70)
    notation Ac.P.Residx1  (infix \<open>\<^sup>*\\<^sub>A\<^sup>1\<close> 70)
    notation Ac.P.Con      (infix \<open>\<^sup>*\<frown>\<^sub>A\<^sup>*\<close> 70)
    notation B.comp        (infixr \<open>\<cdot>\<^sub>B\<close> 55)
    notation B.con         (infix \<open>\<frown>\<^sub>B\<close> 50)

    interpretation F_ext: simulation_ext_to_paths A B B.comp F ..

    definition map
    where "map = Ac.Q.ext_to_quotient B F_ext.map"

    sublocale simulation Ac.resid B map
      unfolding map_def Ac.resid_def
      using Ac.Q.ext_to_quotient_props [of B F_ext.map] F_ext.simulation_axioms
            F_ext.preserves_ide B.extensional_rts_axioms Ac.P.ide_char Ac.P_ide_iff_NPath
      by blast

    lemma is_simulation:
    shows "simulation Ac.resid B map"
      ..

    lemma is_extension:
    shows "map \<circ> Ac.incl = F"
    proof -
      have "map \<circ> Ac.incl = map \<circ> Ac.Q.quot \<circ> Ac.P.incl"
        using Ac.incl_def by auto
      also have "... = F_ext.map \<circ> Ac.P.incl"
        using Ac.Q.ext_to_quotient_props [of B F_ext.map]
        by (simp add: B.extensional_rts_axioms F_ext.simulation_axioms
            Ac.P_ide_iff_NPath Ac.P.ide_char map_def)
      also have "... = F"
        by (simp add: F_ext.is_extension)
      finally show ?thesis by blast
    qed

    lemma is_universal:
    shows "\<exists>!F'. simulation Ac.resid B F' \<and> F' \<circ> Ac.incl = F"
    proof
      show 0: "simulation Ac.resid B map \<and> map \<circ> Ac.incl = F"
        using simulation_axioms is_extension by auto
      fix F'
      assume F': "simulation Ac.resid B F' \<and> F' \<circ> Ac.incl = F"
      interpret F': simulation Ac.resid B F'
        using F' by blast
      show "F' = map"
      proof -
        have "F' \<circ> Ac.Q.quot = F_ext.map"
        proof -
          interpret F'_o_quot: simulation Ac.P.Resid B \<open>F' \<circ> Ac.Q.quot\<close>
            using F' Ac.Q.quotient_is_simulation Ac.resid_def by auto
          interpret incl: simulation A Ac.P.Resid Ac.P.incl
            using Ac.P.incl_is_simulation by blast
          interpret F'_o_quot_o_incl: composite_simulation A Ac.P.Resid B Ac.P.incl
                                        \<open>F' \<circ> Ac.Q.quot\<close>
            ..
          have "(F' \<circ> Ac.Q.quot) \<circ> Ac.P.incl = F"
            using F' Ac.incl_def by auto
          hence "\<forall>T. Ac.P.arr T \<longrightarrow> (F' \<circ> Ac.Q.quot) T \<sim>\<^sub>B F_ext.map T"
            using F_ext.is_universal(3) F'_o_quot.simulation_axioms by blast
          hence "\<forall>T. Ac.P.arr T \<longrightarrow> (F' \<circ> Ac.Q.quot) T = F_ext.map T"
            using B.cong_char by blast
          thus ?thesis
          proof -
            have "\<forall>as. (F' \<circ> Ac.Q.quot) as = F_ext.map as \<or> \<not> Ac.P.arr as"
              using \<open>\<forall>T. Ac.P.arr T \<longrightarrow> (F' \<circ> Ac.Q.quot) T = F_ext.map T\<close> by blast
            then show ?thesis
              using F'_o_quot.extensionality F_ext.extensionality by fastforce
          qed
        qed
        thus ?thesis 
          by (metis (no_types, lifting) "0" B.extensional_rts_axioms F'
              F_ext.preserves_ide F_ext.simulation_axioms Ac.P_ide_iff_NPath
              Ac.Q.ext_to_quotient_props(2) Ac.Q.is_couniversal map_def mem_Collect_eq
              Ac.resid_def)
      qed
    qed

  end

  context composite_completion
  begin

    lemma arrows_factor_as_paths:
    assumes "arr \<T>"
    shows "\<exists>T. P.arr T \<and> simulation_ext_to_paths.map R resid comp incl T = \<T>"
    proof -
      interpret inclx: simulation_ext_to_paths R resid comp incl ..
      let ?T = "N.Cong_class_rep \<T>"
      have "P.arr ?T"
        by (metis N.Cong_class_memb_is_arr N.rep_in_Cong_class
            Q.quotient_by_coherent_normal_axioms assms
            quotient_by_coherent_normal.arr_char resid_def)
      moreover have "inclx.map ?T = \<T>"
      proof -
        have "\<And>T. P.arr T \<Longrightarrow> inclx.map T = \<lbrace>T\<rbrace>"
        proof -
          fix T
          show "P.arr T \<Longrightarrow> inclx.map T = \<lbrace>T\<rbrace>"
          proof (induct T)
            show "P.arr [] \<Longrightarrow> inclx.map [] = Q.quot []"
              using P.not_arr_null P.null_char by auto
            fix a U
            assume ind: "P.arr U \<Longrightarrow> inclx.map U = Q.quot U"
            assume aU: "P.arr (a # U)"
            show "inclx.map (a # U) = Q.quot (a # U)"
              using Q.quotient_is_simulation aU cong_char incl_def
                    inclx.is_universal(3) resid_def
              by force
          qed
        qed
        thus ?thesis
          using Q.arr_char assms calculation resid_def by force
      qed
      ultimately show ?thesis by blast
    qed

  end

  lemma simulation_ext_to_composite_completion_comp:
  assumes "extensional_rts_with_composites B"
  and "extensional_rts_with_composites C"
  and "simulation A B F" and "simulation B C G"
  shows "simulation_ext_to_composite_completion.map A C (G \<circ> F) =
         G \<circ> simulation_ext_to_composite_completion.map A B F"
  proof -
    interpret B: extensional_rts_with_composites B
      using assms(1) by blast
    interpret C: extensional_rts_with_composites C
      using assms(2) by blast
    interpret F: simulation A B F
      using assms(3) by blast
    interpret G: simulation B C G
      using assms(4) by blast
    interpret GoF: composite_simulation A B C F G ..
    interpret Ac: composite_completion A ..
    interpret Fc: simulation_ext_to_composite_completion A B F ..
    interpret GoFc: simulation_ext_to_composite_completion A C GoF.map ..
    show "GoFc.map = G \<circ> Fc.map"
    proof -
      have "G \<circ> Fc.map \<circ> Ac.incl = GoFc.map \<circ> Ac.incl"
        using GoFc.is_extension Fc.is_extension comp_assoc by metis
      thus ?thesis
        using GoFc.is_extension GoFc.is_universal GoFc.is_simulation
              G.simulation_axioms Fc.is_simulation simulation_comp
        by metis
    qed
  qed

  (*
   * TODO: Localize to context rts?
   *)
  lemma composite_completion_of_rts:
  assumes "rts A"
  shows "\<exists>(A' :: 'a composite_completion.arr resid) I.
             extensional_rts_with_composites A' \<and> simulation A A' I \<and>
          (\<forall>B (J :: 'a \<Rightarrow> 'c). extensional_rts_with_composites B \<and> simulation A B J
                                 \<longrightarrow> (\<exists>!J'. simulation A' B J' \<and> J' o I = J))"
  proof (intro exI conjI)
    interpret A: rts A
      using assms by auto
    interpret A': composite_completion A ..
    show "extensional_rts_with_composites A'.resid"
      ..
    show "simulation A A'.resid A'.incl"
      using A'.incl_is_simulation by simp
    show "\<forall>B (J :: 'a \<Rightarrow> 'c). extensional_rts_with_composites B \<and> simulation A B J
                                \<longrightarrow> (\<exists>!J'. simulation A'.resid B J' \<and> J' o A'.incl = J)"
    proof (intro allI impI)
      fix B :: "'c resid" and J
      assume 1: "extensional_rts_with_composites B \<and> simulation A B J"
      interpret B: extensional_rts_with_composites B
        using 1 by simp
      interpret J: simulation A B J
        using 1 by simp
      interpret J: simulation_ext_to_composite_completion A B J
        ..
      show "\<exists>!J'. simulation A'.resid B J' \<and> J' \<circ> A'.incl = J"
        using J.is_universal by auto
    qed
  qed

  section "Constructions on RTS's"

  subsection "Products of RTS's"

  locale product_rts =
    A: rts A +
    B: rts B
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
  begin

    notation A.con     (infix \<open>\<frown>\<^sub>A\<close> 50)
    notation A.prfx    (infix \<open>\<lesssim>\<^sub>A\<close> 50)
    notation A.cong    (infix \<open>\<sim>\<^sub>A\<close> 50)

    notation B.con     (infix \<open>\<frown>\<^sub>B\<close> 50)
    notation B.prfx    (infix \<open>\<lesssim>\<^sub>B\<close> 50)
    notation B.cong    (infix \<open>\<sim>\<^sub>B\<close> 50)

    type_synonym ('c, 'd) arr = "'c * 'd"

    abbreviation (input) Null :: "('a, 'b) arr"                                 
    where "Null \<equiv> (A.null, B.null)"

    definition resid :: "('a, 'b) arr \<Rightarrow> ('a, 'b) arr \<Rightarrow> ('a, 'b) arr"
    where "resid t u = (if fst t \<frown>\<^sub>A fst u \<and> snd t \<frown>\<^sub>B snd u
                        then (fst t \\\<^sub>A fst u, snd t \\\<^sub>B snd u)
                        else Null)"

    notation resid      (infix \<open>\\<close> 70)

    sublocale partial_magma resid
      by unfold_locales
        (metis A.con_implies_arr(1-2) A.not_arr_null fst_conv resid_def)

    lemma is_partial_magma:
    shows "partial_magma resid"
      ..

    lemma null_char [simp]:
    shows "null = Null"
      by (metis B.null_is_zero(1) ex_un_null null_is_zero(1) resid_def B.conE snd_conv)

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

    notation con     (infix \<open>\<frown>\<close> 50)

    lemma arr_char [iff]:
    shows "arr t \<longleftrightarrow> A.arr (fst t) \<and> B.arr (snd t)"
      by (metis (no_types, lifting) A.arr_def B.arr_def B.conE null_char resid_def
          arr_def con_def snd_eqD)

    lemma ide_char [iff]:
    shows "ide t \<longleftrightarrow> A.ide (fst t) \<and> B.ide (snd t)"
      by (metis (no_types, lifting) A.residuation_axioms B.residuation_axioms
          arr_char arr_def fst_conv null_char prod.collapse resid_def residuation.conE
          residuation.ide_def residuation.ide_implies_arr residuation_axioms snd_conv)

    lemma con_char [iff]:
    shows "t \<frown> u \<longleftrightarrow> fst t \<frown>\<^sub>A fst u \<and> snd t \<frown>\<^sub>B snd u"
      by (simp add: con_def resid_def B.con_def)

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

    notation prfx    (infix \<open>\<lesssim>\<close> 50)
    notation cong    (infix \<open>\<sim>\<close> 50)

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
                fst_conv A.in_targetsE B.in_targetsE A.arr_resid_iff_con
                B.arr_resid_iff_con A.trg_def B.trg_def snd_conv)
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
        by (metis A.extensionality B.extensionality cong_char prod.collapse)
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
  for A1 :: "'a1 resid"      (infix \<open>\\<^sub>A\<^sub>1\<close> 70)
  and A0 :: "'a0 resid"      (infix \<open>\\<^sub>A\<^sub>0\<close> 70)
  and B1 :: "'b1 resid"      (infix \<open>\\<^sub>B\<^sub>1\<close> 70)
  and B0 :: "'b0 resid"      (infix \<open>\\<^sub>B\<^sub>0\<close> 70)
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
        using map_def F1.extensionality F0.extensionality by auto
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
  for A1 :: "'a1 resid"    (infix \<open>\\<^sub>A\<^sub>1\<close> 70)
  and A0 :: "'a0 resid"    (infix \<open>\\<^sub>A\<^sub>0\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
  and F :: "'a1 * 'a0 \<Rightarrow> 'b"
  begin

    lemma fixing_ide_gives_simulation_1:
    assumes "A1.ide a1"
    shows "simulation A0 B (\<lambda>t0. F (a1, t0))"
    proof
      show "\<And>t0. \<not> A0.arr t0 \<Longrightarrow> F (a1, t0) = B.null"
        using assms extensionality A.arr_char by simp
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
        using assms extensionality A.arr_char by simp
      show "\<And>t1 u1. A1.con t1 u1 \<Longrightarrow> B.con (F (t1, a0)) (F (u1, a0))"
        using assms A.con_char preserves_con by auto
      show "\<And>t1 u1. A1.con t1 u1 \<Longrightarrow> F (t1 \\\<^sub>A\<^sub>1 u1, a0) = F (t1, a0) \\\<^sub>B F (u1, a0)"
        using assms A.con_char A.resid_def preserves_resid
        by (metis A0.ideE fst_conv snd_conv)
    qed

  end

  subsection "Sub-RTS's"

  text\<open>
    A sub-RTS of an RTS \<open>R\<close> may be determined by specifying a subset of the transitions
    of \<open>R\<close> that is closed under residuation and in addition includes some common source
    for every consistent pair of transitions contained in it.
  \<close>

  locale sub_rts =
    R: rts R
  for R :: "'a resid"  (infix \<open>\\<^sub>R\<close> 70)
  and Arr :: "'a \<Rightarrow> bool" +
  assumes inclusion: "Arr t \<Longrightarrow> R.arr t"
  and resid_closed: "\<lbrakk>Arr t; Arr u; R.con t u\<rbrakk> \<Longrightarrow> Arr (t \\\<^sub>R u)"
  and enough_sources: "\<lbrakk>Arr t; Arr u; R.con t u\<rbrakk> \<Longrightarrow>
                          \<exists>a. Arr a \<and> a \<in> R.sources t \<and> a \<in> R.sources u"
  begin

    notation R.con     (infix \<open>\<frown>\<^sub>R\<close> 50)
    notation R.prfx    (infix \<open>\<lesssim>\<^sub>R\<close> 50)
    notation R.cong    (infix \<open>\<sim>\<^sub>R\<close> 50)

    definition resid :: "'a resid"  (infix \<open>\\<close> 70)
    where "t \\ u \<equiv> if Arr t \<and> Arr u \<and> t \<frown>\<^sub>R u then t \\\<^sub>R u else R.null"

    sublocale partial_magma resid
      using R.not_con_null(2) R.null_is_zero(1) resid_def
      by unfold_locales metis

    lemma is_partial_magma:
    shows "partial_magma resid"
      ..

    lemma null_char:
    shows "null = R.null"
      by (metis R.not_arr_null inclusion null_eqI resid_def)

    sublocale residuation resid
      using R.conE R.con_sym R.not_con_null(1) null_is_zero(1) resid_def
      apply unfold_locales
        apply metis
       apply (metis R.con_def R.con_imp_arr_resid resid_closed)
      by (metis (no_types, lifting) R.con_def R.cube resid_closed)

    lemma is_residuation:
    shows "residuation resid"
      ..

    notation con     (infix \<open>\<frown>\<close> 50)

    lemma arr_char:
    shows "arr t \<longleftrightarrow> Arr t"
      by (metis R.con_arr_self R.con_def R.not_arr_null arrE con_def inclusion
          null_is_zero(2) resid_def residuation.con_implies_arr(1) residuation_axioms)

    lemma ide_char:
    shows "ide t \<longleftrightarrow> Arr t \<and> R.ide t"
      by (metis R.ide_def arrI arr_char con_def ide_def not_arr_null resid_def)

    lemma con_char:
    shows "con t u \<longleftrightarrow> Arr t \<and> Arr u \<and> R.con t u"
      by (metis R.conE arr_char con_def not_arr_null null_is_zero(1) resid_def)

    lemma trg_char:
    shows "trg = (\<lambda>t. if arr t then R.trg t else null)"
      using arr_char trg_def R.trg_def resid_def by fastforce

    sublocale rts resid
      using arr_char ide_char con_char trg_char resid_def resid_closed inclusion
      apply unfold_locales
      using R.prfx_reflexive trg_def apply force
         apply (simp add: R.resid_arr_ide)
        apply simp
       apply (meson R.con_sym R.in_sourcesE enough_sources)
      by (metis (no_types, lifting) R.con_target arr_resid_iff_con con_sym_ax null_char)

    lemma is_rts:
    shows "rts resid"
      ..

    notation prfx    (infix \<open>\<lesssim>\<close> 50)
    notation cong    (infix \<open>\<sim>\<close> 50)

    lemma sources_subset:
    shows "sources t \<subseteq> {a. Arr t \<and> a \<in> R.sources t}"
      using con_char ide_char by fastforce

    lemma targets_subset:
    shows "targets t \<subseteq> {b. Arr t \<and> b \<in> R.targets t}"
    proof
      fix b
      assume b: "b \<in> targets t"
      show "b \<in> {b. Arr t \<and> b \<in> R.targets t}"
      by (metis CollectI R.rts_axioms arr_char arr_iff_has_target b con_char
        emptyE ide_char in_targetsE rts.in_targetsI trg_char)
    qed

    lemma prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "prfx t u \<longleftrightarrow> Arr t \<and> Arr u \<and> R.prfx t u"
      using arr_char con_char ide_char
      by (metis R.prfx_implies_con prfx_implies_con resid_closed resid_def)

    lemma cong_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "t \<sim> u \<longleftrightarrow> Arr t \<and> Arr u \<and> t \<sim>\<^sub>R u"
      using prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S by force

    lemma composite_of_char:
    shows "composite_of t u v \<longleftrightarrow> Arr t \<and> Arr u \<and> Arr v \<and> R.composite_of t u v"
    proof
      show "composite_of t u v \<Longrightarrow> Arr t \<and> Arr u \<and> Arr v \<and> R.composite_of t u v"
        by (metis R.composite_of_def R.con_sym composite_ofE con_char prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S
            resid_def rts.prfx_implies_con rts_axioms)
      show "Arr t \<and> Arr u \<and> Arr v \<and> R.composite_of t u v \<Longrightarrow> composite_of t u v"
        using composite_of_def resid_closed resid_def rts.composite_ofE ide_char
        by fastforce
    qed

    lemma join_of_char:
    shows "join_of t u v \<longleftrightarrow> Arr t \<and> Arr u \<and> Arr v \<and> R.join_of t u v"
      using composite_of_char
      by (metis R.bounded_imp_con R.join_of_def join_of_def resid_closed resid_def)

    lemma preserves_weakly_extensional_rts:
    assumes "weakly_extensional_rts R"
    shows "weakly_extensional_rts resid"
      by (metis assms cong_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S ide_char rts_axioms weakly_extensional_rts.intro
          weakly_extensional_rts.weak_extensionality weakly_extensional_rts_axioms.intro)

    lemma preserves_extensional_rts:
    assumes "extensional_rts R"
    shows "extensional_rts resid"
      by (meson assms extensional_rts.cong_char extensional_rts.intro
          extensional_rts_axioms.intro prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S rts_axioms)

    abbreviation incl
    where "incl t \<equiv> if arr t then t else null"

    sublocale Incl: simulation resid R incl
      using resid_closed resid_def
      by unfold_locales (auto simp add: null_char arr_char con_char)

    lemma inclusion_is_simulation:
    shows "simulation resid R incl"
      ..

    lemma incl_cancel_left:
    assumes "transformation X resid F G T" and "transformation X resid F' G' T'"
    and "incl \<circ> T = incl \<circ> T'"
    shows "T = T'"
    proof
      fix x
      interpret T: transformation X resid F G T
        using assms(1) by blast
      interpret T': transformation X resid F' G' T'
        using assms(2) by blast
      show "T x = T' x"
      proof -
        have "T x = (incl \<circ> T) x"
          using T.extensionality T.A.prfx_reflexive T.respects_cong arr_char prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S
          by auto
        also have "... = (incl \<circ> T') x"
          using assms(3) by auto
        also have "... = T' x"
          using T'.extensionality T.A.prfx_reflexive T'.respects_cong arr_char prfx_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S
          by fastforce
        finally show ?thesis by blast
      qed
    qed

    lemma incl_reflects_con:
    assumes "R.con (incl t) (incl u)"
    shows "con t u"
      by (metis (full_types) R.not_con_null(1) R.not_con_null(2) arr_char
          assms con_char null_char)

    lemma corestriction_of_simulation:
    assumes "simulation X R F"
    and "\<And>x. residuation.arr X x \<Longrightarrow> Arr (F x)"
    shows "simulation X resid F" and "incl \<circ> F = F"
    proof -
      interpret X: rts X
        using assms(1) simulation_def by blast
      interpret F: simulation X R F
        using assms(1) by blast
      interpret F': simulation X resid F
        using assms(2) con_char resid_def F.extensionality null_char
              X.con_implies_arr(1-2)
        by unfold_locales auto
      show 1: "simulation X resid F" ..
      show "incl \<circ> F = F"
        using F.extensionality null_char by fastforce
    qed

    lemma corestriction_of_transformation:
    assumes "simulation X resid F" and "simulation X resid G"
    and "transformation X R F G T"
    and "\<And>x. residuation.arr X x \<Longrightarrow> Arr (T x)"
    shows "transformation X resid F G T" and "incl \<circ> T = T"
    proof -
      interpret X: rts X
        using assms(3) transformation_def by blast
      interpret R: weakly_extensional_rts R
        using assms(3) transformation_def by blast
      interpret S: weakly_extensional_rts resid
        by (simp add: R.weakly_extensional_rts_axioms preserves_weakly_extensional_rts)
      interpret F: simulation X resid F
        using assms(1) transformation_def by blast
      interpret G: simulation X resid G
        using assms(2) transformation_def by blast
      interpret T: transformation X R F G T
        using assms(3) by blast
      interpret T': transformation X resid F G T
      proof
        show "\<And>f. \<not> X.arr f \<Longrightarrow> T f = null"
          by (simp add: T.extensionality null_char)
        show "\<And>x x'. \<lbrakk>X.ide x; X.cong x x'\<rbrakk> \<Longrightarrow> T x = T x'"
          using T.respects_cong_ide by blast
        show "\<And>f. X.ide f \<Longrightarrow> src (T f) = F f"
          by (metis F.preserves_ide F.preserves_reflects_arr R.arr_resid_iff_con
              R.arr_src_iff_arr R.ide_implies_arr R.resid_arr_src S.con_imp_eq_src
              S.src_ide T.F.preserves_ide T.preserves_src X.con_implies_arr(2)
              X.ideE arr_char assms(4) con_char)
        show "\<And>f. X.ide f \<Longrightarrow> trg (T f) = G f"
          by (simp add: T.preserves_trg arr_char assms(4) trg_char)
        show "\<And>a f. a \<in> X.sources f \<Longrightarrow> T a \\ F f = T (X a f)"
          by (metis F.preserves_reflects_arr R.residuation_axioms T.naturality1_ax
              X.arr_iff_has_source X.ex_un_null X.ide_implies_arr X.in_sourcesE
              X.not_arr_null X.null_eqI X.source_is_prfx arr_char assms(4) resid_def
              residuation.conI)
        show "\<And>a f. a \<in> X.sources f \<Longrightarrow> F f \\ T a = G f"
          by (metis F.preserves_reflects_arr R.arr_resid_iff_con
              T.G.preserves_reflects_arr T.naturality2_ax X.in_sourcesE
              X.residuation_axioms arr_char assms(4) resid_def
              residuation.con_implies_arr(1) residuation.ide_implies_arr)
        show "\<And>a f. a \<in> X.sources f \<Longrightarrow> join_of (T a) (F f) (T f)"
          by (meson F.preserves_reflects_arr T.naturality3 X.con_implies_arr(1)
              X.ide_implies_arr X.in_sourcesE arr_char assms(4) join_of_char)
      qed
      show 1: "transformation X resid F G T" ..
      show "incl \<circ> T = T"
        using T.extensionality arr_char assms(4) null_char by fastforce
    qed

  end

  locale source_replete_sub_rts =
    R: rts R
  for R :: "'a resid"  (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool" +
  assumes inclusion: "Arr t \<Longrightarrow> R.arr t"
  and resid_closed: "\<lbrakk>Arr t; Arr u; R.con t u\<rbrakk> \<Longrightarrow> Arr (t \\\<^sub>R u)"
  and source_replete: "Arr t \<Longrightarrow> R.sources t \<subseteq> Collect Arr"
  begin

    sublocale sub_rts
      using inclusion resid_closed source_replete
      apply unfold_locales
        apply auto[2]
      by (metis Collect_mem_eq Collect_mono_iff R.con_imp_common_source
          R.sources_eqI R.src_in_sources)

    lemma is_sub_rts:
    shows "sub_rts R Arr"
      ..

    lemma sources_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "sources t = {a. Arr t \<and> a \<in> R.sources t}"
      using source_replete sources_subset
      apply auto[1]
      by (metis Ball_Collect R.in_sourcesE con_char ide_char in_sourcesI)

    lemma targets_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S:
    shows "targets t = {b. Arr t \<and> b \<in> R.targets t}"
    proof
      show "targets t \<subseteq> {b. Arr t \<and> b \<in> R.targets t}"
        using targets_subset by blast
      show "{b. Arr t \<and> b \<in> R.targets t} \<subseteq> targets t"
      proof
        fix b
        assume b: "b \<in> {b. Arr t \<and> b \<in> R.targets t}"
        show "b \<in> targets t"
        by (metis (no_types, lifting) R.in_targetsE R.rts_axioms arr_char b
          con_arr_self mem_Collect_eq rts.in_sourcesI sources_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S sources_resid
          trg_char trg_def trg_in_targets)
      qed
    qed

    interpretation P\<^sub>R: paths_in_rts R
      ..
    interpretation P: paths_in_rts resid
      ..

    (*
     * TODO: It might be possible to prove the following without the additional assumption
     * on sources, if the definition of path were generalized so that only nonempty
     * intersection of the targets of one transition with the sources of the next were
     * required, rather than containment.
     *)

    lemma path_reflection:
    shows "\<lbrakk>P\<^sub>R.Arr T; set T \<subseteq> Collect Arr\<rbrakk> \<Longrightarrow> P.Arr T"
    proof (induct T, simp)
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
          using 1 set arr_char by simp
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
              using targets_subset by blast
            also have "... \<subseteq> R.sources (hd T)"
              using T tT
              by (metis P\<^sub>R.Arr.simps(3) P\<^sub>R.Srcs_simp\<^sub>P list.collapse)
            also have "... \<subseteq> P.Srcs T"
              using P.Arr_imp_arr_hd P.Srcs_simp\<^sub>P \<open>P.Arr T\<close> sources_char\<^sub>S\<^sub>R\<^sub>T\<^sub>S arr_char
              by force
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

  end

  locale sub_rts_of_weakly_extensional_rts =
    R: weakly_extensional_rts R +
    sub_rts R Arr
  for R :: "'a resid"  (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool"
  begin

    sublocale weakly_extensional_rts resid
      using R.weakly_extensional_rts_axioms preserves_weakly_extensional_rts
      by blast

    lemma is_weakly_extensional_rts:
    shows "weakly_extensional_rts resid"
      ..

    lemma src_char:
    shows "src = (\<lambda>t. if arr t then R.src t else null)"
    proof
      fix t
      show "src t = (if arr t then R.src t else null)"
        by (metis R.src_eqI con_arr_src(2) con_char ide_char ide_src src_def)
    qed

    lemma targets_char:
    assumes "arr t"
    shows "targets t = {R.trg t}"
      using assms trg_char trg_in_targets arr_has_un_target by auto

  end

  locale sub_rts_of_extensional_rts =
    R: extensional_rts R +
    sub_rts R Arr
  for R :: "'a resid"  (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool"
  begin

    sublocale sub_rts_of_weakly_extensional_rts ..

    sublocale extensional_rts resid
      using R.extensional_rts_axioms preserves_extensional_rts
      by blast

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

  end

  text \<open>
    Here we justify the terminology ``normal sub-RTS'', which was introduced earlier,
    by showing that a normal sub-RTS really is a sub-RTS.
  \<close>

  lemma (in normal_sub_rts) is_sub_rts:
  shows "source_replete_sub_rts resid (\<lambda>t. t \<in> \<NN>)"
    using elements_are_arr ide_closed
    apply unfold_locales
       apply blast
      apply (meson R.con_def R.con_imp_coinitial R.con_sym_ax forward_stable)
    by blast

end
