section \<open>Package Logic\<close>

text \<open>In this section, we define our package logic, as described in \<^cite>\<open>"Dardinier22"\<close>,
and then prove that this logic is sound and complete for packaging magic wands.\<close>

theory PackageLogic
  imports Main SepAlgebra
begin

subsection Definitions

type_synonym 'a abool = "'a \<Rightarrow> bool"

datatype 'a aassertion =
  AStar "'a aassertion" "'a aassertion"
| AImp "'a abool" "'a aassertion"
| ASem "'a abool"

locale package_logic = sep_algebra +

  fixes unit :: "'a"
  fixes stable :: "'a \<Rightarrow> bool"

  assumes unit_neutral: "Some a = a \<oplus> unit"
      and stable_sum: "stable a \<Longrightarrow> stable b \<Longrightarrow> Some x = a \<oplus> b \<Longrightarrow> stable x"
      and stable_unit: "stable unit"

begin

fun sat :: "'a aassertion \<Rightarrow> 'a \<Rightarrow> bool" where
  "sat (AStar A B) \<phi> \<longleftrightarrow> (\<exists>a b. Some \<phi> = a \<oplus> b \<and> sat A a \<and> sat B b)"
| "sat (AImp b A) \<phi> \<longleftrightarrow> (b \<phi> \<longrightarrow> sat A \<phi>)"
| "sat (ASem A) \<phi> \<longleftrightarrow> A \<phi>"

definition mono_pure_cond where
  "mono_pure_cond b \<longleftrightarrow> (\<forall>\<phi>. b \<phi> \<longleftrightarrow> b |\<phi>| ) \<and> (\<forall>\<phi>' \<phi> r. pure r \<and> Some \<phi>' = \<phi> \<oplus> r \<and> \<not> b \<phi> \<longrightarrow> \<not> b \<phi>')"

definition bool_conj where
  "bool_conj a b x \<longleftrightarrow> a x \<and> b x"

type_synonym 'c pruner = "'c \<Rightarrow> bool"

(* Only positively, so not-well defined = false *)
definition mono_pruner :: "'a pruner \<Rightarrow> bool" where
  "mono_pruner p \<longleftrightarrow> (\<forall>\<phi>' \<phi> r. pure r \<and> p \<phi> \<and> Some \<phi>' = \<phi> \<oplus> r \<longrightarrow> p \<phi>')"
(* opposite of mono_cond *)

fun wf_assertion where
  "wf_assertion (AStar A B) \<longleftrightarrow> wf_assertion A \<and> wf_assertion B"
| "wf_assertion (AImp b A) \<longleftrightarrow> mono_pure_cond b \<and> wf_assertion A"
| "wf_assertion (ASem A) \<longleftrightarrow> mono_pruner A"

type_synonym 'c transformer = "'c \<Rightarrow> 'c"

type_synonym 'c ext_state = "'c \<times> 'c \<times> 'c transformer"

inductive package_rhs ::
  "'a \<Rightarrow> 'a \<Rightarrow> 'a ext_state set \<Rightarrow> 'a abool \<Rightarrow> 'a aassertion \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a ext_state set \<Rightarrow> bool" where 

  AStar: "\<lbrakk> package_rhs \<phi> f S pc A \<phi>' f' S' ; package_rhs \<phi>' f' S' pc B \<phi>'' f'' S'' \<rbrakk> \<Longrightarrow> package_rhs \<phi> f S pc (AStar A B) \<phi>'' f'' S''"
| AImp: "package_rhs \<phi> f S (bool_conj pc b) A \<phi>' f' S' \<Longrightarrow> package_rhs \<phi> f S pc (AImp b A) \<phi>' f' S'"
(* witness means we *choose* how we satisfy B *)
| ASem: "\<lbrakk> \<And>a u T b. (a, u, T) \<in> S \<Longrightarrow> pc a \<Longrightarrow> b = witness (a, u, T) \<Longrightarrow> a \<succeq> b \<and> B b ;
  S' = { (a, u, T) |a u T. (a, u, T) \<in> S \<and> \<not> pc a }
  \<union> { (a \<ominus> b, the (u \<oplus> b), T) |a u T b. (a, u, T) \<in> S \<and> pc a \<and> b = witness (a, u, T) } \<rbrakk>
  \<Longrightarrow> package_rhs \<phi> f S pc (ASem B) \<phi> f S'"

| AddFromOutside: "\<lbrakk> Some \<phi> = \<phi>' \<oplus> m ; package_rhs \<phi>' f' S' pc A \<phi>'' f'' S'' ; stable m ; Some f' = f \<oplus> m ;
  S' = { (r, u, T) |a u T r. (a, u, T) \<in> S \<and> Some r = a \<oplus> (T f' \<ominus> T f)  \<and> r ## u } \<rbrakk>
  \<Longrightarrow> package_rhs \<phi> f S pc A \<phi>'' f'' S''"


definition package_sat where
  "package_sat pc A a' u' u \<longleftrightarrow> (pc |a'| \<longrightarrow> (\<exists>x. Some x = |a'| \<oplus> (u' \<ominus> u ) \<and> sat A x))"

definition package_rhs_connection :: "'a \<Rightarrow> 'a \<Rightarrow> 'a ext_state set \<Rightarrow> 'a abool \<Rightarrow> 'a aassertion \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a ext_state set \<Rightarrow> bool" where
  "package_rhs_connection \<phi> f S pc A \<phi>' f' S' \<longleftrightarrow> f' \<succeq> f \<and> \<phi> ## f \<and> \<phi> \<oplus> f = \<phi>' \<oplus> f' \<and> stable f' \<and>
    (\<forall>(a, u, T) \<in> S. \<exists>au. Some au = a \<oplus> u \<and> (au ## (T f' \<ominus> T f) \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u)))"

definition mono_transformer :: "'a transformer \<Rightarrow> bool" where
  "mono_transformer T \<longleftrightarrow> (\<forall>\<phi> \<phi>'. \<phi>' \<succeq> \<phi> \<longrightarrow> T \<phi>' \<succeq> T \<phi>) \<and> T unit = unit"

definition valid_package_set where
  "valid_package_set S f \<longleftrightarrow> (\<forall>(a, u, T) \<in> S. a ## u \<and> |a| \<succeq> |u| \<and> mono_transformer T \<and> a \<succeq> |T f| )"

definition intuitionistic where
  "intuitionistic A \<longleftrightarrow> (\<forall>\<phi>' \<phi>. \<phi>' \<succeq> \<phi> \<and> A \<phi> \<longrightarrow> A \<phi>')"

definition pure_remains where
  "pure_remains S \<longleftrightarrow> (\<forall>(a, u, p) \<in> S. pure a)"

definition is_footprint_general :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a aassertion \<Rightarrow> 'a aassertion \<Rightarrow> bool" where
  "is_footprint_general w R A B \<longleftrightarrow> (\<forall>a b. sat A a \<and> Some b = a \<oplus> R a w \<longrightarrow> sat B b)"

definition is_footprint_standard :: "'a \<Rightarrow> 'a aassertion \<Rightarrow> 'a aassertion \<Rightarrow> bool" where
  "is_footprint_standard w A B \<longleftrightarrow> (\<forall>a b. sat A a \<and> Some b = a \<oplus> w \<longrightarrow> sat B b)"



subsection Lemmas

lemma is_footprint_generalI:
  assumes "\<And>a b. sat A a \<and> Some b = a \<oplus> R a w \<Longrightarrow> sat B b"
  shows "is_footprint_general w R A B"
  using assms is_footprint_general_def by blast

lemma is_footprint_standardI:
  assumes "\<And>a b. sat A a \<and> Some b = a \<oplus> w \<Longrightarrow> sat B b"
  shows "is_footprint_standard w A B"
  using assms is_footprint_standard_def by blast


lemma mono_pure_condI:
  assumes "\<And>\<phi>. b \<phi> \<longleftrightarrow> b |\<phi>|"
      and "\<And>\<phi> \<phi>' r. pure r \<and> Some \<phi>' = \<phi> \<oplus> r \<and> \<not> b \<phi> \<Longrightarrow> \<not> b \<phi>'"
    shows "mono_pure_cond b"
  using assms(1) assms(2) mono_pure_cond_def by blast

lemma mono_pure_cond_conj:
  assumes "mono_pure_cond pc"
      and "mono_pure_cond b"
    shows "mono_pure_cond (bool_conj pc b)"
proof (rule mono_pure_condI)
  show "\<And>\<phi>. bool_conj pc b \<phi> = bool_conj pc b  |\<phi>|"
    by (metis assms(1) assms(2) bool_conj_def mono_pure_cond_def)
  show "\<And>\<phi> \<phi>' r. pure r \<and> Some \<phi>' = \<phi> \<oplus> r \<and> \<not> bool_conj pc b \<phi> \<Longrightarrow> \<not> bool_conj pc b \<phi>'"
    by (metis assms(1) assms(2) bool_conj_def mono_pure_cond_def)
qed

lemma bigger_sum:
  assumes "Some \<phi> = a \<oplus> b"
      and "\<phi>' \<succeq> \<phi>"
    shows "\<exists>b'. b' \<succeq> b \<and> Some \<phi>' = a \<oplus> b'"
proof -
  obtain r where "Some \<phi>' = \<phi> \<oplus> r"
    using assms(2) greater_def by blast
  then obtain b' where "Some b' = b \<oplus> r"
    by (metis assms(1) asso2 domD domI domIff)
  then show ?thesis
    by (metis \<open>Some \<phi>' = \<phi> \<oplus> r\<close> assms(1) asso1 commutative sep_algebra.greater_equiv sep_algebra_axioms)
qed

lemma wf_assertion_sat_larger_pure:
  assumes "wf_assertion A"
      and "sat A \<phi>"
      and "Some \<phi>' = \<phi> \<oplus> r"
      and "pure r"
    shows "sat A \<phi>'"
  using assms
proof (induct arbitrary: \<phi> \<phi>' r rule: wf_assertion.induct)
  case (1 A B)
  then obtain a b where "Some \<phi> = a \<oplus> b" "sat A a" "sat B b" by (meson sat.simps(1))
  then obtain b' where "Some b' = b \<oplus> r"
    by (metis "1.prems"(3) asso2 option.collapse)
  moreover obtain a' where "Some a' = a \<oplus> r"
    by (metis "1.prems"(3) \<open>Some \<phi> = a \<oplus> b\<close> asso2 commutative option.collapse)
  ultimately show ?case
    using 1
    by (metis \<open>Some \<phi> = a \<oplus> b\<close> \<open>sat A a\<close> \<open>sat B b\<close> asso1 sat.simps(1) wf_assertion.simps(1))
next
  case (2 b A)
  then show ?case
    by (metis mono_pure_cond_def sat.simps(2) wf_assertion.simps(2))
next
  case (3 A)
  then show ?case
    by (metis mono_pruner_def sat.simps(3) wf_assertion.simps(3))
qed


lemma package_satI:
  assumes "pc |a'| \<Longrightarrow> (\<exists>x. Some x = |a'| \<oplus> (u' \<ominus> u ) \<and> sat A x)"
  shows "package_sat pc A a' u' u"
  by (simp add: assms package_sat_def)


lemma package_rhs_connection_instantiate:
  assumes "package_rhs_connection \<phi> f S pc A \<phi>' f' S'"
      and "(a, u, T) \<in> S"
  obtains au where "Some au = a \<oplus> u"
      and "au ## (T f' \<ominus> T f) \<Longrightarrow> \<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u"
  using assms(1) assms(2) package_rhs_connection_def by fastforce

lemma package_rhs_connectionI:
  assumes "\<phi> \<oplus> f = \<phi>' \<oplus> f'"
    and "stable f'"
    and "\<phi> ## f"
    and "f' \<succeq> f"
      and "\<And>a u T. (a, u, T) \<in> S \<Longrightarrow> (\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f' \<ominus> T f) \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u'\<and> u' \<succeq> u \<and> package_sat pc A a' u' u)))"
    shows "package_rhs_connection \<phi> f S pc A \<phi>' f' S'"
  using package_rhs_connection_def assms by auto

lemma valid_package_setI:
  assumes "\<And>a u T. (a, u, T) \<in> S \<Longrightarrow> a ## u \<and> |a| \<succeq> |u| \<and> mono_transformer T \<and> a \<succeq> |T f| "
  shows "valid_package_set S f"
  using assms valid_package_set_def by auto

lemma defined_sum_move:
  assumes "a ## b"
      and "Some b = x \<oplus> y"
      and "Some a' = a \<oplus> x"
    shows "a' ## y"
  by (metis assms defined_def sep_algebra.asso1 sep_algebra_axioms)

lemma bigger_core_sum_defined:
  assumes "|a| \<succeq> b"
  shows "Some a = a \<oplus> b"
  by (metis (no_types, lifting) assms asso1 core_is_smaller greater_equiv max_projection_prop_pure_core mpp_prop pure_def pure_smaller)


lemma package_rhs_proof:
  assumes "package_rhs \<phi> f S pc A \<phi>' f' S'"
      and "valid_package_set S f"
      and "wf_assertion A"
      and "mono_pure_cond pc"
      and "stable f"
      and "\<phi> ## f"
    shows "package_rhs_connection \<phi> f S pc A \<phi>' f' S' \<and> valid_package_set S' f'"
  using assms
proof (induct rule: package_rhs.induct)
  case (AImp \<phi> f S pc b A \<phi>' f' S')
  then have asm0: "package_rhs_connection \<phi> f S (bool_conj pc b) A \<phi>' f' S' \<and> valid_package_set S' f'"
    using mono_pure_cond_conj wf_assertion.simps(2) by blast
  let ?pc = "bool_conj pc b"
  obtain "\<phi> \<oplus> f = \<phi>' \<oplus> f'" "stable f'" "\<phi> ## f" "f' \<succeq> f"
    and \<section>: "\<And>a u T. (a, u, T) \<in> S \<Longrightarrow> (\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f' \<ominus> T f) \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat ?pc A a' u' u)))"
  using asm0 package_rhs_connection_def by force


  have "package_rhs_connection \<phi> f S pc (AImp b A) \<phi>' f' S'"
  proof (rule package_rhs_connectionI)
    show "\<phi> ## f"
      by (simp add: \<open>\<phi> ## f\<close>)
    show "\<phi> \<oplus> f = \<phi>' \<oplus> f'" by (simp add: \<open>\<phi> \<oplus> f = \<phi>' \<oplus> f'\<close>)
    show "stable f'" using \<open>stable f'\<close> by simp
    show "f' \<succeq> f" by (simp add: \<open>f' \<succeq> f\<close>)
    fix a u T assume asm1: "(a, u, T) \<in> S"
    then obtain au where asm2: "Some au = a \<oplus> u \<and> (au ## (T f' \<ominus> T f) \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat ?pc A a' u' u))"
      using \<section> by presburger

    then have "au ## (T f' \<ominus> T f) \<Longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (AImp b A) a' u' u)"
    proof -
      assume asm3: "au ## (T f' \<ominus> T f)"
      then obtain a' u' where au': "(a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat ?pc A a' u' u"
        using asm2 by blast
      have "(the ( |a'| \<oplus> (u' \<ominus> u))) \<succeq> |a'|"
      proof -
        have "u' \<succeq> u' \<ominus> u"
          by (metis minus_default minus_smaller succ_refl)
        then have "a' ## (u' \<ominus> u)"
          by (metis au' asm3 asso3 defined_def minus_exists)
        then show ?thesis
          by (metis core_is_smaller defined_def greater_def option.exhaust_sel sep_algebra.asso2 sep_algebra_axioms)
      qed
      have "package_sat pc (AImp b A) a' u' u"
      proof (rule package_satI)
        assume "pc |a'|"
        then show "\<exists>x. Some x = |a'| \<oplus> (u' \<ominus> u) \<and> sat (AImp b A) x"
        proof (cases "b |a'|")
          case True
          then have "?pc |a'|"
            by (simp add: \<open>pc |a'|\<close> bool_conj_def)
          then show ?thesis
            by (metis au' package_logic.package_sat_def package_logic_axioms sat.simps(2))
        next
          case False
          then have "\<not> b (the ( |a'| \<oplus> (u' \<ominus> u)))"
            using AImp.prems(2) \<open>the ( |a'| \<oplus> (u' \<ominus> u)) \<succeq> |a'|\<close> core_sum max_projection_prop_def max_projection_prop_pure_core minus_exists mono_pure_cond_def wf_assertion.simps(2)
            by metis
          moreover obtain x where "Some x = |a'| \<oplus> (u' \<ominus> u)"
            by (metis au' asm3 asso2 commutative core_is_smaller defined_def minus_and_plus option.collapse)
          ultimately show ?thesis by (metis option.sel sat.simps(2))
        qed
      qed
      then show "\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (AImp b A) a' u' u"
        using au' by blast
    qed
    then show "\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f' \<ominus> T f) \<longrightarrow> (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (AImp b A) a' u' u))"
      using asm2 by auto
  qed
  then show ?case
    using \<open>package_rhs_connection \<phi> f S (bool_conj pc b) A \<phi>' f' S' \<and> valid_package_set S' f'\<close> by blast
next
  case (AStar \<phi> f S pc A \<phi>' f' S' B \<phi>'' f'' S'')
  then have r1: "package_rhs_connection \<phi> f S pc A \<phi>' f' S' \<and> valid_package_set S' f'"
    using wf_assertion.simps(1) by blast
  moreover have "\<phi>' ## f'" using r1 package_rhs_connection_def[of \<phi> f S pc A \<phi>' f' S'] defined_def
    by fastforce
  ultimately have r2: "package_rhs_connection \<phi>' f' S' pc B \<phi>'' f'' S'' \<and> valid_package_set S'' f''"
    using AStar.hyps(4) AStar.prems(2) AStar.prems(3) package_rhs_connection_def by force

  moreover obtain fa_def: "\<phi> \<oplus> f = \<phi>' \<oplus> f'" "stable f'" "\<phi> ## f" "f' \<succeq> f"
    and **: "\<And>a u T. (a, u, T) \<in> S \<Longrightarrow> (\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f' \<ominus> T f) \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u)))"
  using r1 package_rhs_connection_def by fastforce
  then obtain fb_def: "\<phi>' \<oplus> f' = \<phi>'' \<oplus> f''" "stable f''" "\<phi>' ## f'" "f'' \<succeq> f'"
    and "\<And>a u T. (a, u, T) \<in> S' \<Longrightarrow> (\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f'' \<ominus> T f') \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S'' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f'' \<ominus> T f') = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc B a' u' u)))"
    using r2 package_rhs_connection_def by fastforce


  moreover have "package_rhs_connection \<phi> f S pc (AStar A B) \<phi>'' f'' S''"
  proof (rule package_rhs_connectionI)
    show "\<phi> \<oplus> f = \<phi>'' \<oplus> f''" by (simp add: fa_def(1) fb_def(1))
    show "stable f''" by (simp add: fb_def(2))
    show "\<phi> ## f" using fa_def(3) by auto
    show "f'' \<succeq> f" using fa_def(4) fb_def(4) succ_trans by blast


    fix a u T assume asm0: "(a, u, T) \<in> S"
    then have f_def: "Some (T f'' \<ominus> T f) = (T f'' \<ominus> T f') \<oplus> (T f' \<ominus> T f)"
    proof -
      have "mono_transformer T" using valid_package_set_def asm0 \<open>valid_package_set S f\<close> by fastforce
      then have "T f'' \<succeq> T f'"
        by (simp add: fb_def(4) mono_transformer_def)
      moreover have "T f' \<succeq> T f"
        using \<open>mono_transformer T\<close> fa_def(4) mono_transformer_def by blast
      ultimately show ?thesis
        using commutative minus_and_plus minus_equiv_def by presburger
    qed

    then obtain au where au_def: "Some au = a \<oplus> u"
      "au ## (T f' \<ominus> T f) \<Longrightarrow> (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u)"
      using ** asm0 by blast
    then show "\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f'' \<ominus> T f) \<longrightarrow> (\<exists>a' u'. (a', u', T) \<in> S'' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f'' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (AStar A B) a' u' u))"
    proof (cases "au ## (T f'' \<ominus> T f)")
      case True
      moreover have "mono_transformer T" using \<open>valid_package_set S f\<close> valid_package_set_def asm0 by fastforce
      ultimately have "au ## (T f'' \<ominus> T f') \<and> au ## (T f' \<ominus> T f)" using asso3 commutative defined_def f_def
        by metis
      then obtain a' u' where r3: "(a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u"
        using au_def(2) by blast

      then obtain au' where au'_def: "Some au' = a' \<oplus> u'"
        "au' ## (T f'' \<ominus> T f') \<Longrightarrow> (\<exists>a'' u''. (a'', u'', T) \<in> S'' \<and> |a''| \<succeq> |a'| \<and> au' \<oplus> (T f'' \<ominus> T f') = a'' \<oplus> u'' \<and> u'' \<succeq> u' \<and> package_sat pc B a'' u'' u')"
        by (meson package_logic.package_rhs_connection_instantiate package_logic_axioms r2)      
      moreover have "au' ## T f'' \<ominus> T f'"
        using True r3 calculation(1) commutative defined_sum_move f_def by fastforce
      ultimately obtain a'' u'' where r4: "(a'', u'', T) \<in> S'' \<and> |a''| \<succeq> |a'| \<and> au' \<oplus> (T f'' \<ominus> T f') = a'' \<oplus> u'' \<and> u'' \<succeq> u' \<and> package_sat pc B a'' u'' u'"
        by blast

      then have "au \<oplus> (T f'' \<ominus> T f) = a'' \<oplus> u''"
      proof -
        have "au \<oplus> (T f'' \<ominus> T f) = splus (Some au) (Some (T f'' \<ominus> T f))"
          by simp
        also have "... = splus (Some au) (splus (Some (T f'' \<ominus> T f')) (Some (T f' \<ominus> T f)))"
          using f_def by auto
        finally show ?thesis 
          by (metis (full_types) r3 r4 au'_def(1) splus.simps(3) splus_asso splus_comm)
      qed
      moreover have "package_sat pc (AStar A B) a'' u'' u"
      proof (rule package_satI)
        assume "pc |a''|"
        then have "pc |a'|"
          by (metis AStar.prems(3) r4 greater_equiv minus_core minus_core_weaker minus_equiv_def mono_pure_cond_def pure_def)
        then obtain x where "Some x = |a'| \<oplus> (u' \<ominus> u) \<and> sat A x"
          using r3 package_sat_def by fastforce
        then obtain x' where "Some x' = |a''| \<oplus> (u'' \<ominus> u') \<and> sat B x'"
          using \<open>pc |a''|\<close> package_sat_def r4 by presburger

        have "u'' \<succeq> u'' \<ominus> u"
          by (metis minus_default minus_smaller succ_refl)
        moreover have "a'' ## u''"
          using True \<open>au \<oplus> (T f'' \<ominus> T f) = a'' \<oplus> u''\<close> defined_def by auto
        ultimately obtain x'' where "Some x'' = |a''| \<oplus> (u'' \<ominus> u)"
          by (metis commutative defined_def max_projection_prop_pure_core mpp_smaller not_None_eq smaller_compatible)
        moreover have "Some (u'' \<ominus> u) = (u'' \<ominus> u') \<oplus> (u' \<ominus> u)"
          using r4 \<open>(a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u\<close> commutative minus_and_plus minus_equiv_def by presburger
        moreover have "|a''| \<succeq> |a'|"
          using r4 by blast
        moreover have "Some |a''| = |a'| \<oplus> |a''|"
          by (metis (no_types, lifting) calculation(3) core_is_pure sep_algebra.asso1 sep_algebra.minus_exists sep_algebra_axioms)
        ultimately have "Some x'' = x' \<oplus> x"
          using asso1[of _ _ x'] \<open>Some x = |a'| \<oplus> (u' \<ominus> u) \<and> sat A x\<close> \<open>Some x' = |a''| \<oplus> (u'' \<ominus> u') \<and> sat B x'\<close>  commutative
          by metis
        then show "\<exists>x. Some x = |a''| \<oplus> (u'' \<ominus> u) \<and> sat (AStar A B) x"
          using \<open>Some x = |a'| \<oplus> (u' \<ominus> u) \<and> sat A x\<close> \<open>Some x' = |a''| \<oplus> (u'' \<ominus> u') \<and> sat B x'\<close> \<open>Some x'' = |a''| \<oplus> (u'' \<ominus> u)\<close> commutative by fastforce
      qed
      ultimately show ?thesis
        using r3 r4 au_def(1) succ_trans by blast
    next
      case False
      then show ?thesis
        using au_def(1) by blast
    qed
  qed
  ultimately show ?case by blast
next
  case (ASem S pc witness B S' \<phi> f)
  have "valid_package_set S' f"
  proof (rule valid_package_setI)
    fix a' u' T assume asm0: "(a', u', T) \<in> S'"
    then show "a' ## u' \<and> |a'| \<succeq> |u'| \<and> mono_transformer T \<and> a' \<succeq> |T f|"
    proof (cases "(a', u', T) \<in> S")
      case True
      then show ?thesis
        using ASem.prems(1) valid_package_set_def by auto
    next
      case False
      then have "(a', u', T) \<in> {(a \<ominus> b, the (u \<oplus> b), T) |a u T b. (a, u, T) \<in> S \<and> pc a \<and> b = witness (a, u, T)}"
        using ASem.hyps(2) asm0 by blast
      then obtain a u b where "(a, u, T) \<in> S" "pc a" "b = witness (a, u, T)" "a' = a \<ominus> b" "u' = the (u \<oplus> b)" by blast
      then have "a \<succeq> b \<and> B b"
        using ASem.hyps(1) by presburger
      have "a ## u"
        using ASem.prems(1) \<open>(a, u, T) \<in> S\<close> valid_package_set_def by fastforce
      then have "Some u' = u \<oplus> b"
        by (metis \<open>a \<succeq> b \<and> B b\<close> \<open>u' = the (u \<oplus> b)\<close> commutative defined_def option.exhaust_sel smaller_compatible)
      moreover have "Some a = a' \<oplus> b"
        using \<open>a \<succeq> b \<and> B b\<close> \<open>a' = a \<ominus> b\<close> commutative minus_equiv_def by presburger

      ultimately have "a' ## u'"
        by (metis \<open>a ## u\<close> asso1 commutative defined_def)
      moreover have "|a'| \<succeq> |u'|"
      proof -
        have "|a| \<succeq> |u|"
          using ASem.prems(1) \<open>(a, u, T) \<in> S\<close> valid_package_set_def by fastforce
        moreover have "|a'| \<succeq> |a|"
          by (simp add: \<open>a' = a \<ominus> b\<close> minus_core succ_refl)
        moreover have "|a'| \<succeq> |b|"
          using \<open>a \<succeq> b \<and> B b\<close> \<open>a' = a \<ominus> b\<close> max_projection_prop_pure_core minus_core mpp_mono by presburger
        ultimately show ?thesis
          by (metis \<open>Some u' = u \<oplus> b\<close> \<open>a' = a \<ominus> b\<close> core_is_pure core_sum minus_core pure_def smaller_pure_sum_smaller)
      qed
      moreover have "a' \<succeq> |T f|"
      proof -
        have "a \<succeq> |T f|" using \<open>(a, u, T) \<in> S\<close> \<open>valid_package_set S f\<close> valid_package_set_def
          by fastforce
        then show ?thesis
          by (metis \<open>a' = a \<ominus> b\<close> max_projection_prop_pure_core minus_core mpp_mono mpp_smaller sep_algebra.mpp_invo sep_algebra.succ_trans sep_algebra_axioms)
      qed
      ultimately show ?thesis using \<open>(a, u, T) \<in> S\<close> \<open>valid_package_set S f\<close> valid_package_set_def 
        by fastforce
    qed
  qed
  moreover have "package_rhs_connection \<phi> f S pc (ASem B) \<phi> f S'"
  proof (rule package_rhs_connectionI)
    show "\<phi> \<oplus> f = \<phi> \<oplus> f"
      by simp
    show "stable f" by (simp add: ASem.prems(4))
    show "\<phi> ## f" by (simp add: ASem.prems(5))
    show "f \<succeq> f" by (simp add: succ_refl)
            
    fix a u T assume asm0: "(a, u, T) \<in> S"

    then obtain au where "Some au = a \<oplus> u" using \<open>valid_package_set S f\<close> valid_package_set_def defined_def by auto
    then have r0: "(\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> Some au = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (ASem B) a' u' u)"
    proof -
      let ?b = "witness (a, u, T)"
      let ?a = "a \<ominus> ?b"
      let ?u = "the (u \<oplus> ?b)"
      show "\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> Some au = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (ASem B) a' u' u"
      proof (cases "pc a")
        case True
        then have "(?a, ?u, T) \<in> S'" using ASem.hyps(2) asm0 by blast
        then have "a \<succeq> ?b \<and> B ?b" using ASem.hyps(1) True asm0 by blast
        moreover have r1: "(?a, ?u, T) \<in> S' \<and> |?a| \<succeq> |a| \<and> Some au = ?a \<oplus> ?u \<and> ?u \<succeq> u"
        proof
          show "(a \<ominus> witness (a, u, T), the (u \<oplus> witness (a, u, T)), T) \<in> S'"
            by (simp add: \<open>(a \<ominus> witness (a, u, T), the (u \<oplus> witness (a, u, T)), T) \<in> S'\<close>)
          have "|a \<ominus> witness (a, u, T)|  \<succeq>  |a| "
            by (simp add: minus_core succ_refl)
          moreover have "Some au = a \<ominus> witness (a, u, T) \<oplus> the (u \<oplus> witness (a, u, T))"
            using \<open>Some au = a \<oplus> u\<close> \<open>a \<succeq> witness (a, u, T) \<and> B (witness (a, u, T))\<close>
              asso1[of "a \<ominus> witness (a, u, T)" "witness (a, u, T)" a u "the (u \<oplus> witness (a, u, T))"]
              commutative option.distinct(1) option.exhaust_sel asso3 minus_equiv_def
            by metis
          moreover have "the (u \<oplus> witness (a, u, T)) \<succeq> u"
            using \<open>Some au = a \<oplus> u\<close> \<open>a \<succeq> witness (a, u, T) \<and> B (witness (a, u, T))\<close> commutative
              greater_def option.distinct(1) option.exhaust_sel asso3[of u "witness (a, u, T)" ]
            by metis
          ultimately show "|a \<ominus> witness (a, u, T)|  \<succeq>  |a|  \<and> Some au = a \<ominus> witness (a, u, T) \<oplus> the (u \<oplus> witness (a, u, T)) \<and> the (u \<oplus> witness (a, u, T)) \<succeq> u"
            by blast
        qed
        moreover have "package_sat pc (ASem B) ?a ?u u"
        proof (rule package_satI)
          assume "pc |a \<ominus> witness (a, u, T)|"
          have "Some ?u = u \<oplus> ?b"
            by (metis (no_types, lifting) \<open>Some au = a \<oplus> u\<close> calculation(1) commutative minus_equiv_def option.distinct(1) option.exhaust_sel sep_algebra.asso3 sep_algebra_axioms)
          moreover have "?a ## ?u"
            by (metis r1 defined_def option.distinct(1))
          moreover have "?u \<succeq> ?u \<ominus> u"
            using r1 minus_smaller by blast
          ultimately obtain x where "Some x = |a \<ominus> ?b| \<oplus> (?u \<ominus> u)"
            by (metis (no_types, opaque_lifting) \<open>a \<succeq> witness (a, u, T) \<and> B (witness (a, u, T))\<close> commutative defined_def minus_core minus_equiv_def option.exhaust smaller_compatible)
          moreover have "x \<succeq> ?b"
          proof -
            have "?u \<ominus> u \<succeq> ?b"
              using \<open>Some (the (u \<oplus> witness (a, u, T))) = u \<oplus> witness (a, u, T)\<close> minus_bigger by blast
            then show ?thesis
              using calculation greater_equiv succ_trans by blast
          qed
          ultimately show "\<exists>x. Some x = |a \<ominus> witness (a, u, T)| \<oplus> (the (u \<oplus> witness (a, u, T)) \<ominus> u) \<and> sat (ASem B) x"
            using ASem.prems(2) \<open>Some (the (u \<oplus> witness (a, u, T))) = u \<oplus> witness (a, u, T)\<close>
              \<open>a \<succeq> witness (a, u, T) \<and> B (witness (a, u, T))\<close> commutative max_projection_prop_def[of pure core]
              max_projection_prop_pure_core minus_equiv_def_any_elem mono_pruner_def[of B]
              sat.simps(3)[of B] wf_assertion.simps(3)[of B]
            by metis
        qed
        ultimately show ?thesis by blast
      next
        case False
        then have "package_sat pc (ASem B) a u u"
          by (metis ASem.prems(3) mono_pure_cond_def package_sat_def)
        moreover have "(a, u, T) \<in> S'" 
          using False ASem.hyps(2) asm0 by blast
        ultimately show ?thesis
          using \<open>Some au = a \<oplus> u\<close> succ_refl by blast
      qed
    qed
    moreover have "au \<oplus> (T f \<ominus> T f) = Some au"
    proof -
      have "a \<succeq> |T f|" using \<open>(a, u, T) \<in> S\<close> \<open>valid_package_set S f\<close> valid_package_set_def by fastforce
      then have "|a| \<succeq> T f \<ominus> T f"
        using core_is_smaller max_projection_prop_def max_projection_prop_pure_core minusI by presburger
      then have "|au| \<succeq> T f \<ominus> T f"
        using \<open>Some au = a \<oplus> u\<close> core_sum greater_def succ_trans by blast
      then show ?thesis using bigger_core_sum_defined by force
    qed
    ultimately show "\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f \<ominus> T f) \<longrightarrow> (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc (ASem B) a' u' u))"
      using \<open>Some au = a \<oplus> u\<close> by fastforce
  qed
  ultimately show ?case by blast
next
  case (AddFromOutside \<phi> \<phi>' m f' S' pc A \<phi>'' f'' S'' f S)
  have "valid_package_set S' f'"
  proof (rule valid_package_setI)
    fix a' u T assume asm0: "(a', u, T) \<in> S'"
    then obtain a where "(a, u, T) \<in> S" "a' ## u" "Some a' = a \<oplus> (T f' \<ominus> T f)"
      using AddFromOutside.hyps(6) by blast
    then have "|a| \<succeq> |u| \<and> mono_transformer T \<and> a \<succeq> |T f|" using \<open>valid_package_set S f\<close> valid_package_set_def 
      by fastforce
    moreover have "a' \<succeq> |T f'|"
      by (metis (no_types, opaque_lifting) \<open>Some a' = a \<oplus> (T f' \<ominus> T f)\<close> commutative greater_equiv minus_core minus_equiv_def minus_smaller succ_trans unit_neutral)
    ultimately show "a' ## u \<and> |a'| \<succeq> |u| \<and> mono_transformer T \<and> a' \<succeq> |T f'|"
      using \<open>Some a' = a \<oplus> (T f' \<ominus> T f)\<close> \<open>a' ## u\<close> greater_def max_projection_prop_pure_core mpp_mono succ_trans by blast
  qed
  then have r: "package_rhs_connection \<phi>' f' S' pc A \<phi>'' f'' S'' \<and> valid_package_set S'' f''"
    by (metis AddFromOutside.hyps(1) AddFromOutside.hyps(3) AddFromOutside.hyps(4) AddFromOutside.hyps(5) AddFromOutside.prems(2) AddFromOutside.prems(3) AddFromOutside.prems(4) AddFromOutside.prems(5) asso1 commutative defined_def stable_sum)
  then obtain r2: "\<phi>' \<oplus> f' = \<phi>'' \<oplus> f''" "stable f''" "\<phi>' ## f'" "f'' \<succeq> f'"
    "\<And>a u T. (a, u, T) \<in> S' \<Longrightarrow> (\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f'' \<ominus> T f') \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S'' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f'' \<ominus> T f') = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u)))"
    using package_rhs_connection_def by fastforce

  moreover have "package_rhs_connection \<phi> f S pc A \<phi>'' f'' S''"
  proof (rule package_rhs_connectionI)
    show "\<phi> \<oplus> f = \<phi>'' \<oplus> f''"
      by (metis AddFromOutside.hyps(1) AddFromOutside.hyps(5) asso1 commutative r2(1))
    show "stable f''"
      using AddFromOutside.hyps(4) calculation(4) r2(2) stable_sum by blast
    show "\<phi> ## f"
      by (simp add: AddFromOutside.prems(5))
    show "f'' \<succeq> f"
      using AddFromOutside.hyps(5) bigger_sum greater_def r2(4) by blast

    fix a u T
    assume asm0: "(a, u, T) \<in> S"
    then obtain au where "Some au = a \<oplus> u" using \<open>valid_package_set S f\<close> valid_package_set_def defined_def
      by fastforce
    moreover have "au ## (T f'' \<ominus> T f) \<Longrightarrow> (\<exists>a' u'. (a', u', T) \<in> S'' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f'' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u)"
    proof -
      assume asm1: "au ## (T f'' \<ominus> T f)"
      moreover have "mono_transformer T" using \<open>valid_package_set S f\<close> valid_package_set_def asm0
        by fastforce
      then have "Some (T f'' \<ominus> T f) = (T f'' \<ominus> T f') \<oplus> (T f' \<ominus> T f)"
        by (metis AddFromOutside.hyps(5) commutative greater_equiv minus_and_plus minus_equiv_def mono_transformer_def r2(4))
      ultimately have "a ## (T f' \<ominus> T f)"
        using \<open>Some au = a \<oplus> u\<close> asso2 commutative defined_def minus_exists
        by metis
      then obtain a' where "Some a' = a \<oplus> (T f' \<ominus> T f)"
        by (meson defined_def option.collapse)
      moreover have "a' ## u"
      proof -
        have "T f'' \<ominus> T f \<succeq> T f' \<ominus> T f"
          using \<open>Some (T f'' \<ominus> T f) = T f'' \<ominus> T f' \<oplus> (T f' \<ominus> T f)\<close> greater_equiv by blast
        then show ?thesis
          using \<open>Some au = a \<oplus> u\<close> asm1 asso1[of u a au "T f' \<ominus> T f" a'] asso2[of ] calculation commutative
            defined_def[of ] greater_equiv[of "T f'' \<ominus> T f" "T f' \<ominus> T f"]
          by metis
      qed

      ultimately have "(a', u, T) \<in> S'"
        using AddFromOutside.hyps(6) asm0 by blast

      moreover have "au ## (T f'' \<ominus> T f')"
        by (metis \<open>Some (T f'' \<ominus> T f) = T f'' \<ominus> T f' \<oplus> (T f' \<ominus> T f)\<close> asm1 asso3 defined_def)

      then have "\<exists>au. Some au = a' \<oplus> u \<and> (au ## (T f'' \<ominus> T f') \<longrightarrow> (\<exists>a'a u'. (a'a, u', T) \<in> S'' \<and> |a'a| \<succeq> |a'| \<and> au \<oplus> (T f'' \<ominus> T f') = a'a \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a'a u' u))"
        using r2(5) calculation by blast

      then obtain au' a'' u' where r3: "Some au' = a' \<oplus> u" "au' ## (T f'' \<ominus> T f') \<Longrightarrow> (a'', u', T) \<in> S'' \<and> |a''| \<succeq> |a'| \<and> au' \<oplus> (T f'' \<ominus> T f') = a'' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a'' u' u"
        using \<open>au ## (T f'' \<ominus> T f')\<close> by blast
      moreover have "au' ## (T f'' \<ominus> T f')" using \<open>au ## (T f'' \<ominus> T f)\<close> \<open>Some au = a \<oplus> u\<close> r3(1)
      \<open>Some (T f'' \<ominus> T f) = (T f'' \<ominus> T f') \<oplus> (T f' \<ominus> T f)\<close>
        \<open>Some a' = a \<oplus> (T f' \<ominus> T f)\<close> asso1[of u a au "T f' \<ominus> T f" a'] commutative defined_sum_move[of au "T f'' \<ominus> T f"]
        by metis
      ultimately have r4: "(a'', u', T) \<in> S'' \<and> |a''| \<succeq> |a'| \<and> au' \<oplus> (T f'' \<ominus> T f') = a'' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a'' u' u"
        by blast
      moreover have "|a''| \<succeq> |a|"
      proof -
        have "|a'| \<succeq> |a|"
          using \<open>Some a' = a \<oplus> (T f' \<ominus> T f)\<close> core_sum greater_def by blast
        then show ?thesis
          using r4 succ_trans by blast
      qed
      ultimately show "\<exists>a' u'. (a', u', T) \<in> S'' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f'' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u"        
        using \<open>Some (T f'' \<ominus> T f) = T f'' \<ominus> T f' \<oplus> (T f' \<ominus> T f)\<close> \<open>Some a' = a \<oplus> (T f' \<ominus> T f)\<close> \<open>Some au = a \<oplus> u\<close>
          commutative r3(1) asso1 splus.simps(3) splus_asso by metis
    qed
    ultimately show "\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f'' \<ominus> T f) \<longrightarrow> (\<exists>a' u'. (a', u', T) \<in> S'' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f'' \<ominus> T f) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat pc A a' u' u))"
      by blast
  qed
  ultimately show ?case using r by blast
qed

lemma unit_core:
  "|unit| = unit"
  by (meson core_is_pure max_projection_prop_pure_core sep_algebra.cancellative sep_algebra.mpp_invo sep_algebra_axioms unit_neutral)

lemma unit_smaller:
  "\<phi> \<succeq> unit"
  using greater_equiv unit_neutral by auto


subsection \<open>Lemmas for completeness\<close>

lemma sat_star_exists_bigger:
  assumes "sat (AStar A B) \<phi>"
      and "wf_assertion A"
      and "wf_assertion B"
  shows "\<exists>a b. |a| \<succeq> |\<phi>| \<and> |b| \<succeq> |\<phi>| \<and> Some \<phi> = a \<oplus> b \<and> sat A a \<and> sat B b"
proof -
  obtain a b where "Some \<phi> = a \<oplus> b" "sat A a" "sat B b"
    using assms sat.simps(1) by blast
  then obtain a' b' where "Some a' = a \<oplus> |\<phi>|" "Some b' = b \<oplus> |\<phi>|"
    by (meson defined_def greater_def greater_equiv option.collapse smaller_compatible_core)
  then have "a' \<succeq> a \<and> b' \<succeq> b"
    using greater_def by blast
  then have "sat A a' \<and> sat B b'"
    by (metis \<open>Some a' = a \<oplus> |\<phi>|\<close> \<open>Some b' = b \<oplus> |\<phi>|\<close> \<open>sat A a\<close> \<open>sat B b\<close> assms(2) assms(3) max_projection_prop_pure_core mpp_prop package_logic.wf_assertion_sat_larger_pure package_logic_axioms)
  moreover have "Some \<phi> = a' \<oplus> b'"
    by (metis (no_types, lifting) \<open>Some \<phi> = a \<oplus> b\<close> \<open>Some a' = a \<oplus> |\<phi>|\<close> \<open>Some b' = b \<oplus> |\<phi>|\<close> asso1 commutative core_is_smaller)
  ultimately show ?thesis
    by (metis \<open>Some a' = a \<oplus> |\<phi>|\<close> \<open>Some b' = b \<oplus> |\<phi>|\<close> commutative extract_core greater_equiv max_projection_prop_pure_core mpp_mono)
qed

lemma let_pair_instantiate:
  assumes "(a, b) = f x y"
  shows "(let (a, b) = f x y in g a b) = g a b"
  by (metis assms case_prod_conv)


lemma greater_than_sum_exists:
  assumes "a \<succeq> b"
      and "Some b = b1 \<oplus> b2"
    shows "\<exists>r. Some a = r \<oplus> b2 \<and> |r| \<succeq> |a| \<and> r \<succeq> b1"
proof -
  obtain r where "Some a = r \<oplus> b2 \<and> r \<succeq> b1"
    by (metis assms(1) assms(2) bigger_sum commutative)
  then obtain r' where "Some r' = r \<oplus> |a|"
    by (metis defined_def greater_def option.exhaust smaller_compatible_core)
  then have "Some a = r' \<oplus> b2"
    by (metis \<open>Some a = r \<oplus> b2 \<and> r \<succeq> b1\<close> commutative core_is_smaller sep_algebra.asso1 sep_algebra_axioms)
  then show ?thesis
    by (metis \<open>Some a = r \<oplus> b2 \<and> r \<succeq> b1\<close> \<open>Some r' = r \<oplus> |a|\<close> core_is_pure greater_def smaller_than_core succ_trans)
qed

lemma bigger_the:
  assumes "Some a = x' \<oplus> y"
      and "x' \<succeq> x"
    shows "the (   |a|  \<oplus>  x') \<succeq> the (   |a|  \<oplus> x)"
proof -
  have "a \<succeq> x'"
    using assms(1) greater_def by blast
  then have "|a|  ##  x'"
    using commutative defined_def smaller_compatible_core by auto
  moreover have "|a|  ## x"
    by (metis assms(2) calculation defined_def sep_algebra.asso3 sep_algebra.minus_exists sep_algebra_axioms)
  ultimately show ?thesis
    using addition_bigger assms(2) commutative defined_def by force
qed

lemma wf_assertion_and_the:
  assumes "|a| ## b"
      and "sat A b"
      and "wf_assertion A"
    shows "sat A (the ( |a| \<oplus> b))"
  by (metis assms(1) assms(2) assms(3) commutative defined_def max_projection_prop_pure_core option.collapse sep_algebra.mpp_prop sep_algebra_axioms wf_assertion_sat_larger_pure)

lemma minus_some:
  assumes "a \<succeq> b"
  shows "Some a = b \<oplus> (a \<ominus> b)"
  using assms commutative minus_equiv_def by force

lemma core_mono:
  assumes "a \<succeq> b"
  shows "|a| \<succeq> |b|"
  using assms max_projection_prop_pure_core mpp_mono by auto

lemma prove_last_completeness:
  assumes "a' \<succeq> a"
      and "Some a = nf1 \<oplus> f2"
    shows "a' \<ominus> nf1 \<succeq> f2"
  by (meson assms(1) assms(2) greater_def greater_minus_trans minus_bigger succ_trans)

lemma completeness_aux:
  assumes "\<And>a u T. (a, u, T) \<in> S \<Longrightarrow> |f1 a u T| \<succeq> |a| \<and> Some a = f1 a u T \<oplus> f2 a u T \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> (f1 a u T))))"
      and "valid_package_set S f"
      and "wf_assertion A"
      and "mono_pure_cond pc"
      and "stable f \<and> \<phi> ## f"
    shows "\<exists>S'. package_rhs \<phi> f S pc A \<phi> f S' \<and> (\<forall>(a', u', T) \<in> S'. \<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> f2 a u T \<and> |a'| = |a| )"
  using assms
proof (induct A arbitrary: S pc f1 f2)
  case (AImp b A)
  let ?pc = "bool_conj pc b"

  have r0: "\<exists>S'. package_rhs \<phi> f S (bool_conj pc b) A \<phi> f S' \<and> (\<forall>a\<in>S'. case a of (a', u', T) \<Rightarrow> \<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> f2 a u T \<and> |a'| = |a| )"
  proof (rule AImp(1))
    show "valid_package_set S f"
      by (simp add: AImp.prems(2))
    show "wf_assertion A" using AImp.prems(3) by auto
    show "mono_pure_cond (bool_conj pc b)"
      by (meson AImp.prems(3) AImp.prems(4) mono_pure_cond_conj wf_assertion.simps(2))
    show "stable f \<and> \<phi> ## f" using \<open>stable f \<and> \<phi> ## f\<close> by simp

    fix a u T
    assume asm0: "(a, u, T) \<in> S"
    then have "Some a = f1 a u T \<oplus> f2 a u T"
      using AImp.prems(1) by blast
    moreover have "bool_conj pc b |a| \<Longrightarrow> sat A (the ( |a| \<oplus> f1 a u T))"
    proof -
      assume "bool_conj pc b |a|"
      then have "pc |a|"
        by (meson bool_conj_def)
      then have "|f1 a u T| \<succeq> |a| \<and> Some a = f1 a u T \<oplus> f2 a u T \<and> sat (AImp b A) (the ( |a| \<oplus> f1 a u T))"
        using AImp.prems(1) asm0(1) by blast
      moreover have "b (the ( |a| \<oplus> f1 a u T))"
      proof -
        have "|a| ## f1 a u T \<and> |a| \<succeq> |f1 a u T|"
          by (metis calculation commutative core_is_smaller defined_def greater_def max_projection_prop_pure_core mpp_mono option.discI succ_antisym)
        then obtain x where "Some x = |a| \<oplus> f1 a u T"
          by (meson defined_def option.collapse)
        then have "|x| = |a|"
          by (metis \<open>Some x = |a| \<oplus> f1 a u T\<close> \<open>|a| ## f1 a u T \<and> |a| \<succeq> |f1 a u T|\<close> commutative core_is_pure core_sum max_projection_prop_pure_core mpp_smaller smaller_than_core)
        then show ?thesis
          by (metis AImp.prems(3) \<open>Some x = |a| \<oplus> f1 a u T\<close> \<open>bool_conj pc b |a|\<close> bool_conj_def mono_pure_cond_def option.sel wf_assertion.simps(2))
      qed
      ultimately show "sat A (the ( |a| \<oplus> f1 a u T))" by (metis sat.simps(2))
    qed
    ultimately show "|f1 a u T| \<succeq> |a| \<and> Some a = f1 a u T \<oplus> f2 a u T \<and> (bool_conj pc b |a| \<longrightarrow> sat A (the ( |a| \<oplus> f1 a u T)))" 
      by (metis AImp.prems(1) asm0)
  qed
  then obtain S' where r: "package_rhs \<phi> f S (bool_conj pc b) A \<phi> f S'" "\<And>a' u' T. (a', u', T) \<in> S' \<Longrightarrow> (\<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> f2 a u T)"
    by fast
  moreover have "package_rhs \<phi> f S pc (AImp b A) \<phi> f S'"
    by (simp add: package_rhs.AImp r(1))
  ultimately show ?case
    using r0 package_rhs.AImp by blast
next
  case (ASem A)
  let ?witness = "\<lambda>(a, u, T). the ( |a| \<oplus> f1 a u T)"

  obtain S' where S'_def: "S' = { (a, u, T) |a u T. (a, u, T) \<in> S \<and> \<not> pc a }
  \<union> { (a \<ominus> b, the (u \<oplus> b), T) |a u T b. (a, u, T) \<in> S \<and> pc a \<and> b = ?witness (a, u, T) }"
    by blast

  have "package_rhs \<phi> f S pc (ASem A) \<phi> f S'"
  proof (rule package_rhs.ASem)
    show "S' = {(a, u, T) |a u T. (a, u, T) \<in> S \<and> \<not> pc a} \<union> {(a \<ominus> b, the (u \<oplus> b), T) |a u T b. (a, u, T) \<in> S \<and> pc a \<and> b = ?witness (a, u, T)}"
      using S'_def by blast
    fix a u T b
    assume asm0: "(a, u, T) \<in> S" "pc a" "b = (case (a, u, T) of (a, u, T) \<Rightarrow> the ( |a| \<oplus> f1 a u T))"
    then have "b = the ( |a| \<oplus> f1 a u T)" by fastforce
    moreover have "pc |a|"
      by (meson ASem.prems(4) asm0(2) mono_pure_cond_def)
    then obtain "|f1 a u T| \<succeq> |a|" "Some a = f1 a u T \<oplus> f2 a u T" "sat (ASem A) (the ( |a| \<oplus> f1 a u T))"
      using ASem.prems(1) asm0(1) by blast
    then have "Some b = |a| \<oplus> f1 a u T" by (metis calculation commutative defined_def minus_bigger minus_core option.exhaust_sel smaller_compatible_core)
    moreover have "a \<succeq> b"
    proof -
      have "a \<succeq> f1 a u T"
        using \<open>Some a = f1 a u T \<oplus> f2 a u T\<close> greater_def by blast
      then show ?thesis
        by (metis calculation(2) commutative max_projection_prop_pure_core mpp_smaller sep_algebra.mpp_prop sep_algebra_axioms smaller_pure_sum_smaller)
    qed
    ultimately show "a \<succeq> b \<and> A b"
      using \<open>sat (ASem A) (the ( |a| \<oplus> f1 a u T))\<close> sat.simps(3) by blast
  qed

  moreover have r0: "\<And>a' u' T. (a', u', T) \<in> S' \<Longrightarrow> (\<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> f2 a u T \<and> |a'| = |a| )"
  proof -
    fix a' u' T assume asm0: "(a', u', T) \<in> S'"
    then show "\<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> f2 a u T \<and> |a'| = |a| "
    proof (cases "(a', u', T) \<in> {(a, u, T) |a u T. (a, u, T) \<in> S \<and> \<not> pc a}")
      case True
      then show ?thesis using ASem.prems(1) greater_equiv by fastforce
    next
      case False
      then have "(a', u', T) \<in> { (a \<ominus> b, the (u \<oplus> b), T) |a u T b. (a, u, T) \<in> S \<and> pc a \<and> b = ?witness (a, u, T) }"
        using S'_def asm0 by blast
      then obtain a u b where "a' = a \<ominus> b" "u' = the (u \<oplus> b)" "(a, u, T) \<in> S" "pc a" "b = ?witness (a, u, T)"
        by blast
      then have "a' \<succeq> f2 a u T"
      proof -
        have "a \<succeq> b"
        proof -
          have "a \<succeq> f1 a u T"
            using ASem.prems(1) \<open>(a, u, T) \<in> S\<close> greater_def by blast
          moreover have "Some b = |a| \<oplus> f1 a u T"
            by (metis \<open>b = (case (a, u, T) of (a, u, T) \<Rightarrow> the ( |a| \<oplus> f1 a u T))\<close> calculation case_prod_conv commutative defined_def option.exhaust_sel smaller_compatible_core)
          ultimately show ?thesis
            by (metis commutative max_projection_prop_pure_core mpp_smaller sep_algebra.mpp_prop sep_algebra_axioms smaller_pure_sum_smaller)
        qed
        then show ?thesis
          using ASem.prems(1)[of a u T]
            \<open>(a, u, T) \<in> S\<close> \<open>a' = a \<ominus> b\<close> \<open>b = (case (a, u, T) of (a, u, T) \<Rightarrow> the ( |a| \<oplus> f1 a u T))\<close>
            commutative core_is_smaller minus_bigger option.exhaust_sel option.simps(3)
            asso1[of "f2 a u T" "f1 a u T" a "|a|" "the ( |a|  \<oplus> f1 a u T)"] asso2[of "f2 a u T" "f1 a u T"]
            split_conv
          by metis
      qed
      then show ?thesis
        using \<open>(a, u, T) \<in> S\<close> \<open>a' = a \<ominus> b\<close> minus_core by blast
    qed
  qed

  ultimately show ?case by blast
next
  case (AStar A B)

  let ?fA = "\<lambda>a u T. SOME x. \<exists>y. Some (f1 a u T) = x \<oplus> y \<and> |x| \<succeq> |f1 a u T| \<and> |y| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> x)) \<and> sat B (the ( |a| \<oplus> y)))"
  let ?fB = "\<lambda>a u T. SOME y. Some (f1 a u T) = ?fA a u T \<oplus> y \<and> |y| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat B (the ( |a| \<oplus> y)))"
  let ?f2 = "\<lambda>a u T. the (?fB a u T \<oplus> f2 a u T)"

  have r: "\<And>a u T. (a, u, T) \<in> S \<Longrightarrow> Some (f1 a u T) = ?fA a u T \<oplus> ?fB a u T \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |?fB a u T| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> ?fB a u T)))
  \<and> Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T"
  proof -
    fix a u T assume asm0: "(a, u, T) \<in> S"
    then have r0: "Some a = f1 a u T \<oplus> f2 a u T \<and> (pc |a| \<longrightarrow> sat (AStar A B) (the ( |a| \<oplus> f1 a u T)))"
      using AStar.prems(1) by blast
    then have "\<exists>x y. Some (the ( |a| \<oplus> f1 a u T )) = x \<oplus> y \<and> (pc |a| \<longrightarrow> sat A x) \<and> (pc |a| \<longrightarrow> sat B y) \<and>
      x \<succeq> |(the ( |a| \<oplus> f1 a u T))| \<and> y \<succeq> |(the ( |a| \<oplus> f1 a u T))|"
    proof (cases "pc |a|")
      case True
      then show ?thesis
        using AStar.prems(3) r0
          max_projection_prop_def[of pure core] max_projection_prop_pure_core
          sat_star_exists_bigger[of A B "(the ( |a|  \<oplus> f1 a u T))"]
          succ_trans[of ] wf_assertion.simps(1)[of A B]
        by blast
    next
      case False
      then have "Some (the ( |a| \<oplus> f1 a u T )) = the ( |a| \<oplus> f1 a u T) \<oplus> |the ( |a| \<oplus> f1 a u T )|"
        by (simp add: core_is_smaller)
      then show ?thesis by (metis False max_projection_prop_pure_core mpp_smaller succ_refl)
    qed
    then obtain x y where "Some (the ( |a| \<oplus> f1 a u T)) = x \<oplus> y" "pc |a| \<longrightarrow> sat A x" "pc |a| \<longrightarrow> sat B y"
      "x \<succeq> |(the ( |a| \<oplus> f1 a u T))|" "y \<succeq> |(the ( |a| \<oplus> f1 a u T))|" by blast
    moreover obtain af where "Some af = |a| \<oplus> f1 a u T"
      by (metis r0 commutative defined_def minus_bigger minus_core option.exhaust_sel smaller_compatible_core)
    ultimately have "Some (f1 a u T) = x \<oplus> y"
      by (metis AStar.prems(1) r0 asm0 commutative core_is_smaller greater_def max_projection_prop_pure_core mpp_mono option.sel succ_antisym)
    moreover have "|a| ## x \<and> |a| ## y"
      by (metis \<open>Some af = |a| \<oplus> f1 a u T\<close> calculation commutative defined_def option.discI sep_algebra.asso3 sep_algebra_axioms)
    then have "the ( |a| \<oplus> x) \<succeq> x \<and> the ( |a| \<oplus> y) \<succeq> y"
      using commutative defined_def greater_def by auto

    ultimately have pc_implies_sat: "pc |a| \<Longrightarrow> sat A (the ( |a| \<oplus> x)) \<and> sat B (the ( |a| \<oplus> y))"
      by (metis AStar.prems(3) \<open>pc |a| \<longrightarrow> sat A x\<close> \<open>pc |a| \<longrightarrow> sat B y\<close> \<open>|a| ## x \<and> |a| ## y\<close> commutative defined_def max_projection_prop_pure_core option.exhaust_sel package_logic.wf_assertion.simps(1) package_logic_axioms sep_algebra.mpp_prop sep_algebra_axioms wf_assertion_sat_larger_pure)

    have r1: "\<exists>y. Some (f1 a u T) = ?fA a u T \<oplus> y \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |y| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> y)))"
    proof (rule someI_ex)
      show "\<exists>x y. Some (f1 a u T) = x \<oplus> y \<and> |x| \<succeq> |f1 a u T| \<and> |y| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> x)) \<and> sat B (the ( |a| \<oplus> y)))"
        using \<open>Some (f1 a u T) = x \<oplus> y\<close> \<open>Some (the ( |a| \<oplus> f1 a u T)) = x \<oplus> y\<close> pc_implies_sat \<open>x \<succeq> |the ( |a| \<oplus> f1 a u T)|\<close> \<open>y \<succeq> |the ( |a| \<oplus> f1 a u T)|\<close> core_is_pure max_projection_propE(3) max_projection_prop_pure_core option.sel pure_def
        by (metis AStar.prems(1) asm0 minusI minus_core)
    qed
    then obtain yy where yy_prop: "Some (f1 a u T) = ?fA a u T \<oplus> yy \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |yy| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> yy)))"
      by blast
    moreover have r2: "Some (f1 a u T) = ?fA a u T \<oplus> ?fB a u T \<and> |?fB a u T| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat B (the ( |a| \<oplus> ?fB a u T)))"
    proof (rule someI_ex)
      show "\<exists>y. Some (f1 a u T) = ?fA a u T \<oplus> y \<and> |y| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat B (the ( |a| \<oplus> y)))"
        using r1 by blast
    qed
    ultimately have "?fB a u T \<oplus> f2 a u T \<noteq> None"
      using r0
        option.distinct(1) [of ] option.exhaust_sel[of "?fB a u T \<oplus> f2 a u T"] asso2[of "?fA a u T" "?fB a u T" "f1 a u T" "f2 a u T"]
      by metis
    then show "Some (f1 a u T) = ?fA a u T \<oplus> ?fB a u T \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |?fB a u T| \<succeq> |a|
      \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> ?fB a u T))) \<and> Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T"
      using r0 r2 yy_prop
         option.distinct(1) option.exhaust_sel[of "?fB a u T \<oplus> f2 a u T"] asso2[of "?fA a u T" "?fB a u T" "f1 a u T" "f2 a u T"] 
      by simp
  qed
  have ih1: "\<exists>S'. package_rhs \<phi> f S pc A \<phi> f S' \<and> (\<forall>a\<in>S'. case a of (a', u', T) \<Rightarrow> \<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T \<and> |a'| = |a| )"
  proof (rule AStar(1))
    show "valid_package_set S f"
      by (simp add: AStar.prems(2))
    show "wf_assertion A"
      using AStar.prems(3) by auto
    show "mono_pure_cond pc"
      by (simp add: AStar.prems(4))
    show "stable f \<and> \<phi> ## f" using \<open>stable f \<and> \<phi> ## f\<close> by simp

    fix a u T
    assume asm0: "(a, u, T) \<in> S"
    then have b: "Some (f1 a u T) = ?fA a u T \<oplus> ?fB a u T \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |?fB a u T| \<succeq> |a| \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> ?fB a u T)))"
      using r by fast
    show "|?fA a u T| \<succeq> |a| \<and> Some a = ?fA a u T \<oplus> ?f2 a u T \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)))"
    proof -
      have "|?fA a u T| \<succeq> |a|"
      using AStar.prems(1)[of a u T] asm0 b asso1[of "?fA a u T" "?fB a u T" "f1 a u T" ]
        asso2[of "?fA a u T" "?fB a u T" ] option.sel succ_trans[of "|?fA a u T|" _ "|a|"]
        by blast
      moreover have "Some a = ?fA a u T \<oplus> ?f2 a u T"
        using AStar.prems(1)[of a u T] asm0 b asso1[of "?fA a u T" "?fB a u T" "f1 a u T" "f2 a u T" "?f2 a u T"]
          asso2[of "?fA a u T" "?fB a u T" "f1 a u T" "f2 a u T"] option.sel
  option.exhaust_sel[of "?fB a u T \<oplus> f2 a u T" "Some a = ?fA a u T \<oplus> ?f2 a u T"]
        by force
      moreover have "pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T))"
        using AStar.prems(1)[of a u T] asm0 b
          asso2[of "?fA a u T" "?fB a u T" ] option.sel succ_trans[of "|?fA a u T|" _ "|a|"]
        by blast
      ultimately show ?thesis
        by blast
    qed
  qed
  then obtain S' where r': "package_rhs \<phi> f S pc A \<phi> f S'" "\<And>a' u' T. (a', u', T) \<in> S' \<Longrightarrow> \<exists>a u. (a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T  \<and> |a'| = |a| "
    by fast

  let ?project = "\<lambda>a' T. (SOME r. \<exists>a u. r = (a, u) \<and> (a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T \<and> |a'| = |a| )"
  have project_prop: "\<And>a' u' T. (a', u', T) \<in> S' \<Longrightarrow> \<exists>a u. ?project a' T = (a, u) \<and> (a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T  \<and> |a'| = |a| "
  proof -
    fix a' u' T assume "(a', u', T) \<in> S'"
    then obtain a u where "(a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T  \<and> |a'| = |a| "
      using r' by blast
    moreover show "\<exists>a u. ?project a' T = (a, u) \<and> (a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T \<and> |a'| = |a| "
    proof (rule someI_ex)
      show "\<exists>r a u. r = (a, u) \<and> (a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T \<and> |a'| = |a| " using calculation by blast
    qed
  qed

  let ?nf1 = "\<lambda>a' u' T. let (a, u) = ?project a' T in (SOME r. Some r = |a'| \<oplus> ?fB a u T)"
  let ?nf2 = "\<lambda>a' u' T. a' \<ominus> ?nf1 a' u' T"

  have "\<exists>S''. package_rhs \<phi> f S' pc B \<phi> f S'' \<and> (\<forall>a\<in>S''. case a of (a', u', T) \<Rightarrow> \<exists>a u. (a, u, T) \<in> S' \<and> a' \<succeq> ?nf2 a u T \<and> |a'| = |a| )"
  proof (rule AStar(2))
    show "stable f \<and> \<phi> ## f" using \<open>stable f \<and> \<phi> ## f\<close> by simp

    then show "valid_package_set S' f"
      using AStar.prems \<open>package_rhs \<phi> f S pc A \<phi> f S'\<close> package_logic.package_rhs_proof package_logic.wf_assertion.simps(1) package_logic_axioms
      by metis
    show "wf_assertion B"
      using AStar.prems(3) by auto
    show "mono_pure_cond pc"
      by (simp add: AStar.prems(4))
    fix a' u' T assume "(a', u', T) \<in> S'"
    then obtain a u where a_u_def: "(a, u) = ?project a' T" "(a, u, T) \<in> S" "a' \<succeq> ?f2 a u T" "|a'| = |a|"
      using project_prop by force
    define nf1 where "nf1 = ?nf1 a' u' T"
    define nf2 where "nf2 = ?nf2 a' u' T"
    moreover have rnf1_def: "Some nf1 = |a'| \<oplus> ?fB a u T"
    proof -
      let ?x = "(SOME r. Some r = |a'| \<oplus> ?fB a u T )"
      have "Some ?x = |a'| \<oplus> ?fB a u T"
      proof (rule someI_ex)
        have "Some (f1 a u T) = ?fA a u T \<oplus> ?fB a u T \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |?fB a u T| \<succeq> |a|
          \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> ?fB a u T)))"
          using r a_u_def by blast
        then have "Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T"
          by (metis (no_types, lifting) AStar.prems(1) a_u_def(2) asso2 option.distinct(1) option.exhaust_sel)
        moreover have "a' \<succeq> (?f2 a u T)" using \<open>a' \<succeq> ?f2 a u T\<close> by blast
        ultimately have "a' \<succeq> ?fB a u T" using succ_trans greater_def
          by blast
        then obtain r where "Some r = |a'| \<oplus> ?fB a u T"
          using
           commutative
           greater_equiv[of a' "?fB a u T"]
           minus_equiv_def_any_elem[of a']
          by fastforce
        then show "\<exists>r. Some r = |a'| \<oplus> ?fB a u T" by blast
      qed
      moreover have "?nf1 a' u' T = ?x"
        using let_pair_instantiate[of a u _ a' T "\<lambda>a u. (SOME r. Some r = |a'| \<oplus> ?fB a u T )"] a_u_def
        by fast
      ultimately show ?thesis using nf1_def by argo
    qed

    moreover have rnf2_def: "Some a' = nf1 \<oplus> nf2"
    proof -
      have "nf2 = a' \<ominus> nf1" using nf1_def nf2_def by blast
      moreover have "a' \<succeq> nf1"
      proof -
        have "?f2 a u T \<succeq> nf1"
        proof -
          have "Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T" using r \<open>(a, u, T) \<in> S\<close> by blast
          then have "?f2 a u T \<succeq> ?fB a u T"
            using greater_def by blast
          moreover have "?f2 a u T \<succeq> |a'|"
          proof -
            have "|?f2 a u T| \<succeq> |a|"
            proof -
              have "|?f2 a u T| \<succeq> |?fB a u T|" using \<open>?f2 a u T \<succeq> ?fB a u T\<close> core_mono by blast
              moreover have "|?fB a u T| \<succeq> |a|" using r \<open>(a, u, T) \<in> S\<close> by blast
              ultimately show ?thesis using succ_trans \<open>|a'| = |a|\<close> by blast
            qed
            then show ?thesis
              using a_u_def(4)
                bigger_core_sum_defined[of "?f2 a u T"]
                greater_equiv[of _ "|a|"]
              by auto
          qed
          ultimately show ?thesis using
              core_is_pure[of a'] commutative pure_def[of "|a'|"] smaller_pure_sum_smaller[of _ _ "|a'|"] rnf1_def
            by (metis (no_types, lifting))
        qed
        then show ?thesis using \<open>a' \<succeq> ?f2 a u T\<close> succ_trans by blast
      qed
      ultimately show ?thesis using minus_some nf2_def by blast
    qed

    moreover have "pc  |a'| \<Longrightarrow> sat B (the ( |a'|  \<oplus> ?nf1 a' u' T))"
    proof -
      assume "pc  |a'|"
      moreover have "|a'| = |a|"
        by (simp add: a_u_def(4))
      then have "pc |a|" using \<open>pc  |a'|\<close> by simp
      ultimately have "sat B (the ( |a| \<oplus> ?fB a u T))"
        using r a_u_def by blast
      then have "sat B (the ( |a'| \<oplus> ?fB a u T))" using \<open>|a'| = |a|\<close> by simp

      then show "sat B (the ( |a'|  \<oplus> ?nf1 a' u' T))"
      proof -
        have "nf1 \<succeq> |a'|" using rnf1_def
          using greater_def by blast
        then have "Some nf1 = |a'| \<oplus> nf1"
          by (metis bigger_core_sum_defined commutative core_mono max_projection_prop_pure_core mpp_invo)
        then show ?thesis using nf1_def rnf1_def \<open>sat B (the ( |a'| \<oplus> ?fB a u T))\<close> by argo
      qed
    qed
    moreover have "|?nf1 a' u' T|  \<succeq>  |a'|"
    proof -
      have "?nf1 a' u' T \<succeq> |a'|" using nf1_def greater_def rnf1_def by blast
      then show ?thesis
        using max_projection_propE(3) max_projection_prop_pure_core sep_algebra.mpp_prop sep_algebra_axioms by fastforce
    qed
    ultimately show "|?nf1 a' u' T|  \<succeq>  |a'|  \<and> Some a' = ?nf1 a' u' T \<oplus> ?nf2 a' u' T \<and> (pc  |a'|  \<longrightarrow> sat B (the ( |a'|  \<oplus> ?nf1 a' u' T)))"
      using nf1_def
      by blast
  qed

  then obtain S'' where S''_prop: "package_rhs \<phi> f S' pc B \<phi> f S''" "\<And>a' u' T. (a', u', T) \<in> S'' \<Longrightarrow> \<exists>a u. (a, u, T) \<in> S' \<and> a' \<succeq> ?nf2 a u T  \<and> |a'| = |a| "
    by fast

  then have "package_rhs \<phi> f S pc (AStar A B) \<phi> f S''"
    using \<open>package_rhs \<phi> f S pc A \<phi> f S'\<close> package_rhs.AStar by presburger
  moreover have "\<And>a'' u'' T. (a'', u'', T) \<in> S'' \<Longrightarrow> \<exists>a u. (a, u, T) \<in> S \<and> a'' \<succeq> f2 a u T  \<and> |a''| = |a|"
  proof -
    fix a'' u'' T assume asm0: "(a'', u'', T) \<in> S''"

    
    then obtain a' u' where "(a', u', T) \<in> S' \<and> a'' \<succeq> ?nf2 a' u' T  \<and> |a''| = |a'| "
      using S''_prop by blast

    then obtain a u where a_u_def: "(a, u) = ?project a' T" "(a, u, T) \<in> S" "a' \<succeq> ?f2 a u T" "|a'| = |a|"
      using project_prop by force

    define nf1 where "nf1 = ?nf1 a' u' T"
    define nf2 where "nf2 = ?nf2 a' u' T"

    moreover have rnf1_def: "Some nf1 = |a'| \<oplus> ?fB a u T"
    proof -
      let ?x = "(SOME r. Some r = |a'| \<oplus> ?fB a u T )"
      have "Some ?x = |a'| \<oplus> ?fB a u T"
      proof (rule someI_ex)
        have "Some (f1 a u T) = ?fA a u T \<oplus> ?fB a u T \<and> |?fA a u T| \<succeq> |f1 a u T| \<and> |?fB a u T| \<succeq> |a|
          \<and> (pc |a| \<longrightarrow> sat A (the ( |a| \<oplus> ?fA a u T)) \<and> sat B (the ( |a| \<oplus> ?fB a u T)))"
          using r a_u_def by blast
        then have "Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T"
          by (metis (no_types, lifting) AStar.prems(1) a_u_def(2) asso2 option.distinct(1) option.exhaust_sel)
        moreover have "a' \<succeq> (?f2 a u T)" using \<open>a' \<succeq> ?f2 a u T\<close> by blast
        ultimately have "a' \<succeq> ?fB a u T" using succ_trans greater_def
          by blast
        then obtain r where "Some r = |a'| \<oplus> ?fB a u T"
          using commutative greater_equiv[of a' "?fB a u T"] minus_equiv_def_any_elem[of a' ] by fastforce
        then show "\<exists>r. Some r = |a'| \<oplus> ?fB a u T" by blast
      qed
      moreover have "?nf1 a' u' T = ?x"
        using let_pair_instantiate[of a u _ a' T "\<lambda>a u. (SOME r. Some r = |a'| \<oplus> ?fB a u T )"] a_u_def
        by fast
      ultimately show ?thesis using nf1_def by argo
    qed

    moreover have rnf2_def: "a' \<succeq> nf1 \<and> ?nf2 a' u' T \<succeq> f2 a u T"
    proof -
      have "nf2 = a' \<ominus> nf1" using nf1_def nf2_def by blast
      moreover have "a' \<succeq> nf1 \<and> a' \<ominus> nf1 \<succeq> f2 a u T"
      proof -
        have "?f2 a u T \<succeq> nf1"
        proof -
          have "Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T" using r \<open>(a, u, T) \<in> S\<close> by blast
          then have "?f2 a u T \<succeq> ?fB a u T"
            using greater_def by blast
          moreover have "?f2 a u T \<succeq> |a'|"
          proof -
            have "|?f2 a u T| \<succeq> |a|"
            proof -
              have "|?f2 a u T| \<succeq> |?fB a u T|" using \<open>?f2 a u T \<succeq> ?fB a u T\<close> core_mono by blast
              moreover have "|?fB a u T| \<succeq> |a|" using r \<open>(a, u, T) \<in> S\<close> by blast
              ultimately show ?thesis using succ_trans \<open>|a'| = |a|\<close> by blast
            qed
            then show ?thesis
              using a_u_def(4)
                bigger_core_sum_defined
                greater_equiv[of "?f2 a u T" "|a'|"]
              by auto
          qed
          ultimately show ?thesis using 
              core_is_pure[of "a'"] commutative pure_def[of "|a'|"] smaller_pure_sum_smaller[of "?f2 a u T" _ "|a'|"] rnf1_def
            by simp
        qed
        then have r1: "a' \<succeq> nf1" using \<open>a' \<succeq> ?f2 a u T\<close> succ_trans by blast
        then have "Some a' = nf1 \<oplus> nf2" using minus_some nf2_def \<open>nf2 = a' \<ominus> nf1\<close> by presburger
        have r2: "a' \<ominus> nf1 \<succeq> f2 a u T"
          using \<open>a' \<succeq> ?f2 a u T\<close>
        proof (rule prove_last_completeness)

          have "Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T"
            using r \<open>(a, u, T) \<in> S\<close> by blast
          moreover have "Some nf1 = |a'| \<oplus> ?fB a u T" using rnf1_def by blast

          have "Some (?f2 a u T) = ?fB a u T \<oplus> f2 a u T" using r \<open>(a, u, T) \<in> S\<close> by blast
          then have "?f2 a u T \<succeq> ?fB a u T"
            using greater_def by blast
          moreover have "?f2 a u T \<succeq> |a'|"
          proof -
            have "|?f2 a u T| \<succeq> |a|"
            proof -
              have "|?f2 a u T| \<succeq> |?fB a u T|" using \<open>?f2 a u T \<succeq> ?fB a u T\<close> core_mono by blast
              moreover have "|?fB a u T| \<succeq> |a|" using r \<open>(a, u, T) \<in> S\<close> by blast
              ultimately show ?thesis using succ_trans \<open>|a'| = |a|\<close> by blast
            qed
            then show ?thesis
              using a_u_def(4)
                bigger_core_sum_defined[of _ "|a|"]
                greater_equiv[of "?f2 a u T" "|a|"]
              by auto
          qed
          ultimately show "Some (?f2 a u T) = nf1 \<oplus> f2 a u T"
            using asso1[of "|a'|" "?fB a u T" nf1 "f2 a u T" "?f2 a u T"]
            asso1[of "|a'|" "|a'|" "|a'|" ] core_is_pure[of "a'"] greater_def[of "?f2 a u T" "|a'|"] rnf1_def
            by (metis (no_types, lifting))
        qed
        then show ?thesis using \<open>a' \<succeq> ?f2 a u T\<close> succ_trans using r1 by force
      qed
      ultimately show ?thesis  using nf2_def by argo
    qed
    ultimately have "(a, u, T) \<in> S \<and> a' \<succeq> ?f2 a u T \<and> ?nf2 a' u' T \<succeq> f2 a u T" using nf1_def nf2_def
        a_u_def by blast
    then have "a'' \<succeq> f2 a u T \<and>  |a''| = |a'| " using \<open>(a', u', T) \<in> S' \<and> a'' \<succeq> ?nf2 a' u' T \<and> |a''| = |a'| \<close>
      using succ_trans by blast
    then show "\<exists>a u. (a, u, T) \<in> S \<and> a'' \<succeq> f2 a u T  \<and> |a''| = |a| " using r'
      using a_u_def(2) a_u_def(4) by auto
  qed
  ultimately show ?case by blast
qed






subsection Soundness

theorem general_soundness:
  assumes "package_rhs \<phi> unit { (a, unit, T) |a T. (a, T) \<in> S } (\<lambda>_. True) A \<phi>' f S'"
      and "\<And>a T. (a, T) \<in> S \<Longrightarrow> mono_transformer T"
      and "wf_assertion A"
      and "intuitionistic (sat A) \<or> pure_remains S'"
    shows "Some \<phi> = \<phi>' \<oplus> f \<and> stable f \<and> (\<forall>(a, T) \<in> S. a ## T f \<longrightarrow> sat A (the (a \<oplus> T f)))"
proof -
  let ?S = "{ (a, unit, p) |a p. (a, p) \<in> S }"
  let ?pc = "\<lambda>_. True"
  have "package_rhs_connection \<phi> unit ?S ?pc A \<phi>' f S' \<and> valid_package_set S' f"
  proof (rule package_rhs_proof)
    show "package_rhs \<phi> unit {(a, unit, p) |a p. (a, p) \<in> S} (\<lambda>_. True) A \<phi>' f S'"
      using assms(1) by auto
    show "valid_package_set {(a, unit, p) |a p. (a, p) \<in> S} unit"
    proof (rule valid_package_setI)
      fix a u T
      assume "(a, u, T) \<in> {(a, unit, p) |a p. (a, p) \<in> S}"
      then have "u = unit" by blast
      moreover have "|T unit| = unit"
        using \<open>(a, u, T) \<in> {(a, unit, p) |a p. (a, p) \<in> S}\<close> assms(2) mono_transformer_def unit_core by fastforce
      then show "a ## u \<and> |a| \<succeq> |u| \<and> mono_transformer T \<and> a \<succeq>  |T unit|"
        using \<open>(a, u, T) \<in> {(a, unit, p) |a p. (a, p) \<in> S}\<close> assms(2) defined_def unit_core unit_neutral unit_smaller by auto
    qed
    show "wf_assertion A" by (simp add: assms(3))
    show "mono_pure_cond (\<lambda>_. True)"
      using mono_pure_cond_def by auto
    show "stable unit" by (simp add: stable_unit)
    show "\<phi> ## unit"
      using defined_def unit_neutral by auto
  qed

  then obtain r: "\<phi> \<oplus> unit = \<phi>' \<oplus> f" "stable f"
    "\<And>a u T. (a, u, T) \<in> ?S \<Longrightarrow> (\<exists>au. Some au = a \<oplus> u \<and> (au ## (T f \<ominus> T unit) \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> (T f \<ominus> T unit) = a' \<oplus> u' \<and> u' \<succeq> u \<and> package_sat ?pc A a' u' u)))"
    using package_rhs_connection_def by force

  moreover have "\<And>a T x. (a, T) \<in> S \<and> Some x = a \<oplus> T f \<Longrightarrow> sat A x"
  proof -
    fix a T x assume asm0: "(a, T) \<in> S \<and> Some x = a \<oplus> T f"
    then have "T f \<ominus> T unit = T f"
      by (metis assms(2) commutative minus_equiv_def mono_transformer_def option.sel unit_neutral unit_smaller)
    then obtain au where au_def: "Some au = a \<oplus> unit \<and> (au ## T f \<longrightarrow>
      (\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> au \<oplus> T f = a' \<oplus> u' \<and> u' \<succeq> unit \<and> package_sat ?pc A a' u' unit))"
      using r asm0 by fastforce
    then have "au = a" by (metis option.inject unit_neutral)
    then have "(\<exists>a' u'. (a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> a \<oplus> T f = a' \<oplus> u' \<and> package_sat ?pc A a' u' unit)"
      using au_def asm0 defined_def       
      by auto
    then obtain a' u' where r0: "(a', u', T) \<in> S' \<and> |a'| \<succeq> |a| \<and> a \<oplus> T f = a' \<oplus> u' \<and> package_sat ?pc A a' u' unit"
      by presburger
    then obtain y where "Some y = |a'| \<oplus> (u' \<ominus> unit)" "sat A y"
      using package_sat_def by auto
    then have "Some y =  |a'| \<oplus> u'"
      by (metis commutative minus_equiv_def splus.simps(3) unit_neutral unit_smaller)
    then have "x \<succeq> y"
      by (metis r0 addition_bigger asm0 max_projection_prop_pure_core mpp_smaller)
    then show "sat A x"
    proof (cases "intuitionistic (sat A)")
      case True
      then show ?thesis by (meson \<open>Some y = |a'| \<oplus> (u' \<ominus> unit)\<close> \<open>sat A y\<close> \<open>x \<succeq> y\<close> intuitionistic_def)
    next
      case False
      then have "pure_remains S'" using assms(4) by auto
      then have "pure a'" using pure_remains_def r0
        by fast
      then show ?thesis using r0 \<open>Some y = |a'| \<oplus> (u' \<ominus> unit)\<close> \<open>sat A y\<close> \<open>Some y = |a'| \<oplus> u'\<close> asm0 core_is_smaller
          core_max option.sel pure_def asso1[of a'] by metis
    qed
  qed
  then have "(\<forall>(a, T) \<in> S. a ## T f \<longrightarrow> sat A (the (a \<oplus> T f)))"
    using sep_algebra.defined_def sep_algebra_axioms by fastforce
  moreover have "Some \<phi> = \<phi>' \<oplus> f \<and> stable f"
    using r(1) r(2) unit_neutral by auto
  ultimately show ?thesis by blast
qed

theorem soundness:
  assumes "wf_assertion B"
      and "\<And>a. sat A a \<Longrightarrow> a \<in> S"
      and "\<And>a. a \<in> S \<Longrightarrow> mono_transformer (R a)"
      and "package_rhs \<sigma> unit { (a, unit, R a) |a. a \<in> S } (\<lambda>_. True) B \<sigma>' w S'"
      and "intuitionistic (sat B) \<or> pure_remains S'"
    shows "stable w \<and> Some \<sigma> = \<sigma>' \<oplus> w \<and> is_footprint_general w R A B"
proof -
  let ?S = "{ (a, R a) |a. a \<in> S} "
  have r: "Some \<sigma> = \<sigma>' \<oplus> w \<and> stable w \<and> (\<forall>(a, T)\<in>{(a, R a) |a. a \<in> S}. a ## T w \<longrightarrow> sat B (the (a \<oplus> T w)))"
  proof (rule general_soundness)
    show "package_rhs \<sigma> unit {(a, unit, T) |a T. (a, T) \<in> {(a, R a) |a. a \<in> S}} (\<lambda>_. True) B \<sigma>' w S'"
      using assms(4) by auto
    show "\<And>a T. (a, T) \<in> {(a, R a) |a. a \<in> S} \<Longrightarrow> mono_transformer T" using assms(3) by blast
    show "wf_assertion B" by (simp add: assms(1))
    show "intuitionistic (sat B) \<or> pure_remains S'" by (simp add: assms(5))
  qed
  moreover have "is_footprint_general w R A B"
  proof (rule is_footprint_generalI)
    fix a b assume asm: "sat A a \<and> Some b = a \<oplus> R a w"
    then have "(a, R a) \<in> ?S"
      using assms(2) by blast
    then have "sat B (the (a \<oplus> R a w))" using r using asm defined_def by fastforce
    then show "sat B b" by (metis asm option.sel)
  qed
  ultimately show ?thesis by blast
qed

corollary soundness_paper:
  assumes "wf_assertion B"
      and "\<And>a. sat A a \<Longrightarrow> a \<in> S"
      and "package_rhs \<sigma> unit { (a, unit, id) |a. a \<in> S } (\<lambda>_. True) B \<sigma>' w S'"
      and "intuitionistic (sat B) \<or> pure_remains S'"
    shows "stable w \<and> Some \<sigma> = \<sigma>' \<oplus> w \<and> is_footprint_standard w A B"
proof -
  have "stable w \<and> Some \<sigma> = \<sigma>' \<oplus> w \<and> is_footprint_general w (\<lambda>_. id) A B"
    using assms soundness[of B A S "\<lambda>_. id" \<sigma> \<sigma>' w S']
    by (simp add: mono_transformer_def)
  then show ?thesis
    using is_footprint_general_def is_footprint_standardI by fastforce
qed



subsection Completeness

theorem general_completeness:
  assumes "\<And>a u T x. (a, u, T) \<in> S \<Longrightarrow> Some x = a \<oplus> T f \<Longrightarrow> sat A x"
      and "Some \<phi> = \<phi>' \<oplus> f"
      and "stable f"
      and "valid_package_set S unit"
      and "wf_assertion A"
    shows "\<exists>S'. package_rhs \<phi> unit S (\<lambda>_. True) A \<phi>' f S'"
proof -
  define S' where "S' = { (r, u, T) |a u T r. (a, u, T) \<in> S \<and> Some r = a \<oplus> (T f \<ominus> T unit) \<and> r ## u }"
  let ?pc = "\<lambda>_. True"
  have "\<exists>S''. package_rhs \<phi>' f S' ?pc A \<phi>' f S''"
  proof -
    let ?f2 = "\<lambda>a u T. unit"
    let ?f1 = "\<lambda>a u T. a"
    have "\<exists>S''. package_rhs \<phi>' f S' ?pc A \<phi>' f S'' \<and> (\<forall>(a', u', T) \<in> S''. \<exists>a u. (a, u, T) \<in> S' \<and> a' \<succeq> ?f2 a u T \<and> |a'| = |a| )"
    proof (rule completeness_aux)
      show "mono_pure_cond (\<lambda>_. True)" by (simp add: mono_pure_cond_def)
      show "wf_assertion A" by (simp add: assms(5))
      show "valid_package_set S' f"
      proof (rule valid_package_setI)
        fix a' u' T
        assume "(a', u', T) \<in> S'"
        then obtain a where asm: "(a, u', T) \<in> S \<and> Some a' = a \<oplus> (T f \<ominus> T unit) \<and> a' ## u'"
          using S'_def by blast
        then have "a ## u' \<and>  |a|  \<succeq>  |u'|  \<and> mono_transformer T "
          using assms(4) valid_package_set_def by fastforce
        moreover have "|T f \<ominus> T unit| = |T f|"
          by (simp add: minus_core)
        ultimately show "a' ## u' \<and>  |a'|  \<succeq>  |u'|  \<and> mono_transformer T \<and> a' \<succeq>  |T f| "
          by (meson asm core_sum greater_def greater_equiv minus_equiv_def mono_transformer_def succ_trans unit_neutral)
      qed
      show "stable f \<and> \<phi>' ## f"
        by (metis assms(2) assms(3) defined_def domI domIff)
      fix a u T
      assume "(a, u, T) \<in> S'"
      then obtain a' u' where "(a', u', T) \<in> S" "Some a = a' \<oplus> (T f \<ominus> T unit)" using S'_def by blast
      moreover have "T f \<ominus> T unit = T f"
      proof -
        have "mono_transformer T" using \<open>valid_package_set S unit\<close> valid_package_set_def \<open>(a', u', T) \<in> S\<close> by auto
        then show ?thesis
          by (metis commutative minus_default minus_equiv_def mono_transformer_def option.sel unit_neutral)
      qed

      then have "sat A (the ( |a|  \<oplus> a))"
        by (metis assms(1) calculation(1) calculation(2) commutative core_is_smaller option.sel)
      then show "|a|  \<succeq>  |a|  \<and> Some a = a \<oplus> unit \<and> (True \<longrightarrow> sat A (the ( |a|  \<oplus> a)))"
        by (simp add: succ_refl unit_neutral)
    qed
    then show ?thesis by auto
  qed
  then obtain S'' where "package_rhs \<phi>' f S' ?pc A \<phi>' f S''" by blast
  have "package_rhs \<phi> unit S ?pc A \<phi>' f S''"
    using assms(2)
  proof (rule package_rhs.AddFromOutside)
    show "package_rhs \<phi>' f S' ?pc A \<phi>' f S''"
      by (simp add: \<open>package_rhs \<phi>' f S' ?pc A \<phi>' f S''\<close>)
    show "stable f" using assms(3) by simp
    show "Some f = unit \<oplus> f"
      by (simp add: commutative unit_neutral)
    show "S' = { (r, u, T) |a u T r. (a, u, T) \<in> S \<and> Some r = a \<oplus> (T f \<ominus> T unit) \<and> r ## u }"
      using S'_def by blast
  qed
  then show ?thesis
    by blast
qed

theorem completeness:
  assumes "wf_assertion B"
      and "stable w \<and> is_footprint_general w R A B"
      and "Some \<sigma> = \<sigma>' \<oplus> w"
      and "\<And>a. sat A a \<Longrightarrow> mono_transformer (R a)"
    shows "\<exists>S'. package_rhs \<sigma> unit {(a, unit, R a) |a. sat A a} (\<lambda>_. True) B \<sigma>' w S'"
proof -
  let ?S = "{(a, unit, R a) |a. sat A a}"
  have "\<exists>S'. package_rhs \<sigma> unit {(a, unit, R a) |a. sat A a} (\<lambda>_. True) B \<sigma>' w S'"
  proof (rule general_completeness[of ?S w B \<sigma> \<sigma>'])
    show "\<And>a u T x. (a, u, T) \<in> {(a, unit, R a) |a. sat A a} \<Longrightarrow> Some x = a \<oplus> T w \<Longrightarrow> sat B x"
      using assms(2) is_footprint_general_def by blast
    show "Some \<sigma> = \<sigma>' \<oplus> w" by (simp add: assms(3))
    show "stable w" by (simp add: assms(2))
    show "wf_assertion B" by (simp add: assms(1))

    show "valid_package_set {(a, unit, R a) |a. sat A a} unit"
    proof (rule valid_package_setI)
      fix a u T assume asm0: "(a, u, T) \<in> {(a, unit, R a) |a. sat A a}"
      then have "u = unit \<and> T = R a \<and> sat A a" by fastforce
      then show "a ## u \<and>  |a|  \<succeq>  |u|  \<and> mono_transformer T \<and> a \<succeq>  |T unit|"
        using assms(4) defined_def mono_transformer_def unit_core unit_neutral unit_smaller by auto
    qed
  qed
  then show ?thesis by meson
qed

corollary completeness_paper:
  assumes "wf_assertion B"
      and "stable w \<and> is_footprint_standard w A B"
      and "Some \<sigma> = \<sigma>' \<oplus> w"
    shows "\<exists>S'. package_rhs \<sigma> unit {(a, unit, id) |a. sat A a} (\<lambda>_. True) B \<sigma>' w S'"
proof -
  have "\<exists>S'. package_rhs \<sigma> unit {(a, unit, (\<lambda>_. id) a) |a. sat A a} (\<lambda>_. True) B \<sigma>' w S'"
    using assms(1)
  proof (rule completeness)
    show "stable w \<and> is_footprint_general w (\<lambda>a. id) A B"
      using assms(2) is_footprint_general_def is_footprint_standard_def by force
    show "Some \<sigma> = \<sigma>' \<oplus> w" by (simp add: assms(3))
    show "\<And>a. sat A a \<Longrightarrow> mono_transformer id" using mono_transformer_def by auto
  qed
  then show ?thesis by meson
qed


end

end
