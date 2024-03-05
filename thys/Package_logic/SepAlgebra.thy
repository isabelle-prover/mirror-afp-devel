section \<open>Separation Algebra\<close>

text \<open>In this section, we formalize the concept of a separation algebra~\<^cite>\<open>"Calcagno2007" and "Dockins2009"\<close>, on which our package logic is based.\<close>

theory SepAlgebra
  imports Main
begin

type_synonym 'a property = "'a \<Rightarrow> bool"

locale sep_algebra =

  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option" (infixl "\<oplus>" 63)

  fixes core :: "'a \<Rightarrow> 'a" (" |_| ")
  (* Largest duplicable part of a state *)

  assumes commutative: "a \<oplus> b = b \<oplus> a"
      and asso1: "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
      and asso2: "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"

(* The core of x is the max of { p | pure p \<and> x \<ge> p} *)
      and core_is_smaller: "Some x = x \<oplus> |x|"
      and core_is_pure: "Some |x| = |x| \<oplus> |x|"
      and core_max: "Some x = x \<oplus> c \<Longrightarrow> (\<exists>r. Some |x| = c \<oplus> r)"
      and core_sum: "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"

      and positivity: "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
      and cancellative: "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"

begin

lemma asso3:
  assumes "a \<oplus> b = None"
      and "b \<oplus> c = Some bc"
    shows "a \<oplus> bc = None"
  by (metis assms(1) assms(2) sep_algebra.asso2 sep_algebra.commutative sep_algebra_axioms)

subsection  \<open>Definitions\<close>

definition defined :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "##" 62) where
  "a ## b \<longleftrightarrow> a \<oplus> b \<noteq> None"

definition greater :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<succeq>" 50) where
  "a \<succeq> b \<longleftrightarrow> (\<exists>c. Some a = b \<oplus> c)"

definition pure :: "'a \<Rightarrow> bool" where
  "pure a \<longleftrightarrow> Some a = a \<oplus> a"

definition minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>" 63)
  where "b \<ominus> a = (THE_default b (\<lambda>x. Some b = a \<oplus> x \<and> x \<succeq> |b| ))"

definition add_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<otimes>" 60) where
  "A \<otimes> B = { \<phi> | \<phi> a b. a \<in> A \<and> b \<in> B \<and> Some \<phi> = a \<oplus> b }"

definition greater_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<ggreater>" 50) where
  "A \<ggreater> B \<longleftrightarrow> (\<forall>a \<in> A. \<exists>b \<in> B. a \<succeq> b)"

definition up_closed :: "'a set \<Rightarrow> bool" where
  "up_closed A \<longleftrightarrow> (\<forall>\<phi>'. (\<exists>\<phi> \<in> A. \<phi>' \<succeq> \<phi>) \<longrightarrow> \<phi>' \<in> A)"

definition equiv :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<sim>" 40) where
  "A \<sim> B \<longleftrightarrow> A \<ggreater> B \<and> B \<ggreater> A"

definition setify :: "'a property \<Rightarrow> ('a set \<Rightarrow> bool)" where
  "setify P A \<longleftrightarrow> (\<forall>x \<in> A. P x)"

definition mono_prop :: "'a property \<Rightarrow> bool" where
  "mono_prop P \<longleftrightarrow> (\<forall>x y. y \<succeq> x \<and> P x \<longrightarrow> P y)"

definition under :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "under A \<omega> = { \<omega>' | \<omega>'. \<omega>' \<in> A \<and> \<omega> \<succeq> \<omega>'}"

definition max_projection_prop :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "max_projection_prop P f \<longleftrightarrow> (\<forall>x. x \<succeq> f x \<and> P (f x) \<and>
  (\<forall>p. P p \<and> x \<succeq> p \<longrightarrow> f x \<succeq> p))"

inductive multi_plus :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  MPSingle: "multi_plus [a] a"
| MPConcat: "\<lbrakk> length la > 0 ; length lb > 0 ; multi_plus la a ; multi_plus lb b ; Some \<omega> = a \<oplus> b \<rbrakk> \<Longrightarrow> multi_plus (la @ lb)  \<omega>"

fun splus :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "splus None _ = None"
| "splus _ None = None"
| "splus (Some a) (Some b) = a \<oplus> b"



subsection \<open>First lemmata\<close>

lemma greater_equiv:
  "a \<succeq> b \<longleftrightarrow> (\<exists>c. Some a = c \<oplus> b)"
  using commutative greater_def by auto

lemma smaller_compatible:
  assumes "a' ## b"
      and "a' \<succeq> a"
    shows "a ## b"
  by (metis (full_types) assms(1) assms(2) asso3 commutative defined_def greater_def)

lemma bigger_sum_smaller:
  assumes "Some c = a \<oplus> b"
      and "a \<succeq> a'"
    shows "\<exists>b'. b' \<succeq> b \<and> Some c = a' \<oplus> b'"
proof -
  obtain r where "Some a = a' \<oplus> r" 
    using assms(2) greater_def by auto
  then obtain br where "Some br = r \<oplus> b"
    by (metis assms(1) asso2 domD domIff option.discI)
  then have "Some c = a' \<oplus> br" 
    by (metis \<open>Some a = a' \<oplus> r\<close> assms(1) asso1)
  then show ?thesis 
    using \<open>Some br = r \<oplus> b\<close> commutative greater_def by force
qed

subsubsection \<open>splus\<close>

lemma splus_develop:
  assumes "Some a = b \<oplus> c"
  shows "a \<oplus> d = splus (splus (Some b) (Some c)) (Some d)"
  by (metis assms splus.simps(3))

lemma splus_comm:
  "splus a b = splus b a"
  apply (cases a)
   apply (cases b)
    apply simp_all
  apply (cases b)
  by (simp_all add: commutative)

lemma splus_asso:
  "splus (splus a b) c = splus a (splus b c)"
proof (cases a)
  case None
  then show ?thesis 
    by simp
next
  case (Some a')
  then have "a = Some a'" by simp
  then show ?thesis
  proof (cases b)
    case None
    then show ?thesis by (simp add: Some)
  next
    case (Some b')
    then have "b = Some b'" by simp
    then show ?thesis
    proof (cases c)
      case None
      then show ?thesis by (simp add: splus_comm)
    next
      case (Some c')
      then have "c = Some c'" by simp
      then show ?thesis
      proof (cases "a' \<oplus> b'")
        case None
        then have "a' \<oplus> b' = None" by simp
        then show ?thesis
        proof (cases "b' \<oplus> c'")
          case None
          then show ?thesis 
            by (simp add: Some \<open>a = Some a'\<close> \<open>a' \<oplus> b' = None\<close> \<open>b = Some b'\<close>)
        next
          case (Some bc)
          then show ?thesis
            by (metis (full_types) None \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> sep_algebra.asso2 sep_algebra_axioms splus.simps(2) splus.simps(3) splus_comm)
        qed
      next
        case (Some ab)
        then have "Some ab = a' \<oplus> b'" by simp
        then show ?thesis
        proof (cases "b' \<oplus> c'")
          case None
          then show ?thesis 
            by (metis Some \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> asso2 splus.simps(2) splus.simps(3))
        next
          case (Some bc)
          then show ?thesis
            by (metis \<open>Some ab = a' \<oplus> b'\<close> \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> sep_algebra.asso1 sep_algebra_axioms splus.simps(3))
        qed
      qed
    qed
  qed
qed







subsubsection \<open>Pure\<close>

(* Maybe need more *)
lemma pure_stable:
  assumes "pure a"
      and "pure b"
      and "Some c = a \<oplus> b"
    shows "pure c"
  by (metis assms asso1 commutative pure_def)

(* Specific to pure *)
lemma pure_smaller:
  assumes "pure a"
      and "a \<succeq> b"
    shows "pure b"
  by (metis assms greater_def positivity pure_def)


subsection \<open>Succ is an order\<close>

lemma succ_antisym:
  assumes "a \<succeq> b"
      and "b \<succeq> a"
    shows "a = b"
proof -
  obtain ra where "Some a = b \<oplus> ra" 
    using assms(1) greater_def by auto
  obtain rb where "Some b = a \<oplus> rb" 
    using assms(2) greater_def by auto
  then have "Some a = splus (Some a) (splus (Some ra) (Some rb))"
  proof -
    have "Some b = splus (Some a) (Some rb)"
      by (simp add: \<open>Some b = a \<oplus> rb\<close>)
    then show ?thesis
      by (metis (full_types) \<open>Some a = b \<oplus> ra\<close> sep_algebra.splus.simps(3) sep_algebra_axioms splus_asso splus_comm)
  qed
  moreover have "Some b = splus (Some b) (splus (Some ra) (Some rb))"
    by (metis \<open>Some a = b \<oplus> ra\<close> \<open>Some b = a \<oplus> rb\<close> sep_algebra.splus.simps(3) sep_algebra_axioms splus_asso)
  moreover have "pure ra \<and> pure rb"
  proof -
    obtain rab where "Some rab = ra \<oplus> rb" 
      by (metis calculation(2) splus.elims splus.simps(3))
    then have "|a| \<succeq> rab" 
      by (metis calculation(1) core_max greater_def splus.simps(3))
    then have "pure rab" 
      using core_is_pure pure_def pure_smaller by blast
    moreover have "rab \<succeq> ra \<and> rab \<succeq> rb" 
      using \<open>Some rab = ra \<oplus> rb\<close> greater_def greater_equiv by blast
    ultimately have "pure ra" using pure_smaller 
      by blast
    moreover have "pure rb" 
      using \<open>pure rab\<close> \<open>rab \<succeq> ra \<and> rab \<succeq> rb\<close> pure_smaller by blast
    ultimately show ?thesis 
      by blast
  qed
  ultimately show ?thesis 
    by (metis \<open>Some b = a \<oplus> rb\<close> option.inject pure_def sep_algebra.splus.simps(3) sep_algebra_axioms splus_asso)
qed

lemma succ_trans:
  assumes "a \<succeq> b"
      and "b \<succeq> c"
    shows "a \<succeq> c"
  using assms(1) assms(2) bigger_sum_smaller greater_def by blast

lemma succ_refl:
  "a \<succeq> a" 
  using core_is_smaller greater_def by blast








subsection \<open>Core (pure) and stabilize (stable)\<close>

lemma max_projection_propI:
  assumes "\<And>x. x \<succeq> f x"
      and "\<And>x. P (f x)"
      and "\<And>x p. P p \<and> x \<succeq> p \<Longrightarrow> f x \<succeq> p"
    shows "max_projection_prop P f"
  by (simp add: assms(1) assms(2) assms(3) max_projection_prop_def)

lemma max_projection_propE:
  assumes "max_projection_prop P f"
    shows "\<And>x. x \<succeq> f x"
      and "\<And>x. P (f x)"
      and "\<And>x p. P p \<and> x \<succeq> p \<Longrightarrow> f x \<succeq> p"
  using assms max_projection_prop_def by auto

lemma max_projection_prop_pure_core:
  "max_projection_prop pure core"
proof (rule max_projection_propI)
  fix x
  show "x \<succeq> |x|" 
    using core_is_smaller greater_equiv by blast
  show "pure |x|" 
    by (simp add: core_is_pure pure_def)
  show "\<And>p. pure p \<and> x \<succeq> p \<Longrightarrow> |x| \<succeq> p"
  proof -
    fix p assume "pure p \<and> x \<succeq> p"
    then obtain r where "Some x = p \<oplus> r" 
      using greater_def by blast
    then show "|x| \<succeq> p"
      by (metis \<open>pure p \<and> x \<succeq> p\<close> asso1 commutative core_max greater_equiv pure_def)
  qed
qed

lemma mpp_smaller:
  assumes "max_projection_prop P f"
  shows "x \<succeq> f x"
  using assms max_projection_propE(1) by auto

lemma mpp_compatible:
  assumes "max_projection_prop P f"
      and "a ## b"
    shows "f a ## f b"
  by (metis (mono_tags, opaque_lifting) assms(1) assms(2) commutative defined_def max_projection_prop_def smaller_compatible)



lemma mpp_prop:
  assumes "max_projection_prop P f"
  shows "P (f x)"
  by (simp add: assms max_projection_propE(2))


lemma mppI:
  assumes "max_projection_prop P f"
      and "a \<succeq> x"
      and "P x"
      and "x \<succeq> f a"
    shows "x = f a"
proof -
  have "f a \<succeq> x" 
    using assms max_projection_propE(3) by auto
  then show ?thesis 
    by (simp add: assms(4) succ_antisym)
qed

lemma mpp_invo:
  assumes "max_projection_prop P f"
  shows "f (f x) = f x"
  using assms max_projection_prop_def succ_antisym by auto

lemma mpp_mono:
  assumes "max_projection_prop P f"
      and "a \<succeq> b"
    shows "f a \<succeq> f b"
  by (metis assms max_projection_prop_def succ_trans)


subsection \<open>Subtraction\<close>

lemma addition_bigger:
  assumes "a' \<succeq> a"
      and "Some x' = a' \<oplus> b"
      and "Some x = a \<oplus> b"
    shows "x' \<succeq> x"
  by (metis assms asso1 bigger_sum_smaller greater_def)


lemma smaller_than_core:
  assumes "y \<succeq> x"
      and "Some z = x \<oplus> |y|"
    shows "|z| = |y|"
proof -
  have "Some |z| = |x| \<oplus> |y|"
    using assms(2) core_sum max_projection_prop_pure_core mpp_invo by fastforce
  then have "Some |z| = |x| \<oplus> |y|"
    by simp
  moreover have "|z| \<succeq> |y|" 
    using calculation greater_equiv by blast
  ultimately show ?thesis 
    by (meson addition_bigger assms(1) assms(2) core_is_smaller core_sum greater_def succ_antisym)
qed

lemma extract_core:
  assumes "Some b = a \<oplus> x \<and> x \<succeq> |b|"
  shows "|x| = |b|"
proof -
  obtain r where "Some x = r \<oplus> |b|"
    using assms greater_equiv by auto
  show ?thesis
  proof (rule smaller_than_core)
    show "Some x = r \<oplus> |b|"
      using \<open>Some x = r \<oplus> |b|\<close> by auto
    show "b \<succeq> r"
      by (metis \<open>Some x = r \<oplus> |b|\<close> assms commutative greater_def succ_trans)
  qed
qed


lemma minus_unique:
  assumes "Some b = a \<oplus> x \<and> x \<succeq> |b|"
      and "Some b = a \<oplus> y \<and> y \<succeq> |b|"
    shows "x = y"
proof -
  have "|x| = |b|"
    using assms(1) extract_core by blast
  moreover have "|y| = |b|"
    using assms(2) extract_core by blast
  ultimately show ?thesis
    using assms(1) assms(2) cancellative by auto
qed

lemma minus_exists:
  assumes "b \<succeq> a"
  shows "\<exists>x. Some b = a \<oplus> x \<and> x \<succeq> |b|"
  using assms bigger_sum_smaller core_is_smaller by blast

lemma minus_equiv_def:
  assumes "b \<succeq> a"
    shows "Some b = a \<oplus> (b \<ominus> a) \<and> (b \<ominus> a) \<succeq> |b|"
proof -
  let ?x = "THE_default b (\<lambda>x. Some b = a \<oplus> x \<and> x \<succeq> |b| )"
  have "(\<lambda>x. Some b = a \<oplus> x \<and> x \<succeq> |b| ) ?x"
  proof (rule THE_defaultI')
    show "\<exists>!x. Some b = a \<oplus> x \<and> x \<succeq> |b|"
      using assms local.minus_unique minus_exists by blast
  qed
  then show ?thesis by (metis minus_def)
qed

lemma minus_default:
  assumes "\<not> b \<succeq> a"
  shows "b \<ominus> a = b"
  using THE_default_none assms greater_def minus_def by fastforce

lemma minusI:
  assumes "Some b = a \<oplus> x"
      and "x \<succeq> |b|"
    shows "x = b \<ominus> a"  
  using assms(1) assms(2) greater_def local.minus_unique minus_equiv_def by blast

lemma minus_core:
  "|a \<ominus> b| = |a|"
proof (cases "a \<succeq> b")
  case True
  then have "Some a = b \<oplus> (a \<ominus> b) \<and> a \<ominus> b \<succeq> |a|"
    using minus_equiv_def by auto
  then show ?thesis
    using extract_core by blast
next
  case False
  then show ?thesis by (simp add: minus_default)
qed


lemma minus_core_weaker:
  "|a \<ominus> b| = |a| \<ominus> |b|"
proof (cases "a \<succeq> b")
  case True
  then show ?thesis 
    by (metis greater_equiv max_projection_prop_pure_core minus_core minus_default minus_equiv_def mpp_invo succ_antisym)
next
  case False
  then show ?thesis
    by (metis greater_equiv max_projection_prop_pure_core minus_default minus_equiv_def mpp_invo succ_antisym)
qed

lemma minus_equiv_def_any_elem:
  assumes "Some x = a \<oplus> b"
  shows "Some (x \<ominus> a) = b \<oplus> |x|"
proof -
  obtain r where "Some r = b \<oplus> |x|" 
    by (metis assms core_is_smaller domD domIff option.simps(3) sep_algebra.asso2 sep_algebra_axioms)
  have "r = x \<ominus> a"
  proof (rule minusI)
    show "Some x = a \<oplus> r" 
      by (metis \<open>Some r = b \<oplus> |x|\<close> assms asso1 core_is_smaller)
    moreover show "r \<succeq> |x|"
      using \<open>Some r = b \<oplus> |x|\<close> greater_equiv by blast
  qed
  then show ?thesis 
    using \<open>Some r = b \<oplus> |x|\<close> by blast
qed

lemma minus_bigger:
  assumes "Some x = a \<oplus> b"
  shows "x \<ominus> a \<succeq> b"
  using assms greater_def minus_equiv_def_any_elem by blast

lemma minus_smaller:
  assumes "x \<succeq> a"
  shows "x \<succeq> x \<ominus> a"
  using assms greater_equiv minus_equiv_def by blast

lemma minus_sum:
  assumes "Some a = b \<oplus> c"
      and "x \<succeq> a"
    shows "x \<ominus> a = (x \<ominus> b) \<ominus> c"
proof (rule minusI)
  obtain r where "Some r = c \<oplus> (x \<ominus> a)"
    by (metis assms(1) assms(2) asso2 minus_equiv_def option.exhaust_sel)
  have "r = (x \<ominus> b)"
  proof (rule minusI)
    show "Some x = b \<oplus> r" 
      by (metis \<open>Some r = c \<oplus> (x \<ominus> a)\<close> assms(1) assms(2) asso1 minus_equiv_def)
    moreover show "r \<succeq> |x|" 
      by (meson \<open>Some r = c \<oplus> (x \<ominus> a)\<close> assms(2) greater_equiv sep_algebra.minus_equiv_def sep_algebra_axioms succ_trans)
  qed
  then show "Some (x \<ominus> b) = c \<oplus> (x \<ominus> a)" 
    using \<open>Some r = c \<oplus> (x \<ominus> a)\<close> by blast
  moreover show "x \<ominus> a \<succeq> |x \<ominus> b|"
    by (simp add: assms(2) minus_core minus_equiv_def)
qed

lemma smaller_compatible_core:
  assumes "y \<succeq> x"
  shows "x ## |y|"
  by (metis assms asso2 core_is_smaller defined_def greater_equiv option.discI)

lemma smaller_pure_sum_smaller:
  assumes "y \<succeq> a"
      and "y \<succeq> b"
      and "Some x = a \<oplus> b"
      and "pure b"
    shows "y \<succeq> x"
proof -
  obtain r where "Some y = r \<oplus> b" "r \<succeq> a"
    by (metis assms(1) assms(2) assms(4) asso1 greater_equiv pure_def)
  then show ?thesis
    using addition_bigger assms(3) by blast
qed

lemma greater_minus_trans:
  assumes "y \<succeq> x"
      and "x \<succeq> a"
    shows "y \<ominus> a \<succeq> x \<ominus> a"
proof -
  obtain r where "Some y = x \<oplus> r" 
    using assms(1) greater_def by blast
  then obtain ra where "Some x = a \<oplus> ra" 
    using assms(2) greater_def by blast
  then have "Some (x \<ominus> a) = ra \<oplus> |x|"
    by (simp add: minus_equiv_def_any_elem)
  then obtain yy where "Some yy = (x \<ominus> a) \<oplus> r" 
    by (metis (full_types) \<open>Some y = x \<oplus> r\<close> assms(2) asso3 commutative minus_equiv_def not_Some_eq)
  then obtain "Some x = a \<oplus> (x \<ominus> a)" "x \<ominus> a \<succeq>  |x|"
    by (simp_all add: assms(2) sep_algebra.minus_equiv_def sep_algebra_axioms)
  then obtain y' where "Some y' = a \<oplus> yy"
    using \<open>Some y = x \<oplus> r\<close> \<open>Some yy = x \<ominus> a \<oplus> r\<close> asso1
    by metis
  moreover have "y \<succeq> y'"
    by (metis \<open>Some x = a \<oplus> (x \<ominus> a)\<close> \<open>Some y = x \<oplus> r\<close> \<open>Some yy = x \<ominus> a \<oplus> r\<close> asso1 calculation option.inject succ_refl)
  moreover obtain x' where "Some x' = (x \<ominus> a) \<oplus> a" 
    using assms(2) commutative minus_equiv_def by fastforce
  then have "y \<succeq> x'" 
    by (metis assms(1) assms(2) commutative minus_equiv_def option.sel)
  moreover have "x' \<succeq> x \<ominus> a" 
    using \<open>Some x' = x \<ominus> a \<oplus> a\<close> greater_def by auto
  ultimately show ?thesis 
    using \<open>Some x' = x \<ominus> a \<oplus> a\<close> \<open>Some y = x \<oplus> r\<close> assms(2) asso1 commutative greater_equiv minus_bigger minus_equiv_def option.sel sep_algebra.succ_trans sep_algebra_axioms
  proof -
    have f1: "Some y' = a \<oplus> yy"
      by (simp add: \<open>Some y' = a \<oplus> yy\<close> commutative)
    then have "y = y'"
      by (metis \<open>Some y = x \<oplus> r\<close> \<open>Some yy = x \<ominus> a \<oplus> r\<close> \<open>x \<succeq> a\<close> asso1 minus_equiv_def option.sel)
    then show ?thesis
      using f1 by (metis (no_types) \<open>Some yy = x \<ominus> a \<oplus> r\<close> commutative greater_equiv minus_bigger sep_algebra.succ_trans sep_algebra_axioms)
  qed
qed




lemma minus_and_plus:
  assumes "Some \<omega>' = \<omega> \<oplus> r"
      and "\<omega> \<succeq> a"
    shows "Some (\<omega>' \<ominus> a) = (\<omega> \<ominus> a) \<oplus> r"
proof -
  have "\<omega> \<succeq> \<omega> \<ominus> a" 
    by (simp add: assms(2) minus_smaller)
  then have "(\<omega> \<ominus> a) ## r" 
    by (metis (full_types) assms(1) defined_def option.discI sep_algebra.smaller_compatible sep_algebra_axioms)
  then obtain x where "Some x = (\<omega> \<ominus> a) \<oplus> r"
    using defined_def by auto
  then have "Some \<omega>' = a \<oplus> x \<and> x \<succeq> |\<omega>'|"
    by (metis (no_types, lifting) assms asso1 core_sum max_projection_prop_pure_core minus_core minus_equiv_def mpp_smaller option.inject)
  then have "x = \<omega>' \<ominus> a" 
    by (simp add: minusI)
  then show ?thesis 
    using \<open>Some x = \<omega> \<ominus> a \<oplus> r\<close> by blast
qed









subsection \<open>Lifting the algebra to sets of states\<close>

lemma add_set_commm:
  "A \<otimes> B = B \<otimes> A"
proof
  show "A \<otimes> B \<subseteq> B \<otimes> A"
    using add_set_def sep_algebra.commutative sep_algebra_axioms by fastforce
  show "B \<otimes> A \<subseteq> A \<otimes> B"
    using add_set_def commutative by fastforce
qed

lemma x_elem_set_product:
  "x \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = a \<oplus> b)"
  using sep_algebra.add_set_def sep_algebra_axioms by fastforce

lemma x_elem_set_product_splus:
  "x \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = splus (Some a) (Some b))"
  using sep_algebra.add_set_def sep_algebra_axioms by fastforce

lemma add_set_asso:
  "(A \<otimes> B) \<otimes> C = A \<otimes> (B \<otimes> C)" (is "?A = ?B")
proof -
  have "?A \<subseteq> ?B"
  proof (rule subsetI)
    fix x assume "x \<in> ?A"
    then obtain ab c where "Some x = ab \<oplus> c" "ab \<in> A \<otimes> B" "c \<in> C"
      using x_elem_set_product by auto
    then obtain a b where "Some ab = a \<oplus> b" "a \<in> A" "b \<in> B"
      using x_elem_set_product by auto
    then obtain bc where "Some bc = b \<oplus> c" 
      by (metis \<open>Some x = ab \<oplus> c\<close> asso2 option.exhaust)
    then show "x \<in> ?B" 
      by (metis \<open>Some ab = a \<oplus> b\<close> \<open>Some x = ab \<oplus> c\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close> asso1 x_elem_set_product)
  qed
  moreover have "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix x assume "x \<in> ?B"
    then obtain a bc where "Some x = a \<oplus> bc" "a \<in> A" "bc \<in> B \<otimes> C"
      using x_elem_set_product by auto
    then obtain b c where "Some bc = b \<oplus> c" "c \<in> C" "b \<in> B"
      using x_elem_set_product by auto
    then obtain ab where "Some ab = a \<oplus> b"
      by (metis \<open>Some x = a \<oplus> bc\<close> asso3 option.collapse)
    then show "x \<in> ?A"
      by (metis \<open>Some bc = b \<oplus> c\<close> \<open>Some x = a \<oplus> bc\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close> asso1 x_elem_set_product)
  qed
  ultimately show ?thesis by blast
qed

lemma up_closedI:
  assumes "\<And>\<phi>' \<phi>. (\<phi>' :: 'a) \<succeq> \<phi> \<and> \<phi> \<in> A \<Longrightarrow> \<phi>' \<in> A"
  shows "up_closed A"
  using assms up_closed_def by blast

lemma up_closed_plus_UNIV:
  "up_closed (A \<otimes> UNIV)"
proof (rule up_closedI)
  fix \<phi> \<phi>'
  assume asm: "\<phi>' \<succeq> \<phi> \<and> \<phi> \<in> A \<otimes> UNIV"
  then obtain r a b where "Some \<phi>' = \<phi> \<oplus> r" "Some \<phi> = a \<oplus> b" "a \<in> A"
    using greater_def x_elem_set_product by auto
  then obtain br where "Some br = b \<oplus> r" 
    by (metis asso2 option.exhaust_sel)
  then have "Some \<phi>' = a \<oplus> br" 
    by (metis \<open>Some \<phi> = a \<oplus> b\<close> \<open>Some \<phi>' = \<phi> \<oplus> r\<close> splus.simps(3) splus_asso)
  then show "\<phi>' \<in> A \<otimes> UNIV" 
    using \<open>a \<in> A\<close> x_elem_set_product by auto
qed


lemma succ_set_trans:
  assumes "A \<ggreater> B"
      and "B \<ggreater> C"
    shows "A \<ggreater> C"
  by (meson assms(1) assms(2) greater_set_def succ_trans)

lemma greater_setI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<succeq> b)"
    shows "A \<ggreater> B"
  by (simp add: assms greater_set_def)  

lemma bigger_set:
  assumes "A' \<ggreater> A"
  shows "A' \<otimes> B \<ggreater> A \<otimes> B"
proof (rule greater_setI)
  fix x assume "x \<in> A' \<otimes> B"
  then obtain a' b where "Some x = a' \<oplus> b" "a' \<in> A'" "b \<in> B"
    using x_elem_set_product by auto
  then obtain a where "a' \<succeq> a" "a \<in> A"
    using assms greater_set_def by blast
  then obtain ab where "Some ab = a \<oplus> b"
    by (metis \<open>Some x = a' \<oplus> b\<close> asso2 domD domIff greater_equiv)
  then show "\<exists>ab\<in>A \<otimes> B. x \<succeq> ab"
    using \<open>Some x = a' \<oplus> b\<close> \<open>a \<in> A\<close> \<open>a' \<succeq> a\<close> \<open>b \<in> B\<close> addition_bigger x_elem_set_product by blast
qed

lemma bigger_singleton:
  assumes "\<phi>' \<succeq> \<phi>"
  shows "{\<phi>'} \<ggreater> {\<phi>}"
  by (simp add: assms greater_set_def)

lemma add_set_elem:
  "\<phi> \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. Some \<phi> = a \<oplus> b \<and> a \<in> A \<and> b \<in> B)"
  using add_set_def by auto

lemma up_closed_sum:
  assumes "up_closed A"
    shows "up_closed (A \<otimes> B)"
proof (rule up_closedI)
  fix \<phi>' \<phi> assume asm: "\<phi>' \<succeq> \<phi> \<and> \<phi> \<in> A \<otimes> B"
  then obtain a b where "a \<in> A" "b \<in> B" "Some \<phi> = a \<oplus> b" 
    using add_set_elem by auto
  moreover obtain r where "Some \<phi>' = \<phi> \<oplus> r" 
    using asm greater_def by blast
  then obtain ar where "Some ar = a \<oplus> r" 
    by (metis asso2 calculation(3) commutative option.exhaust_sel option.simps(3))
  then have "ar \<in> A" 
    by (meson assms calculation(1) greater_def sep_algebra.up_closed_def sep_algebra_axioms)
  then show "\<phi>' \<in> A \<otimes> B" 
    by (metis \<open>Some \<phi>' = \<phi> \<oplus> r\<close> \<open>Some ar = a \<oplus> r\<close> add_set_elem asso1 calculation(2) calculation(3) commutative)
qed

lemma up_closed_bigger_subset:
  assumes "up_closed B"
      and "A \<ggreater> B"
    shows "A \<subseteq> B"
  by (meson assms(1) assms(2) greater_set_def sep_algebra.up_closed_def sep_algebra_axioms subsetI)

lemma up_close_equiv:
  assumes "up_closed A"
      and "up_closed B"
    shows "A \<sim> B \<longleftrightarrow> A = B"
proof -
  have "A \<sim> B \<longleftrightarrow> A \<ggreater> B \<and> B \<ggreater> A" 
    using local.equiv_def by auto
  also have "... \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A" 
    by (metis assms(1) assms(2) greater_set_def set_eq_subset succ_refl up_closed_bigger_subset)
  ultimately show ?thesis 
    by blast
qed

lemma equiv_stable_sum:
  assumes "A \<sim> B"
  shows "A \<otimes> C \<sim> B \<otimes> C"
  using assms bigger_set local.equiv_def by auto

lemma equiv_up_closed_subset:
  assumes "up_closed A"
      and "equiv B C"
    shows "B \<subseteq> A \<longleftrightarrow> C \<subseteq> A" (is "?B \<longleftrightarrow> ?C")
proof -
  have "?B \<Longrightarrow> ?C"
    by (meson greater_set_def up_closed_def equiv_def assms(1) assms(2) subsetD subsetI)
  moreover have "?C \<Longrightarrow> ?B"
    by (meson greater_set_def up_closed_def equiv_def assms(1) assms(2) subsetD subsetI)
  ultimately show ?thesis by blast
qed

lemma mono_propI:
  assumes "\<And>x y. y \<succeq> x \<and> P x \<Longrightarrow> P y"
  shows "mono_prop P"
  using assms mono_prop_def by blast

lemma mono_prop_set:
  assumes "A \<ggreater> B"
      and "setify P B"
      and "mono_prop P"
    shows "setify P A"
  using assms(1) assms(2) assms(3) greater_set_def local.setify_def mono_prop_def by auto

lemma mono_prop_set_equiv:
  assumes "mono_prop P"
      and "equiv A B"
    shows "setify P A \<longleftrightarrow> setify P B"
  by (meson assms(1) assms(2) local.equiv_def sep_algebra.mono_prop_set sep_algebra_axioms)

lemma setify_sum:
  "setify P (A \<otimes> B) \<longleftrightarrow> (\<forall>x \<in> A. setify P ({x} \<otimes> B))" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<Longrightarrow> ?B" 
    using local.setify_def sep_algebra.add_set_elem sep_algebra_axioms singletonD by fastforce
  moreover have "?B \<Longrightarrow> ?A" 
    using add_set_elem local.setify_def by fastforce
  ultimately show ?thesis by blast
qed

lemma setify_sum_image:
  "setify P ((Set.image f A) \<otimes> B) \<longleftrightarrow> (\<forall>x \<in> A. setify P ({f x} \<otimes> B))"
proof
  show "setify P (f ` A \<otimes> B) \<Longrightarrow> \<forall>x\<in>A. setify P ({f x} \<otimes> B)"
    by (meson rev_image_eqI sep_algebra.setify_sum sep_algebra_axioms)
  show "\<forall>x\<in>A. setify P ({f x} \<otimes> B) \<Longrightarrow> setify P (f ` A \<otimes> B)"
    by (metis (mono_tags, lifting) image_iff sep_algebra.setify_sum sep_algebra_axioms)
qed

lemma equivI:
  assumes "A \<ggreater> B"
    and "B \<ggreater> A"
    shows "equiv A B"
  by (simp add: assms(1) assms(2) local.equiv_def)

lemma sub_bigger:
  assumes "A \<subseteq> B"
  shows "A \<ggreater> B" 
  by (meson assms greater_set_def in_mono succ_refl)

lemma larger_set_refl:
  "A \<ggreater> A"
  by (simp add: sub_bigger)


definition upper_closure where
  "upper_closure A = { \<phi>' |\<phi>' \<phi>. \<phi>' \<succeq> \<phi> \<and> \<phi> \<in> A }"



lemma upper_closure_up_closed:
  "up_closed (upper_closure A)"
proof (rule up_closedI)
  fix \<phi>' \<phi>
  assume asm0: "\<phi>' \<succeq> \<phi> \<and> \<phi> \<in> upper_closure A"
  then obtain a where "a \<in> A \<and> \<phi> \<succeq> a"
    using sep_algebra.upper_closure_def sep_algebra_axioms by fastforce
  then have "\<phi>' \<succeq> a"
    using asm0 succ_trans by blast
  then show "\<phi>' \<in> upper_closure A"
    using \<open>a \<in> A \<and> \<phi> \<succeq> a\<close> upper_closure_def by auto
qed


subsection \<open>Addition of more than two states\<close>

lemma multi_decompose:
  assumes "multi_plus l \<omega>"
    shows "length l \<ge> 2 \<Longrightarrow> (\<exists>a b la lb. l = la @ lb \<and> length la > 0 \<and> length lb > 0 \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b)"
  using assms
  apply (rule multi_plus.cases)
  by auto[2]



lemma multi_take_drop:
  assumes "multi_plus l \<omega>"
      and "length l \<ge> 2"
    shows "\<exists>n a b. n > 0 \<and> n < length l \<and> multi_plus (take n l) a \<and> multi_plus (drop n l) b \<and> Some \<omega> = a \<oplus> b"
proof -
  obtain a b la lb where asm0: "l = la @ lb \<and> length la > 0 \<and> length lb > 0 \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b"
    using assms(1) assms(2) multi_decompose by blast
  let ?n = "length la"
  have "la = take ?n l"
    by (simp add: asm0)
  moreover have "lb = drop ?n l" 
    by (simp add: asm0)
  ultimately show ?thesis 
    by (metis asm0 length_drop zero_less_diff)
qed

lemma multi_plus_single:
  assumes "multi_plus [v] a"
  shows "a = v"
  using assms
  apply (cases)
  apply simp
  by (metis (no_types, lifting) Nil_is_append_conv butlast.simps(2) butlast_append length_greater_0_conv)

lemma multi_plus_two:
  assumes "length l \<ge> 2"
  shows "multi_plus l \<omega> \<longleftrightarrow> (\<exists>a b la lb. l = (la @ lb) \<and> length la > 0 \<and> length lb > 0 \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b)" (is "?A \<longleftrightarrow> ?B")
  by (meson MPConcat assms multi_decompose)

lemma multi_plus_head_tail:
  "length l \<le> n \<and> length l \<ge> 2 \<longrightarrow> (multi_plus l \<omega> \<longleftrightarrow> (\<exists>r. Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r))"
proof (induction n arbitrary: l \<omega>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have IH: "\<And>(l :: 'a list) \<omega>. length l \<le> n \<and> length l \<ge> 2 \<longrightarrow> multi_plus l \<omega> = (\<exists>r. Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r)"
    by blast
  then show ?case
  proof (cases "n = 0")
    case True
    then have "n = 0" by simp
    then show ?thesis by linarith
  next
    case False
    then have "length (l :: 'a list) \<ge> 2 \<and> length l \<le> n + 1 \<Longrightarrow> multi_plus l \<omega> \<longleftrightarrow> (\<exists>r. Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r)"
      (is "length l \<ge> 2  \<and> length l \<le> n + 1 \<Longrightarrow> ?A \<longleftrightarrow> ?B")
    proof -
      assume asm: "length (l :: 'a list) \<ge> 2 \<and> length l \<le> n + 1"
      have "?B \<Longrightarrow> ?A"
      proof -
        assume "?B"
        then obtain r where "Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r" by blast
        then have "multi_plus [hd l] (hd l)" 
          using MPSingle by blast
        moreover have "[hd l] @ (tl l) = l" 
          by (metis Suc_le_length_iff asm append_Cons list.collapse list.simps(3) numeral_2_eq_2 self_append_conv2)
        ultimately show ?A 
          by (metis (no_types, lifting) MPConcat Suc_1 Suc_le_mono asm \<open>Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r\<close> append_Nil2 length_Cons length_greater_0_conv list.size(3) not_one_le_zero zero_less_Suc)
      qed
      moreover have "?A \<Longrightarrow> ?B"
      proof -
        assume ?A
        then obtain la lb a b where "l = la @ lb" "length la > 0" "length lb > 0" "multi_plus la a" "multi_plus lb b" "Some \<omega> = a \<oplus> b"
          using asm multi_decompose by blast
        then have r0: "length la \<le> n \<and> length la \<ge> 2 \<longrightarrow> multi_plus la a = (\<exists>r. Some a = hd la \<oplus> r \<and> multi_plus (tl la) r)"
          using IH by blast
        then show ?B
        proof (cases "length la \<ge> 2")
          case True
          then obtain ra where "Some a = (hd la) \<oplus> ra" "multi_plus (tl la) ra"
            by (metis Suc_eq_plus1 \<open>0 < length lb\<close> \<open>l = la @ lb\<close> r0 \<open>multi_plus la a\<close> append_eq_conv_conj asm drop_eq_Nil le_add1 le_less_trans length_append length_greater_0_conv less_Suc_eq_le order.not_eq_order_implies_strict)
          moreover obtain rab where "Some rab = ra \<oplus> b"
            by (metis \<open>Some \<omega> = a \<oplus> b\<close> calculation(1) asso2 option.exhaust_sel)
          then have "multi_plus ((tl la) @ lb) rab" 
            by (metis (no_types, lifting) Nil_is_append_conv \<open>multi_plus lb b\<close> calculation(2) length_greater_0_conv list.simps(3) multi_plus.cases sep_algebra.MPConcat sep_algebra_axioms)
          moreover have "Some \<omega> = hd la \<oplus> rab" 
            by (metis \<open>Some \<omega> = a \<oplus> b\<close> \<open>Some rab = ra \<oplus> b\<close> asso1 calculation(1))
          ultimately show ?B 
            using \<open>0 < length la\<close> \<open>l = la @ lb\<close> by auto
        next
          case False
          then have "length la = 1" 
            using \<open>0 < length la\<close> by linarith
          then have "la = [a]"
            by (metis Nitpick.size_list_simp(2) One_nat_def Suc_le_length_iff \<open>multi_plus la a\<close> diff_Suc_1 le_numeral_extra(4) length_0_conv list.sel(3) sep_algebra.multi_plus_single sep_algebra_axioms)
          then show ?thesis 
            using \<open>Some \<omega> = a \<oplus> b\<close> \<open>l = la @ lb\<close> \<open>multi_plus lb b\<close> by auto
        qed
      qed
      then show ?thesis using calculation by blast
    qed
    then show ?thesis by (metis (no_types, lifting) Suc_eq_plus1)
  qed
qed

lemma not_multi_plus_empty:
  "\<not> multi_plus [] \<omega>"
  by (metis Nil_is_append_conv length_greater_0_conv list.simps(3) sep_algebra.multi_plus.simps sep_algebra_axioms)

lemma multi_plus_deter:
  "length l \<le> n \<Longrightarrow> multi_plus l \<omega> \<Longrightarrow> multi_plus l \<omega>' \<Longrightarrow> \<omega> = \<omega>'"
proof (induction n arbitrary: l \<omega> \<omega>')
  case 0
  then show ?case 
    using multi_plus.cases by auto
next
  case (Suc n)
  then show ?case
  proof (cases "length l \<ge> 2")
    case True
    then obtain r where "Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r"
      using Suc.prems(2) multi_plus_head_tail by blast
    moreover obtain r' where "Some \<omega>' = (List.hd l) \<oplus> r' \<and> multi_plus (List.tl l) r'"
      using Suc.prems(3) True multi_plus_head_tail by blast
    ultimately have "r = r'" 
      by (metis Suc.IH Suc.prems(1) drop_Suc drop_eq_Nil)
    then show ?thesis 
      by (metis \<open>Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r\<close> \<open>Some \<omega>' = hd l \<oplus> r' \<and> multi_plus (tl l) r'\<close> option.inject)
  next
    case False
    then have "length l \<le> 1" 
      by simp
    then show ?thesis
    proof (cases "length l = 0")
      case True
      then show ?thesis
        using Suc.prems(2) sep_algebra.not_multi_plus_empty sep_algebra_axioms by fastforce
    next
      case False
      then show ?thesis 
        by (metis One_nat_def Suc.prems(2) Suc.prems(3) Suc_length_conv \<open>length l \<le> 1\<close> le_SucE le_zero_eq length_greater_0_conv less_numeral_extra(3) sep_algebra.multi_plus_single sep_algebra_axioms)
    qed      
  qed
qed

lemma multi_plus_implies_multi_plus_of_drop:
  assumes "multi_plus l \<omega>"
      and "n < length l"
    shows "\<exists>a. multi_plus (drop n l) a \<and> \<omega> \<succeq> a"
  using assms
proof (induction n arbitrary: l \<omega>)
  case 0
  then show ?case using succ_refl by fastforce
next
  case (Suc n)
  then have "length l \<ge> 2" 
    by linarith
  then obtain r where "Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r" 
    using Suc.prems(1) multi_plus_head_tail by blast
  then obtain a where "multi_plus (drop n (List.tl l)) a \<and> r \<succeq> a" 
    using Suc.IH Suc.prems(2) by fastforce
  then show ?case 
    by (metis \<open>Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r\<close> bigger_sum_smaller commutative drop_Suc greater_def)
qed

lemma multi_plus_bigger_than_head:
  assumes "length l > 0"
      and "multi_plus l \<omega>"
    shows "\<omega> \<succeq> List.hd l"
proof (cases "length l \<ge> 2")
  case True
  then obtain r where "Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r" 
    using assms(1) assms(2) multi_plus_head_tail by blast
  then show ?thesis 
    using greater_def by blast
next
  case False
  then show ?thesis
    by (metis Cons_nth_drop_Suc MPSingle assms(1) assms(2) drop_0 drop_eq_Nil hd_conv_nth length_greater_0_conv not_less_eq_eq numeral_2_eq_2 sep_algebra.multi_plus_deter sep_algebra_axioms succ_refl)
qed

lemma multi_plus_bigger:
  assumes "i < length l"
      and "multi_plus l \<omega>"
    shows "\<omega> \<succeq> (l ! i)"
proof -
  obtain a where "multi_plus (drop i l) a \<and> \<omega> \<succeq> a"
    using assms(1) assms(2) multi_plus_implies_multi_plus_of_drop order.strict_trans by blast
  moreover have "List.hd (drop i l) = l ! i" 
    by (simp add: assms(1) hd_drop_conv_nth)
  then show ?thesis
    by (metis (no_types, lifting) succ_trans assms(1) assms(2) drop_eq_Nil leD length_greater_0_conv multi_plus_bigger_than_head multi_plus_implies_multi_plus_of_drop)
qed


lemma sum_then_singleton:
  "Some a = b \<oplus> c \<longleftrightarrow> {a} = {b} \<otimes> {c}" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<Longrightarrow> ?B"
  proof -
    assume ?A
    then have "{a} \<subseteq> {b} \<otimes> {c}"
      using add_set_elem by auto
    moreover have "{b} \<otimes> {c} \<subseteq> {a}"
    proof (rule subsetI)
      fix x assume "x \<in> {b} \<otimes> {c}"
      then show "x \<in> {a}"
        by (metis \<open>Some a = b \<oplus> c\<close> option.sel sep_algebra.add_set_elem sep_algebra_axioms singleton_iff)
    qed
    ultimately show ?thesis by blast
  qed
  moreover have "?B \<Longrightarrow> ?A" 
    using add_set_elem by auto
  ultimately show ?thesis by blast
qed

lemma empty_set_sum:
  "{} \<otimes> A = {}" 
  by (simp add: add_set_def)


end

end
