(*
  File:     Cardinality_Continuum/Cardinality_Continuum_Library.thy
  Author:   Manuel Eberl (University of Innsbruck)

  Some missing facts about cardinality and equipollence, but most notably
  the definition and cardinality results about the "finite subsets of" operator and the
  "functions with finite support" operator.
*)
section \<open>Auxiliary material\<close>
theory Cardinality_Continuum_Library
  imports "HOL-Library.Equipollence" "HOL-Cardinals.Cardinals"
begin

subsection \<open>Miscellaneous facts about cardinalities\<close>

(* Equipollence *)
lemma eqpoll_Pow [intro]:
  assumes "A \<approx> B"
  shows   "Pow A \<approx> Pow B"
proof -
  from assms obtain f where "bij_betw f A B"
    unfolding eqpoll_def by blast
  hence "bij_betw ((`) f) (Pow A) (Pow B)"
    by (rule bij_betw_Pow)
  thus ?thesis
    unfolding eqpoll_def by blast
qed

lemma lepoll_UNIV_nat_iff: "A \<lesssim> (UNIV :: nat set) \<longleftrightarrow> countable A"
  unfolding countable_def lepoll_def by simp

lemma countable_eqpoll:     
  assumes "countable A" "A \<approx> B"
  shows   "countable B"
  using assms countable_iff_bij unfolding eqpoll_def by blast

lemma countable_eqpoll_cong: "A \<approx> B \<Longrightarrow> countable A \<longleftrightarrow> countable B"
  using countable_eqpoll[of A B] countable_eqpoll[of B A]
  by (auto simp: eqpoll_sym)

lemma eqpoll_UNIV_nat_iff: "A \<approx> (UNIV :: nat set) \<longleftrightarrow> countable A \<and> infinite A"
proof
  assume *: "A \<approx> (UNIV :: nat set)"
  show "countable A \<and> infinite A"
    using eqpoll_finite_iff[OF *] countable_eqpoll_cong[OF *] by simp
next
  assume *: "countable A \<and> infinite A"
  thus "A \<approx> (UNIV :: nat set)"
    by (meson countableE_infinite eqpoll_def)
qed


(* HOL-Cardinals *)
lemma ordLeq_finite_infinite:
  "finite A \<Longrightarrow> infinite B \<Longrightarrow> (card_of A, card_of B) \<in> ordLeq"
  by (meson card_of_Well_order card_of_ordLeq_finite ordLeq_total)

lemma eqpoll_imp_card_of_ordIso: "A \<approx> B \<Longrightarrow> |A| =o |B|"
  by (simp add: eqpoll_iff_card_of_ordIso)

lemma card_of_Func: "|Func A B| =o |B| ^c |A|"
  by (simp add: cexp_def)

lemma card_of_leq_natLeq_iff_countable:
  "|X| \<le>o natLeq \<longleftrightarrow> countable X"
proof -
  have "countable X  \<longleftrightarrow> |X| \<le>o |UNIV :: nat set|"
    unfolding countable_def by (meson card_of_ordLeq top_greatest)
  with card_of_nat show ?thesis
    using ordIso_symmetric ordLeq_ordIso_trans by blast
qed

lemma card_of_Sigma_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> |B x| =o |B' x|"
  shows   "|SIGMA x:A. B x| =o |SIGMA x:A. B' x|"
proof -
  have "\<exists>f. bij_betw f (B x) (B' x)" if "x \<in> A" for x
    using assms that card_of_ordIso by blast
  then obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> bij_betw (f x) (B x) (B' x)"
    by metis
  have "bij_betw (\<lambda>(x,y). (x, f x y)) (SIGMA x:A. B x) (SIGMA x:A. B' x)"
    using f by (fastforce simp: bij_betw_def inj_on_def image_def)
  thus ?thesis
    by (rule card_of_ordIsoI)
qed

lemma Cfinite_cases:
  assumes "Cfinite c"
  obtains n :: nat where "(c, natLeq_on n) \<in> ordIso"
proof -
  from assms have "card_of (Field c) =o natLeq_on (card (Field c))"
    by (simp add: cfinite_def finite_imp_card_of_natLeq_on)
  with that[of "card (Field c)"] show ?thesis
    using assms card_of_unique ordIso_transitive by blast
qed

lemma empty_nat_ordIso_czero: "({} :: (nat \<times> nat) set) =o czero"
proof -
  have "({} :: (nat \<times> nat) set) =o |{} :: nat set|"
    using finite_imp_card_of_natLeq_on[of "{} :: nat set"] by (simp add: ordIso_symmetric)
  moreover have "|{} :: nat set| =o czero"
    by (simp add: card_of_ordIso_czero_iff_empty)
  ultimately show "({} :: (nat \<times> nat) set) =o czero"
    using ordIso_symmetric ordIso_transitive by blast
qed

lemma card_order_on_empty: "card_order_on {} {}"
  unfolding card_order_on_def well_order_on_def linear_order_on_def partial_order_on_def
            preorder_on_def antisym_def trans_def refl_on_def total_on_def ordLeq_def embed_def
  by (auto intro!: ordLeq_refl)

lemma natLeq_on_plus_ordIso: "natLeq_on (m + n) =o natLeq_on m +c natLeq_on n"
proof -
  have "{0..<m+n} = {0..<m} \<union> {m..<m+n}"
    by auto
  also have "card_of ({0..<m} \<union> {m..<m+n}) =o card_of ({0..<m} <+> {m..<m+n})"
    by (rule card_of_Un_Plus_ordIso) auto
  also have "card_of ({0..<m} <+> {m..<m+n}) =o card_of {0..<m} +c card_of {m..<m+n}"
    by (rule Plus_csum)
  also have "card_of {0..<m} +c card_of {m..<m+n} =o natLeq_on m +c natLeq_on n"
    using finite_imp_card_of_natLeq_on[of "{m..<m+n}"]
    by (intro csum_cong card_of_less) auto
  finally have "|{0..<m+n}| =o natLeq_on m +c natLeq_on n" .
  moreover have "card_of {0..<m+n} =o natLeq_on (m + n)"
    by (rule card_of_less)
  ultimately show ?thesis
    using ordIso_symmetric ordIso_transitive by blast
qed

lemma natLeq_on_1_ord_iso: "natLeq_on 1 =o BNF_Cardinal_Arithmetic.cone"
proof -
  have "|{0..<1::nat}| =o natLeq_on 1"
    by (rule card_of_less)
  hence "|{0::nat}| =o natLeq_on 1"
    by simp
  moreover have "|{0::nat}| =o BNF_Cardinal_Arithmetic.cone"
    by (rule single_cone)
  ultimately show ?thesis
    using ordIso_symmetric ordIso_transitive by blast
qed

lemma cexp_infinite_finite_ordLeq:
  assumes "Cinfinite c" "Cfinite c'"
  shows   "c ^c c' \<le>o c"
proof -
  have c: "Card_order c"
    using assms by auto
  from assms obtain n where n: "c' =o natLeq_on n"
    using Cfinite_cases by auto
  have "c ^c c' =o c ^c natLeq_on n"
    using assms(2) by (intro cexp_cong2 c n) auto
  also have "c ^c natLeq_on n \<le>o c"
  proof (induction n)
    case 0
    have "c ^c natLeq_on 0 =o c ^c czero"
      by (intro cexp_cong2) (use assms in \<open>auto simp: empty_nat_ordIso_czero card_order_on_empty\<close>)
    also have "c ^c czero =o BNF_Cardinal_Arithmetic.cone"
      by (rule cexp_czero)
    also have "BNF_Cardinal_Arithmetic.cone \<le>o c"
      using assms by (simp add: Cfinite_cone Cfinite_ordLess_Cinfinite ordLess_imp_ordLeq)
    finally show ?case .
  next
    case (Suc n)
    have "c ^c natLeq_on (Suc n) =o c ^c (natLeq_on n +c natLeq_on 1)"
      using assms natLeq_on_plus_ordIso[of n 1]
      by (intro cexp_cong2) (auto simp: natLeq_on_Card_order intro: ordIso_symmetric)
    also have "c ^c (natLeq_on n +c natLeq_on 1) =o c ^c natLeq_on n *c c ^c natLeq_on 1"
      by (rule cexp_csum)
    also have "c ^c natLeq_on n *c c ^c natLeq_on 1 \<le>o c *c c"
    proof (rule cprod_mono)
      show "c ^c natLeq_on n \<le>o c"
        by (rule Suc.IH)
      have "c ^c natLeq_on 1 =o c ^c BNF_Cardinal_Arithmetic.cone"
        by (intro cexp_cong2 c natLeq_on_1_ord_iso natLeq_on_Card_order)
      also have "c ^c BNF_Cardinal_Arithmetic.cone =o c"
        by (intro cexp_cone c)
      finally show "c ^c natLeq_on 1 \<le>o c"
        by (rule ordIso_imp_ordLeq)
    qed
    also have "c *c c =o c"
      using assms(1) by (rule cprod_infinite)
    finally show "c ^c natLeq_on (Suc n) \<le>o c" .
  qed
  finally show ?thesis .  
qed

lemma cexp_infinite_finite_ordIso:
  assumes "Cinfinite c" "Cfinite c'" "BNF_Cardinal_Arithmetic.cone \<le>o c'"
  shows   "c ^c c' =o c"
proof -
  have c: "Card_order c"
    using assms by auto
  have "c =o c ^c BNF_Cardinal_Arithmetic.cone"
    by (rule ordIso_symmetric, rule cexp_cone) fact
  also have "c ^c BNF_Cardinal_Arithmetic.cone \<le>o c ^c c'"
    by (intro cexp_mono2 c assms Card_order_cone) (use cone_not_czero in auto)
  finally have "c \<le>o c ^c c'" .
  moreover have "c ^c c' \<le>o c"
    by (rule cexp_infinite_finite_ordLeq) fact+
  ultimately show ?thesis
    by (simp add: ordIso_iff_ordLeq)
qed

lemma Cfinite_ordLeq_Cinfinite:
  assumes "Cfinite c" "Cinfinite c'"
  shows   "c \<le>o c'"
  using assms Cfinite_ordLess_Cinfinite ordLess_imp_ordLeq by blast

lemma cfinite_card_of_iff [simp]: "BNF_Cardinal_Arithmetic.cfinite (card_of X) \<longleftrightarrow> finite X"
  by (simp add: cfinite_def)

lemma cinfinite_card_of_iff [simp]: "BNF_Cardinal_Arithmetic.cinfinite (card_of X) \<longleftrightarrow> infinite X"
  by (simp add: cinfinite_def)

lemma Func_conv_PiE: "Func A B = PiE A (\<lambda>_. B)"
  by (auto simp: Func_def PiE_def extensional_def)

lemma finite_Func [intro]:
  assumes "finite A" "finite B"
  shows   "finite (Func A B)"
  using assms unfolding Func_conv_PiE by (intro finite_PiE)

lemma ordLeq_antisym: "(c, c') \<in> ordLeq \<Longrightarrow> (c', c) \<in> ordLeq \<Longrightarrow> (c, c') \<in> ordIso"
  using ordIso_iff_ordLeq by auto

lemma cmax_cong:
  assumes "(c1, c1') \<in> ordIso" "(c2, c2') \<in> ordIso" "Card_order c1" "Card_order c2"
  shows   "cmax c1 c2 =o cmax c1' c2'"
proof -
  have [intro]: "Card_order c1'" "Card_order c2'"
    using assms Card_order_ordIso2 by auto
  have "c1 \<le>o c2 \<or> c2 \<le>o c1"
    by (intro ordLeq_total) (use assms in auto)
  thus ?thesis
  proof
    assume le: "c1 \<le>o c2"
    with assms have le': "c1' \<le>o c2'"
      by (meson ordIso_iff_ordLeq ordLeq_transitive)
    have "cmax c1 c2 =o c2"
      by (rule cmax2) (use le assms in auto)
    moreover have "cmax c1' c2' =o c2'"
      by (rule cmax2) (use le' assms in auto)
    ultimately show ?thesis
      using assms ordIso_symmetric ordIso_transitive by metis
  next
    assume le: "c2 \<le>o c1"
    with assms have le': "c2' \<le>o c1'"
      by (meson ordIso_iff_ordLeq ordLeq_transitive)
    have "cmax c1 c2 =o c1"
      by (rule cmax1) (use le assms in auto)
    moreover have "cmax c1' c2' =o c1'"
      by (rule cmax1) (use le' assms in auto)
    ultimately show ?thesis
      using assms ordIso_symmetric ordIso_transitive by metis
  qed
qed


subsection \<open>The set of finite subsets\<close>

text \<open>
  We define an operator \<open>FinPow(X)\<close> that, given a set \<open>X\<close>, returns the set of all
  finite subsets of that set. For finite \<open>X\<close>, this is boring since it is obviously just the
  power set. For infinite \<open>X\<close>, it is however a useful concept to have.

  We will show that if \<open>X\<close> is infinite then the cardinality of \<open>FinPow(X)\<close> is exactly
  the same as that of \<open>X\<close>.
\<close>
definition FinPow :: "'a set \<Rightarrow> 'a set set" where
  "FinPow X = {Y. Y \<subseteq> X \<and> finite Y}"

lemma finite_FinPow [intro]: "finite A \<Longrightarrow> finite (FinPow A)"
  by (auto simp: FinPow_def)

lemma in_FinPow_iff: "Y \<in> FinPow X \<longleftrightarrow> Y \<subseteq> X \<and> finite Y"
  by (auto simp: FinPow_def)

lemma FinPow_subseteq_Pow: "FinPow X \<subseteq> Pow X"
  unfolding FinPow_def by blast

lemma FinPow_eq_Pow: "finite X \<Longrightarrow> FinPow X = Pow X"
  unfolding FinPow_def using finite_subset by blast

theorem card_of_FinPow_infinite:
  assumes "infinite A"
  shows   "|FinPow A| =o |A|"
proof -
  have "set ` lists A = FinPow A"
    using finite_list[where ?'a = 'a] by (force simp: FinPow_def)
  hence "|FinPow A| \<le>o |lists A|"
    by (metis card_of_image)
  also have "|lists A| =o |A|"
    using assms by (rule card_of_lists_infinite)
  finally have "|FinPow A| \<le>o |A|" .
  moreover have "inj_on (\<lambda>x. {x}) A" "(\<lambda>x. {x}) ` A \<subseteq> FinPow A"
    by (auto simp: inj_on_def FinPow_def)
  hence "|A| \<le>o |FinPow A|"
    using card_of_ordLeq by blast
  ultimately show ?thesis
    by (simp add: ordIso_iff_ordLeq)
qed


subsection \<open>The set of functions with finite support\<close>

text \<open>
  Next, we define an operator $\text{Func\_finsupp}_z(A, B)$ that, given sets \<open>A\<close> and \<open>B\<close> and
  an element \<open>z \<in> B\<close>, returns the set of functions \<open>f : A \<rightarrow> B\<close> that have \<^emph>\<open>finite support\<close>, i.e.\ 
  that map all but a finite subset of \<open>A\<close> to \<open>z\<close>.
\<close>
definition Func_finsupp :: "'b \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "Func_finsupp z A B = {f\<in>A \<rightarrow> B. (\<forall>x. x \<notin> A \<longrightarrow> f x = z) \<and> finite {x. f x \<noteq> z}}"

lemma bij_betw_Func_finsup_Func_finite:
  assumes "finite A"
  shows   "bij_betw (\<lambda>f. restrict f A) (Func_finsupp z A B) (Func A B)"
  by (rule bij_betwI[of _ _ _ "\<lambda>f x. if x \<in> A then f x else z"])
     (use assms in \<open>auto simp: Func_finsupp_def Func_def\<close>)

lemma eqpoll_Func_finsup_Func_finite: "finite A \<Longrightarrow> Func_finsupp z A B \<approx> Func A B"
  by (meson bij_betw_Func_finsup_Func_finite eqpoll_def)

lemma card_of_Func_finsup_finite: "finite A \<Longrightarrow> |Func_finsupp z A B| =o |B| ^c |A|"
  using eqpoll_Func_finsup_Func_finite
  by (metis Field_card_of cexp_def eqpoll_imp_card_of_ordIso)

text \<open>
  The cases where $A$ and $B$ are both finite or $B = \{0\}$ or $A = \emptyset$ are of course
  trivial.

  Perhaps not completely obviously, it turns out that in all other cases, the cardinality of
  $\text{Func\_finsupp}_z(A, B)$ is exactly $\text{max}(|A|, |B|)$.
\<close>
theorem card_of_Func_finsupp_infinite:
  assumes "z \<in> B" and "B - {z} \<noteq> {}" and "A \<noteq> {}"
  assumes "infinite A \<or> infinite B"
  shows   "|Func_finsupp z A B| =o cmax |A| |B|"
proof -
  have inf_cmax: "Cinfinite (cmax |A| |B| )"
    using assms by (simp add: Card_order_cmax cinfinite_def finite_cmax)

  have "bij_betw (\<lambda>f. ({x. f x \<noteq> z}, restrict f {x. f x \<noteq> z}))
          (Func_finsupp z A B) (SIGMA X:FinPow A. Func X (B - {z}))"
    by (rule bij_betwI[of _ _ _ "\<lambda>(X,f) x. if x \<in> -X \<union> -A then z else f x"])
       (fastforce simp: Func_def Func_finsupp_def FinPow_def fun_eq_iff \<open>z \<in> B\<close> split: if_splits)+
  hence "|Func_finsupp z A B| =o |SIGMA X:FinPow A. Func X (B - {z})|"
    by (rule card_of_ordIsoI)

  also have "|SIGMA X:FinPow A. Func X (B - {z})| =o cmax |A| |B|"
  proof (rule ordLeq_antisym)
    show "|SIGMA X:FinPow A. Func X (B - {z})| \<le>o cmax |A| |B|"
    proof (intro card_of_Sigma_ordLeq_infinite_Field ballI)
      show "infinite (Field (cmax |A| |B| ))"
        using assms by (simp add: finite_cmax)
    next
      show "Card_order (cmax |A| |B| )"
        by (intro Card_order_cmax) auto
    next
      show "|FinPow A| \<le>o cmax |A| |B|"
      proof (cases "finite A")
        assume "infinite A"
        hence "|FinPow A| =o |A|"
          by (rule card_of_FinPow_infinite)
        also have "|A| \<le>o cmax |A| |B|"
          by (simp add: ordLeq_cmax)
        finally show ?thesis .
      next
        assume A: "finite A"
        have "finite (FinPow A)"
          using A by auto
        thus "|FinPow A| \<le>o cmax |A| |B|"
          using A by (intro Cfinite_ordLeq_Cinfinite inf_cmax) auto
      qed
    next
      show "|Func X (B - {z})| \<le>o cmax |A| |B|" if "X \<in> FinPow A" for X
      proof (cases "finite B")
        case True
        have "finite X"
          using that by (auto simp: FinPow_def)
        hence "finite (Func X (B - {z}))"
          using True by blast
        with inf_cmax show ?thesis
          by (intro Cfinite_ordLeq_Cinfinite) auto
      next
        case False
        have "|Func X (B - {z})| =o |B - {z}| ^c |X|"
          by (rule card_of_Func)
        also have "|B - {z}| ^c |X| \<le>o |B - {z}|"
          by (rule cexp_infinite_finite_ordLeq) (use False that in \<open>auto simp: FinPow_def\<close>)
        also have "|B - {z}| =o |B|"
          using False by (simp add: infinite_card_of_diff_singl)
        also have "|B| \<le>o cmax |A| |B|"
          by (simp add: ordLeq_cmax)
        finally show ?thesis .
      qed
    qed
  next
    have "cmax |A| |B| =o |A| *c |B - {z}|"
    proof (cases "|A| \<le>o |B|")
      case False
      have "\<not>|B - {z}| =o czero"
        using \<open>B - {z} \<noteq> {}\<close> by (subst card_of_ordIso_czero_iff_empty) auto
      from False and assms have "infinite A"
        using ordLeq_finite_infinite by blast
      from False have "|B| \<le>o |A|"
        by (simp add: ordLess_imp_ordLeq)
      have "|B - {z}| \<le>o |B|"
        by (rule card_of_mono1) auto
      also note \<open>|B| \<le>o |A|\<close>
      finally have "|A| *c |B - {z}| =o |A|"
        using \<open>infinite A\<close> \<open>\<not>|B - {z}| =o czero\<close> by (intro cprod_infinite1') auto
      moreover have "cmax |A| |B| =o |A|"
        using \<open>|B| \<le>o |A|\<close> by (simp add: cmax1)
      ultimately show ?thesis
        using ordIso_symmetric ordIso_transitive by blast
    next
      case True
      from True and assms have "infinite B"
        using card_of_ordLeq_finite by blast
      have "|A| *c |B - {z}| =o |A| *c |B|"
        using \<open>infinite B\<close>  by (intro cprod_cong2) (simp add: infinite_card_of_diff_singl)
      also have "|A| *c |B| =o |B|"
        using True \<open>infinite B\<close> assms(3)
        by (simp add: card_of_ordIso_czero_iff_empty cprod_infinite2')
      also have "|B| =o cmax |A| |B|"
        using True by (meson card_of_Card_order cmax2 ordIso_symmetric)
      finally show ?thesis
        using ordIso_symmetric ordIso_transitive by blast
    qed
    also have "|A| *c |B - {z}| =o |A \<times> (B - {z})|"
      by (metis Field_card_of card_of_refl cprod_def)
    also have "|A \<times> (B - {z})| \<le>o |SIGMA X:(\<lambda>x. {x})`A. B - {z}|"
      by (intro card_of_Sigma_mono[of "\<lambda>x. {x}"]) auto
    also have "|SIGMA X:(\<lambda>x. {x})`A. B - {z}| =o |SIGMA X:(\<lambda>x. {x})`A. Func X (B - {z})|"
    proof (rule card_of_Sigma_cong; safe)
      fix x assume x: "x \<in> A"
      have "|Func {x} (B - {z})| =o |B - {z}| ^c |{x}|"
        by (simp add: card_of_Func)
      also have "|B - {z}| ^c |{x}| =o |B - {z}| ^c BNF_Cardinal_Arithmetic.cone"
        by (intro cexp_cong2) (auto simp: single_cone)
      also have "|B - {z}| ^c Wellorder_Constructions.cone =o |B - {z}|"
        using card_of_Card_order cexp_cone by blast
      finally show "|B - {z}| =o |Func {x} (B - {z})|"
        using ordIso_symmetric by blast
    qed
    also have "|SIGMA X:(\<lambda>x. {x})`A. Func X (B - {z})| \<le>o |SIGMA X:FinPow A. Func X (B - {z})|"
      by (rule card_of_Sigma_mono) (auto simp: FinPow_def)
    finally show "cmax |A| |B| \<le>o |SIGMA X:FinPow A. Func X (B - {z})|" .
  qed
  finally show ?thesis .
qed

end