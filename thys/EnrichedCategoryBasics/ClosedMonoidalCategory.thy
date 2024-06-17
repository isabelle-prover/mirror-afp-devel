(*  Title:       ClosedMonoidalCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

text\<open>
  A \emph{closed monoidal category} is a monoidal category such that
  for every object \<open>b\<close>, the functor \<open>\<hyphen> \<otimes> b\<close> is a left adjoint functor.
  A right adjoint to this functor takes each object \<open>c\<close> to the \emph{exponential}
  \<open>exp b c\<close>.  The adjunction yields a natural bijection between \<open>hom (- \<otimes> b) c\<close>
  and \<open>hom - (exp b c)\<close>.
  In enriched category theory, the notion of ``hom-set'' from classical category
  theory is generalized to that of ``hom-object'' in a monoidal category.
  When the monoidal category in question is closed, much of the theory of
  set-based categories can be reproduced in the more general enriched setting.
  The main purpose of this section is to prepare the way for such a development;
  in particular we do the main work required to show that a closed monoidal category
  is ``enriched in itself.''
\<close>

theory ClosedMonoidalCategory
imports MonoidalCategory.CartesianMonoidalCategory
begin

  section "Definition and Basic Facts"

  text \<open>
    As is pointed out in \<^cite>\<open>"nlab-internal-hom"\<close>,
    unless symmetry is assumed as part of the definition, there are in fact two notions
    of closed monoidal category: \emph{left}-closed monoidal category and
    \emph{right}-closed monoidal category.
    Here we define versions with and without symmetry, so that we can identify the places
    where symmetry is actually required.
  \<close>

  locale closed_monoidal_category =
    monoidal_category +
  assumes left_adjoint_tensor: "\<And>b. ide b \<Longrightarrow> left_adjoint_functor C C (\<lambda>x. x \<otimes> b)"

  locale closed_symmetric_monoidal_category =
    closed_monoidal_category +
    symmetric_monoidal_category

  text\<open>
    Similarly to what we have done in previous work, besides the definition of
    @{locale closed_monoidal_category}, which adds an assumed property to
    @{locale monoidal_category} but not any additional structure, we find it convenient
    also to define \<open>elementary_closed_monoidal_category\<close>, which assumes particular
    exponential structure to have been chosen, and uses this given structure to express
    the properties of a closed monoidal category in a more elementary way.
  \<close>

  locale elementary_closed_monoidal_category =
    monoidal_category +
  fixes exp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and eval :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and Curry :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes eval_in_hom_ax: "\<lbrakk> ide b; ide c \<rbrakk> \<Longrightarrow> \<guillemotleft>eval b c : exp b c \<otimes> b \<rightarrow> c\<guillemotright>"
  and ide_exp [intro, simp]: "\<lbrakk> ide b; ide c \<rbrakk> \<Longrightarrow> ide (exp b c)"
  and Curry_in_hom_ax: "\<lbrakk> ide a; ide b; ide c; \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright> \<rbrakk>
                          \<Longrightarrow> \<guillemotleft>Curry a b c g : a \<rightarrow> exp b c\<guillemotright>"
  and Uncurry_Curry: "\<lbrakk> ide a; ide b; ide c; \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright> \<rbrakk>
                          \<Longrightarrow> eval b c \<cdot> (Curry a b c g \<otimes> b) = g"
  and Curry_Uncurry: "\<lbrakk> ide a; ide b; ide c; \<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright> \<rbrakk>
                          \<Longrightarrow> Curry a b c (eval b c \<cdot> (h \<otimes> b)) = h"

  locale elementary_closed_symmetric_monoidal_category =
    symmetric_monoidal_category +
    elementary_closed_monoidal_category
  begin

    sublocale elementary_symmetric_monoidal_category
                C tensor \<I> lunit runit assoc sym
      using induces_elementary_symmetric_monoidal_category\<^sub>C\<^sub>M\<^sub>C by blast

  end

  text\<open>
    We now show that, except for the fact that a particular choice of structure has been made,
    closed monoidal categories and elementary closed monoidal categories amount to the
    same thing.
  \<close>

  subsection "An ECMC is a CMC"

  context elementary_closed_monoidal_category
  begin

    notation Curry  ("Curry[_, _, _]")

    abbreviation Uncurry  ("Uncurry[_, _]")
    where "Uncurry[b, c] f \<equiv> eval b c \<cdot> (f \<otimes> b)"

    lemma Curry_in_hom [intro]:
    assumes "ide a" and "ide b" and "\<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>" and "y = exp b c"
    shows "\<guillemotleft>Curry[a, b, c] g : a \<rightarrow> y\<guillemotright>"
      using assms Curry_in_hom_ax [of a b c g] by fastforce

    lemma Curry_simps [simp]:
    assumes "ide a" and "ide b" and "\<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "arr (Curry[a, b, c] g)"
    and "dom (Curry[a, b, c] g) = a"
    and "cod (Curry[a, b, c] g) = exp b c"
      using assms Curry_in_hom by blast+

    lemma eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C [intro]:
    assumes "ide b" and "ide c" and "x = exp b c \<otimes> b"
    shows "\<guillemotleft>eval b c : x \<rightarrow> c\<guillemotright>"
      using assms eval_in_hom_ax by blast

    lemma eval_simps [simp]:
    assumes "ide b" and "ide c"
    shows "arr (eval b c)" and "dom (eval b c) = exp b c \<otimes> b" and "cod (eval b c) = c"
      using assms eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C by blast+

    lemma Uncurry_in_hom [intro]:
    assumes "ide b" and "ide c" and "\<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright>" and "x = a \<otimes> b"
    shows "\<guillemotleft>Uncurry[b, c] f : x \<rightarrow> c\<guillemotright>"
      using assms by auto

    lemma Uncurry_simps [simp]:
    assumes "ide b" and "ide c" and "\<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright>"
    shows "arr (Uncurry[b, c] f)"
    and "dom (Uncurry[b, c] f) = a \<otimes> b"
    and "cod (Uncurry[b, c] f) = c"
      using assms Uncurry_in_hom by blast+

    lemma Uncurry_exp:
    assumes "ide a" and "ide b"
    shows "Uncurry[a, b] (exp a b) = eval a b"
      using assms
      by (metis comp_arr_dom eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C in_homE)

    lemma comp_Curry_arr:
    assumes "ide b" and "\<guillemotleft>f : x \<rightarrow> a\<guillemotright>" and "\<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "Curry[a, b, c] g \<cdot> f = Curry[x, b, c] (g \<cdot> (f \<otimes> b))"
    proof -
      have a: "ide a" and c: "ide c" and x: "ide x"
        using assms(2-3) by auto
      have "Curry[a, b, c] g \<cdot> f =
            Curry[x, b, c] (Uncurry[b, c] (Curry[a, b, c] g \<cdot> f))"
        using assms(1-3) a c x Curry_Uncurry comp_in_homI Curry_in_hom
        by presburger
      also have "... = Curry[x, b, c] (eval b c \<cdot> (Curry[a, b, c] g \<otimes> b) \<cdot> (f \<otimes> b))"
        using assms a c interchange
        by (metis comp_ide_self Curry_in_hom ideD(1) seqI')
      also have "... = Curry[x, b, c] (Uncurry[b, c] (Curry[a, b, c] g) \<cdot> (f \<otimes> b))"
        using comp_assoc by simp
      also have "... = Curry[x, b, c] (g \<cdot> (f \<otimes> b))"
        using a c assms(1,3) Uncurry_Curry by simp
      finally show ?thesis by blast
    qed

    lemma terminal_arrow_from_functor_eval:
    assumes "ide b" and "ide c"
    shows "terminal_arrow_from_functor C C (\<lambda>x. T (x, b)) (exp b c) c (eval b c)"
    proof -
      interpret "functor" C C \<open>\<lambda>x. T (x, b)\<close>
        using assms(1) interchange T.is_extensional
        by unfold_locales auto
      interpret arrow_from_functor C C \<open>\<lambda>x. T (x, b)\<close> \<open>exp b c\<close> c \<open>eval b c\<close>
        using assms eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
        by unfold_locales auto
      show ?thesis
      proof
        show "\<And>a f. arrow_from_functor C C (\<lambda>x. T (x, b)) a c f \<Longrightarrow>
                      \<exists>!g. arrow_from_functor.is_coext C C
                             (\<lambda>x. T (x, b)) (exp b c) (eval b c) a f g"
        proof -
          fix a f
          assume f: "arrow_from_functor C C (\<lambda>x. T (x, b)) a c f"
          interpret f: arrow_from_functor C C \<open>\<lambda>x. T (x, b)\<close> a c f
            using f by simp
          show "\<exists>!g. is_coext a f g"
          proof
            have a: "ide a"
              using f.arrow by simp
            show "is_coext a f (Curry[a, b, c] f)"
              unfolding is_coext_def
              using assms a Curry_in_hom Uncurry_Curry f.arrow by force
            show "\<And>g. is_coext a f g \<Longrightarrow> g = Curry[a, b, c] f"
              unfolding is_coext_def
              using assms a Curry_Uncurry f.arrow arrI by force
          qed
        qed
      qed
    qed

    lemma is_closed_monoidal_category:
    shows "closed_monoidal_category C T \<alpha> \<iota>"
      using T.is_extensional interchange terminal_arrow_from_functor_eval
      apply unfold_locales
           apply auto[5]
      by metis

    lemma retraction_eval_ide_self:
    assumes "ide a"
    shows "retraction (eval a a)"
      by (metis Uncurry_Curry assms comp_lunit_lunit'(1) ide_unity comp_assoc
          lunit_in_hom retractionI)

  end

  context elementary_closed_symmetric_monoidal_category
  begin

    lemma is_closed_symmetric_monoidal_category:
    shows "closed_symmetric_monoidal_category C T \<alpha> \<iota> \<sigma>"
      by (simp add: closed_symmetric_monoidal_category.intro
          is_closed_monoidal_category symmetric_monoidal_category_axioms)

  end

  subsection "A CMC Extends to an ECMC"

  context closed_monoidal_category
  begin

    (*
     * TODO: Currently there is a definition of "has_as_exponential", with related facts,
     * in CartesianCategory.  Since that definition actually makes sense more generally
     * for monoidal categories, it should be moved there, or perhaps to the present theory.
     * Then the statements of the following fact and definitions should be simplified.
     *
     * Also, a certain amount of the material below is currently replicated in
     * CartesianClosedCategory.  I don't really want CartesianClosedCategory to depend on
     * the present theory, though.  At the moment I am not sure what would be the best
     * way to remove the duplication consistent with this constraint.
     *)

    lemma has_exponentials:
    assumes "ide b" and "ide c"
    shows "\<exists>x e. ide x \<and> \<guillemotleft>e : x \<otimes> b \<rightarrow> c\<guillemotright> \<and>
                 (\<forall>a g. ide a \<and>
                        \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright> \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = e \<cdot> (f \<otimes> b)))"
    proof -
      interpret F: left_adjoint_functor C C \<open>\<lambda>x. x \<otimes> b\<close>
        using assms(1) left_adjoint_tensor by simp
      obtain x e where e: "terminal_arrow_from_functor C C (\<lambda>x. x \<otimes> b) x c e"
        using assms F.ex_terminal_arrow [of c] by auto
      interpret e: terminal_arrow_from_functor C C \<open>\<lambda>x. x \<otimes> b\<close> x c e
        using e by simp
      have "\<And>a g. \<lbrakk> ide a; \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright> \<rbrakk>
                      \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = e \<cdot> (f \<otimes> b)"
        using e.is_terminal category_axioms F.functor_axioms
        unfolding e.is_coext_def arrow_from_functor_def
                  arrow_from_functor_axioms_def
        by simp
      thus ?thesis
        using e.arrow by metis
    qed

    definition some_exp  ("exp\<^sup>?")
    where "exp\<^sup>? b c \<equiv> SOME x. ide x \<and>
                                (\<exists>e. \<guillemotleft>e : x \<otimes> b \<rightarrow> c\<guillemotright> \<and>
                                  (\<forall>a g. ide a \<and> \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>
                                          \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = e \<cdot> (f \<otimes> b))))"

    definition some_eval  ("eval\<^sup>?")
    where "eval\<^sup>? b c \<equiv> SOME e. \<guillemotleft>e : exp\<^sup>? b c \<otimes> b \<rightarrow> c\<guillemotright> \<and>
                                 (\<forall>a g. ide a \<and> \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>
                                          \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> g = e \<cdot> (f \<otimes> b)))"

    definition some_Curry  ("Curry\<^sup>?[_, _, _]")
    where "Curry\<^sup>?[a, b, c] g \<equiv>
           THE f. \<guillemotleft>f : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> g = eval\<^sup>? b c \<cdot> (f \<otimes> b)"

    abbreviation some_Uncurry  ("Uncurry\<^sup>?[_, _]")
    where "Uncurry\<^sup>?[b, c] f \<equiv> eval\<^sup>? b c \<cdot> (f \<otimes> b)"

    lemma Curry_uniqueness:
    assumes "ide b" and "ide c"
    shows "ide (exp\<^sup>? b c)" and "\<guillemotleft>eval\<^sup>? b c : exp\<^sup>? b c \<otimes> b \<rightarrow> c\<guillemotright>"
    and "\<lbrakk> ide a; \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright> \<rbrakk>
             \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> g = Uncurry\<^sup>?[b, c] f"
      using assms some_exp_def some_eval_def has_exponentials
            someI_ex [of "\<lambda>x. ide x \<and> (\<exists>e. \<guillemotleft>e : x \<otimes> b \<rightarrow> c\<guillemotright> \<and>
                                           (\<forall>a g. ide a \<and> \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>
                                              \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = e \<cdot> (f \<otimes> b))))"]
            someI_ex [of "\<lambda>e. \<guillemotleft>e : exp\<^sup>? b c \<otimes> b \<rightarrow> c\<guillemotright> \<and>
                              (\<forall>a g. ide a \<and> \<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>
                                           \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> g = e \<cdot> (f \<otimes> b)))"]
      by auto

    lemma some_eval_in_hom [intro]:
    assumes "ide b" and "ide c" and "x = exp\<^sup>? b c \<otimes> b"
    shows "\<guillemotleft>eval\<^sup>? b c : x \<rightarrow> c\<guillemotright>"
      using assms Curry_uniqueness by simp

    lemma some_Uncurry_some_Curry:
    assumes "ide a" and "ide b" and "\<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>Curry\<^sup>?[a, b, c] g : a \<rightarrow> exp\<^sup>? b c\<guillemotright>"
    and "Uncurry\<^sup>?[b, c] (Curry\<^sup>?[a, b, c] g) = g"
    proof -
      have "ide c"
        using assms(3) by auto
      hence 1: "\<guillemotleft>Curry\<^sup>?[a, b, c] g : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and>
                g = Uncurry\<^sup>?[b, c] (Curry\<^sup>?[a, b, c] g)"
        using assms some_Curry_def Curry_uniqueness
              theI' [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> g = Uncurry\<^sup>?[b, c] f"]
        by simp
      show "\<guillemotleft>Curry\<^sup>?[a, b, c] g : a \<rightarrow> exp\<^sup>? b c\<guillemotright>"
        using 1 by simp
      show "Uncurry\<^sup>?[b, c] (Curry\<^sup>?[a, b, c] g) = g"
        using 1 by simp
    qed

    lemma some_Curry_some_Uncurry:
    assumes "ide b" and "ide c" and "\<guillemotleft>h : a \<rightarrow> exp\<^sup>? b c\<guillemotright>"
    shows "Curry\<^sup>?[a, b, c] (Uncurry\<^sup>?[b, c] h) = h"
    proof -
      have "\<exists>!f. \<guillemotleft>f : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> Uncurry\<^sup>?[b, c] h = Uncurry\<^sup>?[b, c] f"
        using assms ide_dom ide_in_hom
              Curry_uniqueness(3) [of b c a "Uncurry\<^sup>?[b, c] h"]
        by auto
      moreover have "\<guillemotleft>h : a \<rightarrow> exp\<^sup>? b c\<guillemotright> \<and> Uncurry\<^sup>?[b, c] h = Uncurry\<^sup>?[b, c] h"
        using assms by simp
      ultimately show ?thesis
        using assms some_Curry_def Curry_uniqueness some_Uncurry_some_Curry
              the1_equality [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> some_exp b c\<guillemotright> \<and>
                                     Uncurry\<^sup>?[b, c] h = Uncurry\<^sup>?[b, c] f"]
        by simp
    qed

    lemma extends_to_elementary_closed_monoidal_category\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_closed_monoidal_category
             C T \<alpha> \<iota> some_exp some_eval some_Curry"
      using Curry_uniqueness some_Uncurry_some_Curry
            some_Curry_some_Uncurry
      by unfold_locales auto

  end

  context closed_symmetric_monoidal_category
  begin

    lemma extends_to_elementary_closed_symmetric_monoidal_category\<^sub>C\<^sub>M\<^sub>C:
    shows "elementary_closed_symmetric_monoidal_category
             C T \<alpha> \<iota> \<sigma> some_exp some_eval some_Curry"
      by (simp add: elementary_closed_symmetric_monoidal_category_def
          extends_to_elementary_closed_monoidal_category\<^sub>C\<^sub>M\<^sub>C
          symmetric_monoidal_category_axioms)

  end

  section "Internal Hom Functors"

  text \<open>
    For each object \<open>x\<close> of a closed monoidal category \<open>C\<close>, we can define a covariant
    endofunctor \<open>Exp\<^sup>\<rightarrow> x -\<close> of \<open>C\<close>, which takes each arrow \<open>g\<close> to an arrow
    \<open>\<guillemotleft>Exp\<^sup>\<rightarrow> x g : exp x (dom g) \<rightarrow> exp x (cod g)\<guillemotright>\<close>.  Similarly, for each object \<open>y\<close>,
    we can define a contravariant endofunctor \<open>Exp\<^sup>\<leftarrow> - y\<close> of \<open>C\<close>, which takes each arrow
    \<open>f\<close> of \<open>C\<^sup>o\<^sup>p\<close> to an arrow \<open>\<guillemotleft>Exp\<^sup>\<leftarrow> f y : exp (cod f) y \<rightarrow> exp (dom f) y\<guillemotright>\<close> of \<open>C\<close>.
    These two endofunctors commute with each other and compose to form a single binary
    ``internal hom'' functor \<open>Exp\<close> from \<open>C\<^sup>o\<^sup>p \<times> C\<close> to \<open>C\<close>.
  \<close>

  context elementary_closed_monoidal_category
  begin

    abbreviation cov_Exp  ("Exp\<^sup>\<rightarrow>")
    where "Exp\<^sup>\<rightarrow> x g \<equiv> if arr g
                       then Curry[exp x (dom g), x, cod g] (g \<cdot> eval x (dom g))
                       else null"

    abbreviation cnt_Exp  ("Exp\<^sup>\<leftarrow>")
    where "Exp\<^sup>\<leftarrow> f y \<equiv> if arr f
                       then Curry[exp (cod f) y, dom f, y]
                              (eval (cod f) y \<cdot> (exp (cod f) y \<otimes> f))
                       else null"

    lemma cov_Exp_in_hom:
    assumes "ide x" and "arr g"
    shows "\<guillemotleft>Exp\<^sup>\<rightarrow> x g : exp x (dom g) \<rightarrow> exp x (cod g)\<guillemotright>"
      using assms by auto

    lemma cnt_Exp_in_hom:
    assumes "arr f" and "ide y"
    shows "\<guillemotleft>Exp\<^sup>\<leftarrow> f y : exp (cod f) y \<rightarrow> exp (dom f) y\<guillemotright>"
      using assms by force

    lemma cov_Exp_ide:
    assumes "ide a" and "ide b"
    shows "Exp\<^sup>\<rightarrow> a b = exp a b"
      using assms
      by (metis comp_ide_arr Curry_Uncurry eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C ideD(2-3) ide_exp
          ide_in_hom seqI' Uncurry_exp)

    lemma cnt_Exp_ide:
    assumes "ide a" and "ide b"
    shows "Exp\<^sup>\<leftarrow> a b = exp a b"
      using assms Curry_Uncurry ide_exp ide_in_hom by force

    lemma cov_Exp_comp:
    assumes "ide x" and "seq g f"
    shows "Exp\<^sup>\<rightarrow> x (g \<cdot> f) = Exp\<^sup>\<rightarrow> x g \<cdot> Exp\<^sup>\<rightarrow> x f"
    proof -
      have "Exp\<^sup>\<rightarrow> x g \<cdot> Exp\<^sup>\<rightarrow> x f =
            Curry[exp x (cod f), x, cod g] (g \<cdot> eval x (cod f)) \<cdot>
              Curry[exp x (dom f), x, cod f] (f \<cdot> eval x (dom f))"
        using assms by auto
      also have "... = Curry[exp x (dom f), x, cod g]
                         ((g \<cdot> eval x (dom g)) \<cdot>
                            (Curry[exp x (dom f), x, cod f] (f \<cdot> eval x (dom f)) \<otimes> x))"
        using assms cov_Exp_in_hom comp_Curry_arr by auto
      also have "... = Exp\<^sup>\<rightarrow> x (g \<cdot> f)"
        using assms Uncurry_Curry comp_assoc by fastforce
      finally show ?thesis by simp
    qed

    lemma cnt_Exp_comp:
    assumes "seq g f" and "ide y"
    shows "Exp\<^sup>\<leftarrow> (g \<cdot> f) y = Exp\<^sup>\<leftarrow> f y \<cdot> Exp\<^sup>\<leftarrow> g y"
    proof -
      have "Exp\<^sup>\<leftarrow> f y \<cdot> Exp\<^sup>\<leftarrow> g y =
            Curry[exp (cod g) y, dom f, y]
              ((eval (cod f) y \<cdot> (exp (cod f) y \<otimes> f)) \<cdot>
                  (Curry[exp (cod g) y, cod f, y]
                     (eval (cod g) y \<cdot> (exp (cod g) y \<otimes> g)) \<otimes> dom f))"
        using assms
              comp_Curry_arr
                [of "dom f" "Curry[exp (cod g) y, cod f, y]
                               (eval (cod g) y \<cdot> (exp (cod g) y \<otimes> g))"]
        by fastforce
      also have "... = Curry[exp (cod g) y, dom f, y]
                         ((Uncurry[cod f, y]
                             (Curry[exp (cod g) y, cod f, y]
                                      (eval (cod g) y \<cdot> (exp (cod g) y \<otimes> g)))) \<cdot>
                             (exp (cod g) y \<otimes> f))"
        using assms interchange comp_arr_dom comp_cod_arr comp_assoc by auto
      also have "... = Curry[exp (cod g) y, dom f, y]
                         ((eval (cod g) y \<cdot> (exp (cod g) y \<otimes> g)) \<cdot> (exp (cod g) y \<otimes> f))"
        using assms Uncurry_Curry by auto
      also have "... = Exp\<^sup>\<leftarrow> (g \<cdot> f) y"
        using assms interchange comp_assoc by auto
      finally show ?thesis by simp
    qed

    lemma functor_cov_Exp:
    assumes "ide x"
    shows "functor C C (Exp\<^sup>\<rightarrow> x)"
      using assms cov_Exp_ide cov_Exp_in_hom cov_Exp_comp
      by unfold_locales auto

    interpretation Cop: dual_category C ..

    lemma functor_cnt_Exp:
    assumes "ide x"
    shows "functor Cop.comp C (\<lambda>f. Exp\<^sup>\<leftarrow> f x)"
      using assms cnt_Exp_ide cnt_Exp_in_hom cnt_Exp_comp
      by unfold_locales auto

    lemma cov_cnt_Exp_commute:
    assumes "arr f" and "arr g"
    shows "Exp\<^sup>\<rightarrow> (dom f) g \<cdot> Exp\<^sup>\<leftarrow> f (dom g) =
           Exp\<^sup>\<leftarrow> f (cod g) \<cdot> Exp\<^sup>\<rightarrow> (cod f) g"
    proof -
      have "Exp\<^sup>\<rightarrow> (dom f) g \<cdot> Exp\<^sup>\<leftarrow> f (dom g) =
            Curry[exp (cod f) (dom g), dom f, cod g]
              ((g \<cdot> eval (dom f) (dom g)) \<cdot>
                  (Curry[exp (cod f) (dom g), dom f, dom g]
                     (eval (cod f) (dom g) \<cdot> (exp (cod f) (dom g) \<otimes> f)) \<otimes> dom f))"
        using assms cnt_Exp_in_hom comp_Curry_arr by force
      also have "... = Curry[exp (cod f) (dom g), dom f, cod g]
                         (Uncurry[cod f, cod g] (Exp\<^sup>\<rightarrow> (cod f) g) \<cdot>
                            (exp (cod f) (dom g) \<otimes> f))"
        using assms comp_assoc Uncurry_Curry by auto
      also have "... = Curry[exp (cod f) (dom g), dom f, cod g]
                         (eval (cod f) (cod g) \<cdot> (Exp\<^sup>\<rightarrow> (cod f) g \<otimes> cod f) \<cdot>
                            (exp (cod f) (dom g) \<otimes> f))"
        using comp_assoc by auto
      also have "... = Curry[exp (cod f) (dom g), dom f, cod g]
                         (eval (cod f) (cod g) \<cdot> (Exp\<^sup>\<rightarrow> (cod f) g \<otimes> f))"
        using assms interchange comp_arr_dom comp_cod_arr
        by (metis cov_Exp_in_hom ide_cod in_homE)
      also have "... = Curry[exp (cod f) (dom g), dom f, cod g]
                         (eval (cod f) (cod g) \<cdot>
                            (exp (cod f) (cod g) \<otimes> f) \<cdot> (Exp\<^sup>\<rightarrow> (cod f) g \<otimes> dom f))"
        using assms interchange comp_arr_dom comp_cod_arr cov_Exp_in_hom
        by auto
      also have "... = Exp\<^sup>\<leftarrow> f (cod g) \<cdot> Exp\<^sup>\<rightarrow> (cod f) g"
        using assms cov_Exp_in_hom comp_assoc
              comp_Curry_arr
                [of "dom f" "Exp\<^sup>\<rightarrow> (cod f) g" "exp (cod f) (dom g)" _
                    "eval (cod f) (cod g) \<cdot> (exp (cod f) (cod g) \<otimes> f)" "cod g"]
        by simp
      finally show ?thesis by simp
    qed

    definition Exp
    where "Exp f g \<equiv> Exp\<^sup>\<rightarrow> (dom f) g \<cdot> Exp\<^sup>\<leftarrow> f (dom g)"

    lemma Exp_in_hom:
    assumes "arr f" and "arr g"
    shows "\<guillemotleft>Exp f g : Exp (cod f) (dom g) \<rightarrow> Exp (dom f) (cod g)\<guillemotright>"
      using Exp_def assms(1-2) cnt_Exp_ide cov_Exp_ide by auto

    lemma Exp_ide:
    assumes "ide a" and "ide b"
    shows "Exp a b = exp a b"
      unfolding Exp_def
      using assms cov_Exp_ide cnt_Exp_ide by simp

    lemma Exp_comp:
    assumes "seq g f" and "seq k h"
    shows "Exp (g \<cdot> f) (k \<cdot> h) = Exp f k \<cdot> Exp g h"
    proof -
      have "Exp (g \<cdot> f) (k \<cdot> h) = Exp\<^sup>\<rightarrow> (dom f) (k \<cdot> h) \<cdot> Exp\<^sup>\<leftarrow> (g \<cdot> f) (dom h)"
        unfolding Exp_def
        using assms by auto
      also have "... = (Exp\<^sup>\<rightarrow> (dom f) k \<cdot> Exp\<^sup>\<rightarrow> (dom f) h) \<cdot>
                         (Exp\<^sup>\<leftarrow> f (dom h) \<cdot> Exp\<^sup>\<leftarrow> g (dom h))"
        using assms cov_Exp_comp cnt_Exp_comp by auto
      also have "... = (Exp\<^sup>\<rightarrow> (dom f) k \<cdot> Exp\<^sup>\<leftarrow> f (dom k)) \<cdot>
                         (Exp\<^sup>\<rightarrow> (dom g) h \<cdot> Exp\<^sup>\<leftarrow> g (dom h))"
        using assms comp_assoc cov_cnt_Exp_commute
        by (metis (no_types, lifting) seqE)
      also have "... = Exp f k \<cdot> Exp g h"
        unfolding Exp_def by blast
      finally show ?thesis by blast
    qed

    interpretation CopxC: product_category Cop.comp C ..

    lemma functor_Exp:
    shows "binary_functor Cop.comp C C (\<lambda>fg. Exp (fst fg) (snd fg))"
      using Exp_in_hom
      apply unfold_locales
          apply auto[4]
      using Exp_def
        apply auto[2]
      using Exp_comp
      by fastforce

    lemma Exp_x_ide:
    assumes "ide y"
    shows "(\<lambda>x. Exp x y) = (\<lambda>x. Exp\<^sup>\<leftarrow> x y)"
      using assms Exp_ide Exp_def comp_cod_arr cov_Exp_ide by auto

    lemma Exp_ide_y:
    assumes "ide x"
    shows "(\<lambda>y. Exp x y) = (\<lambda>y. Exp\<^sup>\<rightarrow> x y)"
      using assms Exp_ide Exp_def comp_arr_dom cnt_Exp_ide by auto

    lemma Uncurry_Exp_dom:
    assumes "arr f"
    shows "Uncurry (dom f) (cod f) (Exp (dom f) f) = f \<cdot> eval (dom f) (dom f)"
    proof -
      have "Uncurry[dom f, cod f] (Exp (dom f) f) =
            Uncurry[dom f, cod f]
              (Curry[exp (dom f) (dom f), dom f, cod f] (f \<cdot> eval (dom f) (dom f)) \<cdot>
                 Curry[exp (dom f) (dom f), dom f, dom f] (eval (dom f) (dom f)))"
        unfolding Exp_def
        using assms Curry_Uncurry comp_arr_dom by simp
      also have "... = Uncurry[dom f, cod f]
                         (Curry[exp (dom f) (dom f), dom f, cod f]
                            ((f \<cdot> eval (dom f) (dom f)) \<cdot>
                                (Curry[exp (dom f) (dom f), dom f, dom f]
                                   (eval (dom f) (dom f)) \<otimes> dom f)))"
        using assms comp_Curry_arr
        by (metis comp_in_homI' Curry_in_hom eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C ide_dom
            ide_exp in_homE)
      also have "... = f \<cdot> eval (dom f) (dom f)"
        using assms Uncurry_Curry eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C comp_assoc by simp
      finally show ?thesis by simp
    qed

  subsection "Exponentiation by Unity"

    text\<open>
      In this section we define and develop the properties of inverse arrows
      \<open>Up a : a \<rightarrow> exp \<I> a\<close> and \<open>Dn a : exp \<I> a \<rightarrow> a\<close>, which exist in any closed monoidal
      category.
    \<close>

    (*
     * TODO: There are apparently some useful theorems in this that are not otherwise accessible,
     * but probably should be.
     *)
    interpretation elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by blast

    abbreviation Up
    where "Up a \<equiv> Curry[a, \<I>, a] \<r>[a]"

    abbreviation Dn
    where "Dn a \<equiv> eval \<I> a \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> a]"

    lemma isomorphic_exp_unity:
    assumes "ide a"
    shows "\<guillemotleft>Up a : a \<rightarrow> exp \<I> a\<guillemotright>"
    and "\<guillemotleft>Dn a : exp \<I> a \<rightarrow> a\<guillemotright>"
    and "inverse_arrows (Up a) (Dn a)"
    and "isomorphic (exp \<I> a) a"
    proof -
      show 1: "\<guillemotleft>Up a : a \<rightarrow> exp \<I> a\<guillemotright>"
        using assms ide_unity Curry_in_hom by blast
      show 2: "\<guillemotleft>Dn a : exp \<I> a \<rightarrow> a\<guillemotright>"
        using assms eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C [of \<I> a] runit_in_hom ide_unity by blast
      show "inverse_arrows (Up a) (Dn a)"
      proof
        show "ide ((Dn a) \<cdot> Up a)"
          by (metis (no_types, lifting) \<open>\<guillemotleft>Up a : a \<rightarrow> exp \<I> a\<guillemotright>\<close>
              assms comp_runit_runit'(1) ide_unity in_homE comp_assoc 
              runit'_naturality runit_in_hom Uncurry_Curry)
        show "ide (Up a \<cdot> Dn a)"
        proof -
          have "Up a \<cdot> Dn a = (Curry[a, \<I>, a] \<r>[a] \<cdot> eval \<I> a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> a]"
            using comp_assoc by simp
          also have "... =
                     Curry[exp \<I> a \<otimes> \<I>, \<I>, a] (\<r>[a] \<cdot> (eval \<I> a \<otimes> \<I>)) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> a]"
            using assms comp_Curry_arr
            by (metis eval_in_hom_ax ide_unity runit_in_hom)
          also have "... =
                     Curry[exp \<I> a \<otimes> \<I>, \<I>, a] (eval \<I> a \<cdot> \<r>[exp \<I> a \<otimes> \<I>]) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> a]"
            using assms runit_naturality
            by (metis (no_types, lifting) eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C ide_unity in_homE)
          also have "... = (Curry[exp \<I> a, \<I>, a] (eval \<I> a) \<cdot> \<r>[exp \<I> a]) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> a]"
            by (metis assms comp_Curry_arr eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C ide_exp ide_unity
                runit_commutes_with_R runit_in_hom)
          also have "... = Curry[exp \<I> a, \<I>, a] (eval \<I> a) \<cdot> \<r>[exp \<I> a] \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> a]"
            using comp_assoc by simp
          also have "... = Curry[exp \<I> a, \<I>, a] (eval \<I> a)"
            by (metis assms 1 2 calculation comp_arr_ide comp_runit_runit'(1)
                ide_exp ide_unity seqI')
          also have "... = exp \<I> a"
            using assms Curry_Uncurry
            by (metis ide_exp ide_in_hom ide_unity Uncurry_exp)
          finally show ?thesis
            using assms ide_exp ide_unity by presburger
        qed
      qed
      thus "isomorphic (exp \<I> a) a"
        by (metis \<open>\<guillemotleft>Up a : a \<rightarrow> exp \<I> a\<guillemotright>\<close> in_homE isoI isomorphicI
            isomorphic_symmetric)
    qed

    text\<open>
      The maps \<open>Up\<close> and \<open>Dn\<close> are natural in a.
    \<close>

    lemma Up_Dn_naturality:
    assumes "arr f"
    shows "Exp\<^sup>\<rightarrow> \<I> f \<cdot> Up (dom f) = Up (cod f) \<cdot> f"
    and "Dn (cod f) \<cdot> Exp\<^sup>\<rightarrow> \<I> f = f \<cdot> Dn (dom f)"
    proof -
      show 1: "Exp\<^sup>\<rightarrow> \<I> f \<cdot> Up (dom f) = Up (cod f) \<cdot> f"
      proof -
        have "Exp\<^sup>\<rightarrow> \<I> f \<cdot> Up (dom f) =
              Curry[dom f, \<I>, cod f]
                ((f \<cdot> eval \<I> (dom f)) \<cdot> (Curry[dom f, \<I>, dom f] \<r>[dom f] \<otimes> \<I>))"
          using assms comp_Curry_arr isomorphic_exp_unity(1) by auto
        also have "... = Curry[dom f, \<I>, cod f] (\<r>[cod f] \<cdot> (f \<otimes> \<I>))"
          using assms comp_assoc Uncurry_Curry runit_naturality by simp
        also have "... = Up (cod f) \<cdot> f"
          by (metis assms comp_Curry_arr ide_cod ide_unity in_homI runit_in_hom)
        finally show ?thesis by blast
      qed
      have "Exp\<^sup>\<rightarrow> \<I> f \<cdot> inv (Dn (dom f)) = inv (Dn (cod f)) \<cdot> f"
        using assms 1 isomorphic_exp_unity isomorphic_exp_unity
        by (metis ide_cod ide_dom inverse_arrows_sym inverse_unique)
      moreover have 2: "iso (Dn (cod f))"
        using assms isomorphic_exp_unity [of "cod f"] by auto
      moreover have 3: "iso (Dn (dom f))"
        using assms isomorphic_exp_unity [of "dom f"] by auto
      moreover have "seq (inv (Dn (cod f))) f"
        using assms 2 by auto
      ultimately show "Dn (cod f) \<cdot> Exp\<^sup>\<rightarrow> \<I> f = f \<cdot> Dn (dom f)"
        using assms 2 3 inv_inv iso_inv_iso comp_assoc isomorphic_exp_unity
              invert_opposite_sides_of_square
                [of "inv (eval \<I> (cod f) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (cod f)])" f "Exp\<^sup>\<rightarrow> \<I> f"
                    "inv (eval \<I> (dom f) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (dom f)])"]
        by metis
    qed

  subsection "Internal Currying"

    text \<open>
      Currying internalizes to an isomorphism between \<open>exp (x \<otimes> a) b\<close> and \<open>exp x (exp a b)\<close>.
    \<close>

    abbreviation curry
    where "curry x b c \<equiv>
           Curry[exp (x \<otimes> b) c, x, exp b c]
             (Curry[exp (x \<otimes> b) c \<otimes> x, b, c]
                (eval (x \<otimes> b) c \<cdot> \<a>[exp (x \<otimes> b) c, x, b]))"

    abbreviation uncurry
    where "uncurry x b c \<equiv>
           Curry[exp x (exp b c), x \<otimes> b, c]
             (eval b c \<cdot> (eval x (exp b c) \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[exp x (exp b c), x, b])"

    lemma internal_curry:
    assumes "ide x" and "ide a" and "ide b"
    shows "\<guillemotleft>curry x a b : exp (x \<otimes> a) b \<rightarrow> exp x (exp a b)\<guillemotright>"
    and "\<guillemotleft>uncurry x a b : exp x (exp a b) \<rightarrow> exp (x \<otimes> a) b\<guillemotright>"
    and "inverse_arrows (curry x a b) (uncurry x a b)"
    proof -
      show 1: "\<guillemotleft>curry x a b : exp (x \<otimes> a) b \<rightarrow> exp x (exp a b)\<guillemotright>"
        using assms
        by (meson assoc_in_hom comp_in_homI Curry_in_hom eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
            ide_exp tensor_preserves_ide)
      show 2: "\<guillemotleft>uncurry x a b : exp x (exp a b) \<rightarrow> exp (x \<otimes> a) b\<guillemotright>"
        using assms ide_exp by auto
      show "inverse_arrows (curry x a b) (uncurry x a b)"
        (is "inverse_arrows
               (Curry (exp (x \<otimes> a) b) x (exp a b)
                  (Curry (exp (x \<otimes> a) b \<otimes> x) a b ?F))
               (Curry (exp x (exp a b)) (x \<otimes> a) b ?G)")
      proof
        have F: "\<guillemotleft>?F : (exp (x \<otimes> a) b \<otimes> x) \<otimes> a \<rightarrow> b\<guillemotright>"
          using assms ide_exp by simp
        have G: "\<guillemotleft>?G : exp x (exp a b) \<otimes> x \<otimes> a \<rightarrow> b\<guillemotright>"
          using assms ide_exp by auto
        show "ide (uncurry x a b \<cdot> curry x a b)"
        proof -
          have "uncurry x a b \<cdot> curry x a b =
                Curry[exp (x \<otimes> a) b, x \<otimes> a, b] (?G \<cdot> (curry x a b \<otimes> x \<otimes> a))"
            using assms F 1 ide_exp comp_Curry_arr comp_assoc by auto
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b]
                             (eval a b \<cdot> (eval x (exp a b) \<otimes> a) \<cdot> \<a>\<^sup>-\<^sup>1[exp x (exp a b), x, a] \<cdot>
                               (curry x a b \<otimes> x \<otimes> a))"
            using comp_assoc by simp
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b]
                             (eval a b \<cdot> (eval x (exp a b) \<otimes> a) \<cdot>
                                ((curry x a b \<otimes> x) \<otimes> a) \<cdot> \<a>\<^sup>-\<^sup>1[exp (x \<otimes> a) b, x, a])"
            using assms 1 comp_assoc assoc'_naturality [of "curry x a b" x a]
                  ide_char in_homE
            by metis
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b]
                             (eval a b \<cdot> ((eval x (exp a b) \<otimes> a) \<cdot> ((curry x a b \<otimes> x) \<otimes> a)) \<cdot>
                                \<a>\<^sup>-\<^sup>1[exp (x \<otimes> a) b, x, a])"
            using comp_assoc by simp
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b]
                             (eval a b \<cdot> (Uncurry[x, exp a b] (curry x a b) \<otimes> a) \<cdot>
                                \<a>\<^sup>-\<^sup>1[exp (x \<otimes> a) b, x, a])"
            using assms comp_ide_self
                  interchange [of "eval x (exp a b)"
                                   "Curry[exp (x \<otimes> a) b, x, exp a b]
                                           (Curry[exp (x \<otimes> a) b \<otimes> x, a, b] ?F) \<otimes> x"
                                   a a]
            by fastforce
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b]
                             (eval a b \<cdot>
                                (Curry[exp (x \<otimes> a) b \<otimes> x, a, b] ?F \<otimes> a) \<cdot>
                                   \<a>\<^sup>-\<^sup>1[exp (x \<otimes> a) b, x, a])"
            using assms F ide_exp comp_assoc comp_ide_self
                  Uncurry_Curry
                    [of "exp (x \<otimes> a) b" x "exp a b" "Curry[exp (x \<otimes> a) b \<otimes> x, a, b] ?F"]
            by fastforce
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b]
                             (eval (x \<otimes> a) b \<cdot> \<a>[exp (x \<otimes> a) b, x, a] \<cdot>
                                \<a>\<^sup>-\<^sup>1[exp (x \<otimes> a) b, x, a])"
            using assms Uncurry_Curry
            by (metis F ide_exp comp_assoc tensor_preserves_ide)
          also have "... = Curry[exp (x \<otimes> a) b, x \<otimes> a, b] (eval (x \<otimes> a) b)"
            using assms Uncurry_exp by simp
          also have "... = exp (x \<otimes> a) b"
            using assms Curry_Uncurry
            by (metis Curry_Uncurry ide_exp ide_in_hom tensor_preserves_ide
                Uncurry_exp)
          finally have "uncurry x a b \<cdot> curry x a b = exp (x \<otimes> a) b"
            by blast
          thus ?thesis
            using assms by simp
        qed
        show "ide (curry x a b \<cdot> uncurry x a b)"
        proof -
          have "curry x a b \<cdot> uncurry x a b =
                Curry[exp x (exp a b), x, exp a b]
                  (Curry[exp (x \<otimes> a) b \<otimes> x, a, b] ?F \<cdot> (uncurry x a b \<otimes> x))"
            using assms 2 F Curry_in_hom comp_Curry_arr by simp
          also have "... = Curry[exp x (exp a b), x, exp a b]
                             (Curry[exp x (exp a b) \<otimes> x, a, b]
                                (eval (x \<otimes> a) b \<cdot> \<a>[exp (x \<otimes> a) b, x, a] \<cdot>
                                   ((uncurry x a b \<otimes> x) \<otimes> a)))"
          proof -
            have "Curry[exp (x \<otimes> a) b \<otimes> x, a, b] ?F \<cdot> (uncurry x a b \<otimes> x) =
                  Curry[exp x (exp a b) \<otimes> x, a, b] (?F \<cdot> ((uncurry x a b \<otimes> x) \<otimes> a))"
              using assms(1-2) 2 F comp_Curry_arr ide_in_hom by auto
            thus ?thesis
              using comp_assoc by simp
          qed
          also have "... = Curry[exp x (exp a b), x, exp a b]
                             (Curry[exp x (exp a b) \<otimes> x, a, b]
                                (eval (x \<otimes> a) b \<cdot>
                                   (uncurry x a b \<otimes> x \<otimes> a) \<cdot> \<a>[exp x (exp a b), x, a]))"
            using assms 2
              assoc_naturality [of "Curry (exp x (exp a b)) (x \<otimes> a) b ?G" x a]
            by auto
          also have "... = Curry[exp x (exp a b), x, exp a b]
                             (Curry[exp x (exp a b) \<otimes> x, a, b]
                                (eval a b \<cdot> (eval x (exp a b) \<otimes> a) \<cdot>
                                   \<a>\<^sup>-\<^sup>1[exp x (exp a b), x, a] \<cdot> \<a>[exp x (exp a b), x, a]))"
            using assms Uncurry_Curry
            by (metis G ide_exp comp_assoc tensor_preserves_ide)
          also have "... = Curry[exp x (exp a b), x, exp a b]
                             (Curry[exp x (exp a b) \<otimes> x, a, b]
                                (Uncurry[a, b] (eval x (exp a b))))"
            using assms
            by (metis G arrI cod_assoc' comp_arr_dom comp_assoc_assoc'(2)
                ide_exp seqE)
          also have "... = Curry[exp x (exp a b), x, exp a b] (eval x (exp a b))"
            by (simp add: assms(1-3) Curry_Uncurry eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C)
          also have "... = exp x (exp a b)"
            using assms Curry_Uncurry Uncurry_exp
            by (metis ide_exp ide_in_hom)
          finally have "curry x a b \<cdot> uncurry x a b = exp x (exp a b)"
            by blast
          thus ?thesis
            using assms by fastforce
        qed
      qed
    qed

    text \<open>
      Internal currying and uncurrying are the components of natural isomorphisms between
      the contravariant functors \<open>Exp\<^sup>\<leftarrow> (\<hyphen> \<otimes> b) c\<close> and \<open>Exp\<^sup>\<leftarrow> \<hyphen> (exp b c)\<close>.
    \<close>

    lemma uncurry_naturality:
    assumes "ide b" and "ide c" and "Cop.arr f"
    shows "uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c) =
           Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
             (eval (Cop.dom f \<otimes> b) c \<cdot> (uncurry (Cop.dom f) b c \<otimes> f \<otimes> b))"
    and "Exp\<^sup>\<leftarrow> (f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c =
         Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                (eval (Cop.dom f \<otimes> b) c \<cdot> (uncurry (Cop.dom f) b c \<otimes> f \<otimes> b))"
    and "uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c) =
         Exp\<^sup>\<leftarrow> (f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c"
    proof -
      interpret xb: "functor" Cop.comp Cop.comp \<open>\<lambda>x. x \<otimes> b\<close>
        using assms(1) T.fixing_ide_gives_functor_2 [of b]
        by (simp add: category_axioms dual_category.intro dual_functor.intro
            dual_functor.is_functor)
      interpret F: "functor" Cop.comp C \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)\<close>
        using assms functor_cnt_Exp by blast
      have *: "\<And>x. Cop.ide x \<Longrightarrow>
                      Uncurry (x \<otimes> b) c (uncurry x b c) =
                      eval b c \<cdot> (eval x (exp b c) \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[exp x (exp b c), x, b]"
        using assms Uncurry_Curry Cop.ide_char by auto
      show 1: "uncurry (Cop.cod f) b c \<cdot> cnt_Exp f (exp b c) =
               Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                 (eval (Cop.dom f \<otimes> b) c \<cdot> (uncurry (Cop.dom f) b c \<otimes> f \<otimes> b))"
      proof -
        have "uncurry (Cop.cod f) b c \<cdot> cnt_Exp f (exp b c) =
              Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                ((eval b c \<cdot>
                    (eval (Cop.cod f) (exp b c) \<otimes> b) \<cdot>
                       \<a>\<^sup>-\<^sup>1[exp (Cop.cod f) (exp b c), (Cop.cod f), b]) \<cdot>
                         (cnt_Exp f (exp b c) \<otimes> Cop.cod f \<otimes> b))"
          using assms ide_exp cnt_Exp_in_hom comp_Curry_arr by auto
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           ((eval b c \<cdot>
                               (eval (Cop.cod f) (exp b c) \<otimes> b) \<cdot>
                                 ((cnt_Exp f (exp b c) \<otimes> Cop.cod f) \<otimes> b)) \<cdot>
                              \<a>\<^sup>-\<^sup>1[exp (Cop.dom f) (exp b c), Cop.cod f, b])"
          using assms comp_assoc
                assoc'_naturality [of "cnt_Exp f (exp b c)" "Cop.cod f" b]
          by auto
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (Uncurry[b, c]
                              (Uncurry[Cop.cod f, exp b c]
                                 (Curry[exp (Cop.dom f) (exp b c), Cop.cod f, exp b c]
                                    (eval (Cop.dom f) (exp b c) \<cdot>
                                       (exp (Cop.dom f) (exp b c) \<otimes> f)))) \<cdot>
                           \<a>\<^sup>-\<^sup>1[exp (Cop.dom f) (exp b c), Cop.cod f, b])"
          using assms interchange by simp
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (eval b c \<cdot>
                              ((eval (Cop.dom f) (exp b c) \<cdot>
                                  (exp (Cop.dom f) (exp b c) \<otimes> f)) \<otimes> b) \<cdot>
                                  \<a>\<^sup>-\<^sup>1[exp (Cop.dom f) (exp b c), Cop.cod f, b])"
          using assms Uncurry_Curry comp_assoc by force
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (eval b c \<cdot>
                              ((eval (Cop.dom f) (exp b c) \<otimes> b) \<cdot>
                                  ((exp (Cop.dom f) (exp b c) \<otimes> f) \<otimes> b)) \<cdot>
                                \<a>\<^sup>-\<^sup>1[exp (Cop.dom f) (exp b c), Cop.cod f, b])"
          using assms interchange by simp
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           ((eval b c \<cdot> (eval (Cop.dom f) (exp b c) \<otimes> b) \<cdot>
                               \<a>\<^sup>-\<^sup>1[exp (Cop.dom f) (exp b c), cod f, b]) \<cdot>
                                 (exp (Cop.dom f) (exp b c) \<otimes> f \<otimes> b))"
          using assms assoc'_naturality [of "exp (Cop.dom f) (exp b c)" f b] comp_assoc
          by simp
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (Uncurry[Cop.dom f \<otimes> b, c]
                              (uncurry (Cop.dom f) b c) \<cdot>
                                 (exp (Cop.dom f) (exp b c) \<otimes> f \<otimes> b))"
          using assms * by simp
        also have "... =
              Curry (exp (Cop.dom f) (exp b c)) (Cop.cod f \<otimes> b) c
                     (eval (Cop.dom f \<otimes> b) c \<cdot>
                       (uncurry (Cop.dom f) b c \<otimes> (Cop.dom f \<otimes> b) \<cdot> (f \<otimes> b)))"
          using assms ide_exp internal_curry(2) interchange comp_assoc
                comp_arr_dom [of "uncurry (Cop.dom f) b c"]
          by auto
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (eval (Cop.dom f \<otimes> b) c \<cdot>
                              (uncurry (Cop.dom f) b c \<otimes> f \<otimes> b))"
          using assms(1,3) comp_cod_arr interchange by fastforce
        finally show ?thesis by blast
      qed
      show 2: "Exp\<^sup>\<leftarrow> (f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c = ..."
      proof -
        have "Exp\<^sup>\<leftarrow> (f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c =
              Curry[exp (Cop.dom f \<otimes> b) c, Cop.cod f \<otimes> b, c]
                (eval (Cop.dom f \<otimes> b) c \<cdot> (exp (Cop.dom f \<otimes> b) c \<otimes> f \<otimes> b)) \<cdot>
                   uncurry (Cop.dom f) b c"
          using assms comp_arr_dom by simp
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           ((eval (Cop.dom f \<otimes> b) c \<cdot>
                               (exp (Cop.dom f \<otimes> b) c \<otimes> f \<otimes> b)) \<cdot>
                               (uncurry (Cop.dom f) b c \<otimes> Cop.cod f \<otimes> b))"
          using assms Curry_in_hom comp_Curry_arr by force
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (eval (Cop.dom f \<otimes> b) c \<cdot>
                              (exp (Cop.dom f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c
                                 \<otimes> (f \<otimes> b) \<cdot> (Cop.cod f \<otimes> b)))"
        proof -
          have "seq (exp (Cop.dom f \<otimes> b) c) (uncurry (Cop.dom f) b c)"
            using assms by fastforce
          thus ?thesis
            using assms internal_curry comp_assoc interchange by simp
        qed
        also have "... = Curry[exp (Cop.dom f) (exp b c), Cop.cod f \<otimes> b, c]
                           (eval (Cop.dom f \<otimes> b) c \<cdot>
                             (uncurry (Cop.dom f) b c \<otimes> f \<otimes> b))"
        proof -
          have "(f \<otimes> b) \<cdot> (Cop.cod f \<otimes> b) = f \<otimes> b"
            using assms interchange comp_arr_dom comp_cod_arr by simp
          thus ?thesis
            using assms internal_curry comp_cod_arr [of "uncurry (Cop.dom f) b c"]
            by simp
        qed
        finally show ?thesis by simp
      qed
      show "uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c) =
            Exp\<^sup>\<leftarrow> (f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c"
        using 1 2 by simp
    qed

    lemma natural_isomorphism_uncurry:
    assumes "ide b" and "ide c"
    shows "natural_isomorphism Cop.comp C
             (\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)) (\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c)
             (\<lambda>f. uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c))"
    proof -
      interpret xb: "functor" Cop.comp Cop.comp \<open>\<lambda>x. x \<otimes> b\<close>
        using assms(1) T.fixing_ide_gives_functor_2
        by (simp add: category_axioms dual_category.intro dual_functor.intro
            dual_functor.is_functor)
      interpret Exp_c: "functor" Cop.comp C \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x c\<close>
        using assms functor_cnt_Exp by blast
      interpret F: "functor" Cop.comp C \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)\<close>
        using assms functor_cnt_Exp by blast
      interpret G: "functor" Cop.comp C \<open>\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c\<close>
      proof -
        interpret G: composite_functor Cop.comp Cop.comp C
                       \<open>\<lambda>x. x \<otimes> b\<close> \<open>\<lambda>y. Exp\<^sup>\<leftarrow> y c\<close>
          ..
        have "G.map = (\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c)"
          by auto
        thus "functor Cop.comp C (\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c)"
          using G.functor_axioms by metis
      qed
      interpret \<phi>: transformation_by_components Cop.comp C
                     \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)\<close> \<open>\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c\<close>
                     \<open>\<lambda>x. uncurry x b c\<close>
      proof
        show "\<And>a. Cop.ide a \<Longrightarrow>
                     \<guillemotleft>uncurry a b c : Exp\<^sup>\<leftarrow> a (exp b c) \<rightarrow> Exp\<^sup>\<leftarrow> (a \<otimes> b) c\<guillemotright>"
          using assms internal_curry(2) Cop.ide_char cnt_Exp_ide by auto
        show "\<And>f. Cop.arr f \<Longrightarrow>
                     uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c) =
                     Exp\<^sup>\<leftarrow> (f \<otimes> b) c \<cdot> uncurry (Cop.dom f) b c"
          using assms uncurry_naturality by simp
      qed
      have "natural_isomorphism Cop.comp C
              (\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)) (\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c) \<phi>.map"
      proof
        fix a
        assume a: "Cop.ide a"
        show "iso (\<phi>.map a)"
          using a assms internal_curry [of a b c] \<phi>.map_simp_ide
                inverse_arrows_sym
          by auto
      qed
      moreover have "\<phi>.map = (\<lambda>f. uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c))"
        using assms \<phi>.map_def by auto
      ultimately show ?thesis
        unfolding \<phi>.map_def by simp
    qed

    lemma natural_isomorphism_curry:
    assumes "ide b" and "ide c"
    shows "natural_isomorphism Cop.comp C
             (\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c) (\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c))
             (\<lambda>f. curry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> (f \<otimes> b) c)"
    proof -
      interpret \<phi>: natural_isomorphism Cop.comp C
                     \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)\<close> \<open>\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c\<close>
                     \<open>\<lambda>f. uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c)\<close>
        using assms natural_isomorphism_uncurry by blast
      interpret \<psi>: inverse_transformation Cop.comp C
                     \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x (exp b c)\<close> \<open>\<lambda>x. Exp\<^sup>\<leftarrow> (x \<otimes> b) c\<close>
                     \<open>\<lambda>f. uncurry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> f (exp b c)\<close>
        ..
      have 1: "\<And>a. Cop.ide a \<Longrightarrow> \<psi>.map a = curry a b c"
      proof -
        fix a
        assume a: "Cop.ide a"
        have "inverse_arrows
                (uncurry (Cop.cod a) b c \<cdot> Exp\<^sup>\<leftarrow> a (exp b c)) (\<psi>.map a)"
          using assms a \<psi>.inverts_components by blast
        moreover
        have "inverse_arrows
                (uncurry (Cop.cod a) b c \<cdot> Exp\<^sup>\<leftarrow> a (exp b c)) (curry a b c)"
          by (metis assms a Cop.ideD(1,3) Cop.ide_char \<phi>.F.preserves_ide
              \<phi>.preserves_reflects_arr comp_arr_ide internal_curry(3)
              inverse_arrows_sym)
        ultimately show "\<psi>.map a = curry a b c"
          using internal_curry inverse_arrow_unique by simp
      qed
      have "\<psi>.map = (\<lambda>f. curry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> (f \<otimes> b) c)"
      proof
        fix f
        show "\<psi>.map f = curry (Cop.cod f) b c \<cdot> Exp\<^sup>\<leftarrow> (f \<otimes> b) c"
          using assms 1 \<psi>.inverts_components internal_curry(3) \<psi>.is_natural_2
            Cop.ide_char \<psi>.is_extensional
          by auto
      qed
      thus ?thesis
        using \<psi>.natural_isomorphism_axioms by simp
    qed

  subsection "Yoneda Embedding"

    text \<open>
      The internal hom provides a closed monoidal category \<open>C\<close> with a "Yoneda embedding",
      which is a mapping that takes each arrow \<open>g\<close> of \<open>C\<close> to a natural transformation from
      the contravariant functor \<open>Exp\<^sup>\<leftarrow> \<hyphen> (dom g)\<close> to the contravariant functor
      \<open>Exp\<^sup>\<leftarrow> \<hyphen> (cod g)\<close>.  Note that here the target category is \<open>C\<close> itself, not a category
      of sets and functions as in the classical case.  Note also that we are talking here
      about ordinary functors and natural transformations.
      We can easily prove from general considerations that the Yoneda embedding (so-defined)
      is faithful.  However, to obtain a fullness result requires the development of a
      certain amount of enriched category theory, which we do elsewhere.
    \<close>

    lemma yoneda_embedding:
    assumes "\<guillemotleft>g : a \<rightarrow> b\<guillemotright>"
    shows "natural_transformation Cop.comp C
             (\<lambda>x. Exp\<^sup>\<leftarrow> x a) (\<lambda>x. Exp\<^sup>\<leftarrow> x b) (\<lambda>x. Exp x g)"
    and "Uncurry[a, b] (Exp a g \<cdot> Curry[\<I>, a, a] \<l>[a]) \<cdot> \<l>\<^sup>-\<^sup>1[a] = g"
    proof -
      interpret Exp: binary_functor Cop.comp C C \<open>\<lambda>fg. Exp (fst fg) (snd fg)\<close>
        using functor_Exp by blast
      interpret Exp_g: natural_transformation Cop.comp C
                         \<open>\<lambda>x. Exp x (dom g)\<close> \<open>\<lambda>x. Exp x (cod g)\<close> \<open>\<lambda>x. Exp x g\<close>
        using assms Exp.fixing_arr_gives_natural_transformation_2 [of g] by auto
      show "natural_transformation Cop.comp C (\<lambda>x. Exp\<^sup>\<leftarrow> x a) (\<lambda>x. Exp\<^sup>\<leftarrow> x b)
              (\<lambda>x. Exp x g)"
        using assms Exp_x_ide Exp_x_ide Exp_g.natural_transformation_axioms
        by auto
      show "Uncurry[a, b] (Exp a g \<cdot> Curry[\<I>, a, a] \<l>[a]) \<cdot> \<l>\<^sup>-\<^sup>1[a] = g"
      proof -
        have "Uncurry[a, b] (Exp a g \<cdot> Curry[\<I>, a, a] \<l>[a]) \<cdot> \<l>\<^sup>-\<^sup>1[a] =
              (eval a b \<cdot> (Exp a g \<otimes> a) \<cdot> (Curry[\<I>, a, a] \<l>[a] \<otimes> a)) \<cdot> \<l>\<^sup>-\<^sup>1[a]"
          using assms Exp_ide lunit_in_hom
                interchange [of "Exp a g" "Curry[\<I>, a, a] \<l>[a]" a a]
          by auto
        also have "... = g \<cdot> (eval a a \<cdot> (Curry[\<I>, a, a] \<l>[a] \<otimes> a)) \<cdot> \<l>\<^sup>-\<^sup>1[a]"
          using assms Uncurry_Exp_dom comp_assoc by (metis in_homE)
        also have "... = g \<cdot> \<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a]"
          using assms Uncurry_Curry ide_dom ide_unity lunit_in_hom by auto
        also have "... = g"
          using assms comp_arr_dom by force
        finally show ?thesis
          by blast
      qed
    qed

    lemma yoneda_embedding_is_faithful:
    assumes "par g g'" and "(\<lambda>x. Exp x g) = (\<lambda>x. Exp x g')"
    shows "g = g'"
    proof -
      have "g \<cdot> eval (dom g) (dom g) = g' \<cdot> eval (dom g) (dom g)"
        using assms Uncurry_Exp_dom by metis
      thus "g = g'"
        using assms retraction_eval_ide_self retraction_is_epi
        by (metis epiE eval_simps(1,3) ide_dom seqI)
    qed

    text \<open>
      The following is a version of the key fact underlying the classical Yoneda Lemma:
      for any natural transformation \<open>\<tau>\<close> from \<open>Exp\<^sup>\<leftarrow> \<hyphen> a\<close> to \<open>Exp\<^sup>\<leftarrow> \<hyphen> b\<close>,
      there is a fixed arrow \<open>g : a \<rightarrow> b\<close>, depending only on the single component \<open>\<tau> a\<close>,
      such that the compositions \<open>\<tau> x \<cdot> e\<close> of an arbitrary component \<open>\<tau> x\<close> with arbitrary
      global elements \<open>e : \<I> \<rightarrow> exp x a\<close> depend on \<open>\<tau>\<close> only via \<open>g\<close>, and hence only via \<open>\<tau> a\<close>.
    \<close>

    lemma hom_transformation_expansion:
    assumes "natural_transformation
               Cop.comp C (\<lambda>x. Exp\<^sup>\<leftarrow> x a) (\<lambda>x. Exp\<^sup>\<leftarrow> x b) \<tau>"
    and "ide a" and "ide b"
    shows "\<guillemotleft>Uncurry[a, b] (\<tau> a \<cdot> Curry[\<I>, a, a] \<l>[a]) \<cdot> \<l>\<^sup>-\<^sup>1[a] : a \<rightarrow> b\<guillemotright>"
    and "\<And>x e. \<lbrakk>ide x; \<guillemotleft>e : \<I> \<rightarrow> exp x a\<guillemotright>\<rbrakk> \<Longrightarrow>
                \<tau> x \<cdot> e = Exp x (Uncurry[a, b] (\<tau> a \<cdot> Curry[\<I>, a, a] \<l>[a]) \<cdot> \<l>\<^sup>-\<^sup>1[a]) \<cdot> e"
    proof -
      interpret \<tau>: natural_transformation Cop.comp C
                     \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x a\<close> \<open>\<lambda>x. Exp\<^sup>\<leftarrow> x b\<close> \<tau>
        using assms by blast
      let ?Id_a = "Curry[\<I>, a, a] \<l>[a]"
      have Id_a: "\<guillemotleft>?Id_a : \<I> \<rightarrow> exp a a\<guillemotright>"
        using assms ide_unity by blast
      let ?g = "Uncurry[a, b] (\<tau> a \<cdot> ?Id_a) \<cdot> \<l>\<^sup>-\<^sup>1[a]"
      show g: "\<guillemotleft>?g : a \<rightarrow> b\<guillemotright>"
        using assms(2-3) Id_a cnt_Exp_ide by auto
      have *: "\<And>x e. \<lbrakk>ide x; \<guillemotleft>e : \<I> \<rightarrow> exp x a\<guillemotright>\<rbrakk>
                        \<Longrightarrow> \<tau> x \<cdot> e = Curry[exp x a, x, b] (?g \<cdot> eval x a) \<cdot> e"
      proof -
        fix x e
        assume x: "ide x"
        assume e: "\<guillemotleft>e : \<I> \<rightarrow> exp x a\<guillemotright>"
        let ?e' = "Uncurry x a e \<cdot> \<l>\<^sup>-\<^sup>1[x]"
        have e': "\<guillemotleft>?e' : x \<rightarrow> a\<guillemotright>"
          using assms(2) x e by blast
        have 1: "e = Exp\<^sup>\<leftarrow> ?e' a \<cdot> ?Id_a"
        proof -
          have "Exp\<^sup>\<leftarrow> ?e' a \<cdot> ?Id_a =
                Curry[exp a a, x, a] (eval a a \<cdot> (exp a a \<otimes> ?e')) \<cdot> ?Id_a"
            using assms(2) e' by auto
          also have "... =
                     Curry[\<I>, x, a] (eval a a \<cdot> (exp a a \<otimes> ?e') \<cdot> (?Id_a \<otimes> x))"
            using assms(2) Id_a e' x comp_Curry_arr comp_assoc by auto
          also have "... = Curry[\<I>, x, a] (eval a a \<cdot> (?Id_a \<otimes> ?e'))"
            using assms(2) e' Id_a interchange comp_arr_dom comp_cod_arr in_homE
            by (metis (no_types, lifting))
          also have "... = Curry \<I> x a (eval a a \<cdot> (?Id_a \<otimes> a) \<cdot> (\<I> \<otimes> ?e'))"
            using assms(2) interchange
            by (metis (no_types, lifting) e' Id_a comp_arr_ide comp_cod_arr ide_char
                ide_unity in_homE seqI)
          also have "... =
                     Curry[\<I>, x, a] (Uncurry a a (Curry[\<I>, a, a] \<l>[a]) \<cdot> (\<I> \<otimes> ?e'))"
            using comp_assoc by simp
          also have "... = Curry[\<I>, x, a] (\<l>[a] \<cdot> (\<I> \<otimes> ?e'))"
            using assms(2) Uncurry_Curry comp_assoc ide_unity lunit_in_hom
            by presburger
          also have "... = Curry[\<I>, x, a] (?e' \<cdot> \<l>[x])"
            using assms(2) e' in_homE lunit_naturality
            by (metis (no_types, lifting))
          also have "... = Curry[\<I>, x, a] (Uncurry[x, a] e \<cdot> \<l>\<^sup>-\<^sup>1[x] \<cdot> \<l>[x])"
            using comp_assoc by simp
          also have "... = Curry[\<I>, x, a] (Uncurry[x, a] e)"
            using assms(2) x e comp_arr_dom Uncurry_simps(2) by force
          also have "... = e"
            using assms(2) x e Curry_Uncurry ide_unity by blast
          finally show ?thesis by simp
        qed
        have "\<tau> x \<cdot> e = \<tau> x \<cdot> Exp\<^sup>\<leftarrow> ?e' a \<cdot> ?Id_a"
          using 1 by simp
        also have "... = (\<tau> x \<cdot> Exp\<^sup>\<leftarrow> ?e' a) \<cdot> ?Id_a"
          using comp_assoc by simp
        also have "... = (Exp\<^sup>\<leftarrow> ?e' b \<cdot> \<tau> a) \<cdot> ?Id_a"
          using e' \<tau>.naturality [of ?e'] by auto
        also have "... = Curry[exp a b, x, b] (eval a b \<cdot> (exp a b \<otimes> ?e')) \<cdot> \<tau> a \<cdot> ?Id_a"
          using assms(2) e' comp_assoc by auto
        also have "... =
                   Curry[\<I>, x, b] ((eval a b \<cdot> (exp a b \<otimes> ?e')) \<cdot> (\<tau> a \<cdot> ?Id_a \<otimes> x))"
        proof -
          have "\<guillemotleft>\<tau> a \<cdot> ?Id_a : \<I> \<rightarrow> exp a b\<guillemotright>"
            using Id_a assms(2-3) in_homI cnt_Exp_ide
            by (intro comp_in_homI) auto
          moreover have "\<guillemotleft>eval a b \<cdot> (exp a b \<otimes> ?e') : exp a b \<otimes> x \<rightarrow> b\<guillemotright>"
            using assms(2-3) e' ide_in_hom by blast
          ultimately show ?thesis
            using x comp_Curry_arr by blast
        qed
        also have "... = Curry[\<I>, x, b] (eval a b \<cdot> (exp a b \<otimes> ?e') \<cdot> (\<tau> a \<cdot> ?Id_a \<otimes> x))"
          using comp_assoc by simp
        also have "... = Curry[\<I>, x, b] (eval a b \<cdot> (exp a b \<cdot> \<tau> a \<cdot> ?Id_a \<otimes> ?e' \<cdot> x))"
        proof -
          have "seq (exp a b) (\<tau> a \<cdot> Curry[\<I>, a, a] \<l>[a])"
            using assms ide_exp \<tau>.natural_transformation_axioms Id_a Curry_Uncurry
                  ide_exp ide_in_hom
            by auto
          moreover have "seq (Uncurry[x, a] e \<cdot> \<l>\<^sup>-\<^sup>1[x]) x"
            using x e' by auto
          ultimately show ?thesis
            using assms interchange by simp
        qed
        also have "... = Curry[\<I>, x, b] (eval a b \<cdot> (\<tau> a \<cdot> ?Id_a \<otimes> ?e'))"
        proof -
          have "exp a b \<cdot> \<tau> a \<cdot> ?Id_a = \<tau> a \<cdot> ?Id_a"
            using assms(2-3) e' ide_exp comp_ide_arr \<tau>.preserves_hom cnt_Exp_ide
                  Id_a
            by auto
          moreover have "?e' \<cdot> x = ?e'"
            using e' comp_arr_dom by blast
          ultimately show ?thesis
            using interchange by simp
        qed
        also have "... = Curry[\<I>, x, b] (eval a b \<cdot> (\<tau> a \<cdot> ?Id_a \<otimes> a) \<cdot> (\<I> \<otimes> ?e'))"
        proof -
          have "(\<tau> a \<cdot> ?Id_a) \<cdot> \<I> = \<tau> a \<cdot> ?Id_a"
            using assms(2) comp_arr_ide
            by (metis Id_a comp_arr_dom in_homE comp_assoc)
          moreover have "a \<cdot> ?e' = ?e'"
            using e' comp_cod_arr by blast
          moreover have "seq (\<tau> a \<cdot> Curry[\<I>, a, a] \<l>[a]) \<I>"
            using assms(2) cnt_Exp_ide Id_a  by auto
          moreover have "seq a (Uncurry[x, a] e \<cdot> \<l>\<^sup>-\<^sup>1[x])"
            using calculation(2) e' by auto
          ultimately show ?thesis
            using interchange [of "\<tau> a \<cdot> ?Id_a" \<I> a ?e'] by simp
        qed
        also have "... = Curry[\<I>, x, b] (eval a b \<cdot> (\<tau> a \<cdot> ?Id_a \<otimes> a) \<cdot> (\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a]) \<cdot>
                                           (\<I> \<otimes> eval x a \<cdot> (e \<otimes> x) \<cdot> \<l>\<^sup>-\<^sup>1[x]))"
        proof -
          have "(\<I> \<otimes> eval x a) \<cdot> (\<I> \<otimes> (e \<otimes> x) \<cdot> \<l>\<^sup>-\<^sup>1[x]) =
                (\<I> \<otimes> a) \<cdot> (\<I> \<otimes> eval x a) \<cdot> (\<I> \<otimes> (e \<otimes> x) \<cdot> \<l>\<^sup>-\<^sup>1[x])"
            using assms e' L.as_nat_trans.is_natural_2 comp_lunit_lunit'(2) comp_assoc
            by (metis (no_types, lifting) L.as_nat_trans.preserves_comp_2 in_homE)
          thus ?thesis
            using assms e' comp_assoc
            by (elim in_homE) auto
        qed
        also have "... = Curry[\<I>, x, b] (?g \<cdot> \<l>[a] \<cdot> (\<I> \<otimes> eval x a \<cdot> (e \<otimes> x) \<cdot> \<l>\<^sup>-\<^sup>1[x]))"
          using comp_assoc by simp
        also have "... = Curry[\<I>, x, b] (?g \<cdot> (eval x a \<cdot> (e \<otimes> x) \<cdot> \<l>\<^sup>-\<^sup>1[x]) \<cdot> \<l>[x])"
          using lunit_naturality
          by (metis (no_types, lifting) e' in_homE comp_assoc)
        also have "... = Curry[\<I>, x, b] (?g \<cdot> eval x a \<cdot> (e \<otimes> x) \<cdot> \<l>\<^sup>-\<^sup>1[x] \<cdot> \<l>[x])"
          using comp_assoc by simp
        also have "... = Curry[\<I>, x, b] (?g \<cdot> eval x a \<cdot> (e \<otimes> x))"
          using x comp_arr_dom e interchange by fastforce
        also have "... = Curry[\<I>, x, b] ((?g \<cdot> eval x a) \<cdot> (e \<otimes> x))"
          using comp_assoc by simp
        also have "... = Curry[exp x a, x, b] (?g \<cdot> eval x a) \<cdot> e"
          using assms(2) x e g comp_Curry_arr by auto
        finally show "\<tau> x \<cdot> e = Curry[exp x a, x, b] (?g \<cdot> eval x a) \<cdot> e"
          by blast
      qed
      show "\<And>x e. \<lbrakk>ide x; \<guillemotleft>e : \<I> \<rightarrow> exp x a\<guillemotright>\<rbrakk> \<Longrightarrow> \<tau> x \<cdot> e = Exp x ?g \<cdot> e"
      proof -
        fix x e
        assume x: "ide x"
        assume e: "\<guillemotleft>e : \<I> \<rightarrow> exp x a\<guillemotright>"
        have "\<tau> x \<cdot> e = Curry[exp x a, x, b] (?g \<cdot> eval x a) \<cdot> e"
          using x e * \<tau>.natural_transformation_axioms by blast
        also have "... = (Curry[exp x a, x, cod ?g] (?g \<cdot> eval x a) \<cdot>
                            Curry[exp x a, x, a] (Uncurry[x, a] (exp x a))) \<cdot> e"
        proof -
          have "Curry[exp x a, x, a] (Uncurry[x, a] (exp x a)) = exp x a"
            using assms(2) x Curry_Uncurry ide_exp ide_in_hom by force
          thus ?thesis
            using g e comp_cod_arr comp_assoc by fastforce
        qed
        also have "... = Exp x ?g \<cdot> e"
          using x Exp_def cod_comp g by auto
        finally show "\<tau> x \<cdot> e = Exp x ?g \<cdot> e" by blast
      qed
    qed

  section "Enriched Structure"

  text \<open>
    In this section we do the main work involved in showing that a closed monoidal category
    is ``enriched in itself''.  For this, we need to define, for each object \<open>a\<close>, an arrow
    \<open>Id a : \<I> \<rightarrow> exp a a\<close> to serve as the ``identity at \<open>a\<close>'', and for every three objects
    \<open>a\<close>, \<open>b\<close>, and \<open>c\<close>, a ``compositor'' \<open>Comp a b c : exp b c \<otimes> exp a b \<rightarrow> exp a c\<close>.
    We also need to prove that these satisfy the appropriate unit and associativity laws.
    Although essentially all the work is done here, the statement and proof of the the final
    result is deferred to a separate theory \<open>EnrichedCategory\<close> so that a mutual dependence
    between that theory and the present one is not introduced.
  \<close>

    interpretation elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by blast

    definition Id
    where "Id a \<equiv> Curry[\<I>, a, a] \<l>[a]"

    lemma Id_in_hom [intro]:
    assumes "ide a"
    shows "\<guillemotleft>Id a : \<I> \<rightarrow> exp a a\<guillemotright>"
      unfolding Id_def
      using assms Curry_in_hom lunit_in_hom by simp

    lemma Id_simps [simp]:
    assumes "ide a"
    shows "arr (Id a)"
    and "dom (Id a) = \<I>"
    and "cod (Id a) = exp a a"
      using assms Id_in_hom by blast+

    text\<open>
      The next definition follows Kelly \<^cite>\<open>"kelly-enriched-category"\<close>, section 1.6.
    \<close>

    definition Comp
    where "Comp a b c \<equiv>
           Curry[exp b c \<otimes> exp a b, a, c]
             (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot> \<a>[exp b c, exp a b, a])"

    lemma Comp_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>Comp a b c : exp b c \<otimes> exp a b \<rightarrow> exp a c\<guillemotright>"
      using assms ide_exp ide_in_hom Comp_def Curry_in_hom tensor_preserves_ide
      by auto

    lemma Comp_simps [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "arr (Comp a b c)"
    and "dom (Comp a b c) = exp b c \<otimes> exp a b"
    and "cod (Comp a b c) = exp a c"
      using assms Comp_in_hom in_homE by blast+

    lemma Comp_unit_right:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>Comp a a b \<cdot> (exp a b \<otimes> Id a) : exp a b \<otimes> \<I> \<rightarrow> exp a b\<guillemotright>"
    and "Comp a a b \<cdot> (exp a b \<otimes> Id a) = \<r>[exp a b]"
    proof -
      show 0: "\<guillemotleft>Comp a a b \<cdot> (exp a b \<otimes> Id a) : exp a b \<otimes> \<I> \<rightarrow> exp a b\<guillemotright>"
        using assms Id_in_hom tensor_in_hom ide_in_hom ide_exp by force
      show "Comp a a b \<cdot> (exp a b \<otimes> Id a) = \<r>[exp a b]"
      proof (intro runit_eqI)
        show 1: "\<guillemotleft>Comp a a b \<cdot> (exp a b \<otimes> Id a) : exp a b \<otimes> \<I> \<rightarrow> exp a b\<guillemotright>"
          by fact
        show "Comp a a b \<cdot> (exp a b \<otimes> Id a) \<otimes> \<I> = (exp a b \<otimes> \<iota>) \<cdot> \<a>[exp a b, \<I>, \<I>]"
        proof -
          have "\<r>[exp a b] \<cdot> (Comp a a b \<cdot> (exp a b \<otimes> Id a) \<otimes> \<I>) \<cdot>
                  inv \<a>[exp a b, \<I>, \<I>] =
                \<r>[exp a b] \<cdot> ((Comp a a b \<otimes> \<I>) \<cdot> ((exp a b \<otimes> Id a) \<otimes> \<I>)) \<cdot>
                  inv \<a>[exp a b, \<I>, \<I>]"
            using \<open>\<guillemotleft>Comp a a b \<cdot> (exp a b \<otimes> Id a) : exp a b \<otimes> \<I> \<rightarrow> exp a b\<guillemotright>\<close> arrI
            by force
          also have "... = (\<r>[exp a b] \<cdot> (Comp a a b \<otimes> \<I>)) \<cdot>
                             ((exp a b \<otimes> Id a) \<otimes> \<I>) \<cdot> inv \<a>[exp a b, \<I>, \<I>]"
            using comp_assoc by simp
          also have "... = (Comp a a b \<cdot> \<r>[exp a b \<otimes> exp a a]) \<cdot>
                             ((exp a b \<otimes> Id a) \<otimes> \<I>) \<cdot> inv \<a>[exp a b, \<I>, \<I>]"
            using assms runit_naturality
            by (metis Comp_simps(1-2) 1 cod_comp in_homE)
          also have "... = Comp a a b \<cdot>
                             (\<r>[exp a b \<otimes> exp a a] \<cdot> ((exp a b \<otimes> Id a) \<otimes> \<I>)) \<cdot>
                               inv \<a>[exp a b, \<I>, \<I>]"
            using comp_assoc by simp
          also have "... = Comp a a b \<cdot> ((exp a b \<otimes> Id a) \<cdot> \<r>[exp a b \<otimes> \<I>]) \<cdot>
                             inv \<a>[exp a b, \<I>, \<I>]"
            using assms 1 runit_naturality
            by (metis calculation in_homE comp_assoc)
          also have "... = Comp a a b \<cdot> (exp a b \<otimes> Id a) \<cdot> \<r>[exp a b \<otimes> \<I>] \<cdot>
                             inv \<a>[exp a b, \<I>, \<I>]"
            using comp_assoc by simp
          also have "... = Comp a a b \<cdot> (exp a b \<otimes> Id a) \<cdot> (exp a b \<otimes> \<iota>)"
            using assms ide_unity runit_tensor' ide_exp runit_eqI unit_in_hom_ax
              unit_triangle(1)
            by presburger
          also have "... = (Curry[exp a b \<otimes> exp a a, a, b]
                              (eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a]) \<cdot>
                             (exp a b \<otimes> Id a)) \<cdot> (exp a b \<otimes> \<iota>)"
            using Comp_def comp_assoc by simp
          also have "... = Curry[exp a b \<otimes> \<I>, a, b]
                             ((eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a]) \<cdot>
                                 ((exp a b \<otimes> Id a) \<otimes> a)) \<cdot>
                                (exp a b \<otimes> \<iota>)"
          proof -
            have "\<guillemotleft>exp a b \<otimes> Id a : exp a b \<otimes> \<I> \<rightarrow> exp a b \<otimes> exp a a\<guillemotright>"
              using assms by auto
            moreover have "\<guillemotleft>eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a] :
                              (exp a b \<otimes> exp a a) \<otimes> a \<rightarrow> b\<guillemotright>"
              using assms tensor_in_hom ide_in_hom ide_exp eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
              by force
            ultimately show ?thesis
              using assms comp_Curry_arr by simp
          qed
          also have "... = \<r>[exp a b] \<cdot> (exp a b \<otimes> \<iota>)"
          proof -
            have 1: "Uncurry[a, b]
                       (Curry[exp a b \<otimes> \<I>, a, b]
                          ((eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a]) \<cdot>
                              ((exp a b \<otimes> Id a) \<otimes> a))) =
                    (eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a]) \<cdot>
                      ((exp a b \<otimes> Id a) \<otimes> a)"
            proof -
              have "\<guillemotleft>(eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a]) \<cdot>
                       ((exp a b \<otimes> Id a) \<otimes> a) : (exp a b \<otimes> \<I>) \<otimes> a \<rightarrow> b\<guillemotright>"
                using assms tensor_in_hom ide_in_hom eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C ide_exp
                by force
              thus ?thesis
                using assms Uncurry_Curry by auto
            qed
            also have "... = (eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> (exp a b \<otimes> Id a \<otimes> a)) \<cdot>
                                \<a>[exp a b, \<I>, a]"
              using assms ide_exp comp_assoc assoc_naturality [of "exp a b" "Id a" a]
              by auto
            also have "... = (eval a b \<cdot> (exp a b \<otimes> Uncurry[a, a] (Id a))) \<cdot>
                               \<a>[exp a b, \<I>, a]"
              using assms interchange
              by (metis (no_types, lifting) ide_exp lunit_in_hom Uncurry_Curry
                  ide_unity comp_ide_self ideD(1) in_homE Id_def)
            also have "... =  (eval a b \<cdot> (exp a b \<otimes> \<l>[a])) \<cdot> \<a>[exp a b, \<I>, a]"
              by (metis (no_types, lifting) assms(1) lunit_in_hom Uncurry_Curry
                  ide_unity Id_def)
            also have 2: "... = (eval a b \<cdot> (exp a b \<otimes> a) \<cdot> (exp a b \<otimes> \<l>[a])) \<cdot>
                                  \<a>[exp a b, \<I>, a]"
              using assms interchange \<ll>_ide_simp by auto
            also have "... = Uncurry[a, b] (exp a b) \<cdot> (exp a b \<otimes> \<l>[a]) \<cdot> \<a>[exp a b, \<I>, a]"
              using comp_assoc by simp
            also have "... = Uncurry a b \<r>[exp a b]"
              using assms triangle ide_exp 2 comp_assoc by auto
            finally have "Uncurry[a, b]
                            (Curry[exp a b \<otimes> \<I>, a, b]
                               ((eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot>
                                   \<a>[exp a b, exp a a, a]) \<cdot>
                                    ((exp a b \<otimes> Id a) \<otimes> a))) =
                          Uncurry[a, b] \<r>[exp a b]"
              by blast
            hence "Curry[exp a b \<otimes> \<I>, a, b]
                     ((eval a b \<cdot> (exp a b \<otimes> eval a a) \<cdot> \<a>[exp a b, exp a a, a]) \<cdot>
                         ((exp a b \<otimes> Id a) \<otimes> a)) =
                   \<r>[exp a b]"
              using assms 1 Curry_Uncurry runit_in_hom by force
            thus ?thesis
              by presburger
          qed
          finally have "\<r>[exp a b] \<cdot>
                          (Comp a a b \<cdot> (exp a b \<otimes> Id a) \<otimes> \<I>) \<cdot> inv \<a>[exp a b, \<I>, \<I>] =
                        \<r>[exp a b] \<cdot> (exp a b \<otimes> \<iota>)"
            by blast
          hence "(Comp a a b \<cdot> (exp a b \<otimes> Id a) \<otimes> \<I>) \<cdot> inv \<a>[exp a b, \<I>, \<I>] =
                 exp a b \<otimes> \<iota>"
            using assms ide_exp iso_cancel_left [of "\<r>[exp a b]"] iso_runit by fastforce
          thus ?thesis
            by (metis assms(1-2) 0 R.as_nat_trans.is_natural_1 comp_assoc_assoc'(2)
                ide_exp ide_unity in_homE comp_assoc)
        qed
      qed
    qed

    lemma Comp_unit_left:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>Comp a b b \<cdot> (Id b \<otimes> exp a b) : \<I> \<otimes> exp a b \<rightarrow> exp a b\<guillemotright>"
    and "Comp a b b \<cdot> (Id b \<otimes> exp a b) = \<l>[exp a b]"
    proof -
      show 0: "\<guillemotleft>Comp a b b \<cdot> (Id b \<otimes> exp a b) : \<I> \<otimes> exp a b \<rightarrow> exp a b\<guillemotright>"
        using assms ide_exp by simp
      show "Comp a b b \<cdot> (Id b \<otimes> exp a b) = \<l>[exp a b]"
      proof (intro lunit_eqI)
        show "\<guillemotleft>Comp a b b \<cdot> (Id b \<otimes> exp a b) : \<I> \<otimes> exp a b \<rightarrow> exp a b\<guillemotright>"
          by fact
        show "\<I> \<otimes> Comp a b b \<cdot> (Id b \<otimes> exp a b) = (\<iota> \<otimes> exp a b) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, exp a b]"
        proof -
          have "\<l>[exp a b] \<cdot> (\<I> \<otimes> Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> \<a>[\<I>, \<I>, exp a b] =
                \<l>[exp a b] \<cdot> ((\<I> \<otimes> Comp a b b) \<cdot> (\<I> \<otimes> Id b \<otimes> exp a b)) \<cdot> \<a>[\<I>, \<I>, exp a b]"
            using assms 0 interchange [of \<I> \<I> "Comp a b b" "Id b \<otimes> exp a b"] by auto
          also have "... = (\<l>[exp a b] \<cdot> (\<I> \<otimes> Comp a b b)) \<cdot>
                             (\<I> \<otimes> Id b \<otimes> exp a b) \<cdot> \<a>[\<I>, \<I>, exp a b]"
            using comp_assoc by simp
          also have "... = (Comp a b b \<cdot> \<l>[exp b b \<otimes> exp a b]) \<cdot> (\<I> \<otimes> Id b \<otimes> exp a b) \<cdot>
                              \<a>[\<I>, \<I>, exp a b]"
            using assms lunit_naturality
            by (metis 0 Comp_simps(1-2) cod_comp in_homE)
          also have "... = Comp a b b \<cdot>
                             (\<l>[exp b b \<otimes> exp a b] \<cdot> (\<I> \<otimes> Id b \<otimes> exp a b)) \<cdot>
                                \<a>[\<I>, \<I>, exp a b]"
            using comp_assoc by simp
          also have "... =
                     (Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> \<l>[\<I> \<otimes> exp a b] \<cdot> \<a>[\<I>, \<I>, exp a b]"
            using assms 0 lunit_naturality calculation in_homE comp_assoc by metis
          also have "... = (Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> (\<iota> \<otimes> exp a b)"
            using assms(1-2) ide_exp ide_unity lunit_eqI lunit_tensor' unit_in_hom_ax
                  unit_triangle(2)
            by presburger
          also have "... = \<l>[exp a b] \<cdot> (\<iota> \<otimes> exp a b)"
          proof (unfold Comp_def)
            have "(Curry[exp b b \<otimes> exp a b, a, b]
                     (eval b b \<cdot> (exp b b \<otimes> eval a b) \<cdot> \<a>[exp b b, exp a b, a]) \<cdot>
                        (Id b \<otimes> exp a b)) \<cdot>
                    (\<iota> \<otimes> exp a b) =
                  Curry[\<I> \<otimes> exp a b, a, b]
                    ((eval b b \<cdot> (exp b b \<otimes> eval a b) \<cdot> \<a>[exp b b, exp a b, a]) \<cdot>
                       ((Id b \<otimes> exp a b) \<otimes> a)) \<cdot>
                      (\<iota> \<otimes> exp a b)"
            proof -
              have "\<guillemotleft>eval b b \<cdot> (exp b b \<otimes> eval a b) \<cdot> \<a>[exp b b, exp a b, a]
                       : (exp b b \<otimes> exp a b) \<otimes> a \<rightarrow> b\<guillemotright>"
                using assms ide_exp tensor_in_hom ide_in_hom ide_exp eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
                by force
              moreover have "\<guillemotleft>Id b \<otimes> exp a b : \<I> \<otimes> exp a b \<rightarrow> exp b b \<otimes> exp a b\<guillemotright>"
                using assms ide_exp by force
              ultimately show ?thesis
                using assms comp_Curry_arr by force
            qed
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               (eval b b \<cdot> ((exp b b \<otimes> eval a b) \<cdot> (Id b \<otimes> exp a b \<otimes> a)) \<cdot>
                                  \<a>[\<I>, exp a b, a]) \<cdot>
                                 (\<iota> \<otimes> exp a b)"
              using assms assoc_naturality [of "Id b" "exp a b" a] ide_exp comp_assoc
              by force
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               ((eval b b \<cdot> (Id b \<otimes> Uncurry a b (exp a b))) \<cdot>
                                  \<a>[\<I>, exp a b, a]) \<cdot>
                                 (\<iota> \<otimes> exp a b)"
              by (simp add: assms Uncurry_exp comp_cod_arr comp_assoc interchange)
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               ((eval b b \<cdot> (Id b \<otimes> eval a b)) \<cdot> \<a>[\<I>, exp a b, a]) \<cdot>
                                 (\<iota> \<otimes> exp a b)"
              using assms comp_arr_dom
              by (metis eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C in_homE)
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               (((eval b b \<cdot> (Id b \<otimes> b)) \<cdot> (\<I> \<otimes> eval a b)) \<cdot> \<a>[\<I>, exp a b, a]) \<cdot>
                                 (\<iota> \<otimes> exp a b)"
            proof -
              have "Id b \<otimes> eval a b = (Id b \<otimes> b) \<cdot> (\<I> \<otimes> eval a b)"
                using assms interchange
                by (metis Id_simps(1-2) comp_arr_dom comp_ide_arr eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
                    ide_in_hom seqI')
              thus ?thesis using comp_assoc by simp
            qed
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               ((\<l>[b] \<cdot> (\<I> \<otimes> eval a b)) \<cdot> \<a>[\<I>, exp a b, a]) \<cdot>
                               (\<iota> \<otimes> exp a b)"
              using assms Id_def Uncurry_Curry lunit_in_hom ide_unity by simp
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               (eval a b \<cdot> \<l>[exp a b \<otimes> a] \<cdot> \<a>[\<I>, exp a b, a]) \<cdot>
                               (\<iota> \<otimes> exp a b)"
              using assms lunit_naturality eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C in_homE lunit_naturality
                comp_assoc
              by metis
            also have "... = Curry[\<I> \<otimes> exp a b, a, b]
                               (Uncurry[a, b] \<l>[exp a b]) \<cdot> (\<iota> \<otimes> exp a b)"
              using assms ide_exp lunit_tensor' by force
            also have "... = \<l>[exp a b] \<cdot> (\<iota> \<otimes> exp a b)"
              using assms Curry_Uncurry lunit_in_hom ide_exp by auto
            finally show "(Curry[exp b b \<otimes> exp a b, a, b]
                             (eval b b \<cdot> (exp b b \<otimes> eval a b) \<cdot> \<a>[exp b b, exp a b, a]) \<cdot>
                               (Id b \<otimes> exp a b)) \<cdot>
                            (\<iota> \<otimes> exp a b) =
                          \<l>[exp a b] \<cdot> (\<iota> \<otimes> exp a b)"
              by blast
          qed
          finally have 1: "\<l>[exp a b] \<cdot>
                             (\<I> \<otimes> Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> \<a>[\<I>, \<I>, exp a b] =
                           \<l>[exp a b] \<cdot> (\<iota> \<otimes> exp a b)"
            by blast
          have "(\<I> \<otimes> Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> \<a>[\<I>, \<I>, exp a b] =
                (inv \<l>[exp a b] \<cdot> \<l>[exp a b]) \<cdot>
                  (\<I> \<otimes> Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> \<a>[\<I>, \<I>, exp a b]"
            using assms comp_cod_arr by simp
          also have "... = (inv \<l>[exp a b] \<cdot> \<l>[exp a b]) \<cdot> (\<iota> \<otimes> exp a b)"
            using 1 comp_assoc by simp
          also have "... = \<iota> \<otimes> exp a b"
            using assms comp_cod_arr [of "\<iota> \<otimes> exp a b" "\<l>\<^sup>-\<^sup>1[exp a b] \<cdot> \<l>[exp a b]"] arrI
            by auto
          finally have "(\<I> \<otimes> Comp a b b \<cdot> (Id b \<otimes> exp a b)) \<cdot> \<a>[\<I>, \<I>, exp a b] =
                        \<iota> \<otimes> exp a b"
            by blast
          thus ?thesis
            using assms(1-2) 0 L.as_nat_trans.is_natural_1 comp_assoc_assoc'(1)
                  ide_exp ide_unity in_homE comp_assoc
            by metis
        qed
      qed
    qed

    lemma Comp_assoc\<^sub>E\<^sub>C\<^sub>M\<^sub>C:
    assumes "ide a" and "ide b" and "ide c" and "ide d"
    shows "\<guillemotleft>Comp a b d \<cdot> (Comp b c d \<otimes> exp a b) :
              (exp c d \<otimes> exp b c) \<otimes> exp a b \<rightarrow> exp a d\<guillemotright>"
    and "Comp a b d \<cdot> (Comp b c d \<otimes> exp a b) =
         Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot> \<a>[exp c d, exp b c, exp a b]"
    proof -
      show "\<guillemotleft>Comp a b d \<cdot> (Comp b c d \<otimes> exp a b) :
               (exp c d \<otimes> exp b c) \<otimes> exp a b \<rightarrow> exp a d\<guillemotright>"
        using assms by auto
      show "Comp a b d \<cdot> (Comp b c d \<otimes> exp a b) =
            Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot> \<a>[exp c d, exp b c, exp a b]"
      proof -
        have 1: "Uncurry[a, d] (Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot>
                   \<a>[exp c d, exp b c, exp a b]) =
                 Uncurry[a, d] (Comp a b d \<cdot> (Comp b c d \<otimes> exp a b))"
        proof -
          have "Uncurry[a, d]
                  (Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot>
                     \<a>[exp c d, exp b c, exp a b]) =
                Uncurry[a, d]
                  (Curry[exp c d \<otimes> exp a c, a, d]
                     (eval c d \<cdot> (exp c d \<otimes> eval a c) \<cdot> \<a>[exp c d, exp a c, a]) \<cdot>
                    (exp c d \<otimes> Comp a b c) \<cdot> \<a>[exp c d, exp b c, exp a b])"
            using Comp_def by simp
          also have "... = Uncurry[a, d]
                             (Curry[(exp c d \<otimes> exp b c) \<otimes> exp a b, a, d]
                                ((eval c d \<cdot> (exp c d \<otimes> eval a c) \<cdot> \<a>[exp c d, exp a c, a]) \<cdot>
                               ((exp c d \<otimes> Comp a b c) \<cdot>
                                   \<a>[exp c d, exp b c, exp a b] \<otimes> a)))"
            using assms
                  comp_Curry_arr
                    [of a "(exp c d \<otimes> Comp a b c) \<cdot> \<a>[exp c d, exp b c, exp a b]"
                        "(exp c d \<otimes> exp b c) \<otimes> exp a b" "exp c d \<otimes> exp a c"
                        "eval c d \<cdot> (exp c d \<otimes> eval a c) \<cdot> \<a>[exp c d, exp a c, a]" d]
            by auto
          also have "... = eval c d \<cdot>(exp c d \<otimes> eval a c) \<cdot>
                             (\<a>[exp c d, exp a c, a] \<cdot> ((exp c d \<otimes> Comp a b c) \<otimes> a)) \<cdot>
                               (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using assms Uncurry_Curry ide_exp interchange comp_assoc by simp
          also have "... = eval c d \<cdot>
                           (exp c d \<otimes> eval a c) \<cdot>
                             (\<a>[exp c d, exp a c, a] \<cdot>
                               ((exp c d \<otimes>
                                   Curry[exp b c \<otimes> exp a b, a, c]
                                     (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot> \<a>[exp b c, exp a b, a]))
                                  \<otimes> a)) \<cdot>
                               (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            unfolding Comp_def by simp
          also have "... = eval c d \<cdot>
                           (exp c d \<otimes> eval a c) \<cdot>
                             ((exp c d \<otimes>
                                 Curry[exp b c \<otimes> exp a b, a, c]
                                   (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot> \<a>[exp b c, exp a b, a])
                                \<otimes> a) \<cdot>
                                \<a>[exp c d, exp b c \<otimes> exp a b, a]) \<cdot>
                               (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using assms assoc_naturality [of "exp c d" _ a] Comp_def Comp_simps(1-3)
              ide_exp ide_char
            by (metis (no_types, lifting) mem_Collect_eq)
          also have "... = eval c d \<cdot>
                             ((exp c d \<otimes> eval a c) \<cdot>
                                (exp c d \<otimes>
                                   Curry[exp b c \<otimes> exp a b, a, c]
                                     (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot> \<a>[exp b c, exp a b, a])
                                \<otimes> a)) \<cdot>
                               \<a>[exp c d, exp b c \<otimes> exp a b, a] \<cdot>
                                 (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using comp_assoc by simp
          also have "... = eval c d \<cdot>
                           (exp c d \<otimes>
                              Uncurry[a, c]
                                (Curry[exp b c \<otimes> exp a b, a, c]
                                   (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot>
                                      \<a>[exp b c, exp a b, a]))) \<cdot>
                             \<a>[exp c d, exp b c \<otimes> exp a b, a] \<cdot>
                               (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using assms Comp_def Comp_in_hom interchange by auto
          also have "... = eval c d \<cdot>
                             (exp c d \<otimes> (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot>
                                \<a>[exp b c, exp a b, a])) \<cdot>
                               \<a>[exp c d, exp b c \<otimes> exp a b, a] \<cdot>
                                 (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using assms ide_exp tensor_in_hom ide_in_hom ide_exp eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
                  assoc_in_hom Uncurry_Curry
            by force
          also have "... = eval c d \<cdot>
                           ((exp c d \<otimes> eval b c) \<cdot>
                              (exp c d \<otimes> exp b c \<otimes> eval a b) \<cdot>
                                (exp c d \<otimes> \<a>[exp b c, exp a b, a])) \<cdot>
                             \<a>[exp c d, exp b c \<otimes> exp a b, a] \<cdot>
                               (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using assms ide_exp tensor_in_hom interchange by auto
          also have "... = eval c d \<cdot>
                             (exp c d \<otimes> eval b c) \<cdot>
                               (exp c d \<otimes> exp b c \<otimes> eval a b) \<cdot>
                                 (exp c d \<otimes> \<a>[exp b c, exp a b, a]) \<cdot>
                                   \<a>[exp c d, exp b c \<otimes> exp a b, a] \<cdot>
                                     (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            using comp_assoc by simp
          finally have *: "Uncurry[a, d] (Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot>
                             \<a>[exp c d, exp b c, exp a b]) =
                           eval c d \<cdot>
                             (exp c d \<otimes> eval b c) \<cdot>
                                (exp c d \<otimes> exp b c \<otimes> eval a b) \<cdot>
                                   (exp c d \<otimes> \<a>[exp b c, exp a b, a]) \<cdot>
                                     \<a>[exp c d, exp b c \<otimes> exp a b, a] \<cdot>
                                       (\<a>[exp c d, exp b c, exp a b] \<otimes> a)"
            by blast
          have "Uncurry[a, d] (Comp a b d \<cdot> (Comp b c d \<otimes> exp a b)) =
                Uncurry[a, d]
                  (Curry[exp b d \<otimes> exp a b, a, d]
                     (eval b d \<cdot> (exp b d \<otimes> eval a b) \<cdot> \<a>[exp b d, exp a b, a]) \<cdot>
                    (Comp b c d \<otimes> exp a b))"
            using Comp_def by simp
          also have "... = Uncurry[a, d]
                             (Curry[(exp c d \<otimes> exp b c) \<otimes> exp a b, a, d]
                                (eval b d \<cdot> (exp b d \<otimes> eval a b) \<cdot> \<a>[exp b d, exp a b, a] \<cdot>
                                   ((Comp b c d \<otimes> exp a b) \<otimes> a)))"
          proof -
            have "\<guillemotleft>Comp b c d \<otimes> exp a b :
                     (exp c d \<otimes> exp b c) \<otimes> exp a b \<rightarrow> exp b d \<otimes> exp a b\<guillemotright>"
              using assms ide_exp by force
            moreover have "\<guillemotleft>eval b d \<cdot> (exp b d \<otimes> eval a b) \<cdot> \<a>[exp b d, exp a b, a]
                              : (exp b d \<otimes> exp a b) \<otimes> a \<rightarrow> d\<guillemotright>"
                using assms ide_exp tensor_in_hom ide_in_hom ide_exp eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
                by force
            ultimately show ?thesis
              using comp_Curry_arr assms comp_assoc by auto
          qed
          also have "... = eval b d \<cdot> (exp b d \<otimes> eval a b) \<cdot> \<a>[exp b d, exp a b, a] \<cdot>
                             ((Comp b c d \<otimes> exp a b) \<otimes> a)"
            using assms ide_exp Uncurry_Curry by force
          also have "... = eval b d \<cdot>
                             ((exp b d \<otimes> eval a b) \<cdot> (Comp b c d \<otimes> exp a b \<otimes> a)) \<cdot>
                               \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            using assms ide_exp comp_assoc
              assoc_naturality [of "Comp b c d" "exp a b" a]
            by force
          also have "... = eval b d \<cdot> (Comp b c d \<otimes> eval a b) \<cdot>
                             \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            by (simp add: assms comp_arr_dom comp_cod_arr interchange)
          also have "... = eval b d \<cdot>
                             (Curry[exp c d \<otimes> exp b c, b, d]
                                (eval c d \<cdot> (exp c d \<otimes> eval b c) \<cdot> \<a>[exp c d, exp b c, b])
                                  \<otimes> eval a b) \<cdot>
                               \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            unfolding Comp_def by simp
          also have "... = eval b d \<cdot>
                             ((Curry[exp c d \<otimes> exp b c, b, d]
                                 (eval c d \<cdot> (exp c d \<otimes> eval b c) \<cdot> \<a>[exp c d, exp b c, b])
                                   \<otimes> b) \<cdot>
                                 ((exp c d \<otimes> exp b c) \<otimes> eval a b)) \<cdot>
                               \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            by (metis (no_types, lifting) assms Comp_def Comp_simps(1-2)
                comp_arr_dom comp_cod_arr eval_simps(1,3) interchange)
          also have "... = Uncurry[b, d]
                             (Curry[exp c d \<otimes> exp b c, b, d]
                                (eval c d \<cdot> (exp c d \<otimes> eval b c) \<cdot> \<a>[exp c d, exp b c, b])) \<cdot>
                               ((exp c d \<otimes> exp b c) \<otimes> eval a b) \<cdot>
                                 \<a>[exp c d \<otimes> exp b c, exp a b, a]"
             using comp_assoc by simp
          also have "... = eval c d \<cdot> 
                           (exp c d \<otimes> eval b c) \<cdot>
                             (\<a>[exp c d, exp b c, b] \<cdot>
                                ((exp c d \<otimes> exp b c) \<otimes> eval a b)) \<cdot>
                                   \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            using assms ide_exp Uncurry_Curry comp_assoc by auto
          also have "... = eval c d \<cdot> 
                            (exp c d \<otimes> eval b c) \<cdot>
                              ((exp c d \<otimes> exp b c \<otimes> eval a b) \<cdot>
                                 \<a>[exp c d, exp b c, exp a b \<otimes> a]) \<cdot>
                                \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            using assoc_naturality [of "exp c d" "exp b c" "eval a b"]
            by (metis assms arr_cod cod_cod Curry_in_hom dom_dom eval_in_hom\<^sub>E\<^sub>C\<^sub>M\<^sub>C
                ide_exp in_homE)
          also have "... = eval c d \<cdot> 
                             (exp c d \<otimes> eval b c) \<cdot>
                               (exp c d \<otimes> exp b c \<otimes> eval a b) \<cdot>
                                 \<a>[exp c d, exp b c, exp a b \<otimes> a] \<cdot>
                                   \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            using comp_assoc by simp
          finally have **: "Uncurry[a, d] (Comp a b d \<cdot> (Comp b c d \<otimes> exp a b)) =
                            eval c d \<cdot> 
                              (exp c d \<otimes> eval b c) \<cdot>
                                (exp c d \<otimes> exp b c \<otimes> eval a b) \<cdot>
                                   \<a>[exp c d, exp b c, exp a b \<otimes> a] \<cdot>
                                     \<a>[exp c d \<otimes> exp b c, exp a b, a]"
            by blast
          show ?thesis
            using * ** assms ide_exp pentagon by force
        qed
        have "Comp a b d \<cdot> (Comp b c d \<otimes> exp a b) =
              Curry[(exp c d \<otimes> exp b c) \<otimes> exp a b, a, d]
                (Uncurry[a, d] (Comp a b d \<cdot> (Comp b c d \<otimes> exp a b)))"
          using assms ide_exp Curry_Uncurry by fastforce
        also have "... = Curry[(exp c d \<otimes> exp b c) \<otimes> exp a b, a, d]
                           (Uncurry[a, d] (Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot>
                                             \<a>[exp c d, exp b c, exp a b]))"
          using 1 by simp
        also have "... = Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot>
                           \<a>[exp c d, exp b c, exp a b]"
          using assms ide_exp Curry_Uncurry by simp
        finally show "Comp a b d \<cdot> (Comp b c d \<otimes> exp a b) =
                      Comp a c d \<cdot> (exp c d \<otimes> Comp a b c) \<cdot> \<a>[exp c d, exp b c, exp a b]"
          by blast
      qed
    qed

  end

end
