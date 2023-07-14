chapter "The Lambda Calculus"

  text \<open>
    In this second part of the article, we apply the residuated transition system framework
    developed in the first part to the theory of reductions in Church's \<open>\<lambda>\<close>-calculus.
    The underlying idea is to exhibit \<open>\<lambda>\<close>-terms as states (identities) of an RTS,
    with reduction steps as non-identity transitions.  We represent both states and transitions
    in a unified, variable-free syntax based on de Bruijn indices.
    A difficulty one faces in regarding the \<open>\<lambda>\<close>-calculus as an RTS is that
    ``elementary reductions'', in which just one redex is contracted, are not preserved by
    residuation: an elementary reduction can have zero or more residuals along another
    elementary reduction.  However, ``parallel reductions'', which permit the contraction of
    multiple redexes existing in a term to be contracted in a single step, are preserved
    by residuation.  For this reason, in our syntax each term represents a parallel reduction
    of zero or more redexes; a parallel reduction of zero redexes representing an identity.
    We have syntactic constructors for variables, \<open>\<lambda>\<close>-abstractions, and applications.
    An additional constructor represents a \<open>\<beta>\<close>-redex that has been marked for contraction.
    This is a slightly different approach that that taken by other authors
    (\emph{e.g.}~\<^cite>\<open>"barendregt"\<close> or \<^cite>\<open>"huet-residual-theory"\<close>), in which it is the
    application constructor that is marked to indicate a redex to be contracted,
    but it seems more natural in the present setting in which a single syntax is used to
    represent both terms and reductions.

    Once the syntax has been defined, we define the residuation operation and prove
    that it satisfies the conditions for a weakly extensional RTS.  In this RTS, the source
    of a term is obtained by ``erasing'' the markings on redexes, leaving an identity term.
    The target of a term is the contractum of the parallel reduction it represents.
    As the definition of residuation involves the use of substitution, a necessary prerequisite
    is to develop the theory of substitution using de Bruijn indices.
    In addition, various properties concerning the commutation of residuation and substitution
    have to be proved.  This part of the work has benefited greatly from previous work
    of Huet \<^cite>\<open>"huet-residual-theory"\<close>, in which the theory of residuation was formalized
    in the proof assistant Coq.  In particular, it was very helpful to have already available
    known-correct statements of various lemmas regarding indices, substitution, and residuation.
    The development of the theory culminates in the proof of L\'{e}vy's ``Cube Lemma''
    \<^cite>\<open>"levy"\<close>, which is the key axiom in the definition of RTS.

    Once reductions in the \<open>\<lambda>\<close>-calculus have been cast as transitions of an RTS,
    we are able to take advantage of generic results already proved for RTS's; in particular,
    the construction of the RTS of paths, which represent reduction sequences.
    Very little additional effort is required at this point to prove the Church-Rosser Theorem.
    Then, after proving a series of miscellaneous lemmas about reduction paths,
    we turn to the study of developments.  A development of a term is a reduction path from
    that term in which the only redexes that are contracted are those that are residuals of
    redexes in the original term.  We prove the Finite Developments Theorem: all developments
    are finite.  The proof given here follows that given by de Vrijer \<^cite>\<open>"deVrijer"\<close>,
    except that here we make the adaptations necessary for a syntax based on de Bruijn
    indices, rather than the classical named-variable syntax used by de Vrijer.
    Using the Finite Developments Theorem, we define a function that takes a term and constructs
    a ``complete development'' of that term, which is a development in which no residuals of
    original redexes remain to be contracted.

    We then turn our attention to ``standard reduction paths'', which are reduction paths in
    which redexes are contracted in a left-to-right order, perhaps with some skips.
    After giving a definition of standard reduction paths, we define a function that takes a
    term and constructs a complete development that is also standard.
    Using this function as a base case, we then define a function that takes an arbitrary
    parallel reduction path and transforms it into a standard reduction path that is congruent
    to the given path.  The algorithm used is roughly analogous to insertion sort.
    We use this function to prove strong form of the Standardization Theorem: every reduction
    path is congruent to a standard reduction path.  As a corollary of the Standardization
    Theorem, we prove the Leftmost Reduction Theorem: leftmost reduction is a normalizing
    reduction strategy.

    It should be noted that, in this article, we consider only the \<open>\<lambda>\<beta>\<close>-calculus.
    In the early stages of this work, I made an exploratory attempt to incorporate \<open>\<eta>\<close>-reduction
    as well, but after encountering some unanticipated difficulties I decided not to attempt that
    extension until the \<open>\<beta>\<close>-only case had been well-developed.
  \<close>

theory LambdaCalculus
imports Main ResiduatedTransitionSystem
begin

  section "Syntax"

  locale lambda_calculus
  begin

    text \<open>
      The syntax of terms has constructors \<open>Var\<close> for variables, \<open>Lam\<close> for \<open>\<lambda>\<close>-abstraction,
      and \<open>App\<close> for application.  In addition, there is a constructor \<open>Beta\<close> which is used
      to represent a \<open>\<beta>\<close>-redex that has been marked for contraction.  The idea is that
      a term \<open>Beta t u\<close> represents a marked version of the term \<open>App (Lam t) u\<close>.
      Finally, there is a constructor \<open>Nil\<close> which is used to represent the null element
      required for the residuation operation.
    \<close>

    datatype (discs_sels) lambda =
      Nil
    | Var nat
    | Lam lambda
    | App lambda lambda
    | Beta lambda lambda

    text \<open>
      The following notation renders \<open>Beta t u\<close> as a ``marked'' version of \<open>App (Lam t) u\<close>,
      even though the former is a single constructor, whereas the latter contains two
      constructors.
    \<close>

    notation Nil  ("\<^bold>\<sharp>")
    notation Var  ("\<^bold>\<guillemotleft>_\<^bold>\<guillemotright>")
    notation Lam  ("\<^bold>\<lambda>\<^bold>[_\<^bold>]")
    notation App  (infixl "\<^bold>\<circ>" 55)
    notation Beta ("(\<^bold>\<lambda>\<^bold>[_\<^bold>] \<^bold>\<Zspot> _)" [55, 56] 55)

    text \<open>
      The following function computes the set of free variables of a term.
      Note that since variables are represented by numeric indices, this is a set of numbers.
    \<close>

    fun FV
    where "FV \<^bold>\<sharp> = {}"
        | "FV \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = {i}"
        | "FV \<^bold>\<lambda>\<^bold>[t\<^bold>] = (\<lambda>n. n - 1) ` (FV t - {0})"
        | "FV (t \<^bold>\<circ> u) = FV t \<union> FV u"
        | "FV (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = (\<lambda>n. n - 1) ` (FV t - {0}) \<union> FV u"

    subsection "Some Orderings for Induction"

    text \<open>
      We will need to do some simultaneous inductions on pairs and triples of subterms
      of given terms.  We prove the well-foundedness of the associated relations using
      the following size measure.
    \<close>

    fun size :: "lambda \<Rightarrow> nat"
    where "size \<^bold>\<sharp> = 0"
        | "size \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> = 1"
        | "size \<^bold>\<lambda>\<^bold>[t\<^bold>] = size t + 1"
        | "size (t \<^bold>\<circ> u) = size t + size u + 1"
        | "size (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = (size t + 1) + size u + 1"

    lemma wf_if_img_lt:
    fixes r :: "('a * 'a) set" and f :: "'a \<Rightarrow> nat"
    assumes "\<And>x y. (x, y) \<in> r \<Longrightarrow> f x < f y"
    shows "wf r"
      using assms
      by (metis in_measure wf_iff_no_infinite_down_chain wf_measure)

    inductive subterm
    where "\<And>t. subterm t \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        | "\<And>t u. subterm t (t \<^bold>\<circ> u)"
        | "\<And>t u. subterm u (t \<^bold>\<circ> u)"
        | "\<And>t u. subterm t (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
        | "\<And>t u. subterm u (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
        | "\<And>t u v. \<lbrakk>subterm t u; subterm u v\<rbrakk> \<Longrightarrow> subterm t v"

    lemma subterm_implies_smaller:
    shows "subterm t u \<Longrightarrow> size t < size u"
      by (induct rule: subterm.induct) auto

    abbreviation subterm_rel
    where "subterm_rel \<equiv> {(t, u). subterm t u}"

    lemma wf_subterm_rel:
    shows "wf subterm_rel"
      using subterm_implies_smaller wf_if_img_lt
      by (metis case_prod_conv mem_Collect_eq)

    abbreviation subterm_pair_rel
    where "subterm_pair_rel \<equiv> {((t1, t2), u1, u2). subterm t1 u1 \<and> subterm t2 u2}"

    lemma wf_subterm_pair_rel:
    shows "wf subterm_pair_rel"
      using subterm_implies_smaller
            wf_if_img_lt [of subterm_pair_rel "\<lambda>(t1, t2). max (size t1) (size t2)"]
      by fastforce

    abbreviation subterm_triple_rel
    where "subterm_triple_rel \<equiv>
           {((t1, t2, t3), u1, u2, u3). subterm t1 u1 \<and> subterm t2 u2 \<and> subterm t3 u3}"

    lemma wf_subterm_triple_rel:
    shows "wf subterm_triple_rel"
      using subterm_implies_smaller
            wf_if_img_lt [of subterm_triple_rel
                             "\<lambda>(t1, t2, t3). max (max (size t1) (size t2)) (size t3)"]
      by fastforce

    lemma subterm_lemmas:
    shows "subterm t \<^bold>\<lambda>\<^bold>[t\<^bold>]"
    and "subterm t (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) \<and> subterm u (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u)"
    and "subterm t (t \<^bold>\<circ> u) \<and> subterm u (t \<^bold>\<circ> u)"
    and "subterm t (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<and> subterm u (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
      by (metis subterm.simps)+

    subsection "Arrows and Identities"

    text \<open>
      Here we define some special classes of terms.
      An ``arrow'' is a term that contains no occurrences of \<open>Nil\<close>.
      An ``identity'' is an arrow that contains no occurrences of \<open>Beta\<close>.
      It will be important for the commutation of substitution and residuation later on
      that substitution not be used in a way that could create any marked redexes;
      for example, we don't want the substitution of \<open>Lam (Var 0)\<close> for \<open>Var 0\<close> in an
      application \<open>App (Var 0) (Var 0)\<close> to create a new ``marked'' redex.
      The use of the separate constructor \<open>Beta\<close> for marked redexes automatically avoids this.
    \<close>

    fun Arr
    where "Arr \<^bold>\<sharp> = False"
        | "Arr \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> = True"
        | "Arr \<^bold>\<lambda>\<^bold>[t\<^bold>] = Arr t"
        | "Arr (t \<^bold>\<circ> u) = (Arr t \<and> Arr u)"
        | "Arr (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = (Arr t \<and> Arr u)"

    lemma Arr_not_Nil:
    assumes "Arr t"
    shows "t \<noteq> \<^bold>\<sharp>"
      using assms by auto

    fun Ide
    where "Ide \<^bold>\<sharp> = False"
        | "Ide \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> = True"
        | "Ide \<^bold>\<lambda>\<^bold>[t\<^bold>] = Ide t"
        | "Ide (t \<^bold>\<circ> u) = (Ide t \<and> Ide u)"
        | "Ide (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = False"

    lemma Ide_implies_Arr:
    shows "Ide t \<Longrightarrow> Arr t"
      by (induct t) auto

    lemma ArrE [elim]:
    assumes "Arr t"
    and "\<And>i. t = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> \<Longrightarrow> T"
    and "\<And>u. t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<Longrightarrow> T"
    and "\<And>u v. t = u \<^bold>\<circ> v \<Longrightarrow> T"
    and "\<And>u v. t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v \<Longrightarrow> T"
    shows T
      using assms
      by (cases t) auto

    subsection "Raising Indices"

    text \<open>
      For substitution, we need to be able to raise the indices of all free variables
      in a subterm by a specified amount.  To do this recursively, we need to keep track
      of the depth of nesting of \<open>\<lambda>\<close>'s and only raise the indices of variables that are
      already greater than or equal to that depth, as these are the variables that are free
      in the current context.  This leads to defining a function \<open>Raise\<close> that has two arguments:
      the depth threshold \<open>d\<close> and the increment \<open>n\<close> to be added to indices above that threshold.
    \<close>

    fun Raise
    where "Raise _ _ \<^bold>\<sharp> = \<^bold>\<sharp>"
        | "Raise d n \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = (if i \<ge> d then \<^bold>\<guillemotleft>i+n\<^bold>\<guillemotright> else \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>)"
        | "Raise d n \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[Raise (Suc d) n t\<^bold>]"
        | "Raise d n (t \<^bold>\<circ> u) = Raise d n t \<^bold>\<circ> Raise d n u"
        | "Raise d n (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = \<^bold>\<lambda>\<^bold>[Raise (Suc d) n t\<^bold>] \<^bold>\<Zspot> Raise d n u"

    text \<open>
      Ultimately, the definition of substitution will only directly involve the function
      that raises all indices of variables that are free in the outermost context;
      in a term, so we introduce an abbreviation for this special case.
    \<close>

    abbreviation raise
    where "raise == Raise 0"

    lemma size_Raise:
    shows "\<And>d. size (Raise d n t) = size t"
      by (induct t) auto

    lemma Raise_not_Nil:
    assumes "t \<noteq> \<^bold>\<sharp>"
    shows "Raise d n t \<noteq> \<^bold>\<sharp>"
      using assms
      by (cases t) auto

    lemma FV_Raise:
    shows "FV (Raise d n t) = (\<lambda>x. if x \<ge> d then x + n else x) ` FV t"
      apply (induct t arbitrary: d n)
          apply auto[3]
            apply force
           apply force
          apply force
         apply force
        apply force
    proof -
      fix t u d n
      assume ind1: "\<And>d n. FV (Raise d n t) = (\<lambda>x. if d \<le> x then x + n else x) ` FV t"
      assume ind2: "\<And>d n. FV (Raise d n u) = (\<lambda>x. if d \<le> x then x + n else x) ` FV u"
      have "FV (Raise d n (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)) = 
            (\<lambda>x. x - Suc 0) ` ((\<lambda>x. x + n) `
              (FV t \<inter> {x. Suc d \<le> x}) \<union> FV t \<inter> {x. \<not> Suc d \<le> x} - {0}) \<union>
            ((\<lambda>x. x + n) ` (FV u \<inter> {x. d \<le> x}) \<union> FV u \<inter> {x. \<not> d \<le> x})"
        using ind1 ind2 by simp
      also have "... = (\<lambda>x. if d \<le> x then x + n else x) ` FV (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
        by auto force+
      finally show "FV (Raise d n (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)) =
                    (\<lambda>x. if d \<le> x then x + n else x) ` FV (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
        by blast
    qed

    lemma Arr_Raise:
    shows "Arr t \<longleftrightarrow> Arr (Raise d n t)"
      using FV_Raise
      by (induct t arbitrary: d n) auto

    lemma Ide_Raise:
    shows "Ide t \<longleftrightarrow> Ide (Raise d n t)"
      by (induct t arbitrary: d n) auto

    lemma Raise_0:
    shows "Raise d 0 t = t"
      by (induct t arbitrary: d) auto

    lemma Raise_Suc:
    shows "Raise d (Suc n) t = Raise d 1 (Raise d n t)"
      by (induct t arbitrary: d n) auto

    lemma Raise_Var:
    shows "Raise d n \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>if i < d then i else i + n\<^bold>\<guillemotright>"
      by auto

    text \<open>
      The following development of the properties of raising indices, substitution, and
      residuation has benefited greatly from the previous work by Huet \<^cite>\<open>"huet-residual-theory"\<close>.
      In particular, it was very helpful to have correct statements of various lemmas
      available, rather than having to reconstruct them.
    \<close>

    lemma Raise_plus:
    shows "Raise d (m + n) t = Raise (d + m) n (Raise d m t)"
      by (induct t arbitrary: d m n) auto

    lemma Raise_plus':
    shows "\<lbrakk>d' \<le> d + n; d \<le> d'\<rbrakk> \<Longrightarrow> Raise d (m + n) t = Raise d' m (Raise d n t)"
      by (induct t arbitrary: n m d d') auto

    lemma Raise_Raise:
    shows "i \<le> n \<Longrightarrow> Raise i p (Raise n k t) = Raise (p + n) k (Raise i p t)"
      by (induct t arbitrary: i k n p) auto

    lemma raise_plus:
    shows "d \<le> n \<Longrightarrow> raise (m + n) t = Raise d m (raise n t)"
      using Raise_plus' by auto

    lemma raise_Raise:
    shows "raise p (Raise n k t) = Raise (p + n) k (raise p t)"
      by (simp add: Raise_Raise)

    lemma Raise_inj:
    shows "Raise d n t = Raise d n u \<Longrightarrow> t = u"
    proof (induct t arbitrary: d n u)
      show "\<And>d n u. Raise d n \<^bold>\<sharp> = Raise d n u \<Longrightarrow> \<^bold>\<sharp> = u"
        by (metis Raise.simps(1) Raise_not_Nil)
      show "\<And>x d n. Raise d n \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = Raise d n u \<Longrightarrow> \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = u" for u
        using Raise_Var
        apply (cases u, auto)
        by (metis add_lessD1 add_right_imp_eq)
      show "\<And>t d n. \<lbrakk>\<And>d n u'. Raise d n t = Raise d n u' \<Longrightarrow> t = u';
                      Raise d n \<^bold>\<lambda>\<^bold>[t\<^bold>] = Raise d n u\<rbrakk>
                        \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t\<^bold>] = u"
        for u
        apply (cases u, auto)
        by (metis lambda.distinct(9))
      show "\<And>t1 t2 d n. \<lbrakk>\<And>d n u'. Raise d n t1 = Raise d n u' \<Longrightarrow> t1 = u';
                         \<And>d n u'. Raise d n t2 = Raise d n u' \<Longrightarrow> t2 = u';
                         Raise d n (t1 \<^bold>\<circ> t2) = Raise d n u\<rbrakk>
                           \<Longrightarrow> t1 \<^bold>\<circ> t2 = u"
        for u
        apply (cases u, auto)
        by (metis lambda.distinct(11))
      show "\<And>t1 t2 d n. \<lbrakk>\<And>d n u'. Raise d n t1 = Raise d n u' \<Longrightarrow> t1 = u';
                         \<And>d n u'. Raise d n t2 = Raise d n u' \<Longrightarrow> t2 = u';
                         Raise d n (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) = Raise d n u\<rbrakk>
                           \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 = u"
        for u
        apply (cases u, auto)
        by (metis lambda.distinct(13))
    qed

    subsection "Substitution"

    text \<open>
      Following \<^cite>\<open>"huet-residual-theory"\<close>, we now define a generalized substitution operation
      with adjustment of indices.  The ultimate goal is to define the result of contraction
      of a marked redex \<open>Beta t u\<close> to be \<open>subst u t\<close>.  However, to be able to give a proper
      recursive definition of \<open>subst\<close>, we need to introduce a parameter \<open>n\<close> to keep track of the
      depth of nesting of \<open>Lam\<close>'s as we descend into the the term \<open>t\<close>.  So, instead of \<open>subst u t\<close>
      simply substituting \<open>u\<close> for occurrences of \<open>Var 0\<close>, \<open>Subst n u t\<close> will be substituting
      for occurrences of \<open>Var n\<close>, and the term \<open>u\<close> will have the indices of its free variables
      raised by \<open>n\<close> before replacing \<open>Var n\<close>.  In addition, any variables in \<open>t\<close> that have
      indices greater than \<open>n\<close> will have these indices lowered by one, to account for the
      outermost \<open>Lam\<close> that is being removed by the contraction.  We can then define
      \<open>subst u t\<close> to be \<open>Subst 0 u t\<close>.
    \<close>

    fun Subst
    where "Subst _ _ \<^bold>\<sharp> = \<^bold>\<sharp>"
        | "Subst n v \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = (if n < i then \<^bold>\<guillemotleft>i-1\<^bold>\<guillemotright> else if n = i then raise n v else \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>)"
        | "Subst n v \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[Subst (Suc n) v t\<^bold>]"
        | "Subst n v (t \<^bold>\<circ> u) = Subst n v t \<^bold>\<circ> Subst n v u"
        | "Subst n v (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = \<^bold>\<lambda>\<^bold>[Subst (Suc n) v t\<^bold>] \<^bold>\<Zspot> Subst n v u"

    abbreviation subst
    where "subst \<equiv> Subst 0"

    lemma Subst_Nil:
    shows "Subst n v \<^bold>\<sharp> = \<^bold>\<sharp>"
      by (cases "v = \<^bold>\<sharp>") auto

    lemma Subst_not_Nil:
    assumes "v \<noteq> \<^bold>\<sharp>" and "t \<noteq> \<^bold>\<sharp>"
    shows "t \<noteq> \<^bold>\<sharp> \<Longrightarrow> Subst n v t \<noteq> \<^bold>\<sharp>"
      using assms Raise_not_Nil
      by (induct t) auto

    text \<open>
      The following expression summarizes how the set of free variables of a term \<open>Subst d u t\<close>,
      obtained by substituting \<open>u\<close> into \<open>t\<close> at depth \<open>d\<close>, relates to the sets of free variables
      of \<open>t\<close> and \<open>u\<close>.  This expression is not used in the subsequent formal development,
      but it has been left here as an aid to understanding.
    \<close>

    abbreviation FVS
    where "FVS d v t \<equiv> (FV t \<inter> {x. x < d}) \<union>
                        (\<lambda>x. x - 1) ` {x. x > d \<and> x \<in> FV t} \<union>
                        (\<lambda>x. x + d) ` {x. d \<in> FV t \<and> x \<in> FV v}"

    lemma FV_Subst:
    shows "FV (Subst d v t) = FVS d v t"
    proof (induct t arbitrary: d v)
      have "\<And>d t v. (\<lambda>x. x - 1) ` (FVS (Suc d) v t - {0}) = FVS d v \<^bold>\<lambda>\<^bold>[t\<^bold>]"
      proof -
        fix d t v
        have "FVS d v \<^bold>\<lambda>\<^bold>[t\<^bold>] =
              (\<lambda>x. x - Suc 0) ` (FV t - {0}) \<inter> {x. x < d} \<union>
              (\<lambda>x. x - Suc 0) ` {x. d < x \<and> x \<in> (\<lambda>x. x - Suc 0) ` (FV t - {0})} \<union>
              (\<lambda>x. x + d) ` {x. d \<in> (\<lambda>x. x - Suc 0) ` (FV t - {0}) \<and> x \<in> FV v}"
          by simp
        also have "... = (\<lambda>x. x - 1) ` (FVS (Suc d) v t - {0})"
          by auto force+
        finally show "(\<lambda>x. x - 1) ` (FVS (Suc d) v t - {0}) = FVS d v \<^bold>\<lambda>\<^bold>[t\<^bold>]"
          by metis
      qed
      thus "\<And>d t v. (\<And>d v. FV (Subst d v t) = FVS d v t)
                              \<Longrightarrow> FV (Subst d v \<^bold>\<lambda>\<^bold>[t\<^bold>]) = FVS d v \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        by simp
      have "\<And>t u v d. (\<lambda>x. x - 1) ` (FVS (Suc d) v t - {0}) \<union> FVS d v u = FVS d v (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
      proof -
        fix t u v d
        have "FVS d v (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) =
              ((\<lambda>x. x - Suc 0) ` (FV t - {0}) \<union> FV u) \<inter> {x. x < d} \<union>
              (\<lambda>x. x - Suc 0) ` {x. d < x \<and> (x \<in> (\<lambda>x. x - Suc 0) ` (FV t - {0}) \<or> x \<in> FV u)} \<union>
              (\<lambda>x. x + d) ` {x. (d \<in> (\<lambda>x. x - Suc 0) ` (FV t - {0}) \<or> d \<in> FV u) \<and> x \<in> FV v}"
          by simp
        also have "... = (\<lambda>x. x - 1) ` (FVS (Suc d) v t - {0}) \<union> FVS d v u"
          by force
        finally show "(\<lambda>x. x - 1) ` (FVS (Suc d) v t - {0}) \<union> FVS d v u = FVS d v (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
          by metis
      qed
      thus "\<And>t u v d. \<lbrakk>\<And>d v. FV (Subst d v t) = FVS d v t;
                       \<And>d v. FV (Subst d v u) = FVS d v u\<rbrakk>
                            \<Longrightarrow> FV (Subst d v (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)) = FVS d v (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
        by simp
    qed (auto simp add: FV_Raise)

    lemma Arr_Subst:
    assumes "Arr v"
    shows "Arr t \<Longrightarrow> Arr (Subst n v t)"
      using assms Arr_Raise FV_Subst
      by (induct t arbitrary: n) auto

    lemma vacuous_Subst:
    shows "\<lbrakk>Arr v; i \<notin> FV t\<rbrakk> \<Longrightarrow> Raise i 1 (Subst i v t) = t"
      apply (induct t arbitrary: i v, auto)
      by force+

    lemma Ide_Subst_iff:
    shows "Ide (Subst n v t) \<longleftrightarrow> Ide t \<and> (n \<in> FV t \<longrightarrow> Ide v)"
      using Ide_Raise vacuous_Subst
      apply (induct t arbitrary: n)
          apply auto[5]
       apply fastforce
      by (metis Diff_empty Diff_insert0 One_nat_def diff_Suc_1 image_iff insertE
                insert_Diff nat.distinct(1))

    lemma Ide_Subst:
    shows "\<lbrakk>Ide t; Ide v\<rbrakk> \<Longrightarrow> Ide (Subst n v t)"
      using Ide_Raise
      by (induct t arbitrary: n) auto

    lemma Raise_Subst:
    shows "Raise (p + n) k (Subst p v t) = Subst p (Raise n k v) (Raise (Suc (p + n)) k t)"
      using raise_Raise
      apply (induct t arbitrary: v k n p, auto)
      by (metis add_Suc)+

    lemma Raise_Subst':
    assumes "t \<noteq> \<^bold>\<sharp>"
    shows "\<lbrakk>v \<noteq> \<^bold>\<sharp>; k \<le> n\<rbrakk> \<Longrightarrow> Raise k p (Subst n v t) = Subst (p + n) v (Raise k p t)"
      using assms raise_plus
      apply (induct t arbitrary: v k n p, auto)
          apply (metis Raise.simps(1) Subst_Nil Suc_le_mono add_Suc_right)
         apply fastforce
        apply fastforce
       apply (metis Raise.simps(1) Subst_Nil Suc_le_mono add_Suc_right)
      by fastforce

    lemma Raise_subst:
    shows "Raise n k (subst v t) = subst (Raise n k v) (Raise (Suc n) k t)"
      using Raise_0
      apply (induct t arbitrary: v k n, auto)
      by (metis One_nat_def Raise_Subst plus_1_eq_Suc)+

    lemma raise_Subst:
    assumes "t \<noteq> \<^bold>\<sharp>"
    shows "v \<noteq> \<^bold>\<sharp> \<Longrightarrow> raise p (Subst n v t) = Subst (p + n) v (raise p t)"
      using assms Raise_plus raise_Raise Raise_Subst'
      apply (induct t arbitrary: v n p)
      by (meson zero_le)+

    lemma Subst_Raise:
    shows "\<lbrakk>v \<noteq> \<^bold>\<sharp>; d \<le> m; m \<le> n + d\<rbrakk> \<Longrightarrow> Subst m v (Raise d (Suc n) t) = Raise d n t"
      by (induct t arbitrary: v m n d) auto

    lemma Subst_raise:
    shows "\<lbrakk>v \<noteq> \<^bold>\<sharp>; m \<le> n\<rbrakk> \<Longrightarrow> Subst m v (raise (Suc n) t) = raise n t"
      using Subst_Raise
      by (induct t arbitrary: v m n) auto

    lemma Subst_Subst:
    shows "\<lbrakk>v \<noteq> \<^bold>\<sharp>; w \<noteq> \<^bold>\<sharp>\<rbrakk> \<Longrightarrow>
             Subst (m + n) w (Subst m v t) = Subst m (Subst n w v) (Subst (Suc (m + n)) w t)"
      using Raise_0 raise_Subst Subst_not_Nil Subst_raise
      apply (induct t arbitrary: v w m n, auto)
      by (metis add_Suc)+

    text \<open>
      The Substitution Lemma, as given by Huet \<^cite>\<open>"huet-residual-theory"\<close>.
    \<close>

    lemma substitution_lemma:
    shows "\<lbrakk>v \<noteq> \<^bold>\<sharp>; w \<noteq> \<^bold>\<sharp>\<rbrakk> \<Longrightarrow> Subst n v (subst w t) = subst (Subst n v w) (Subst (Suc n) v t)"
      by (metis Subst_Subst add_0)

    section "Lambda-Calculus as an RTS"

    subsection "Residuation"

    text \<open>
      We now define residuation on terms.
      Residuation is an operation which, when defined for terms \<open>t\<close> and \<open>u\<close>,
      produces terms \<open>t \ u\<close> and \<open>u \ t\<close> that represent, respectively, what remains
      of the reductions of \<open>t\<close> after performing the reductions in \<open>u\<close>,
      and what remains of the reductions of \<open>u\<close> after performing the reductions in \<open>t\<close>.

      The definition ensures that, if residuation is defined for two terms, then those
      terms in must be arrows that are \emph{coinitial} (\emph{i.e.}~they are the same
      after erasing marks on redexes).  The residual \<open>t \ u\<close> then has marked redexes at
      positions corresponding to redexes that were originally marked in \<open>t\<close> and that
      were not contracted by any of the reductions of \<open>u\<close>.

      This definition has also benefited from the presentation in \<^cite>\<open>"huet-residual-theory"\<close>.
    \<close>

    fun resid  (infix "\\" 70)
    where "\<^bold>\<guillemotleft>i\<^bold>\<guillemotright> \\ \<^bold>\<guillemotleft>i'\<^bold>\<guillemotright> = (if i = i' then \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> else \<^bold>\<sharp>)"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ \<^bold>\<lambda>\<^bold>[t'\<^bold>] = (if t \\ t' = \<^bold>\<sharp> then \<^bold>\<sharp> else \<^bold>\<lambda>\<^bold>[t \\ t'\<^bold>])"
        | "(t \<^bold>\<circ> u) \\ (t'\<^bold>\<circ> u') = (if t \\ t' = \<^bold>\<sharp> \<or> u \\ u' = \<^bold>\<sharp> then \<^bold>\<sharp> else (t \\ t') \<^bold>\<circ> (u \\ u'))"
        | "(\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \\ (\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u') = (if t \\ t' = \<^bold>\<sharp> \<or> u \\ u' = \<^bold>\<sharp> then \<^bold>\<sharp> else subst (u \\ u') (t \\ t'))"
        | "(\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) \\ (\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u') = (if t \\ t' = \<^bold>\<sharp> \<or> u \\ u' = \<^bold>\<sharp> then \<^bold>\<sharp> else subst (u \\ u') (t \\ t'))"
        | "(\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \\ (\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<circ> u') = (if t \\ t' = \<^bold>\<sharp> \<or> u \\ u' = \<^bold>\<sharp> then \<^bold>\<sharp> else \<^bold>\<lambda>\<^bold>[t \\ t'\<^bold>] \<^bold>\<Zspot> (u \\ u'))"
        | "resid _  _ = \<^bold>\<sharp>"

    text \<open>
      Terms t and u are \emph{consistent} if residuation is defined for them.
    \<close>

    abbreviation Con  (infix "\<frown>" 50)
    where "Con t u \<equiv> resid t u \<noteq> \<^bold>\<sharp>"

    lemma ConE [elim]:
    assumes "t \<frown> t'"
    and "\<And>i. \<lbrakk>t = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>; t' = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>; resid t t' = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>\<rbrakk> \<Longrightarrow> T"
    and "\<And>u u'. \<lbrakk>t = \<^bold>\<lambda>\<^bold>[u\<^bold>]; t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>]; u \<frown> u'; t \\ t' = \<^bold>\<lambda>\<^bold>[u \\ u'\<^bold>]\<rbrakk> \<Longrightarrow> T"
    and "\<And>u v u' v'. \<lbrakk>t = u \<^bold>\<circ> v; t' = u' \<^bold>\<circ> v'; u \<frown> u'; v \<frown> v';
                      t \\ t' = (u \\ u') \<^bold>\<circ> (v \\ v')\<rbrakk> \<Longrightarrow> T"
    and "\<And>u v u' v'. \<lbrakk>t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v; t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<Zspot> v'; u \<frown> u'; v \<frown> v';
                      t \\ t' = subst (v \\ v') (u \\ u')\<rbrakk> \<Longrightarrow> T"
    and "\<And>u v u' v'. \<lbrakk>t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<circ> v; t' = Beta u' v'; u \<frown> u'; v \<frown> v';
                      t \\ t' = subst (v \\ v') (u \\ u')\<rbrakk> \<Longrightarrow> T"
    and "\<And>u v u' v'. \<lbrakk>t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v; t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<circ> v'; u \<frown> u'; v \<frown> v';
                      t \\ t' = \<^bold>\<lambda>\<^bold>[u \\ u'\<^bold>] \<^bold>\<Zspot> (v \\ v')\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms
      apply (cases t; cases t')
                     apply simp_all
           apply metis
          apply metis
         apply metis
        apply (cases "un_App1 t", simp_all)
        apply metis
       apply (cases "un_App1 t'", simp_all)
       apply metis
      by metis

    text \<open>
      A term can only be consistent with another if both terms are ``arrows''.
    \<close>

    lemma Con_implies_Arr1:
    shows "t \<frown> u \<Longrightarrow> Arr t"
    proof (induct t arbitrary: u)
      fix u v t'
      assume ind1: "\<And>u'. u \<frown> u' \<Longrightarrow> Arr u"
      assume ind2: "\<And>v'. v \<frown> v' \<Longrightarrow> Arr v"
      show "u \<^bold>\<circ> v \<frown> t' \<Longrightarrow> Arr (u \<^bold>\<circ> v)"
        using ind1 ind2
        apply (cases t', simp_all)
         apply metis
        apply (cases u, simp_all)
        by (metis lambda.distinct(3) resid.simps(2))
      show "\<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v \<frown> t' \<Longrightarrow> Arr (\<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v)"
        using ind1 ind2
        apply (cases t', simp_all)
         apply (cases "un_App1 t'", simp_all)
        by metis+
    qed auto

    lemma Con_implies_Arr2:
    shows "t \<frown> u \<Longrightarrow> Arr u"
    proof (induct u arbitrary: t)
      fix u' v' t
      assume ind1: "\<And>u. u \<frown> u' \<Longrightarrow> Arr u'"
      assume ind2: "\<And>v. v \<frown> v' \<Longrightarrow> Arr v'"
      show "t \<frown> u' \<^bold>\<circ> v' \<Longrightarrow> Arr (u' \<^bold>\<circ> v')"
        using ind1 ind2
        apply (cases t, simp_all)
         apply metis
        apply (cases u', simp_all)
        by (metis lambda.distinct(3) resid.simps(2))
      show "t \<frown> (\<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<Zspot> v') \<Longrightarrow> Arr (\<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<Zspot> v')"
        using ind1 ind2
        apply (cases t, simp_all)
        apply (cases "un_App1 t", simp_all)
        by metis+
    qed auto

    lemma ConD:
    shows "t \<^bold>\<circ> u \<frown> t' \<^bold>\<circ> u' \<Longrightarrow> t \<frown> t' \<and> u \<frown> u'"
    and "\<^bold>\<lambda>\<^bold>[v\<^bold>] \<^bold>\<Zspot> u \<frown> \<^bold>\<lambda>\<^bold>[v'\<^bold>] \<^bold>\<Zspot> u' \<Longrightarrow> \<^bold>\<lambda>\<^bold>[v\<^bold>] \<frown> \<^bold>\<lambda>\<^bold>[v'\<^bold>] \<and> u \<frown> u'"
    and "\<^bold>\<lambda>\<^bold>[v\<^bold>] \<^bold>\<Zspot> u \<frown> t' \<^bold>\<circ> u' \<Longrightarrow> \<^bold>\<lambda>\<^bold>[v\<^bold>] \<frown> t' \<and> u \<frown> u'"
    and "t \<^bold>\<circ> u \<frown> \<^bold>\<lambda>\<^bold>[v'\<^bold>] \<^bold>\<Zspot> u' \<Longrightarrow> t \<frown> \<^bold>\<lambda>\<^bold>[v'\<^bold>] \<and> u \<frown> u'"
      by auto

    text \<open>
      Residuation on consistent terms preserves arrows.
    \<close>

    lemma Arr_resid:
    shows "t \<frown> u \<Longrightarrow> Arr (t \\ u)"
    proof (induct t arbitrary: u)
      fix t1 t2 u
      assume ind1: "\<And>u. t1 \<frown> u \<Longrightarrow> Arr (t1 \\ u)"
      assume ind2: "\<And>u. t2 \<frown> u \<Longrightarrow> Arr (t2 \\ u)"
      show "t1 \<^bold>\<circ> t2 \<frown> u \<Longrightarrow> Arr ((t1 \<^bold>\<circ> t2) \\ u)"
        using ind1 ind2 Arr_Subst
        apply (cases u, auto)
        apply (cases t1, auto)
        by (metis Arr.simps(3) ConD(2) resid.simps(2) resid.simps(4))
      show "\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<frown> u \<Longrightarrow> Arr ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u)"
        using ind1 ind2 Arr_Subst
        by (cases u) auto
    qed auto

    subsection "Source and Target"

    text \<open>
      Here we give syntactic versions of the \emph{source} and \emph{target} of a term.
      These will later be shown to agree (on arrows) with the versions derived from the residuation.
      The underlying idea here is that a term stands for a reduction sequence in which
      all marked redexes (corresponding to instances of the constructor \<open>Beta\<close>) are contracted
      in a bottom-up fashion.  A term without any marked redexes stands for an empty reduction
      sequence; such terms will be shown to be the identities derived from the residuation.
      The source of term is the identity obtained by erasing all markings; that is, by replacing
      all subterms of the form \<open>Beta t u\<close> by \<open>App (Lam t) u\<close>.  The target of a term is the
      identity that is the result of contracting all the marked redexes.
    \<close>

    fun Src
    where "Src \<^bold>\<sharp> = \<^bold>\<sharp>"
        | "Src \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>"
        | "Src \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[Src t\<^bold>]"
        | "Src (t \<^bold>\<circ> u) = Src t \<^bold>\<circ> Src u"
        | "Src (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = \<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<circ> Src u"

    fun Trg
    where "Trg \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>"
        | "Trg \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[Trg t\<^bold>]"
        | "Trg (t \<^bold>\<circ> u) = Trg t \<^bold>\<circ> Trg u"
        | "Trg (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = subst (Trg u) (Trg t)"
        | "Trg _ = \<^bold>\<sharp>"

    lemma Ide_Src:
    shows "Arr t \<Longrightarrow> Ide (Src t)"
      by (induct t) auto

    lemma Ide_iff_Src_self:
    assumes "Arr t"
    shows "Ide t \<longleftrightarrow> Src t = t"
      using assms Ide_Src
      by (induct t) auto

    lemma Arr_Src [simp]:
    assumes "Arr t"
    shows "Arr (Src t)"
      using assms Ide_Src Ide_implies_Arr by blast

    lemma Con_Src:
    shows "\<lbrakk>size t + size u \<le> n; t \<frown> u\<rbrakk> \<Longrightarrow> Src t \<frown> Src u"
      by (induct n arbitrary: t u) auto

    lemma Src_eq_iff:
    shows "Src \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = Src \<^bold>\<guillemotleft>i'\<^bold>\<guillemotright> \<longleftrightarrow> i = i'"
    and "Src (t \<^bold>\<circ> u) = Src (t' \<^bold>\<circ> u') \<longleftrightarrow> Src t = Src t' \<and> Src u = Src u'"
    and "Src (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = Src (\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u') \<longleftrightarrow> Src t = Src t' \<and> Src u = Src u'"
    and "Src (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) = Src (\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u') \<longleftrightarrow> Src t = Src t' \<and> Src u = Src u'"
      by auto

    lemma Src_Raise:
    shows "Src (Raise d n t) = Raise d n (Src t)"
      by (induct t arbitrary: d) auto

    lemma Src_Subst [simp]:
    shows "\<lbrakk>Arr t; Arr u\<rbrakk> \<Longrightarrow> Src (Subst d t u) = Subst d (Src t) (Src u)"
      using Src_Raise
      by (induct u arbitrary: d X) auto

    lemma Ide_Trg:
    shows "Arr t \<Longrightarrow> Ide (Trg t)"
      using Ide_Subst
      by (induct t) auto

    lemma Ide_iff_Trg_self:
    shows "Arr t \<Longrightarrow> Ide t \<longleftrightarrow> Trg t = t"
      apply (induct t)
          apply auto
      by (metis Ide.simps(5) Ide_Subst Ide_Trg)+

    lemma Arr_Trg [simp]:
    assumes "Arr X"
    shows "Arr (Trg X)"
      using assms Ide_Trg Ide_implies_Arr by blast

    lemma Src_Src [simp]:
    assumes "Arr t"
    shows "Src (Src t) = Src t"
      using assms Ide_Src Ide_iff_Src_self Ide_implies_Arr by blast

    lemma Trg_Src [simp]:
    assumes "Arr t"
    shows "Trg (Src t) = Src t"
      using assms Ide_Src Ide_iff_Trg_self Ide_implies_Arr by blast

    lemma Trg_Trg [simp]:
    assumes "Arr t"
    shows "Trg (Trg t) = Trg t"
      using assms Ide_Trg Ide_iff_Trg_self Ide_implies_Arr by blast

    lemma Src_Trg [simp]:
    assumes "Arr t"
    shows "Src (Trg t) = Trg t"
      using assms Ide_Trg Ide_iff_Src_self Ide_implies_Arr by blast

    text \<open>
      Two terms are syntactically \emph{coinitial} if they are arrows with the same source;
      that is, they represent two reductions from the same starting term.
    \<close>

    abbreviation Coinitial
    where "Coinitial t u \<equiv> Arr t \<and> Arr u \<and> Src t = Src u"

    text \<open>
      We now show that terms are consistent if and only if they are coinitial.
    \<close>

    lemma Coinitial_cases:
    assumes "Arr t" and "Arr t'" and "Src t = Src t'"
    shows "(t = \<^bold>\<sharp> \<and> t' = \<^bold>\<sharp>) \<or>
           (\<exists>x. t = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<and> t' = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>) \<or>
           (\<exists>u u'. t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<and> t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>]) \<or>
           (\<exists>u v u' v'. t = u \<^bold>\<circ> v \<and> t' = u' \<^bold>\<circ> v') \<or>
           (\<exists>u v u' v'. t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v \<and> t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<Zspot> v') \<or>
           (\<exists>u v u' v'. t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<circ> v \<and> t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<Zspot> v') \<or>
           (\<exists>u v u' v'. t = \<^bold>\<lambda>\<^bold>[u\<^bold>] \<^bold>\<Zspot> v \<and> t' = \<^bold>\<lambda>\<^bold>[u'\<^bold>] \<^bold>\<circ> v')"
      using assms
      by (cases t; cases t') auto

    lemma Con_implies_Coinitial_ind:
    shows "\<lbrakk>size t + size u \<le> n; t \<frown> u\<rbrakk> \<Longrightarrow> Coinitial t u"
      using Con_implies_Arr1 Con_implies_Arr2
      by (induct n arbitrary: t u) auto

    lemma Coinitial_implies_Con_ind:
    shows "\<lbrakk>size (Src t) \<le> n; Coinitial t u\<rbrakk> \<Longrightarrow> t \<frown> u"
    proof (induct n arbitrary: t u)
      show "\<And>t u. \<lbrakk>size (Src t) \<le> 0; Coinitial t u\<rbrakk> \<Longrightarrow> t \<frown> u"
        by auto
      fix n t u
      assume Coinitial: "Coinitial t u"
      assume n: "size (Src t) \<le> Suc n"
      assume ind: "\<And>t u. \<lbrakk>size (Src t) \<le> n; Coinitial t u\<rbrakk> \<Longrightarrow> t \<frown> u"
      show "t \<frown> u"
        using n ind Coinitial Coinitial_cases [of t u] Subst_not_Nil by auto
    qed

    lemma Coinitial_iff_Con:
    shows "Coinitial t u \<longleftrightarrow> t \<frown> u"
      using Coinitial_implies_Con_ind Con_implies_Coinitial_ind by blast

    lemma Coinitial_Raise_Raise:
    shows "Coinitial t u \<Longrightarrow> Coinitial (Raise d n t) (Raise d n u)"
      using Arr_Raise Src_Raise
      apply (induct t arbitrary: d n u, auto)
      by (metis Raise.simps(3-4))

    lemma Con_sym:
    shows "t \<frown> u \<longleftrightarrow> u \<frown> t"
      by (metis Coinitial_iff_Con)

    lemma ConI [intro, simp]:
    assumes "Arr t" and "Arr u" and "Src t = Src u"
    shows "Con t u"
      using assms Coinitial_iff_Con by blast

    lemma Con_Arr_Src [simp]:
    assumes "Arr t"
    shows "t \<frown> Src t" and "Src t \<frown> t"
      using assms
      by (auto simp add: Ide_Src Ide_implies_Arr)

    lemma resid_Arr_self:
    shows "Arr t \<Longrightarrow> t \\ t = Trg t"
      by (induct t) auto

    text \<open>
      The following result is not used in the formal development that follows,
      but it requires some proof and might eventually be useful.
    \<close>

    lemma finite_branching:
    shows "Ide a \<Longrightarrow> finite {t. Arr t \<and> Src t = a}"
    proof (induct a)
      show "Ide \<^bold>\<sharp> \<Longrightarrow> finite {t. Arr t \<and> Src t = \<^bold>\<sharp>}"
        by simp
      fix x
      have "\<And>t. Src t = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<longleftrightarrow> t = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        using Src.elims by blast
      thus "finite {t. Arr t \<and> Src t = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>}"
        by simp
      next
      fix a
      assume a: "Ide \<^bold>\<lambda>\<^bold>[a\<^bold>]"
      assume ind: "Ide a \<Longrightarrow> finite {t. Arr t \<and> Src t = a}"
      have "{t. Arr t \<and> Src t = \<^bold>\<lambda>\<^bold>[a\<^bold>]} = Lam ` {t. Arr t \<and> Src t = a}"
        using Coinitial_cases by fastforce
      thus "finite {t. Arr t \<and> Src t = \<^bold>\<lambda>\<^bold>[a\<^bold>]}"
        using a ind by simp
      next
      fix a1 a2
      assume ind1: "Ide a1 \<Longrightarrow> finite {t. Arr t \<and> Src t = a1}"
      assume ind2: "Ide a2 \<Longrightarrow> finite {t. Arr t \<and> Src t = a2}"
      assume a: "Ide (\<^bold>\<lambda>\<^bold>[a1\<^bold>] \<^bold>\<Zspot> a2)"
      show "finite {t. Arr t \<and> Src t = \<^bold>\<lambda>\<^bold>[a1\<^bold>] \<^bold>\<Zspot> a2}"
        using a ind1 ind2 by simp
      next
      fix a1 a2
      assume ind1: "Ide a1 \<Longrightarrow> finite {t. Arr t \<and> Src t = a1}"
      assume ind2: "Ide a2 \<Longrightarrow> finite {t. Arr t \<and> Src t = a2}"
      assume a: "Ide (a1 \<^bold>\<circ> a2)"
      have "{t. Arr t \<and> Src t = a1 \<^bold>\<circ> a2} =
            ({t. is_App t} \<inter> ({t. Arr t \<and> Src (un_App1 t) = a1 \<and> Src (un_App2 t) = a2})) \<union>
            ({t. is_Beta t \<and> is_Lam a1} \<inter>
             ({t. Arr t \<and> is_Lam a1 \<and> Src (un_Beta1 t) = un_Lam a1 \<and> Src (un_Beta2 t) = a2}))"
        by fastforce
      have "{t. Arr t \<and> Src t = a1 \<^bold>\<circ> a2} =
            (\<lambda>(t1, t2). t1 \<^bold>\<circ> t2) ` ({t1. Arr t1 \<and> Src t1 = a1} \<times> {t2. Arr t2 \<and> Src t2 = a2}) \<union>
            (\<lambda>(t1, t2). \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) `
              ({t1t2. is_Lam a1} \<inter>
                 {t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
      proof
        show "(\<lambda>(t1, t2). t1 \<^bold>\<circ> t2) ` ({t1. Arr t1 \<and> Src t1 = a1} \<times> {t2. Arr t2 \<and> Src t2 = a2}) \<union>
              (\<lambda>(t1, t2). \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) `
                ({t1t2. is_Lam a1} \<inter>
                   {t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})
                \<subseteq> {t. Arr t \<and> Src t = a1 \<^bold>\<circ> a2}"
          by auto
        show "{t. Arr t \<and> Src t = a1 \<^bold>\<circ> a2}
                \<subseteq> (\<lambda>(t1, t2). t1 \<^bold>\<circ> t2) `
                    ({t1. Arr t1 \<and> Src t1 = a1} \<times> {t2. Arr t2 \<and> Src t2 = a2}) \<union>
                  (\<lambda>(t1, t2). \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) `
                    ({t1t2. is_Lam a1} \<inter>
                       {t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
        proof
          fix t
          assume t: "t \<in> {t. Arr t \<and> Src t = a1 \<^bold>\<circ> a2}"
          have "is_App t \<or> is_Beta t"
            using t by auto
          moreover have "is_App t \<Longrightarrow> t \<in> (\<lambda>(t1, t2). t1 \<^bold>\<circ> t2) `
                                        ({t1. Arr t1 \<and> Src t1 = a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
            using t image_iff is_App_def by fastforce
          moreover have "is_Beta t \<Longrightarrow>
                           t \<in> (\<lambda>(t1, t2). \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) `
                             ({t1t2. is_Lam a1} \<inter>
                                {t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
            using t is_Beta_def by fastforce
          ultimately show "t \<in> (\<lambda>(t1, t2). t1 \<^bold>\<circ> t2) `
                                 ({t1. Arr t1 \<and> Src t1 = a1} \<times> {t2. Arr t2 \<and> Src t2 = a2}) \<union>
                               (\<lambda>(t1, t2). \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) `
                                 ({t1t2. is_Lam a1} \<inter>
                                    {t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
            by blast
        qed
      qed
      moreover have "finite ({t1. Arr t1 \<and> Src t1 = a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
        using a ind1 ind2 Ide.simps(4) by blast
      moreover have "is_Lam a1 \<Longrightarrow>
                     finite ({t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
      proof -
        assume a1: "is_Lam a1"
        have "Ide (un_Lam a1)"
          using a a1 is_Lam_def by force
        have "Lam ` {t1. Arr t1 \<and> Src t1 = un_Lam a1} = {t. Arr t \<and> Src t = a1}"
        proof
          show "Lam ` {t1. Arr t1 \<and> Src t1 = un_Lam a1} \<subseteq> {t. Arr t \<and> Src t = a1}"
            using a1 by fastforce
          show "{t. Arr t \<and> Src t = a1} \<subseteq> Lam ` {t1. Arr t1 \<and> Src t1 = un_Lam a1}"
          proof
            fix t
            assume t: "t \<in> {t. Arr t \<and> Src t = a1}"
            have "is_Lam t"
              using a1 t by auto
            hence "un_Lam t \<in> {t1. Arr t1 \<and> Src t1 = un_Lam a1}"
              using is_Lam_def t by force
            thus "t \<in> Lam ` {t1. Arr t1 \<and> Src t1 = un_Lam a1}"
              by (metis \<open>is_Lam t\<close> lambda.collapse(2) rev_image_eqI)
          qed
        qed
        moreover have "inj Lam"
          using inj_on_def by blast
        ultimately have "finite {t1. Arr t1 \<and> Src t1 = un_Lam a1}"
          by (metis (mono_tags, lifting) Ide.simps(4) a finite_imageD ind1 injD inj_onI)
        moreover have "finite {t2. Arr t2 \<and> Src t2 = a2}"
          using Ide.simps(4) a ind2 by blast
        ultimately
        show "finite ({t1. Arr t1 \<and> Src t1 = un_Lam a1} \<times> {t2. Arr t2 \<and> Src t2 = a2})"
          by blast
      qed
      ultimately show "finite {t. Arr t \<and> Src t = a1 \<^bold>\<circ> a2}"
        using a ind1 ind2 by simp
    qed

    subsection "Residuation and Substitution"

    text \<open>
      We now develop a series of lemmas that involve the interaction of residuation
      and substitution.
    \<close>

    lemma Raise_resid:
    shows "t \<frown> u \<Longrightarrow> Raise k n (t \\ u) = Raise k n t \\ Raise k n u"
    proof -
      (*
       * Note: This proof uses subterm induction because the hypothesis Con t u yields
       * cases in which App and Beta terms are compared, so that the first argument to App
       * needs to be unfolded.
       *)
      let ?P = "\<lambda>(t, u). \<forall>k n. t \<frown> u \<longrightarrow> Raise k n (t \\ u) = Raise k n t \\ Raise k n u"
      have "\<And>t u.
               \<forall>t' u'. ((t', u'), (t, u)) \<in> subterm_pair_rel \<longrightarrow>
                         (\<forall>k n. t' \<frown> u' \<longrightarrow>
                                Raise k n (t' \\ u') = Raise k n t' \\ Raise k n u') \<Longrightarrow>
               (\<And>k n. t \<frown> u \<Longrightarrow> Raise k n (t \\ u) = Raise k n t \\ Raise k n u)"
        using subterm_lemmas Coinitial_iff_Con Coinitial_Raise_Raise Raise_subst by auto
      thus "t \<frown> u \<Longrightarrow> Raise k n (t \\ u) = Raise k n t \\ Raise k n u"
        using wf_subterm_pair_rel wf_induct [of subterm_pair_rel ?P] by blast
    qed

    lemma Con_Raise:
    shows "t \<frown> u \<Longrightarrow> Raise d n t \<frown> Raise d n u"
      by (metis Raise_not_Nil Raise_resid)

    text \<open>
      The following is Huet's Commutation Theorem \<^cite>\<open>"huet-residual-theory"\<close>:
      ``substitution commutes with residuation''.
    \<close>

    lemma resid_Subst:
    assumes "t \<frown> t'" and "u \<frown> u'"
    shows "Subst n t u \\ Subst n t' u' = Subst n (t \\ t') (u \\ u')"
    proof -
      let ?P = "\<lambda>(u, u'). \<forall>n t t'. t \<frown> t' \<and> u \<frown> u' \<longrightarrow>
                                     Subst n t u \\ Subst n t' u' = Subst n (t \\ t') (u \\ u')"
      have "\<And>u u'. \<forall>w w'. ((w, w'), (u, u')) \<in> subterm_pair_rel \<longrightarrow>
                             (\<forall>n v v'. v \<frown> v' \<and> w \<frown> w' \<longrightarrow>
                               Subst n v w \\ Subst n v' w' = Subst n (v \\ v') (w \\ w')) \<Longrightarrow>
                   \<forall>n t t'. t \<frown> t' \<and> u \<frown> u' \<longrightarrow>
                              Subst n t u \\ Subst n t' u' = Subst n (t \\ t') (u \\ u')"
        using subterm_lemmas Raise_resid Subst_not_Nil Con_Raise Raise_subst substitution_lemma
        by auto
      thus ?thesis
        using assms wf_subterm_pair_rel wf_induct [of subterm_pair_rel ?P] by auto
    qed

    lemma Trg_Subst [simp]:
    shows "\<lbrakk>Arr t; Arr u\<rbrakk> \<Longrightarrow> Trg (Subst d t u) = Subst d (Trg t) (Trg u)"
      by (metis Arr_Subst Arr_Trg Arr_not_Nil resid_Arr_self resid_Subst)

    lemma Src_resid:
    shows "t \<frown> u \<Longrightarrow> Src (t \\ u) = Trg u"
    proof (induct u arbitrary: t, auto simp add: Arr_resid)
      fix t t1'
      show "\<And>t2'. \<lbrakk>\<And>t1. t1 \<frown> t1' \<Longrightarrow> Src (t1 \\ t1') = Trg t1';
                   \<And>t2. t2 \<frown> t2' \<Longrightarrow> Src (t2 \\ t2') = Trg t2';
                   t \<frown> t1' \<^bold>\<circ> t2'\<rbrakk>
                      \<Longrightarrow> Src (t \\ (t1' \<^bold>\<circ> t2')) = Trg t1' \<^bold>\<circ> Trg t2'"
        apply (cases t; cases t1')
                            apply auto
        by (metis Src.simps(3) lambda.distinct(3) lambda.sel(2) resid.simps(2))
    qed

    lemma Coinitial_resid_resid:
    assumes "t \<frown> v" and "u \<frown> v"
    shows "Coinitial (t \\ v) (u \\ v)"
      using assms Src_resid Arr_resid Coinitial_iff_Con by presburger

    lemma Con_implies_is_Lam_iff_is_Lam:
    assumes "t \<frown> u"
    shows "is_Lam t \<longleftrightarrow> is_Lam u"
      using assms by auto

    lemma Con_implies_Coinitial3:
    assumes "t \\ v \<frown> u \\ v"
    shows "Coinitial v u" and "Coinitial v t" and "Coinitial u t"
      using assms
      by (metis Coinitial_iff_Con resid.simps(7))+

    text \<open>
      We can now prove L\'{e}vy's ``Cube Lemma'' \<^cite>\<open>"levy"\<close>, which is the key axiom
      for a residuated transition system.
    \<close>

    lemma Cube:
    shows "v \\ t \<frown> u \\ t \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
    proof -
      let ?P = "\<lambda>(t, u, v). v \\ t \<frown> u \\ t \<longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      have "\<And>t u v.
               \<forall>t' u' v'.
                 ((t', u', v'), (t, u, v)) \<in> subterm_triple_rel \<longrightarrow> ?P (t', u', v') \<Longrightarrow>
                   v \\ t \<frown> u \\ t \<longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      proof -
        fix t u v
        assume ind: "\<forall>t' u' v'. 
                       ((t', u', v'), (t, u, v)) \<in> subterm_triple_rel \<longrightarrow> ?P (t', u', v')"
        show "v \\ t \<frown> u \\ t \<longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
        proof (intro impI)
          assume con: "v \\ t \<frown> u \\ t"
          have "Con v t"
            using con by auto
          moreover have "Con u t"
            using con by auto
          ultimately show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
            using subterm_lemmas ind Coinitial_iff_Con Coinitial_resid_resid resid_Subst
            apply (elim ConE [of v t] ConE [of u t])
                                apply simp_all
                    apply metis
                   apply metis
                  apply (cases "un_App1 t"; cases "un_App1 v", simp_all)
                  apply metis
                 apply metis
                apply metis
               apply metis
              apply metis
             apply (cases "un_App1 u", simp_all)
             apply metis
            by metis
        qed
      qed
      hence "?P (t, u, v)"
        using wf_subterm_triple_rel wf_induct [of subterm_triple_rel ?P] by blast
      thus "v \\ t \<frown> u \\ t \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
        by simp
    qed

    subsection "Residuation Determines an RTS"

    text \<open>
      We are now in a position to verify that the residuation operation that we have defined
      satisfies the axioms for a residuated transition system, and that various notions
      which we have defined syntactically above (\emph{e.g.}~arrow, source, target) agree
      with the versions derived abstractly from residuation.
    \<close>

    sublocale partial_magma resid
      apply unfold_locales
      by (metis Arr.simps(1) Coinitial_iff_Con)

    lemma null_char [simp]:
    shows "null = \<^bold>\<sharp>"
      using null_def
      by (metis null_is_zero(2) resid.simps(7))

    sublocale residuation resid
      using null_char Arr_resid Coinitial_iff_Con Cube
      apply (unfold_locales, auto)
      by metis+

    (* TODO: Try to understand when notation is and is not inherited. *)
    notation resid  (infix "\\" 70)

    lemma resid_is_residuation:
    shows "residuation resid"
      ..

    lemma arr_char [iff]:
    shows "arr t \<longleftrightarrow> Arr t"
      using Coinitial_iff_Con arr_def con_def null_char by auto

    lemma ide_char [iff]:
    shows "ide t \<longleftrightarrow> Ide t"
      by (metis Ide_iff_Trg_self Ide_implies_Arr arr_char arr_resid_iff_con ide_def
          resid_Arr_self)

    lemma resid_Arr_Ide:
    shows "\<lbrakk>Ide a; Coinitial t a\<rbrakk> \<Longrightarrow> t \\ a = t"
      using Ide_iff_Src_self
      by (induct t arbitrary: a, auto)

    lemma resid_Ide_Arr:
    shows "\<lbrakk>Ide a; Coinitial a t\<rbrakk> \<Longrightarrow> Ide (a \\ t)"
      by (metis Coinitial_resid_resid ConI Ide_iff_Trg_self cube resid_Arr_Ide resid_Arr_self)

    lemma resid_Arr_Src [simp]:
    assumes "Arr t"
    shows "t \\ Src t = t"
      using assms Ide_Src
      by (simp add: Ide_implies_Arr resid_Arr_Ide)

    lemma resid_Src_Arr [simp]:
    assumes "Arr t"
    shows "Src t \\ t = Trg t"
      using assms
      by (metis (full_types) Con_Arr_Src(2) Con_implies_Arr1 Src_Src Src_resid cube
          resid_Arr_Src resid_Arr_self)

    sublocale rts resid
    proof
      show "\<And>a t. \<lbrakk>ide a; con t a\<rbrakk> \<Longrightarrow> t \\ a = t"
        using ide_char resid_Arr_Ide
        by (metis Coinitial_iff_Con con_def null_char)
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        by (simp add: Ide_Trg resid_Arr_self trg_def)
      show "\<And>a t. \<lbrakk>ide a; con a t\<rbrakk> \<Longrightarrow> ide (resid a t)"
        using ide_char null_char resid_Ide_Arr Coinitial_iff_Con con_def by force
      show "\<And>t u. con t u \<Longrightarrow> \<exists>a. ide a \<and> con a t \<and> con a u"
        by (metis Coinitial_iff_Con Ide_Src Ide_iff_Src_self Ide_implies_Arr con_def
            ide_char null_char)
      show "\<And>t u v. \<lbrakk>ide (resid t u); con u v\<rbrakk> \<Longrightarrow> con (resid t u) (resid v u)"
        by (metis Coinitial_resid_resid ide_char not_arr_null null_char resid_Ide_Arr
                  con_def con_sym ide_implies_arr)
    qed

    lemma is_rts:
    shows "rts resid"
      ..

    lemma sources_char\<^sub>\<Lambda>:
    shows "sources t = (if Arr t then {Src t} else {})"
    proof (cases "Arr t")
      show "\<not> Arr t \<Longrightarrow> ?thesis"
        using arr_char arr_iff_has_source by auto
      assume t: "Arr t"
      have 1: "{Src t} \<subseteq> sources t"
        using t Ide_Src by force
      moreover have "sources t \<subseteq> {Src t}"
        by (metis Coinitial_iff_Con Ide_iff_Src_self ide_char in_sourcesE null_char
                  con_def singleton_iff subsetI)
      ultimately show ?thesis
        using t by auto
    qed

    lemma sources_simp [simp]:
    assumes "Arr t"
    shows "sources t = {Src t}"
      using assms sources_char\<^sub>\<Lambda> by auto

    lemma sources_simps [simp]:
    shows "sources \<^bold>\<sharp> = {}"
    and "sources \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = {\<^bold>\<guillemotleft>x\<^bold>\<guillemotright>}"
    and "arr t \<Longrightarrow> sources \<^bold>\<lambda>\<^bold>[t\<^bold>] = {\<^bold>\<lambda>\<^bold>[Src t\<^bold>]}"
    and "\<lbrakk>arr t; arr u\<rbrakk> \<Longrightarrow> sources (t \<^bold>\<circ> u) = {Src t \<^bold>\<circ> Src u}"
    and "\<lbrakk>arr t; arr u\<rbrakk> \<Longrightarrow> sources (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = {\<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<circ> Src u}"
      using sources_char\<^sub>\<Lambda> by auto

    lemma targets_char\<^sub>\<Lambda>:
    shows "targets t = (if Arr t then {Trg t} else {})"
    proof (cases "Arr t")
      show "\<not> Arr t \<Longrightarrow> ?thesis"
        by (meson arr_char arr_iff_has_target)
      assume t: "Arr t"
      have 1: "{Trg t} \<subseteq> targets t"
        using t resid_Arr_self trg_def trg_in_targets by force
      moreover have "targets t \<subseteq> {Trg t}"
        by (metis 1 Ide_iff_Src_self arr_char ide_char ide_implies_arr
            in_targetsE insert_subset prfx_implies_con resid_Arr_self
            sources_resid sources_simp t)
      ultimately show ?thesis
        using t by auto
    qed

    lemma targets_simp [simp]:
    assumes "Arr t"
    shows "targets t = {Trg t}"
      using assms targets_char\<^sub>\<Lambda> by auto

    lemma targets_simps [simp]:
    shows "targets \<^bold>\<sharp> = {}"
    and "targets \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = {\<^bold>\<guillemotleft>x\<^bold>\<guillemotright>}"
    and "arr t \<Longrightarrow> targets \<^bold>\<lambda>\<^bold>[t\<^bold>] = {\<^bold>\<lambda>\<^bold>[Trg t\<^bold>]}"
    and "\<lbrakk>arr t; arr u\<rbrakk> \<Longrightarrow> targets (t \<^bold>\<circ> u) = {Trg t \<^bold>\<circ> Trg u}"
    and "\<lbrakk>arr t; arr u\<rbrakk> \<Longrightarrow> targets (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = {subst (Trg u) (Trg t)}"
      using targets_char\<^sub>\<Lambda> by auto

    lemma seq_char:
    shows "seq t u \<longleftrightarrow> Arr t \<and> Arr u \<and> Trg t = Src u"
      using seq_def arr_char sources_char\<^sub>\<Lambda> targets_char\<^sub>\<Lambda> by force

    lemma seqI\<^sub>\<Lambda> [intro, simp]:
    assumes "Arr t" and "Arr u" and "Trg t = Src u"
    shows "seq t u"
      using assms seq_char by simp

    lemma seqE\<^sub>\<Lambda> [elim]:
    assumes "seq t u"
    and "\<lbrakk>Arr t; Arr u; Trg t = Src u\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms seq_char by blast

    text \<open>
      The following classifies the ways that transitions can be sequential.  It is useful
      for later proofs by case analysis.
    \<close>

    lemma seq_cases:
    assumes "seq t u"
    shows "(is_Var t \<and> is_Var u) \<or>
           (is_Lam t \<and> is_Lam u) \<or>
           (is_App t \<and> is_App u) \<or>
           (is_App t \<and> is_Beta u \<and> is_Lam (un_App1 t)) \<or>
           (is_App t \<and> is_Beta u \<and> is_Beta (un_App1 t)) \<or>
           is_Beta t"
      using assms seq_char
      by (cases t; cases u) auto

    sublocale confluent_rts resid
      by (unfold_locales) fastforce

    lemma is_confluent_rts:
    shows "confluent_rts resid"
      ..

    lemma con_char [iff]:
    shows "con t u \<longleftrightarrow> Con t u"
      by fastforce

    lemma coinitial_char [iff]:
    shows "coinitial t u \<longleftrightarrow> Coinitial t u"
      by fastforce

    lemma sources_Raise:
    assumes "Arr t"
    shows "sources (Raise d n t) = {Raise d n (Src t)}"
      using assms
      by (simp add: Coinitial_Raise_Raise Src_Raise)

    lemma targets_Raise:
    assumes "Arr t"
    shows "targets (Raise d n t) = {Raise d n (Trg t)}"
      using assms
      by (metis Arr_Raise ConI Raise_resid resid_Arr_self targets_char\<^sub>\<Lambda>)

    lemma sources_subst [simp]:
    assumes "Arr t" and "Arr u"
    shows "sources (subst t u) = {subst (Src t) (Src u)}"
      using assms sources_char\<^sub>\<Lambda> Arr_Subst arr_char by simp

    lemma targets_subst [simp]:
    assumes "Arr t" and "Arr u"
    shows "targets (subst t u) = {subst (Trg t) (Trg u)}"
      using assms targets_char\<^sub>\<Lambda> Arr_Subst arr_char by simp

    notation prfx  (infix "\<lesssim>" 50)
    notation cong  (infix "\<sim>" 50)

    lemma prfx_char [iff]:
    shows "t \<lesssim> u \<longleftrightarrow> Ide (t \\ u)"
      using ide_char by simp

    lemma prfx_Var_iff:
    shows "u \<lesssim> \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> \<longleftrightarrow> u = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>"
      by (metis Arr.simps(2) Coinitial_iff_Con Ide.simps(1) Ide_iff_Src_self Src.simps(2)
          ide_char resid_Arr_Ide)

    lemma prfx_Lam_iff:
    shows "u \<lesssim> Lam t \<longleftrightarrow> is_Lam u \<and> un_Lam u \<lesssim> t"
      using ide_char Arr_not_Nil Con_implies_is_Lam_iff_is_Lam Ide_implies_Arr is_Lam_def
      by fastforce

    lemma prfx_App_iff:
    shows "u \<lesssim> t1 \<^bold>\<circ> t2 \<longleftrightarrow> is_App u \<and> un_App1 u \<lesssim> t1 \<and> un_App2 u \<lesssim> t2"
      using ide_char
      by (cases u; cases t1) auto

    lemma prfx_Beta_iff:
    shows "u \<lesssim> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<longleftrightarrow> 
           (is_App u \<and> un_App1 u \<lesssim> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<and> un_App2 u \<frown> t2 \<and>
             (0 \<in> FV (un_Lam (un_App1 u) \\ t1) \<longrightarrow> un_App2 u \<lesssim> t2)) \<or>
           (is_Beta u \<and> un_Beta1 u \<lesssim> t1 \<and> un_Beta2 u \<frown> t2 \<and>
             (0 \<in> FV (un_Beta1 u \\ t1) \<longrightarrow> un_Beta2 u \<lesssim> t2))"
      using ide_char Ide_Subst_iff
      by (cases u; cases "un_App1 u") auto

    lemma cong_Ide_are_eq:
    assumes "t \<sim> u" and "Ide t" and "Ide u"
    shows "t = u"
      using assms
      by (metis Coinitial_iff_Con Ide_iff_Src_self con_char prfx_implies_con)

    lemma eq_Ide_are_cong:
    assumes "t = u" and "Ide t"
    shows "t \<sim> u"
      using assms Ide_implies_Arr resid_Ide_Arr by blast

    sublocale weakly_extensional_rts resid
      apply unfold_locales
      by (metis Coinitial_iff_Con Ide_iff_Src_self Ide_implies_Arr ide_char ide_def)

    lemma is_weakly_extensional_rts:
    shows "weakly_extensional_rts resid"
      ..

    lemma src_char [simp]:
    shows "src t = (if Arr t then Src t else \<^bold>\<sharp>)"
      using src_def by force

    lemma trg_char [simp]:
    shows "trg t = (if Arr t then Trg t else \<^bold>\<sharp>)"
      by (metis Coinitial_iff_Con resid_Arr_self trg_def)

    text \<open>
      We ``almost'' have an extensional RTS.
      The case that fails is \<open>\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<sim> u \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 = u\<close>.
      This is because \<open>t1\<close> might ignore its argument, so that \<open>subst t2 t1 = subst t2' t1\<close>,
      with both sides being identities, even if \<open>t2 \<noteq> t2'\<close>.

      The following gives a concrete example of such a situation.
    \<close>

    abbreviation non_extensional_ex1
    where "non_extensional_ex1 \<equiv> \<^bold>\<lambda>\<^bold>[\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>]\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>])"

    abbreviation non_extensional_ex2
    where "non_extensional_ex2 \<equiv> \<^bold>\<lambda>\<^bold>[\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>]\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>])"

    lemma non_extensional:
    shows "\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> non_extensional_ex1 \<sim> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> non_extensional_ex2"
    and "\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot>  non_extensional_ex1 \<noteq> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> non_extensional_ex2"
      by auto

    text \<open>
      The following gives an example of two terms that are both coinitial and coterminal,
      but which are not congruent.
    \<close>

    abbreviation cong_nontrivial_ex1
    where "cong_nontrivial_ex1 \<equiv>
           \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>])"

    abbreviation cong_nontrivial_ex2
    where "cong_nontrivial_ex2 \<equiv>
           \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright> \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>])"

    lemma cong_nontrivial:
    shows "coinitial cong_nontrivial_ex1 cong_nontrivial_ex2"
    and "coterminal cong_nontrivial_ex1 cong_nontrivial_ex2"
    and "\<not> cong cong_nontrivial_ex1 cong_nontrivial_ex2"
      by auto

    text \<open>
      Every two coinitial transitions have a join, obtained structurally by unioning the sets
      of marked redexes.
    \<close>

    fun Join  (infix "\<squnion>" 52)
    where "\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<squnion> \<^bold>\<guillemotleft>x'\<^bold>\<guillemotright> = (if x = x' then \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> else \<^bold>\<sharp>)"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<squnion> \<^bold>\<lambda>\<^bold>[t'\<^bold>] = \<^bold>\<lambda>\<^bold>[t \<squnion> t'\<^bold>]"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u \<squnion> \<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u' = \<^bold>\<lambda>\<^bold>[(t \<squnion> t')\<^bold>] \<^bold>\<Zspot> (u \<squnion> u')"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u \<squnion> \<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<circ> u' = \<^bold>\<lambda>\<^bold>[(t \<squnion> t')\<^bold>] \<^bold>\<Zspot> (u \<squnion> u')"
        | "t \<^bold>\<circ> u \<squnion> t'\<^bold>\<circ> u' = (t \<squnion> t') \<^bold>\<circ> (u \<squnion> u')"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u \<squnion> \<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u' = \<^bold>\<lambda>\<^bold>[(t \<squnion> t')\<^bold>] \<^bold>\<Zspot> (u \<squnion> u')"
        | "_ \<squnion> _ = \<^bold>\<sharp>"

    lemma Join_sym:
    shows "t \<squnion> u = u \<squnion> t"
      using Join.induct [of "\<lambda>t u. t \<squnion> u = u \<squnion> t"] by auto

    lemma Src_Join:
    shows "Coinitial t u \<Longrightarrow> Src (t \<squnion> u) = Src t"
    proof (induct t arbitrary: u)
      show "\<And>u. Coinitial \<^bold>\<sharp> u \<Longrightarrow> Src (\<^bold>\<sharp> \<squnion> u) = Src \<^bold>\<sharp>"
        by simp
      show "\<And>x u. Coinitial \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u \<Longrightarrow> Src (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<squnion> u) = Src \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        by auto
      fix t u
      assume ind: "\<And>u. Coinitial t u \<Longrightarrow> Src (t \<squnion> u) = Src t"
      assume tu: "Coinitial \<^bold>\<lambda>\<^bold>[t\<^bold>] u"
      show "Src (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<squnion> u) = Src \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        using tu ind
        by (cases u) auto
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. Coinitial t1 u1 \<Longrightarrow> Src (t1 \<squnion> u1) = Src t1"
      assume ind2: "\<And>u2. Coinitial t2 u2 \<Longrightarrow> Src (t2 \<squnion> u2) = Src t2"
      assume tu: "Coinitial (t1 \<^bold>\<circ> t2) u"
      show "Src (t1 \<^bold>\<circ> t2 \<squnion> u) = Src (t1 \<^bold>\<circ> t2)"
        using tu ind1 ind2
        apply (cases u, simp_all)
        apply (cases t1, simp_all)
        by (metis Arr.simps(3) Join.simps(2) Src.simps(3) lambda.sel(2))
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. Coinitial t1 u1 \<Longrightarrow> Src (t1 \<squnion> u1) = Src t1"
      assume ind2: "\<And>u2. Coinitial t2 u2 \<Longrightarrow> Src (t2 \<squnion> u2) = Src t2"
      assume tu: "Coinitial (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u"
      show "Src ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \<squnion> u) = Src (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        using tu ind1 ind2
        apply (cases u, simp_all)
        by (cases "un_App1 u") auto
    qed

    lemma resid_Join:
    shows "Coinitial t u \<Longrightarrow> (t \<squnion> u) \\ u = t \\ u"
    proof (induct t arbitrary: u)
      show "\<And>u. Coinitial \<^bold>\<sharp> u \<Longrightarrow> (\<^bold>\<sharp> \<squnion> u) \\ u = \<^bold>\<sharp> \\ u"
        by auto
      show "\<And>x u. Coinitial \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u \<Longrightarrow> (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<squnion> u) \\ u = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \\ u"
        by auto
      fix t u
      assume ind: "\<And>u. Coinitial t u \<Longrightarrow> (t \<squnion> u) \\ u = t \\ u"
      assume tu: "Coinitial \<^bold>\<lambda>\<^bold>[t\<^bold>] u"
      show "(\<^bold>\<lambda>\<^bold>[t\<^bold>] \<squnion> u) \\ u = \<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u"
        using tu ind
        by (cases u) auto
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. Coinitial t1 u1 \<Longrightarrow> (t1 \<squnion> u1) \\ u1 = t1 \\ u1"
      assume ind2: "\<And>u2. Coinitial t2 u2 \<Longrightarrow> (t2 \<squnion> u2) \\ u2 = t2 \\ u2"
      assume tu: "Coinitial (t1 \<^bold>\<circ> t2) u"
      show "(t1 \<^bold>\<circ> t2 \<squnion> u) \\ u = (t1 \<^bold>\<circ> t2) \\ u"
        using tu ind1 ind2 Coinitial_iff_Con
        apply (cases u, simp_all)
      proof -
        fix u1 u2
        assume u: "u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2"
        have t2u2: "t2 \<frown> u2"
          using Arr_not_Nil Arr_resid tu u by simp
        have t1u1: "Coinitial (un_Lam t1 \<squnion> u1) u1"
        proof -
          have "Arr (un_Lam t1 \<squnion> u1)"
            by (metis Arr.simps(3-5) Coinitial_iff_Con Con_implies_is_Lam_iff_is_Lam
                Join.simps(2) Src.simps(3-5) ind1 lambda.collapse(2) lambda.disc(8)
                lambda.sel(3) tu u)
          thus ?thesis
            using Src_Join
            by (metis Arr.simps(3-5) Coinitial_iff_Con Con_implies_is_Lam_iff_is_Lam
                Src.simps(3-5) lambda.collapse(2) lambda.disc(8) lambda.sel(2-3) tu u)
        qed
        have "un_Lam t1 \<frown> u1"
          using t1u1
          by (metis Coinitial_iff_Con Con_implies_is_Lam_iff_is_Lam ConD(4) lambda.collapse(2)
              lambda.disc(8) resid.simps(2) tu u)
        thus "(t1 \<^bold>\<circ> t2 \<squnion> \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2) = (t1 \<^bold>\<circ> t2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)"
          using u tu t1u1 t2u2 ind1 ind2
          apply (cases t1, auto)
        proof -
          fix v
          assume v: "t1 = \<^bold>\<lambda>\<^bold>[v\<^bold>]"
          show "subst (t2 \\ u2) ((v \<squnion> u1) \\ u1) = subst (t2 \\ u2) (v \\ u1)"
          proof -
            have "subst (t2 \\ u2) ((v \<squnion> u1) \\ u1) = (t1 \<^bold>\<circ> t2 \<squnion> \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)"
              by (simp add: Coinitial_iff_Con ind2 t2u2 v)
            also have "... = (t1 \<^bold>\<circ> t2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)"
            proof -
              have "(t1 \<^bold>\<circ> t2 \<squnion> \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2) =
                    (\<^bold>\<lambda>\<^bold>[(v \<squnion> u1)\<^bold>] \<^bold>\<Zspot> (t2 \<squnion> u2)) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)"
                using v by simp
              also have "... = subst (t2 \\ u2) ((v \<squnion> u1) \\ u1)"
                by (simp add: Coinitial_iff_Con ind2 t2u2)
              also have "... = subst (t2 \\ u2) (v \\ u1)"
              proof -
                have "(t1 \<squnion> \<^bold>\<lambda>\<^bold>[u1\<^bold>]) \\ \<^bold>\<lambda>\<^bold>[u1\<^bold>] = t1 \\ \<^bold>\<lambda>\<^bold>[u1\<^bold>]"
                  using u tu ind1 by simp
                thus ?thesis
                  using \<open>un_Lam t1 \ u1 \<noteq> \<^bold>\<sharp>\<close> t1u1 v by force
              qed
              also have "... = (t1 \<^bold>\<circ> t2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)"
                using tu u v by force
              finally show ?thesis by blast
            qed
            also have "... = subst (t2 \\ u2) (v \\ u1)"
              by (simp add: t2u2 v)
            finally show ?thesis by auto
          qed
        qed
      qed
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. Coinitial t1 u1 \<Longrightarrow> (t1 \<squnion> u1) \\ u1 = t1 \\ u1"
      assume ind2: "\<And>u2. Coinitial t2 u2 \<Longrightarrow> (t2 \<squnion> u2) \\ u2 = t2 \\ u2"
      assume tu: "Coinitial (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u"
      show "((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \<squnion> u) \\ u = (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u"
        using tu ind1 ind2 Coinitial_iff_Con
        apply (cases u, simp_all)
      proof -
        fix u1 u2
        assume u: "u = u1 \<^bold>\<circ> u2"
        show "(\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<squnion> u1 \<^bold>\<circ> u2) \\ (u1 \<^bold>\<circ> u2) = (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ (u1 \<^bold>\<circ> u2)"
          using ind1 ind2 tu u
          by (cases u1) auto
      qed
    qed

    lemma prfx_Join:
    shows "Coinitial t u \<Longrightarrow> u \<lesssim> t \<squnion> u"
    proof (induct t arbitrary: u)
      show "\<And>u. Coinitial \<^bold>\<sharp> u \<Longrightarrow> u \<lesssim> \<^bold>\<sharp> \<squnion> u"
        by simp
      show "\<And>x u. Coinitial \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u \<Longrightarrow> u \<lesssim> \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<squnion> u"
        by auto
      fix t u
      assume ind: "\<And>u. Coinitial t u \<Longrightarrow> u \<lesssim> t \<squnion> u"
      assume tu: "Coinitial \<^bold>\<lambda>\<^bold>[t\<^bold>] u"
      show "u \<lesssim> \<^bold>\<lambda>\<^bold>[t\<^bold>] \<squnion> u"
        using tu ind
        apply (cases u, auto)
        by force
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. Coinitial t1 u1 \<Longrightarrow> u1 \<lesssim> t1 \<squnion> u1"
      assume ind2: "\<And>u2. Coinitial t2 u2 \<Longrightarrow> u2 \<lesssim> t2 \<squnion> u2"
      assume tu: "Coinitial (t1 \<^bold>\<circ> t2) u"
      show "u \<lesssim> t1 \<^bold>\<circ> t2 \<squnion> u"
        using tu ind1 ind2 Coinitial_iff_Con
        apply (cases u, simp_all)
         apply (metis Ide.simps(1))
      proof -
        fix u1 u2
        assume u: "u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2"
        assume 1: "Arr t1 \<and> Arr t2 \<and> Arr u1 \<and> Arr u2 \<and> Src t1 = \<^bold>\<lambda>\<^bold>[Src u1\<^bold>] \<and> Src t2 = Src u2"
        have 2: "u1 \<frown> un_Lam t1 \<squnion> u1"
          by (metis "1" Coinitial_iff_Con Con_implies_is_Lam_iff_is_Lam Con_Arr_Src(2)
              lambda.collapse(2) lambda.disc(8) resid.simps(2) resid_Join)
        have 3: "u2 \<frown> t2 \<squnion> u2"
          by (metis "1" conE ind2 null_char prfx_implies_con)
        show "Ide ((\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2) \\ (t1 \<^bold>\<circ> t2 \<squnion> \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2))"
         using u tu 1 2 3 ind1 ind2
         apply (cases t1, simp_all)
         by (metis Arr.simps(3) Ide.simps(3) Ide_Subst Join.simps(2) Src.simps(3) resid.simps(2))
       qed
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. Coinitial t1 u1 \<Longrightarrow> u1 \<lesssim> t1 \<squnion> u1"
      assume ind2: "\<And>u2. Coinitial t2 u2 \<Longrightarrow> u2 \<lesssim> t2 \<squnion> u2"
      assume tu: "Coinitial (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u"
      show "u \<lesssim> (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \<squnion> u"
        using tu ind1 ind2 Coinitial_iff_Con
        apply (cases u, simp_all)
         apply (cases "un_App1 u", simp_all)
        by (metis Ide.simps(1) Ide_Subst)+
    qed

    lemma Ide_resid_Join:
    shows "Coinitial t u \<Longrightarrow> Ide (u \\ (t \<squnion> u))"
      using ide_char prfx_Join by blast

    lemma join_of_Join:
    assumes "Coinitial t u"
    shows "join_of t u (t \<squnion> u)"
    proof (unfold join_of_def composite_of_def, intro conjI)
      show "t \<lesssim> t \<squnion> u"
        using assms Join_sym prfx_Join [of u t] by simp
      show "u \<lesssim> t \<squnion> u"
        using assms Ide_resid_Join ide_char by simp
      show "(t \<squnion> u) \\ t \<lesssim> u \\ t"
        by (metis \<open>prfx u (Join t u)\<close> arr_char assms cong_subst_right(2) prfx_implies_con
            prfx_reflexive resid_Join con_sym cube)
      show "u \\ t \<lesssim> (t \<squnion> u) \\ t"
        by (metis Coinitial_resid_resid \<open>prfx t (Join t u)\<close> \<open>prfx u (Join t u)\<close> conE ide_char
            null_char prfx_implies_con resid_Ide_Arr cube)
      show "(t \<squnion> u) \\ u \<lesssim> t \\ u"
        using \<open>(t \<squnion> u) \ t \<lesssim> u \ t\<close> cube by auto
      show "t \\ u \<lesssim> (t \<squnion> u) \\ u"
        by (metis \<open>(t \<squnion> u) \ t \<lesssim> u \ t\<close> assms cube resid_Join)
    qed

    sublocale rts_with_joins resid
      using join_of_Join
      apply unfold_locales
      by (metis Coinitial_iff_Con conE joinable_def null_char)

    lemma is_rts_with_joins:
    shows "rts_with_joins resid"
      ..

    subsection "Simulations from Syntactic Constructors"

    text \<open>
      Here we show that the syntactic constructors \<open>Lam\<close> and \<open>App\<close>, as well as the substitution
      operation \<open>subst\<close>, determine simulations.  In addition, we show that \<open>Beta\<close> determines
      a transformation from \<open>App \<circ> (Lam \<times> Id)\<close> to \<open>subst\<close>.
    \<close>  

    abbreviation Lam\<^sub>e\<^sub>x\<^sub>t
    where "Lam\<^sub>e\<^sub>x\<^sub>t t \<equiv> if arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>"

    lemma Lam_is_simulation:
    shows "simulation resid resid Lam\<^sub>e\<^sub>x\<^sub>t"
      using Arr_resid Coinitial_iff_Con
      by unfold_locales auto

    interpretation Lam: simulation resid resid Lam\<^sub>e\<^sub>x\<^sub>t
      using Lam_is_simulation by simp

    interpretation \<Lambda>x\<Lambda>: product_of_weakly_extensional_rts resid resid
      ..

    abbreviation App\<^sub>e\<^sub>x\<^sub>t
    where "App\<^sub>e\<^sub>x\<^sub>t t \<equiv> if \<Lambda>x\<Lambda>.arr t then fst t \<^bold>\<circ> snd t else \<^bold>\<sharp>"

    lemma App_is_binary_simulation:
    shows "binary_simulation resid resid resid App\<^sub>e\<^sub>x\<^sub>t"
    proof
      show "\<And>t. \<not> \<Lambda>x\<Lambda>.arr t \<Longrightarrow> App\<^sub>e\<^sub>x\<^sub>t t = null"
        by auto
      show "\<And>t u. \<Lambda>x\<Lambda>.con t u \<Longrightarrow> con (App\<^sub>e\<^sub>x\<^sub>t t) (App\<^sub>e\<^sub>x\<^sub>t u)"
        using \<Lambda>x\<Lambda>.con_char Coinitial_iff_Con by auto
      show "\<And>t u. \<Lambda>x\<Lambda>.con t u \<Longrightarrow> App\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.resid t u) = App\<^sub>e\<^sub>x\<^sub>t t \\ App\<^sub>e\<^sub>x\<^sub>t u"
        using \<Lambda>x\<Lambda>.arr_char \<Lambda>x\<Lambda>.resid_def
        apply simp
        by (metis Arr_resid Con_implies_Arr1 Con_implies_Arr2)
    qed

    interpretation App: binary_simulation resid resid resid App\<^sub>e\<^sub>x\<^sub>t
      using App_is_binary_simulation by simp

    abbreviation subst\<^sub>e\<^sub>x\<^sub>t
    where "subst\<^sub>e\<^sub>x\<^sub>t \<equiv> \<lambda>t. if \<Lambda>x\<Lambda>.arr t then subst (snd t) (fst t) else \<^bold>\<sharp>"

    lemma subst_is_binary_simulation:
    shows "binary_simulation resid resid resid subst\<^sub>e\<^sub>x\<^sub>t"
    proof
      show "\<And>t. \<not> \<Lambda>x\<Lambda>.arr t \<Longrightarrow> subst\<^sub>e\<^sub>x\<^sub>t t = null"
        by auto
      show "\<And>t u. \<Lambda>x\<Lambda>.con t u \<Longrightarrow> con (subst\<^sub>e\<^sub>x\<^sub>t t) (subst\<^sub>e\<^sub>x\<^sub>t u)"
        using \<Lambda>x\<Lambda>.con_char con_char Subst_not_Nil resid_Subst \<Lambda>x\<Lambda>.coinitialE
              \<Lambda>x\<Lambda>.con_imp_coinitial
        apply simp
        by metis
      show "\<And>t u. \<Lambda>x\<Lambda>.con t u \<Longrightarrow> subst\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.resid t u) = subst\<^sub>e\<^sub>x\<^sub>t t \\ subst\<^sub>e\<^sub>x\<^sub>t u"
        using \<Lambda>x\<Lambda>.arr_char \<Lambda>x\<Lambda>.resid_def
        apply simp
        by (metis Arr_resid Con_implies_Arr1 Con_implies_Arr2 resid_Subst)
    qed

    interpretation subst: binary_simulation resid resid resid subst\<^sub>e\<^sub>x\<^sub>t
      using subst_is_binary_simulation by simp

    interpretation Id: identity_simulation resid
      ..
    interpretation Lam_Id: product_simulation resid resid resid resid Lam\<^sub>e\<^sub>x\<^sub>t Id.map
      ..
    interpretation App_o_Lam_Id: composite_simulation \<Lambda>x\<Lambda>.resid \<Lambda>x\<Lambda>.resid resid Lam_Id.map App\<^sub>e\<^sub>x\<^sub>t
      ..

    abbreviation Beta\<^sub>e\<^sub>x\<^sub>t
    where "Beta\<^sub>e\<^sub>x\<^sub>t t \<equiv> if \<Lambda>x\<Lambda>.arr t then \<^bold>\<lambda>\<^bold>[fst t\<^bold>] \<^bold>\<Zspot> snd t else \<^bold>\<sharp>"

    lemma Beta_is_transformation:
    shows "transformation \<Lambda>x\<Lambda>.resid resid App_o_Lam_Id.map subst\<^sub>e\<^sub>x\<^sub>t Beta\<^sub>e\<^sub>x\<^sub>t"
    proof
      show "\<And>f. \<not> \<Lambda>x\<Lambda>.arr f \<Longrightarrow> Beta\<^sub>e\<^sub>x\<^sub>t f = null"
        by simp
      show "\<And>f. \<Lambda>x\<Lambda>.ide f \<Longrightarrow> src (Beta\<^sub>e\<^sub>x\<^sub>t f) = App_o_Lam_Id.map f"
        using \<Lambda>x\<Lambda>.src_char \<Lambda>x\<Lambda>.src_ide Lam_Id.map_def by force
      show "\<And>f. \<Lambda>x\<Lambda>.ide f \<Longrightarrow> trg (Beta\<^sub>e\<^sub>x\<^sub>t f) = subst\<^sub>e\<^sub>x\<^sub>t f"
        using \<Lambda>x\<Lambda>.trg_char \<Lambda>x\<Lambda>.trg_ide by force
      show "\<And>f. \<Lambda>x\<Lambda>.arr f \<Longrightarrow>
                  Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f) \\ App_o_Lam_Id.map f = Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.trg f)"
          using \<Lambda>x\<Lambda>.src_char \<Lambda>x\<Lambda>.trg_char Arr_Trg Arr_not_Nil Lam_Id.map_def by simp
      show "\<And>f. \<Lambda>x\<Lambda>.arr f \<Longrightarrow> App_o_Lam_Id.map f \\ Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f) = subst\<^sub>e\<^sub>x\<^sub>t f"
          using \<Lambda>x\<Lambda>.src_char \<Lambda>x\<Lambda>.trg_char Lam_Id.map_def by auto
      show "\<And>f. \<Lambda>x\<Lambda>.arr f \<Longrightarrow> join_of (Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f)) (App_o_Lam_Id.map f) (Beta\<^sub>e\<^sub>x\<^sub>t f)"
      proof -
        fix f
        assume f: "\<Lambda>x\<Lambda>.arr f"
        show "join_of (Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f)) (App_o_Lam_Id.map f) (Beta\<^sub>e\<^sub>x\<^sub>t f)"
        proof (intro join_ofI composite_ofI)
          show "App_o_Lam_Id.map f \<lesssim> Beta\<^sub>e\<^sub>x\<^sub>t f"
            using f Lam_Id.map_def Ide_Subst arr_char prfx_char prfx_reflexive by auto
          show "Beta\<^sub>e\<^sub>x\<^sub>t f \\ Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f) \<sim> App_o_Lam_Id.map f \\ Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f)"
            using f Lam_Id.map_def \<Lambda>x\<Lambda>.src_char trg_char trg_def
            apply auto
            by (metis Arr_Subst Ide_Trg)
          show 1: "Beta\<^sub>e\<^sub>x\<^sub>t f \\ App_o_Lam_Id.map f \<sim> Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f) \\ App_o_Lam_Id.map f"
            using f Lam_Id.map_def Ide_Subst \<Lambda>x\<Lambda>.src_char Ide_Trg Arr_resid Coinitial_iff_Con
                  resid_Arr_self
            apply simp
            by metis
          show "Beta\<^sub>e\<^sub>x\<^sub>t (\<Lambda>x\<Lambda>.src f) \<lesssim> Beta\<^sub>e\<^sub>x\<^sub>t f"
            using f 1 Lam_Id.map_def Ide_Subst \<Lambda>x\<Lambda>.src_char resid_Arr_self by auto
        qed
      qed
    qed

    text \<open>
      The next two results are used to show that mapping App over lists of transitions
      preserves paths.
    \<close>

    lemma App_is_simulation1:
    assumes "ide a"
    shows "simulation resid resid (\<lambda>t. if arr t then t \<^bold>\<circ> a else \<^bold>\<sharp>)"
    proof -
      have "(\<lambda>t. if \<Lambda>x\<Lambda>.arr (t, a) then fst (t, a) \<^bold>\<circ> snd (t, a) else \<^bold>\<sharp>) =
            (\<lambda>t. if arr t then t \<^bold>\<circ> a else \<^bold>\<sharp>)"
        using assms ide_implies_arr by force
      thus ?thesis
        using assms App.fixing_ide_gives_simulation_0 [of a] by auto
    qed

    lemma App_is_simulation2:
    assumes "ide a"
    shows "simulation resid resid (\<lambda>t. if arr t then a \<^bold>\<circ> t else \<^bold>\<sharp>)"
    proof -
      have "(\<lambda>t. if \<Lambda>x\<Lambda>.arr (a, t) then fst (a, t) \<^bold>\<circ> snd (a, t) else \<^bold>\<sharp>) =
            (\<lambda>t. if arr t then a \<^bold>\<circ> t else \<^bold>\<sharp>)"
        using assms ide_implies_arr by force
      thus ?thesis
        using assms App.fixing_ide_gives_simulation_1 [of a] by auto
    qed

    subsection "Reduction and Conversion"

    text \<open>
      Here we define the usual relations of reduction and conversion.
      Reduction is the least transitive relation that relates \<open>a\<close> to \<open>b\<close> if there exists
      an arrow \<open>t\<close> having \<open>a\<close> as its source and \<open>b\<close> as its target.
      Conversion is the least transitive relation that relates \<open>a\<close> to b if there exists
      an arrow \<open>t\<close> in either direction between \<open>a\<close> and \<open>b\<close>.
    \<close>

    inductive red
    where "Arr t \<Longrightarrow> red (Src t) (Trg t)"
        | "\<lbrakk>red a b; red b c\<rbrakk> \<Longrightarrow> red a c"

    inductive cnv
    where "Arr t \<Longrightarrow> cnv (Src t) (Trg t)"
        | "Arr t \<Longrightarrow> cnv (Trg t) (Src t)"
        | "\<lbrakk>cnv a b; cnv b c\<rbrakk> \<Longrightarrow> cnv a c"

    lemma cnv_refl:
    assumes "Ide a"
    shows "cnv a a"
      using assms
      by (metis Ide_iff_Src_self Ide_implies_Arr cnv.simps)

    lemma cnv_sym:
    shows "cnv a b \<Longrightarrow> cnv b a"
      apply (induct rule: cnv.induct)
      using cnv.intros(1-2)
        apply auto[2]
      using cnv.intros(3) by blast

    lemma red_imp_cnv:
    shows "red a b \<Longrightarrow> cnv a b"
      using cnv.intros(1,3) red.inducts by blast

  end

  text \<open>
    We now define a locale that extends the residuation operation defined above
    to paths, using general results that have already been shown for paths in an RTS.
    In particular, we are taking advantage of the general proof of the Cube Lemma for
    residuation on paths.

    Our immediate goal is to prove the Church-Rosser theorem, so we first prove a lemma
    that connects the reduction relation to paths.  Later, we will prove many more
    facts in this locale, thereby developing a general framework for reasoning about
    reduction paths in the \<open>\<lambda>\<close>-calculus.
  \<close>

  locale reduction_paths =
    \<Lambda>: lambda_calculus
  begin

    sublocale \<Lambda>: rts \<Lambda>.resid
      by (simp add: \<Lambda>.is_rts_with_joins rts_with_joins.axioms(1))
    sublocale paths_in_weakly_extensional_rts \<Lambda>.resid
      ..
    sublocale paths_in_confluent_rts \<Lambda>.resid
      using confluent_rts.axioms(1) \<Lambda>.is_confluent_rts paths_in_rts_def
            paths_in_confluent_rts.intro
      by blast

    notation \<Lambda>.resid  (infix "\\" 70)
    notation \<Lambda>.con    (infix "\<frown>" 50)
    notation \<Lambda>.prfx   (infix "\<lesssim>" 50)
    notation \<Lambda>.cong   (infix "\<sim>" 50)

    notation Resid    (infix "\<^sup>*\\\<^sup>*" 70)
    notation Resid1x  (infix "\<^sup>1\\\<^sup>*" 70)
    notation Residx1  (infix "\<^sup>*\\\<^sup>1" 70)
    notation con      (infix "\<^sup>*\<frown>\<^sup>*" 50)
    notation prfx     (infix "\<^sup>*\<lesssim>\<^sup>*" 50)
    notation cong     (infix "\<^sup>*\<sim>\<^sup>*" 50)

    lemma red_iff:
    shows "\<Lambda>.red a b \<longleftrightarrow> (\<exists>T. Arr T \<and> Src T = a \<and> Trg T = b)"
    proof
      show "\<Lambda>.red a b \<Longrightarrow> \<exists>T. Arr T \<and> Src T = a \<and> Trg T = b"
      proof (induct rule: \<Lambda>.red.induct)
        show "\<And>t. \<Lambda>.Arr t \<Longrightarrow> \<exists>T. Arr T \<and> Src T = \<Lambda>.Src t \<and> Trg T = \<Lambda>.Trg t"
          by (metis Arr.simps(2) Srcs.simps(2) Srcs_simp\<^sub>P\<^sub>W\<^sub>E Trg.simps(2) \<Lambda>.trg_def
              \<Lambda>.arr_char \<Lambda>.resid_Arr_self \<Lambda>.sources_char\<^sub>\<Lambda> singleton_insert_inj_eq')
        show "\<And>a b c. \<lbrakk>\<exists>T. Arr T \<and> Src T = a \<and> Trg T = b;
                       \<exists>T. Arr T \<and> Src T = b \<and> Trg T = c\<rbrakk>
                           \<Longrightarrow> \<exists>T. Arr T \<and> Src T = a \<and> Trg T = c"
          by (metis Arr.simps(1) Arr_appendI\<^sub>P\<^sub>W\<^sub>E Srcs_append Srcs_simp\<^sub>P\<^sub>W\<^sub>E Trgs_append
              Trgs_simp\<^sub>P\<^sub>W\<^sub>E singleton_insert_inj_eq')
      qed
      show "\<exists>T. Arr T \<and> Src T = a \<and> Trg T = b \<Longrightarrow> \<Lambda>.red a b"
      proof -
        have "Arr T \<Longrightarrow> \<Lambda>.red (Src T) (Trg T)" for T
        proof (induct T)
          show "Arr [] \<Longrightarrow> \<Lambda>.red (Src []) (Trg [])"
            by auto
          fix t T
          assume ind: "Arr T \<Longrightarrow> \<Lambda>.red (Src T) (Trg T)"
          assume Arr: "Arr (t # T)"
          show "\<Lambda>.red (Src (t # T)) (Trg (t # T))"
          proof (cases "T = []")
            show "T = [] \<Longrightarrow> ?thesis"
              using Arr arr_char \<Lambda>.red.intros(1) by simp
            assume T: "T \<noteq> []"
            have "\<Lambda>.red (Src (t # T)) (\<Lambda>.Trg t)"
              apply simp
              by (meson Arr Arr.simps(2) Con_Arr_self Con_implies_Arr(1) Con_initial_left
                  \<Lambda>.arr_char \<Lambda>.red.intros(1))
            moreover have "\<Lambda>.Trg t = Src T"
              using Arr
              by (metis Arr.elims(2) Srcs_simp\<^sub>P\<^sub>W\<^sub>E T \<Lambda>.arr_iff_has_target insert_subset
                  \<Lambda>.targets_char\<^sub>\<Lambda> list.sel(1) list.sel(3) singleton_iff)
            ultimately show ?thesis
              using ind
              by (metis (no_types, opaque_lifting) Arr Con_Arr_self Con_implies_Arr(2)
                  Resid_cons(2) T Trg.simps(3) \<Lambda>.red.intros(2) neq_Nil_conv)
          qed
        qed
        thus "\<exists>T. Arr T \<and> Src T = a \<and> Trg T = b \<Longrightarrow> \<Lambda>.red a b"
          by blast
      qed
    qed

  end

  subsection "The Church-Rosser Theorem"

  context lambda_calculus
  begin

    interpretation \<Lambda>x: reduction_paths .

    theorem church_rosser:
    shows "cnv a b \<Longrightarrow> \<exists>c. red a c \<and> red b c"
    proof (induct rule: cnv.induct)
      show "\<And>t. Arr t \<Longrightarrow> \<exists>c. red (Src t) c \<and> red (Trg t) c"
        by (metis Ide_Trg Ide_iff_Src_self Ide_iff_Trg_self Ide_implies_Arr red.intros(1))
      thus "\<And>t. Arr t \<Longrightarrow> \<exists>c. red (Trg t) c \<and> red (Src t) c"
        by auto
      show "\<And>a b c. \<lbrakk>cnv a b; cnv b c; \<exists>x. red a x \<and> red b x; \<exists>y. red b y \<and> red c y\<rbrakk>
                         \<Longrightarrow> \<exists>z. red a z \<and> red c z"
      proof -
        fix a b c
        assume ind1: "\<exists>x. red a x \<and> red b x" and ind2: "\<exists>y. red b y \<and> red c y"
        obtain x where x: "red a x \<and> red b x"
          using ind1 by blast
        obtain y where y: "red b y \<and> red c y"
          using ind2 by blast
        obtain T1 U1 where 1: "\<Lambda>x.Arr T1 \<and> \<Lambda>x.Arr U1 \<and> \<Lambda>x.Src T1 = a \<and> \<Lambda>x.Src U1 = b \<and>
                               \<Lambda>x.Trgs T1 = \<Lambda>x.Trgs U1"
          using x \<Lambda>x.red_iff [of a x] \<Lambda>x.red_iff [of b x] by fastforce
        obtain T2 U2 where 2: "\<Lambda>x.Arr T2 \<and> \<Lambda>x.Arr U2 \<and> \<Lambda>x.Src T2 = b \<and> \<Lambda>x.Src U2 = c \<and>
                               \<Lambda>x.Trgs T2 = \<Lambda>x.Trgs U2"
          using y \<Lambda>x.red_iff [of b y] \<Lambda>x.red_iff [of c y] by fastforce
        show "\<exists>e. red a e \<and> red c e"
        proof -
          let ?T = "T1 @ (\<Lambda>x.Resid T2 U1)" and ?U = "U2 @ (\<Lambda>x.Resid U1 T2)"
          have 3: "\<Lambda>x.Arr ?T \<and> \<Lambda>x.Arr ?U \<and> \<Lambda>x.Src ?T = a \<and> \<Lambda>x.Src ?U = c"
            using 1 2
            by (metis \<Lambda>x.Arr_appendI\<^sub>P\<^sub>W\<^sub>E \<Lambda>x.Arr_has_Trg \<Lambda>x.Con_imp_Arr_Resid \<Lambda>x.Src_append
                \<Lambda>x.Src_resid \<Lambda>x.Srcs_simp\<^sub>P\<^sub>W\<^sub>E \<Lambda>x.Trgs.simps(1) \<Lambda>x.Trgs_simp\<^sub>P\<^sub>W\<^sub>E \<Lambda>x.arrI\<^sub>P
                \<Lambda>x.arr_append_imp_seq \<Lambda>x.confluence_ind singleton_insert_inj_eq')
          moreover have "\<Lambda>x.Trgs ?T = \<Lambda>x.Trgs ?U"
            using 1 2 3 \<Lambda>x.Srcs_simp\<^sub>P\<^sub>W\<^sub>E \<Lambda>x.Trgs_Resid_sym \<Lambda>x.Trgs_append \<Lambda>x.confluence_ind
            by presburger
          ultimately have "\<exists>T U. \<Lambda>x.Arr T \<and> \<Lambda>x.Arr U \<and> \<Lambda>x.Src T = a \<and> \<Lambda>x.Src U = c \<and>
                                 \<Lambda>x.Trgs T = \<Lambda>x.Trgs U"
            by blast
          thus ?thesis
            using \<Lambda>x.red_iff \<Lambda>x.Arr_has_Trg by fastforce
        qed
      qed
    qed

    corollary weak_diamond:
    assumes "red a b" and "red a b'"
    obtains c where "red b c" and "red b' c"
    proof -
      have "cnv b b'"
        using assms
        by (metis cnv.intros(1,3) cnv_sym red.induct)
      thus ?thesis
        using that church_rosser by blast
    qed

    text \<open>
      As a consequence of the Church-Rosser Theorem, the collection of all reduction
      paths forms a coherent normal sub-RTS of the RTS of reduction paths, and on identities
      the congruence induced by this normal sub-RTS coincides with convertibility.
      The quotient of the \<open>\<lambda>\<close>-calculus RTS by this congruence is then obviously discrete:
      the only transitions are identities.
    \<close>

    interpretation Red: normal_sub_rts \<Lambda>x.Resid \<open>Collect \<Lambda>x.Arr\<close>
    proof
      show "\<And>t. t \<in> Collect \<Lambda>x.Arr \<Longrightarrow> \<Lambda>x.arr t"
        by blast
      show "\<And>a. \<Lambda>x.ide a \<Longrightarrow> a \<in> Collect \<Lambda>x.Arr"
        using \<Lambda>x.Ide_char \<Lambda>x.ide_char by blast
      show "\<And>u t. \<lbrakk>u \<in> Collect \<Lambda>x.Arr; \<Lambda>x.coinitial t u\<rbrakk> \<Longrightarrow> \<Lambda>x.Resid u t \<in> Collect \<Lambda>x.Arr"
        by (metis \<Lambda>x.Con_imp_Arr_Resid \<Lambda>x.Resid.simps(1) \<Lambda>x.con_sym \<Lambda>x.confluence\<^sub>P \<Lambda>x.ide_def
            \<open>\<And>a. \<Lambda>x.ide a \<Longrightarrow> a \<in> Collect \<Lambda>x.Arr\<close> mem_Collect_eq \<Lambda>x.arr_resid_iff_con)
      show "\<And>u t. \<lbrakk>u \<in> Collect \<Lambda>x.Arr; \<Lambda>x.Resid t u \<in> Collect \<Lambda>x.Arr\<rbrakk> \<Longrightarrow> t \<in> Collect \<Lambda>x.Arr"
        by (metis \<Lambda>x.Arr.simps(1) \<Lambda>x.Con_implies_Arr(1) mem_Collect_eq)
      show "\<And>u t. \<lbrakk>u \<in> Collect \<Lambda>x.Arr; \<Lambda>x.seq u t\<rbrakk> \<Longrightarrow> \<exists>v. \<Lambda>x.composite_of u t v"
        by (meson \<Lambda>x.obtains_composite_of)
      show "\<And>u t. \<lbrakk>u \<in> Collect \<Lambda>x.Arr; \<Lambda>x.seq t u\<rbrakk> \<Longrightarrow> \<exists>v. \<Lambda>x.composite_of t u v"
        by (meson \<Lambda>x.obtains_composite_of)
    qed

    interpretation Red: coherent_normal_sub_rts \<Lambda>x.Resid \<open>Collect \<Lambda>x.Arr\<close>
      apply unfold_locales
      by (metis Red.Cong_closure_props(4) Red.Cong_imp_arr(2) \<Lambda>x.Con_imp_Arr_Resid
          \<Lambda>x.arr_resid_iff_con \<Lambda>x.con_char \<Lambda>x.sources_resid mem_Collect_eq)

    lemma cnv_iff_Cong:
    assumes "ide a" and "ide b"
    shows "cnv a b \<longleftrightarrow> Red.Cong [a] [b]"
    proof
      assume 1: "Red.Cong [a] [b]"
      obtain U V
        where UV: "\<Lambda>x.Arr U \<and> \<Lambda>x.Arr V \<and> Red.Cong\<^sub>0 (\<Lambda>x.Resid [a] U) (\<Lambda>x.Resid [b] V)"
        using 1 Red.Cong_def [of "[a]" "[b]"] by blast
      have "red a (\<Lambda>x.Trg U) \<and> red b (\<Lambda>x.Trg V)"
        by (metis UV \<Lambda>x.Arr.simps(1) \<Lambda>x.Con_implies_Arr(1) \<Lambda>x.Resid_single_ide(2) \<Lambda>x.Src_resid
            \<Lambda>x.Trg.simps(2) assms(1-2) mem_Collect_eq reduction_paths.red_iff trg_ide)
      moreover have "\<Lambda>x.Trg U = \<Lambda>x.Trg V"
        using UV
        by (metis (no_types, lifting) Red.Cong\<^sub>0_imp_con \<Lambda>x.Arr.simps(1) \<Lambda>x.Con_Arr_self
            \<Lambda>x.Con_implies_Arr(1) \<Lambda>x.Resid_single_ide(2) \<Lambda>x.Src_resid \<Lambda>x.cube \<Lambda>x.ide_def
            \<Lambda>x.resid_arr_ide assms(1) mem_Collect_eq)
      ultimately show "cnv a b"
        by (metis cnv_sym cnv.intros(3) red_imp_cnv)
      next
      assume 1: "cnv a b"
      obtain c where c: "red a c \<and> red b c"
        using 1 church_rosser by blast
      obtain U where U: "\<Lambda>x.Arr U \<and> \<Lambda>x.Src U = a \<and> \<Lambda>x.Trg U = c"
        using c \<Lambda>x.red_iff by blast
      obtain V where V: "\<Lambda>x.Arr V \<and> \<Lambda>x.Src V = b \<and> \<Lambda>x.Trg V = c"
        using c \<Lambda>x.red_iff by blast
      have "\<Lambda>x.Resid1x a U = c \<and> \<Lambda>x.Resid1x b V = c"
        by (metis U V \<Lambda>x.Con_single_ide_ind \<Lambda>x.Ide.simps(2) \<Lambda>x.Resid1x_as_Resid
            \<Lambda>x.Resid_Ide_Arr_ind \<Lambda>x.Resid_single_ide(2) \<Lambda>x.Srcs_simp\<^sub>P\<^sub>W\<^sub>E \<Lambda>x.Trg.simps(2)
            \<Lambda>x.Trg_resid_sym \<Lambda>x.ex_un_Src assms(1-2) singletonD trg_ide)
      hence "Red.Cong\<^sub>0 (\<Lambda>x.Resid [a] U) (\<Lambda>x.Resid [b] V)"
        by (metis Red.Cong\<^sub>0_reflexive U V \<Lambda>x.Con_single_ideI(1) \<Lambda>x.Resid1x_as_Resid
            \<Lambda>x.Srcs_simp\<^sub>P\<^sub>W\<^sub>E \<Lambda>x.arr_resid \<Lambda>x.con_char assms(1-2) empty_set
            list.set_intros(1) list.simps(15))
      thus "Red.Cong [a] [b]"
        using U V Red.Cong_def [of "[a]" "[b]"] by blast
    qed

    interpretation \<Lambda>q: quotient_by_coherent_normal \<Lambda>x.Resid \<open>Collect \<Lambda>x.Arr\<close>
      ..

    lemma quotient_by_cnv_is_discrete:
    shows "\<Lambda>q.arr t \<longleftrightarrow> \<Lambda>q.ide t"
      by (metis Red.Cong_class_memb_is_arr \<Lambda>q.arr_char \<Lambda>q.ide_char' \<Lambda>x.arr_char
          mem_Collect_eq subsetI)

    subsection "Normalization"

    text \<open>
      A \emph{normal form} is an identity that is not the source of any non-identity arrow.
    \<close>

    definition NF
    where "NF a \<equiv> Ide a \<and> (\<forall>t. Arr t \<and> Src t = a \<longrightarrow> Ide t)"

    lemma (in reduction_paths) path_from_NF_is_Ide:
    assumes "\<Lambda>.NF a"
    shows "\<lbrakk>Arr U; Src U = a\<rbrakk> \<Longrightarrow> Ide U"
    proof (induct U, simp)
      fix u U
      assume ind: "\<lbrakk>Arr U; Src U = a\<rbrakk> \<Longrightarrow> Ide U"
      assume uU: "Arr (u # U)" and a: "Src (u # U) = a"
      have "\<Lambda>.Ide u"
        using assms a \<Lambda>.NF_def uU by force
      thus "Ide (u # U)"
        using a uU ind
        by (metis Arr_consE Con_Arr_self Con_imp_eq_Srcs Con_initial_right Ide.simps(2)
                  Ide_consI Srcs.simps(2) Srcs_simp\<^sub>P\<^sub>W\<^sub>E \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr
                  \<Lambda>.sources_char\<^sub>\<Lambda> \<Lambda>.trg_ide \<Lambda>.ide_char
                  singleton_insert_inj_eq)
    qed

    lemma NF_reduct_is_trivial:
    assumes "NF a" and "red a b"
    shows "a = b"
    proof -
      interpret \<Lambda>x: reduction_paths .
      have "\<And>U. \<lbrakk>\<Lambda>x.Arr U; a \<in> \<Lambda>x.Srcs U\<rbrakk> \<Longrightarrow> \<Lambda>x.Ide U"
        using assms \<Lambda>x.path_from_NF_is_Ide
        by (simp add: \<Lambda>x.Srcs_simp\<^sub>P\<^sub>W\<^sub>E)
      thus ?thesis
        using assms \<Lambda>x.red_iff
        by (metis \<Lambda>x.Con_Arr_self \<Lambda>x.Resid_Arr_Ide_ind \<Lambda>x.Src_resid \<Lambda>x.path_from_NF_is_Ide)
    qed

    lemma NF_unique:
    assumes "red t u" and "red t u'" and "NF u" and "NF u'"
    shows "u = u'"
      using assms weak_diamond NF_reduct_is_trivial by metis

    text \<open>
      A term is \emph{normalizable} if it is an identity that is reducible to a normal form.
    \<close>

    definition normalizable
    where "normalizable a \<equiv> Ide a \<and> (\<exists>b. red a b \<and> NF b)"

  end

  section "Reduction Paths"

  text \<open>
    In this section we develop further facts about reduction paths for the \<open>\<lambda>\<close>-calculus.
  \<close>

  context reduction_paths
  begin

    subsection "Sources and Targets"

    lemma Srcs_simp\<^sub>\<Lambda>\<^sub>P:
    shows "Arr t \<Longrightarrow> Srcs t = {\<Lambda>.Src (hd t)}"
      by (metis Arr_has_Src Srcs.elims list.sel(1) \<Lambda>.sources_char\<^sub>\<Lambda>)

    lemma Trgs_simp\<^sub>\<Lambda>\<^sub>P:
    shows "Arr t \<Longrightarrow> Trgs t = {\<Lambda>.Trg (last t)}"
      by (metis Arr.simps(1) Arr_has_Trg Trgs.simps(2) Trgs_append
          append_butlast_last_id not_Cons_self2 \<Lambda>.targets_char\<^sub>\<Lambda>)

    lemma sources_single_Src [simp]:
    assumes "\<Lambda>.Arr t"
    shows "sources [\<Lambda>.Src t] = sources [t]"
      using assms
      by (metis \<Lambda>.Con_Arr_Src(1) \<Lambda>.Ide_Src Ide.simps(2) Resid.simps(3) con_char ideE
          ide_char sources_resid \<Lambda>.con_char \<Lambda>.ide_char list.discI \<Lambda>.resid_Arr_Src)

    lemma targets_single_Trg [simp]:
    assumes "\<Lambda>.Arr t"
    shows "targets [\<Lambda>.Trg t] = targets [t]"
      using assms
      by (metis (full_types) Resid.simps(3) conI\<^sub>P \<Lambda>.Arr_Trg \<Lambda>.arr_char \<Lambda>.resid_Arr_Src
          \<Lambda>.resid_Src_Arr \<Lambda>.arr_resid_iff_con targets_resid_sym)

    lemma sources_single_Trg [simp]:
    assumes "\<Lambda>.Arr t"
    shows "sources [\<Lambda>.Trg t] = targets [t]"
      using assms
      by (metis \<Lambda>.Ide_Trg Ide.simps(2) ideE ide_char sources_resid \<Lambda>.ide_char
          targets_single_Trg)

    lemma targets_single_Src [simp]:
    assumes "\<Lambda>.Arr t"
    shows "targets [\<Lambda>.Src t] = sources [t]"
      using assms
      by (metis \<Lambda>.Arr_Src \<Lambda>.Trg_Src sources_single_Src sources_single_Trg)

    lemma single_Src_hd_in_sources:
    assumes "Arr T"
    shows "[\<Lambda>.Src (hd T)] \<in> sources T"
      using assms
      by (metis Arr.simps(1) Arr_has_Src Ide.simps(2) Resid_Arr_Src Srcs_simp\<^sub>P
          \<Lambda>.source_is_ide conI\<^sub>P empty_set ide_char in_sourcesI \<Lambda>.sources_char\<^sub>\<Lambda>
          list.set_intros(1) list.simps(15))

    lemma single_Trg_last_in_targets:
    assumes "Arr T"
    shows "[\<Lambda>.Trg (last T)] \<in> targets T"
      using assms targets_char\<^sub>P Arr_imp_arr_last Trgs_simp\<^sub>\<Lambda>\<^sub>P \<Lambda>.Ide_Trg by fastforce

    lemma in_sources_iff:
    assumes "Arr T"
    shows "A \<in> sources T \<longleftrightarrow> A \<^sup>*\<sim>\<^sup>* [\<Lambda>.Src (hd T)]"
      using assms
      by (meson single_Src_hd_in_sources sources_are_cong sources_cong_closed)

    lemma in_targets_iff:
    assumes "Arr T"
    shows "B \<in> targets T \<longleftrightarrow> B \<^sup>*\<sim>\<^sup>* [\<Lambda>.Trg (last T)]"
      using assms
      by (meson single_Trg_last_in_targets targets_are_cong targets_cong_closed)

    lemma seq_imp_cong_Trg_last_Src_hd:
    assumes "seq T U"
    shows "\<Lambda>.Trg (last T) \<sim> \<Lambda>.Src (hd U)"
      using assms Arr_imp_arr_hd Arr_imp_arr_last Srcs_simp\<^sub>P\<^sub>W\<^sub>E Trgs_simp\<^sub>P\<^sub>W\<^sub>E
            \<Lambda>.cong_reflexive seq_char
      by (metis Srcs_simp\<^sub>\<Lambda>\<^sub>P Trgs_simp\<^sub>\<Lambda>\<^sub>P \<Lambda>.Arr_Trg \<Lambda>.arr_char singleton_inject)

    lemma sources_char\<^sub>\<Lambda>\<^sub>P:
    shows "sources T = {A. Arr T \<and> A \<^sup>*\<sim>\<^sup>* [\<Lambda>.Src (hd T)]}"
      using in_sources_iff arr_char sources_char\<^sub>P by auto

    lemma targets_char\<^sub>\<Lambda>\<^sub>P:
    shows "targets T = {B. Arr T \<and> B \<^sup>*\<sim>\<^sup>* [\<Lambda>.Trg (last T)]}"
      using in_targets_iff arr_char targets_char by auto

    lemma Src_hd_eqI:
    assumes "T \<^sup>*\<sim>\<^sup>* U"
    shows "\<Lambda>.Src (hd T) = \<Lambda>.Src (hd U)"
      using assms
      by (metis Con_imp_eq_Srcs Con_implies_Arr(1) Ide.simps(1) Srcs_simp\<^sub>\<Lambda>\<^sub>P ide_char
          singleton_insert_inj_eq')

    lemma Trg_last_eqI:
    assumes "T \<^sup>*\<sim>\<^sup>* U"
    shows "\<Lambda>.Trg (last T) = \<Lambda>.Trg (last U)"
    proof -
      have 1: "[\<Lambda>.Trg (last T)] \<in> targets T \<and> [\<Lambda>.Trg (last U)] \<in> targets U"
        using assms
        by (metis Con_implies_Arr(1) Ide.simps(1) ide_char single_Trg_last_in_targets)
      have "\<Lambda>.cong (\<Lambda>.Trg (last T)) (\<Lambda>.Trg (last U))"
        by (metis "1" Ide.simps(2) Resid.simps(3) assms con_char cong_implies_coterminal
            coterminal_iff ide_char prfx_implies_con targets_are_cong)
      moreover have "\<Lambda>.Ide (\<Lambda>.Trg (last T)) \<and> \<Lambda>.Ide (\<Lambda>.Trg (last U))"
        using "1" Ide.simps(2) ide_char by blast
      ultimately show ?thesis
        using \<Lambda>.weak_extensionality by blast
    qed

    lemma Trg_last_Src_hd_eqI:
    assumes "seq T U"
    shows "\<Lambda>.Trg (last T) = \<Lambda>.Src (hd U)"
      using assms Arr_imp_arr_hd Arr_imp_arr_last \<Lambda>.Ide_Src \<Lambda>.weak_extensionality \<Lambda>.Ide_Trg
            seq_char seq_imp_cong_Trg_last_Src_hd
      by force

    lemma seqI\<^sub>\<Lambda>\<^sub>P [intro]:
    assumes "Arr T" and "Arr U" and "\<Lambda>.Trg (last T) = \<Lambda>.Src (hd U)"
    shows "seq T U"
      by (metis assms Arr_imp_arr_last Srcs_simp\<^sub>\<Lambda>\<^sub>P \<Lambda>.arr_char \<Lambda>.targets_char\<^sub>\<Lambda>
          Trgs_simp\<^sub>P seq_char)

    lemma conI\<^sub>\<Lambda>\<^sub>P [intro]:
    assumes "arr T" and "arr U" and "\<Lambda>.Src (hd T) = \<Lambda>.Src (hd U)"
    shows "T \<^sup>*\<frown>\<^sup>* U"
      using assms
      by (simp add: Srcs_simp\<^sub>\<Lambda>\<^sub>P arr_char con_char confluence_ind)

    subsection "Mapping Constructors over Paths"

    lemma Arr_map_Lam:
    assumes "Arr T"
    shows "Arr (map \<Lambda>.Lam T)"
    proof -
      interpret Lam: simulation \<Lambda>.resid \<Lambda>.resid \<open>\<lambda>t. if \<Lambda>.arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>\<close>
        using \<Lambda>.Lam_is_simulation by simp
      interpret simulation Resid Resid
                  \<open>\<lambda>T. if Arr T then map (\<lambda>t. if \<Lambda>.arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>) T else []\<close>
        using assms Lam.lifts_to_paths by blast
      have "map (\<lambda>t. if \<Lambda>.Arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>) T = map \<Lambda>.Lam T"
        using assms set_Arr_subset_arr by fastforce
      thus ?thesis
        using assms preserves_reflects_arr [of T] arr_char
        by (simp add: \<open>map (\<lambda>t. if \<Lambda>.Arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>) T = map \<Lambda>.Lam T\<close>)
    qed

    lemma Arr_map_App1:
    assumes "\<Lambda>.Ide b" and "Arr T"
    shows "Arr (map (\<lambda>t. t \<^bold>\<circ> b) T)"
    proof -
      interpret App1: simulation \<Lambda>.resid \<Lambda>.resid \<open>\<lambda>t. if \<Lambda>.arr t then t \<^bold>\<circ> b else \<^bold>\<sharp>\<close>
        using assms \<Lambda>.App_is_simulation1 [of b] by simp
      interpret simulation Resid Resid
                  \<open>\<lambda>T. if Arr T then map (\<lambda>t. if \<Lambda>.arr t then t \<^bold>\<circ> b else \<^bold>\<sharp>) T else []\<close>
        using assms App1.lifts_to_paths by blast
      have "map (\<lambda>t. if \<Lambda>.arr t then t \<^bold>\<circ> b else \<^bold>\<sharp>) T = map (\<lambda>t. t \<^bold>\<circ> b) T"
        using assms set_Arr_subset_arr by auto
      thus ?thesis
        using assms preserves_reflects_arr arr_char
        by (metis (mono_tags, lifting))
    qed

    lemma Arr_map_App2:
    assumes "\<Lambda>.Ide a" and "Arr T"
    shows "Arr (map (\<Lambda>.App a) T)"
    proof -
      interpret App2: simulation \<Lambda>.resid \<Lambda>.resid \<open>\<lambda>u. if \<Lambda>.arr u then a \<^bold>\<circ> u else \<^bold>\<sharp>\<close>
        using assms \<Lambda>.App_is_simulation2 by simp
      interpret simulation Resid Resid
                  \<open>\<lambda>T. if Arr T then map (\<lambda>u. if \<Lambda>.arr u then a \<^bold>\<circ> u else \<^bold>\<sharp>) T else []\<close>
        using assms App2.lifts_to_paths by blast
      have "map (\<lambda>u. if \<Lambda>.arr u then a \<^bold>\<circ> u else \<^bold>\<sharp>) T = map (\<lambda>u. a \<^bold>\<circ> u) T"
        using assms set_Arr_subset_arr by auto
      thus ?thesis
        using assms preserves_reflects_arr arr_char
        by (metis (mono_tags, lifting))
    qed

    interpretation \<Lambda>\<^sub>L\<^sub>a\<^sub>m: sub_rts \<Lambda>.resid \<open>\<lambda>t. \<Lambda>.Arr t \<and> \<Lambda>.is_Lam t\<close>
    proof
     show "\<And>t. \<Lambda>.Arr t \<and> \<Lambda>.is_Lam t \<Longrightarrow> \<Lambda>.arr t"
       by blast
     show "\<And>t. \<Lambda>.Arr t \<and> \<Lambda>.is_Lam t \<Longrightarrow> \<Lambda>.sources t \<subseteq> {t. \<Lambda>.Arr t \<and> \<Lambda>.is_Lam t}"
       by auto
     show "\<lbrakk>\<Lambda>.Arr t \<and> \<Lambda>.is_Lam t; \<Lambda>.Arr u \<and> \<Lambda>.is_Lam u; \<Lambda>.con t u\<rbrakk>
                    \<Longrightarrow> \<Lambda>.Arr (t \\ u) \<and> \<Lambda>.is_Lam (t \\ u)"
             for t u
       apply (cases t; cases u)
                           apply simp_all
       using \<Lambda>.Coinitial_resid_resid
       by presburger
    qed

    interpretation un_Lam: simulation \<Lambda>\<^sub>L\<^sub>a\<^sub>m.resid \<Lambda>.resid
                             \<open>\<lambda>t. if \<Lambda>\<^sub>L\<^sub>a\<^sub>m.arr t then \<Lambda>.un_Lam t else \<^bold>\<sharp>\<close>
    proof
      let ?un_Lam = "\<lambda>t. if \<Lambda>\<^sub>L\<^sub>a\<^sub>m.arr t then \<Lambda>.un_Lam t else \<^bold>\<sharp>"
      show "\<And>t. \<not> \<Lambda>\<^sub>L\<^sub>a\<^sub>m.arr t \<Longrightarrow> ?un_Lam t = \<Lambda>.null"
        by auto
      show "\<And>t u. \<Lambda>\<^sub>L\<^sub>a\<^sub>m.con t u \<Longrightarrow> \<Lambda>.con (?un_Lam t) (?un_Lam u)"
        by auto
      show "\<And>t u. \<Lambda>\<^sub>L\<^sub>a\<^sub>m.con t u \<Longrightarrow> ?un_Lam (\<Lambda>\<^sub>L\<^sub>a\<^sub>m.resid t u) = ?un_Lam t \\ ?un_Lam u"
        using \<Lambda>\<^sub>L\<^sub>a\<^sub>m.resid_closed \<Lambda>\<^sub>L\<^sub>a\<^sub>m.resid_def by auto
    qed

    lemma Arr_map_un_Lam:
    assumes "Arr T" and "set T \<subseteq> Collect \<Lambda>.is_Lam"
    shows "Arr (map \<Lambda>.un_Lam T)"
    proof -
      have "map (\<lambda>t. if \<Lambda>\<^sub>L\<^sub>a\<^sub>m.arr t then \<Lambda>.un_Lam t else \<^bold>\<sharp>) T = map \<Lambda>.un_Lam T"
        using assms set_Arr_subset_arr by auto
      thus ?thesis
        using assms
        by (metis (no_types, lifting) \<Lambda>\<^sub>L\<^sub>a\<^sub>m.path_reflection \<Lambda>.arr_char mem_Collect_eq
            set_Arr_subset_arr subset_code(1) un_Lam.preserves_paths)
    qed

    interpretation \<Lambda>\<^sub>A\<^sub>p\<^sub>p: sub_rts \<Lambda>.resid \<open>\<lambda>t. \<Lambda>.Arr t \<and> \<Lambda>.is_App t\<close>
    proof
      show "\<And>t. \<Lambda>.Arr t \<and> \<Lambda>.is_App t \<Longrightarrow> \<Lambda>.arr t"
        by blast
      show "\<And>t. \<Lambda>.Arr t \<and> \<Lambda>.is_App t \<Longrightarrow> \<Lambda>.sources t \<subseteq> {t. \<Lambda>.Arr t \<and> \<Lambda>.is_App t}"
        by auto
      show "\<lbrakk>\<Lambda>.Arr t \<and> \<Lambda>.is_App t; \<Lambda>.Arr u \<and> \<Lambda>.is_App u; \<Lambda>.con t u\<rbrakk>
                 \<Longrightarrow> \<Lambda>.Arr (t \\ u) \<and> \<Lambda>.is_App (t \\ u)"
            for t u
        using \<Lambda>.Arr_resid
        by (cases t; cases u) auto
    qed

    interpretation un_App1: simulation \<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid \<Lambda>.resid 
                             \<open>\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App1 t else \<^bold>\<sharp>\<close>
    proof
      let ?un_App1 = "\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App1 t else \<^bold>\<sharp>"
      show "\<And>t. \<not> \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t \<Longrightarrow> ?un_App1 t = \<Lambda>.null"
        by auto
      show "\<And>t u. \<Lambda>\<^sub>A\<^sub>p\<^sub>p.con t u \<Longrightarrow> \<Lambda>.con (?un_App1 t) (?un_App1 u)"
        by auto
      show "\<Lambda>\<^sub>A\<^sub>p\<^sub>p.con t u \<Longrightarrow> ?un_App1 (\<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid t u) = ?un_App1 t \\ ?un_App1 u"
              for t u
        using \<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid_def \<Lambda>.Arr_resid
        by (cases t; cases u) auto
    qed

    interpretation un_App2: simulation \<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid \<Lambda>.resid 
                             \<open>\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App2 t else \<^bold>\<sharp>\<close>
    proof
      let ?un_App2 = "\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App2 t else \<^bold>\<sharp>"
      show "\<And>t. \<not> \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t \<Longrightarrow> ?un_App2 t = \<Lambda>.null"
        by auto
      show "\<And>t u. \<Lambda>\<^sub>A\<^sub>p\<^sub>p.con t u \<Longrightarrow> \<Lambda>.con (?un_App2 t) (?un_App2 u)"
        by auto
      show "\<Lambda>\<^sub>A\<^sub>p\<^sub>p.con t u \<Longrightarrow> ?un_App2 (\<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid t u) = ?un_App2 t \\ ?un_App2 u"
              for t u
        using \<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid_def \<Lambda>.Arr_resid
        by (cases t; cases u) auto
    qed

    lemma Arr_map_un_App1:
    assumes "Arr T" and "set T \<subseteq> Collect \<Lambda>.is_App"
    shows "Arr (map \<Lambda>.un_App1 T)"
    proof -
      interpret P\<^sub>A\<^sub>p\<^sub>p: paths_in_rts \<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid
        ..
      interpret un_App1: simulation P\<^sub>A\<^sub>p\<^sub>p.Resid Resid
                          \<open>\<lambda>T. if P\<^sub>A\<^sub>p\<^sub>p.Arr T then
                                 map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App1 t else \<^bold>\<sharp>) T
                               else []\<close>
        using un_App1.lifts_to_paths by simp
      have 1: "map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App1 t else \<^bold>\<sharp>) T = map \<Lambda>.un_App1 T"
        using assms set_Arr_subset_arr by auto
      have 2: "P\<^sub>A\<^sub>p\<^sub>p.Arr T"
        using assms set_Arr_subset_arr \<Lambda>\<^sub>A\<^sub>p\<^sub>p.path_reflection [of T] by blast
      hence "arr (if P\<^sub>A\<^sub>p\<^sub>p.Arr T then map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App1 t else \<^bold>\<sharp>) T else [])"
        using un_App1.preserves_reflects_arr [of T] by blast
      hence "Arr (if P\<^sub>A\<^sub>p\<^sub>p.Arr T then map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App1 t else \<^bold>\<sharp>) T else [])"
        using arr_char by auto
      hence "Arr (if P\<^sub>A\<^sub>p\<^sub>p.Arr T then map \<Lambda>.un_App1 T else [])"
        using 1 by metis
      thus ?thesis
        using 2 by simp
    qed

    lemma Arr_map_un_App2:
    assumes "Arr T" and "set T \<subseteq> Collect \<Lambda>.is_App"
    shows "Arr (map \<Lambda>.un_App2 T)"
    proof -
      interpret P\<^sub>A\<^sub>p\<^sub>p: paths_in_rts \<Lambda>\<^sub>A\<^sub>p\<^sub>p.resid
        ..
      interpret un_App2: simulation P\<^sub>A\<^sub>p\<^sub>p.Resid Resid
                           \<open>\<lambda>T. if P\<^sub>A\<^sub>p\<^sub>p.Arr T then
                                  map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App2 t else \<^bold>\<sharp>) T
                                else []\<close>
        using un_App2.lifts_to_paths by simp
      have 1: "map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App2 t else \<^bold>\<sharp>) T = map \<Lambda>.un_App2 T"
        using assms set_Arr_subset_arr by auto
      have 2: "P\<^sub>A\<^sub>p\<^sub>p.Arr T"
        using assms set_Arr_subset_arr \<Lambda>\<^sub>A\<^sub>p\<^sub>p.path_reflection [of T] by blast
      hence "arr (if P\<^sub>A\<^sub>p\<^sub>p.Arr T then map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App2 t else \<^bold>\<sharp>) T else [])"
        using un_App2.preserves_reflects_arr [of T] by blast
      hence "Arr (if P\<^sub>A\<^sub>p\<^sub>p.Arr T then map (\<lambda>t. if \<Lambda>\<^sub>A\<^sub>p\<^sub>p.arr t then \<Lambda>.un_App2 t else \<^bold>\<sharp>) T else [])"
        using arr_char by blast
      hence "Arr (if P\<^sub>A\<^sub>p\<^sub>p.Arr T then map \<Lambda>.un_App2 T else [])"
        using 1 by metis
      thus ?thesis
        using 2 by simp
    qed

    lemma map_App_map_un_App1:
    shows "\<lbrakk>Arr U; set U \<subseteq> Collect \<Lambda>.is_App; \<Lambda>.Ide b; \<Lambda>.un_App2 ` set U \<subseteq> {b}\<rbrakk> \<Longrightarrow>
              map (\<lambda>t. \<Lambda>.App t b) (map \<Lambda>.un_App1 U) = U"
      by (induct U) auto

    lemma map_App_map_un_App2:
    shows "\<lbrakk>Arr U; set U \<subseteq> Collect \<Lambda>.is_App; \<Lambda>.Ide a; \<Lambda>.un_App1 ` set U \<subseteq> {a}\<rbrakk> \<Longrightarrow>
              map (\<Lambda>.App a) (map \<Lambda>.un_App2 U) = U"
      by (induct U) auto

    lemma map_Lam_Resid:
    assumes "coinitial T U"
    shows "map \<Lambda>.Lam (T \<^sup>*\\\<^sup>* U) = map \<Lambda>.Lam T \<^sup>*\\\<^sup>* map \<Lambda>.Lam U"
    proof -
      interpret Lam: simulation \<Lambda>.resid \<Lambda>.resid \<open>\<lambda>t. if \<Lambda>.arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>\<close>
        using \<Lambda>.Lam_is_simulation by simp
      interpret Lamx: simulation Resid Resid
                        \<open>\<lambda>T. if Arr T then
                               map (\<lambda>t. if \<Lambda>.arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>) T
                         else []\<close>
        using Lam.lifts_to_paths by simp
      have "\<And>T. Arr T \<Longrightarrow> map (\<lambda>t. if \<Lambda>.arr t then \<^bold>\<lambda>\<^bold>[t\<^bold>] else \<^bold>\<sharp>) T = map \<Lambda>.Lam T"
        using set_Arr_subset_arr by auto
      moreover have "Arr (T \<^sup>*\\\<^sup>* U)"
        using assms confluence\<^sub>P Con_imp_Arr_Resid con_char by force
      moreover have "T \<^sup>*\<frown>\<^sup>* U"
        using assms confluence by simp
      moreover have "Arr T \<and> Arr U"
        using assms arr_char by auto
      ultimately show ?thesis
        using assms Lamx.preserves_resid [of T U] by presburger
    qed

    lemma map_App1_Resid:
    assumes "\<Lambda>.Ide x" and "coinitial T U"
    shows "map (\<Lambda>.App x) (T \<^sup>*\\\<^sup>* U) = map (\<Lambda>.App x) T \<^sup>*\\\<^sup>* map (\<Lambda>.App x) U"
    proof -
      interpret App: simulation \<Lambda>.resid \<Lambda>.resid \<open>\<lambda>t. if \<Lambda>.arr t then x \<^bold>\<circ> t else \<^bold>\<sharp>\<close>
        using assms \<Lambda>.App_is_simulation2 by simp
      interpret Appx: simulation Resid Resid
                        \<open>\<lambda>T. if Arr T then map (\<lambda>t. if \<Lambda>.arr t then x \<^bold>\<circ> t else \<^bold>\<sharp>) T else []\<close>
        using App.lifts_to_paths by simp
      have "\<And>T. Arr T \<Longrightarrow> map (\<lambda>t. if \<Lambda>.arr t then x \<^bold>\<circ> t else \<^bold>\<sharp>) T = map (\<Lambda>.App x) T"
        using set_Arr_subset_arr by auto
      moreover have "Arr (T \<^sup>*\\\<^sup>* U)"
        using assms confluence\<^sub>P Con_imp_Arr_Resid con_char by force
      moreover have "T \<^sup>*\<frown>\<^sup>* U"
        using assms confluence by simp
      moreover have "Arr T \<and> Arr U"
        using assms arr_char by auto
      ultimately show ?thesis
        using assms Appx.preserves_resid [of T U] by presburger
    qed

    lemma map_App2_Resid:
    assumes "\<Lambda>.Ide x" and "coinitial T U"
    shows "map (\<lambda>t. t \<^bold>\<circ> x) (T \<^sup>*\\\<^sup>* U) = map (\<lambda>t. t \<^bold>\<circ> x) T \<^sup>*\\\<^sup>* map (\<lambda>t. t \<^bold>\<circ> x) U"
    proof -
      interpret App: simulation \<Lambda>.resid \<Lambda>.resid \<open>\<lambda>t. if \<Lambda>.arr t then t \<^bold>\<circ> x else \<^bold>\<sharp>\<close>
        using assms \<Lambda>.App_is_simulation1 by simp
      interpret Appx: simulation Resid Resid
                        \<open>\<lambda>T. if Arr T then map (\<lambda>t. if \<Lambda>.arr t then t \<^bold>\<circ> x else \<^bold>\<sharp>) T else []\<close>
        using App.lifts_to_paths by simp
      have "\<And>T. Arr T \<Longrightarrow> map (\<lambda>t. if \<Lambda>.arr t then t \<^bold>\<circ> x else \<^bold>\<sharp>) T = map (\<lambda>t. t \<^bold>\<circ> x) T"
        using set_Arr_subset_arr by auto
      moreover have "Arr (T \<^sup>*\\\<^sup>* U)"
        using assms confluence\<^sub>P Con_imp_Arr_Resid con_char by force
      moreover have "T \<^sup>*\<frown>\<^sup>* U"
        using assms confluence by simp
      moreover have "Arr T \<and> Arr U"
        using assms arr_char by auto
      ultimately show ?thesis
        using assms Appx.preserves_resid [of T U] by presburger
    qed

    lemma cong_map_Lam:
    shows "T \<^sup>*\<sim>\<^sup>* U \<Longrightarrow> map \<Lambda>.Lam T \<^sup>*\<sim>\<^sup>* map \<Lambda>.Lam U"
      apply (induct U arbitrary: T)
       apply (simp add: ide_char)
      by (metis map_Lam_Resid cong_implies_coinitial cong_reflexive ideE
          map_is_Nil_conv Con_imp_Arr_Resid arr_char)

    lemma cong_map_App1:
    shows "\<lbrakk>\<Lambda>.Ide x; T \<^sup>*\<sim>\<^sup>* U\<rbrakk> \<Longrightarrow> map (\<Lambda>.App x) T \<^sup>*\<sim>\<^sup>* map (\<Lambda>.App x) U"
      apply (induct U arbitrary: x T)
       apply (simp add: ide_char)
      apply (intro conjI)
      by (metis Nil_is_map_conv arr_resid_iff_con con_char con_imp_coinitial
                cong_reflexive ideE map_App1_Resid)+

    lemma cong_map_App2:
    shows "\<lbrakk>\<Lambda>.Ide x; T \<^sup>*\<sim>\<^sup>* U\<rbrakk> \<Longrightarrow> map (\<lambda>X. X \<^bold>\<circ> x) T \<^sup>*\<sim>\<^sup>* map (\<lambda>X. X \<^bold>\<circ> x) U"
      apply (induct U arbitrary: x T)
       apply (simp add: ide_char)
      apply (intro conjI)
      by (metis Nil_is_map_conv arr_resid_iff_con con_char cong_implies_coinitial
                   cong_reflexive ide_def arr_char ideE map_App2_Resid)+

    subsection "Decomposition of `App Paths'"

    text \<open>
      The following series of results is aimed at showing that a reduction path, all of whose
      transitions have \<open>App\<close> as their top-level constructor, can be factored up to congruence
      into a reduction path in which only the ``rator'' components are reduced, followed
      by a reduction path in which only the ``rand'' components are reduced.
    \<close>

    lemma orthogonal_App_single_single:
    assumes "\<Lambda>.Arr t" and "\<Lambda>.Arr u"
    shows "[\<Lambda>.Src t \<^bold>\<circ> u] \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src u] = [\<Lambda>.Trg t \<^bold>\<circ> u]"
    and "[t \<^bold>\<circ> \<Lambda>.Src u] \<^sup>*\\\<^sup>* [\<Lambda>.Src t \<^bold>\<circ> u] = [t \<^bold>\<circ> \<Lambda>.Trg u]"
      using assms arr_char \<Lambda>.Arr_not_Nil by auto

    lemma orthogonal_App_single_Arr:
    shows "\<lbrakk>Arr [t]; Arr U\<rbrakk> \<Longrightarrow>
              map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd U)] = map (\<Lambda>.App (\<Lambda>.Trg t)) U \<and>
              [t \<^bold>\<circ> \<Lambda>.Src (hd U)] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) U = [t \<^bold>\<circ> \<Lambda>.Trg (last U)]"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>Arr [t]; Arr []\<rbrakk> \<Longrightarrow>
                   map (\<Lambda>.App (\<Lambda>.Src t)) [] \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd [])] = map (\<Lambda>.App (\<Lambda>.Trg t)) [] \<and>
                   [t \<^bold>\<circ> \<Lambda>.Src (hd [])] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) [] = [t \<^bold>\<circ> \<Lambda>.Trg (last [])]"
        by fastforce
      fix t u U
      assume ind: "\<And>t. \<lbrakk>Arr [t]; Arr U\<rbrakk> \<Longrightarrow>
                         map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd U)] =
                         map (\<Lambda>.App (\<Lambda>.Trg t)) U \<and>
                         [t \<^bold>\<circ> \<Lambda>.Src (hd U)] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) U = [t \<^bold>\<circ> \<Lambda>.Trg (last U)]"
      assume t: "Arr [t]"
      assume uU: "Arr (u # U)"
      show "map (\<Lambda>.App (\<Lambda>.Src t)) (u # U) \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] =
            map (\<Lambda>.App (\<Lambda>.Trg t)) (u # U) \<and>
            [t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) (u # U) =
            [t \<^bold>\<circ> \<Lambda>.Trg (last (u # U))]"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using t uU orthogonal_App_single_single by simp
        assume U: "U \<noteq> []"
        have 2: "coinitial ([\<Lambda>.Src t \<^bold>\<circ> u] @ map (\<Lambda>.App (\<Lambda>.Src t)) U) [t \<^bold>\<circ> \<Lambda>.Src u]"
        proof
          show 3: "arr ([\<Lambda>.Src t \<^bold>\<circ> u] @ map (\<Lambda>.App (\<Lambda>.Src t)) U)"
            using t uU
            by (metis Arr_iff_Con_self Arr_map_App2 Con_rec(1) append_Cons append_Nil arr_char
                \<Lambda>.Con_implies_Arr2 \<Lambda>.Ide_Src \<Lambda>.con_char list.simps(9))
          show "sources ([\<Lambda>.Src t \<^bold>\<circ> u] @ map (\<Lambda>.App (\<Lambda>.Src t)) U) = sources [t \<^bold>\<circ> \<Lambda>.Src u]"
          proof -
            have "seq [\<Lambda>.Src t \<^bold>\<circ> u] (map (\<Lambda>.App (\<Lambda>.Src t)) U)"
              using U 3 arr_append_imp_seq by force
            thus ?thesis
              using sources_append [of "[\<Lambda>.Src t \<^bold>\<circ> u]" "map (\<Lambda>.App (\<Lambda>.Src t)) U"]
                    sources_single_Src [of "\<Lambda>.Src t \<^bold>\<circ> u"]
                    sources_single_Src [of "t \<^bold>\<circ> \<Lambda>.Src u"]
              using arr_char t
              by (simp add: seq_char)
          qed
        qed
        show ?thesis
        proof
          show 4: "map (\<Lambda>.App (\<Lambda>.Src t)) (u # U) \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] =
                   map (\<Lambda>.App (\<Lambda>.Trg t)) (u # U)"
          proof -
            have "map (\<Lambda>.App (\<Lambda>.Src t)) (u # U) \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] =
                  ([\<Lambda>.Src t \<^bold>\<circ> u] @ map (\<Lambda>.App (\<Lambda>.Src t)) U) \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src u]"
              by simp
            also have "... = [\<Lambda>.Src t \<^bold>\<circ> u] \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src u] @
                               map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>* ([t \<^bold>\<circ> \<Lambda>.Src u] \<^sup>*\\\<^sup>* [\<Lambda>.Src t \<^bold>\<circ> u])"
              by (meson "2" Resid_append(1) con_char confluence not_Cons_self2)
            also have "... = [\<Lambda>.Trg t \<^bold>\<circ> u] @ map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Trg u]"
              using t \<Lambda>.Arr_not_Nil
              by (metis Arr_imp_arr_hd \<Lambda>.arr_char list.sel(1) orthogonal_App_single_single(1)
                  orthogonal_App_single_single(2) uU)
            also have "... = [\<Lambda>.Trg t \<^bold>\<circ> u] @ map (\<Lambda>.App (\<Lambda>.Trg t)) U"
            proof -
              have "\<Lambda>.Src (hd U) = \<Lambda>.Trg u"
                using U uU Arr.elims(2) Srcs_simp\<^sub>\<Lambda>\<^sub>P by force
              thus ?thesis
                using t uU ind Arr.elims(2) by fastforce
            qed
            also have "... = map (\<Lambda>.App (\<Lambda>.Trg t)) (u # U)"
              by auto
            finally show ?thesis by blast
          qed
          show "[t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) (u # U) =
                [t \<^bold>\<circ> \<Lambda>.Trg (last (u # U))]"
          proof -
            have "[t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) (u # U) =
                  ([t \<^bold>\<circ> \<Lambda>.Src (hd (u # U))] \<^sup>*\\\<^sup>* [\<Lambda>.Src t \<^bold>\<circ> u]) \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) U"
              by (metis U 4 Con_sym Resid_cons(2) list.distinct(1) list.simps(9) map_is_Nil_conv)
            also have "... = [t \<^bold>\<circ> \<Lambda>.Trg u] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) U"
              by (metis Arr_imp_arr_hd lambda_calculus.arr_char list.sel(1)
                  orthogonal_App_single_single(2) t uU)
            also have "... = [t \<^bold>\<circ> \<Lambda>.Trg (last (u # U))]"
              by (metis 2 t U uU Con_Arr_self Con_cons(1) Con_implies_Arr(1) Trg_last_Src_hd_eqI
                  arr_append_imp_seq coinitialE ind \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                  \<Lambda>.lambda.inject(3) last.simps list.distinct(1) list.map_sel(1) map_is_Nil_conv)
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma orthogonal_App_Arr_Arr:
    shows "\<lbrakk>Arr T; Arr U\<rbrakk> \<Longrightarrow>
              map (\<Lambda>.App (\<Lambda>.Src (hd T))) U \<^sup>*\\\<^sup>* map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Src (hd U))) T =
              map (\<Lambda>.App (\<Lambda>.Trg (last T))) U \<and>
              map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src (hd T))) U =
              map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"
    proof (induct T arbitrary: U)
      show "\<And>U. \<lbrakk>Arr []; Arr U\<rbrakk>
                  \<Longrightarrow> map (\<Lambda>.App (\<Lambda>.Src (hd []))) U \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) [] =
                      map (\<Lambda>.App (\<Lambda>.Trg (last []))) U \<and>
                      map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) [] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src (hd []))) U =
                      map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) []"
        by simp
      fix t T U
      assume ind: "\<And>U. \<lbrakk>Arr T; Arr U\<rbrakk>
                          \<Longrightarrow> map (\<Lambda>.App (\<Lambda>.Src (hd T))) U \<^sup>*\\\<^sup>*
                                map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Src (hd U))) T =
                              map (\<Lambda>.App (\<Lambda>.Trg (last T))) U \<and>
                              map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src (hd T))) U =
                              map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"
      assume tT: "Arr (t # T)"
      assume U: "Arr U"
      show "map (\<Lambda>.App (\<Lambda>.Src (hd (t # T)))) U \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) (t # T) =
            map (\<Lambda>.App (\<Lambda>.Trg (last (t # T)))) U \<and>
            map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) (t # T) \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src (hd (t # T)))) U =
            map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) (t # T)"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using tT U
          by (simp add: orthogonal_App_single_Arr)
        assume T: "T \<noteq> []"
        have 1: "Arr T"
          using T tT Arr_imp_Arr_tl by fastforce
        have 2: "\<Lambda>.Src (hd T) = \<Lambda>.Trg t"
          using tT T Arr.elims(2) Srcs_simp\<^sub>\<Lambda>\<^sub>P by force
        show ?thesis
        proof
          show 3: "map (\<Lambda>.App (\<Lambda>.Src (hd (t # T)))) U \<^sup>*\\\<^sup>*
                     map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) (t # T) =
                   map (\<Lambda>.App (\<Lambda>.Trg (last (t # T)))) U"
          proof -
            have "map (\<Lambda>.App (\<Lambda>.Src (hd (t # T)))) U \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) (t # T) =
                  map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>*
                  ([\<Lambda>.App t (\<Lambda>.Src (hd U))] @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T)"
              using tT U by simp
            also have "... = (map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd U)]) \<^sup>*\\\<^sup>*
                             map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T"
              using tT U Resid_append(2)
              by (metis Con_appendI(2) Resid.simps(1) T map_is_Nil_conv not_Cons_self2)
            also have "... = map (\<Lambda>.App (\<Lambda>.Trg t)) U \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T"
              using tT U orthogonal_App_single_Arr Arr_imp_arr_hd by fastforce
            also have "... = map (\<Lambda>.App (\<Lambda>.Trg (last (t # T)))) U"
              using tT U 1 2 ind by auto
            finally show ?thesis by blast
          qed
          show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) (t # T) \<^sup>*\\\<^sup>*
                  map (\<Lambda>.App (\<Lambda>.Src (hd (t # T)))) U =
                map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) (t # T)"
          proof -
            have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) (t # T) \<^sup>*\\\<^sup>*
                    map (\<Lambda>.App (\<Lambda>.Src (hd (t # T)))) U =
                  ([t \<^bold>\<circ> \<Lambda>.Src (hd U)] @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T) \<^sup>*\\\<^sup>*
                    map (\<Lambda>.App (\<Lambda>.Src t)) U"
              using tT U by simp
            also have "... = ([t \<^bold>\<circ> \<Lambda>.Src (hd U)] \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Src t)) U) @
                             (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T \<^sup>*\\\<^sup>*
                                 (map (\<Lambda>.App (\<Lambda>.Src t)) U \<^sup>*\\\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src (hd U)]))"
              using tT U 3 Con_sym
                    Resid_append(1)
                      [of "[t \<^bold>\<circ> \<Lambda>.Src (hd U)]" "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T"
                       "map (\<Lambda>.App (\<Lambda>.Src t)) U"]
              by fastforce
            also have "... = [t \<^bold>\<circ> \<Lambda>.Trg (last U)] @
                               map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T \<^sup>*\\\<^sup>* map (\<Lambda>.App (\<Lambda>.Trg t)) U"
              using tT U Arr_imp_arr_hd orthogonal_App_single_Arr by fastforce
            also have "... = [t \<^bold>\<circ> \<Lambda>.Trg (last U)] @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"
              using tT U "1" "2" ind by presburger
            also have "... = map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) (t # T)"
              by simp
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma orthogonal_App_cong:
    assumes "Arr T" and "Arr U"
    shows "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map (\<Lambda>.App (\<Lambda>.Trg (last T))) U \<^sup>*\<sim>\<^sup>*
           map (\<Lambda>.App (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"
(*
      using assms orthogonal_App_Arr_Arr [of T U] Arr.simps(1) Con_imp_Arr_Resid
            Con_implies_Arr(1) Resid_Arr_self  Resid_append_ind ide_char list.map_disc_iff cube
      by (smt (verit))
*)
    proof
      have 1: "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T)"
        using assms Arr_imp_arr_hd Arr_map_App1 \<Lambda>.Ide_Src by force
      have 2: "Arr (map (\<Lambda>.App (\<Lambda>.Trg (last T))) U)"
        using assms Arr_imp_arr_last Arr_map_App2 \<Lambda>.Ide_Trg by force
      have 3: "Arr (map (\<Lambda>.App (\<Lambda>.Src (hd T))) U)"
        using assms Arr_imp_arr_hd Arr_map_App2 \<Lambda>.Ide_Src by force
      have 4: "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T)"
        using assms Arr_imp_arr_last Arr_map_App1 \<Lambda>.Ide_Trg by force
      have 5: "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map (\<Lambda>.App (\<Lambda>.Trg (last T))) U)"
        using assms
        by (metis (no_types, lifting) 1 2 Arr.simps(2) Arr_has_Src Arr_imp_arr_last
            Srcs.simps(1) Srcs_Resid_Arr_single Trgs_simp\<^sub>P arr_append arr_char last_map
            orthogonal_App_single_Arr seq_char)
      have 6: "Arr (map (\<Lambda>.App (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T)"
        using assms
        by (metis (no_types, lifting) 3 4 Arr.simps(2) Arr_has_Src Arr_imp_arr_hd
            Srcs.simps(1) Srcs.simps(2) Srcs_Resid Srcs_simp\<^sub>P arr_append arr_char hd_map
            orthogonal_App_single_Arr seq_char)
      have 7: "Con (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U)
                   (map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T)"
        using assms orthogonal_App_Arr_Arr [of T U]
        by (metis 1 2 5 6 Con_imp_eq_Srcs Resid.simps(1) Srcs_append confluence_ind)
      have 8: "Con (map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T)
                   (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U)"
        using 7 Con_sym by simp
      show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U \<^sup>*\<lesssim>\<^sup>*
            map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"
      proof -
        have "(map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U) \<^sup>*\\\<^sup>*
                (map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T) =
              map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T @
                (map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U \<^sup>*\\\<^sup>* map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U) \<^sup>*\\\<^sup>*
                   (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T)"
          using assms 7 orthogonal_App_Arr_Arr
                Resid_append2
                  [of "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T" "map (\<Lambda>.App (\<Lambda>.Trg (last T))) U"
                      "map (\<Lambda>.App (\<Lambda>.Src (hd T))) U" "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"]
          by fastforce
        moreover have "Ide ..."
          using assms 1 2 3 4 5 6 7 Resid_Arr_self
          by (metis Arr_append_iff\<^sub>P Con_Arr_self Con_imp_Arr_Resid Ide_appendI\<^sub>P
              Resid_Ide_Arr_ind append_Nil2 calculation)
        ultimately show ?thesis
          using ide_char by presburger
      qed
      show "map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T \<^sup>*\<lesssim>\<^sup>*
            map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U"
      proof -
        have "map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T =
              map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U"
          by (simp add: assms orthogonal_App_Arr_Arr)
        have "(map ((\<^bold>\<circ>) (\<Lambda>.Src (hd T))) U @ map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T) \<^sup>*\\\<^sup>*
                (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T @ map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U) =
              (map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U) \<^sup>*\\\<^sup>* map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U @
                 (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T \<^sup>*\\\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T) \<^sup>*\\\<^sup>*
                    (map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U \<^sup>*\\\<^sup>* map ((\<^bold>\<circ>) (\<Lambda>.Trg (last T))) U)"
          using assms 8 orthogonal_App_Arr_Arr [of T U]
                Resid_append2
                  [of "map (\<Lambda>.App (\<Lambda>.Src (hd T))) U" "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last U)) T"
                      "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd U)) T" "map (\<Lambda>.App (\<Lambda>.Trg (last T))) U"]
          by fastforce
        moreover have "Ide ..."
          using assms 1 2 3 4 5 6 8 Resid_Arr_self Arr_append_iff\<^sub>P Con_sym
          by (metis Con_Arr_self Con_imp_Arr_Resid Ide_appendI\<^sub>P Resid_Ide_Arr_ind
              append_Nil2 calculation)
        ultimately show ?thesis
          using ide_char by presburger
      qed
    qed

    text \<open>
      We arrive at the final objective of this section: factorization, up to congruence,
      of a path whose transitions all have \<open>App\<close> as the top-level constructor,
      into the composite of a path that reduces only the ``rators'' and a path
      that reduces only the ``rands''.
    \<close>

    lemma map_App_decomp:
    shows "\<lbrakk>Arr U; set U \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow>
             map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 (hd U))) (map \<Lambda>.un_App1 U) @
               map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U) \<^sup>*\<sim>\<^sup>*
             U"
    proof (induct U)
      show "Arr [] \<Longrightarrow> map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 (hd []))) (map \<Lambda>.un_App1 []) @
                         map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last [])))) (map \<Lambda>.un_App2 []) \<^sup>*\<sim>\<^sup>*
                       []"
        by simp
      fix u U
      assume ind: "\<lbrakk>Arr U; set U \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow>
                       map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Src (\<Lambda>.un_App2 (hd U)))) (map \<Lambda>.un_App1 U) @
                         map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U) \<^sup>*\<sim>\<^sup>*
                       U"
      assume uU: "Arr (u # U)"
      assume set: "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
      have u: "\<Lambda>.Arr u \<and> \<Lambda>.is_App u"
        using set set_Arr_subset_arr uU by fastforce
      show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 (hd (u # U)))) (map \<Lambda>.un_App1 (u # U)) @
              map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
            u # U"
      proof (cases "U = []")
        assume U: "U = []"
        show ?thesis
          using u U \<Lambda>.Con_sym \<Lambda>.Ide_iff_Src_self \<Lambda>.resid_Arr_self \<Lambda>.resid_Src_Arr
                \<Lambda>.resid_Arr_Src \<Lambda>.Src_resid \<Lambda>.Arr_resid ide_char \<Lambda>.Arr_not_Nil
          by (cases u, simp_all)
        next
        assume U: "U \<noteq> []"
        have 1: "Arr (map \<Lambda>.un_App1 U)"
          using U set Arr_map_un_App1 uU
          by (metis Arr_imp_Arr_tl list.distinct(1) list.map_disc_iff list.map_sel(2) list.sel(3))
        have 2: "Arr [\<Lambda>.un_App2 u]"
          using U uU set
          by (metis Arr.simps(2) Arr_imp_arr_hd Arr_map_un_App2 hd_map list.discI list.sel(1))
        have 3: "\<Lambda>.Arr (\<Lambda>.un_App1 u) \<and> \<Lambda>.Arr (\<Lambda>.un_App2 u)"
          using uU set
          by (metis Arr_imp_arr_hd Arr_map_un_App1 Arr_map_un_App2 \<Lambda>.arr_char
              list.distinct(1) list.map_sel(1) list.sel(1))
        have 4: "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                   [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u] \<^sup>*\<sim>\<^sup>*
                 [\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u] @
                   map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U)"
        proof -
          have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U) =
                map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U)"
            using U uU set by simp
          moreover have "map (\<Lambda>.App (\<Lambda>.Trg (last (map \<Lambda>.un_App1 U)))) [\<Lambda>.un_App2 u] =
                         [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]"
            by (simp add: U last_map)
          moreover have "map (\<Lambda>.App (\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)))) [\<Lambda>.un_App2 u] =
                         [\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u]"
            by simp
          moreover have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U) =
                         map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U)"
            using U uU set by blast
          ultimately show ?thesis
            using U uU set last_map hd_map 1 2 3
                  orthogonal_App_cong [of "map \<Lambda>.un_App1 U" "[\<Lambda>.un_App2 u]"]
            by presburger
        qed
        have 5: "\<Lambda>.Arr (\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u))"
          by (simp add: 3)
        have 6: "Arr (map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U))"
          by (metis 1 Arr_imp_arr_last Arr_map_App2 Arr_map_un_App2 Con_implies_Arr(2)
              Ide.simps(1) Resid_Arr_self Resid_cons(2) U insert_subset
              \<Lambda>.Ide_Trg \<Lambda>.arr_char last_map list.simps(15) set uU)
        have 7: "\<Lambda>.Arr (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))"
          by (metis 4 Arr.simps(2) Arr_append_iff\<^sub>P Con_implies_Arr(2) Ide.simps(1)
              U ide_char \<Lambda>.Arr.simps(4) \<Lambda>.arr_char list.map_disc_iff not_Cons_self2)
        have 8: "\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) = \<Lambda>.Trg (\<Lambda>.un_App1 u)"
        proof -
          have "\<Lambda>.Src (hd U) = \<Lambda>.Trg u"
            using u uU U by fastforce
          thus ?thesis
            using u uU U set
            apply (cases u; cases "hd U")
                                apply (simp_all add: list.map_sel(1))
            using list.set_sel(1)
            by fastforce
        qed
        have 9: "\<Lambda>.Src (\<Lambda>.un_App2 (hd U)) = \<Lambda>.Trg (\<Lambda>.un_App2 u)"
        proof -
          have "\<Lambda>.Src (hd U) = \<Lambda>.Trg u"
            using u uU U by fastforce
          thus ?thesis
            using u uU U set
            apply (cases u; cases "hd U")
                                apply simp_all
            by (metis lambda_calculus.lambda.disc(15) list.set_sel(1) mem_Collect_eq
                subset_code(1))
        qed
        have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 (hd (u # U)))) (map \<Lambda>.un_App1 (u # U)) @
                map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) (map \<Lambda>.un_App2 (u # U)) =
              [\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u))
                     (map \<Lambda>.un_App1 U) @ [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]) @
                  map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))) (map \<Lambda>.un_App2 U)"
          using uU U by simp
        also have 12: "cong ... ([\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                               ([\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u] @
                                  map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U)) @
                                 map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))) (map \<Lambda>.un_App2 U))"
        proof (intro cong_append [of "[\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)]"]
                     cong_append [where U = "map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X)
                                                 (map \<Lambda>.un_App2 U)"])
          show "[\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] \<^sup>*\<sim>\<^sup>* [\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)]"
            using 5 arr_char cong_reflexive Arr.simps(2) \<Lambda>.arr_char by presburger
          show "map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U) \<^sup>*\<sim>\<^sup>*
                map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U)"
            using 6 cong_reflexive by auto
          show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                  [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u] \<^sup>*\<sim>\<^sup>*
                [\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u] @
                  map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U)"
            using 4 by simp
          show 10: "seq [\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)]
                        ((map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                           [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]) @
                             map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U))"
          proof
            show "Arr [\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)]"
              using 5 Arr.simps(2) by blast
            show "Arr ((map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                          [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]) @
                         map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U))"
            proof (intro Arr_appendI\<^sub>P\<^sub>W\<^sub>E)
              show "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U))"
                using 1 3 Arr_map_App1 lambda_calculus.Ide_Src by blast
              show "Arr [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]"
                by (simp add: 3 7)
              show "Trg (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U)) =
                    Src [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]"
                by (metis 4 Arr_appendE\<^sub>P\<^sub>W\<^sub>E Con_implies_Arr(2) Ide.simps(1) U ide_char
                    list.map_disc_iff not_Cons_self2)
              show "Arr (map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U))"
                using 6 by simp
              show "Trg (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                           [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]) =
                    Src (map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U))"
                using U uU set 1 3 6 7 9 Srcs_simp\<^sub>P\<^sub>W\<^sub>E Arr_imp_arr_hd Arr_imp_arr_last
                apply auto
                by (metis Nil_is_map_conv hd_map \<Lambda>.Src.simps(4) \<Lambda>.Src_Trg \<Lambda>.Trg_Trg
                    last_map list.map_comp)
            qed
            show "\<Lambda>.Trg (last [\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)]) =
                  \<Lambda>.Src (hd ((map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                                [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u]) @
                               map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U)))"
              using 8 9
              by (simp add: 3 U hd_map)
          qed
          show "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)) (map \<Lambda>.un_App1 U) @
                      [\<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> \<Lambda>.un_App2 u])
                    (map (\<lambda>X. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> X) (map \<Lambda>.un_App2 U))"
            by (metis Nil_is_map_conv U 10 append_is_Nil_conv arr_append_imp_seq seqE)
        qed
        also have 11: "[\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                         ([\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u] @
                            map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U)) @
                           map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))) (map \<Lambda>.un_App2 U) =
                       ([\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                         [\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u]) @
                         map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U) @
                           map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))) (map \<Lambda>.un_App2 U)"
          by simp
        also have "cong ... ([u] @ U)"
        proof (intro cong_append)
          show "seq ([\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                       [\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u])
                    (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U) @
                       map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))) (map \<Lambda>.un_App2 U))"
            by (metis 5 11 12 U Arr.simps(1-2) Con_implies_Arr(2) Ide.simps(1) Nil_is_map_conv
                append_is_Nil_conv arr_append_imp_seq arr_char ide_char \<Lambda>.arr_char)
          show "[\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                  [\<Lambda>.Src (hd (map \<Lambda>.un_App1 U)) \<^bold>\<circ> \<Lambda>.un_App2 u] \<^sup>*\<sim>\<^sup>*
                [u]"
          proof -
            have "[\<Lambda>.un_App1 u \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)] @
                    [\<Lambda>.Trg (\<Lambda>.un_App1 u) \<^bold>\<circ> \<Lambda>.un_App2 u] \<^sup>*\<sim>\<^sup>*
                  [u]"
              using u uU U \<Lambda>.Arr_Trg \<Lambda>.Arr_not_Nil \<Lambda>.resid_Arr_self
              apply (cases u)
                  apply auto
              by force+
            thus ?thesis using 8 by simp
          qed
          show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [\<Lambda>.un_App2 u])) (map \<Lambda>.un_App1 U) @
                  map ((\<^bold>\<circ>) (\<Lambda>.Trg (\<Lambda>.un_App1 (last U)))) (map \<Lambda>.un_App2 U) \<^sup>*\<sim>\<^sup>*
                U"
            using ind set 9
            apply simp
            using U uU by blast
        qed
        also have "[u] @ U = u # U"
          by simp
        finally show ?thesis by blast
      qed
    qed

    subsection "Miscellaneous"

    lemma Resid_parallel:
    assumes "cong t t'" and "coinitial t u"
    shows "u \<^sup>*\\\<^sup>* t = u \<^sup>*\\\<^sup>* t'"
    proof -
      have "u \<^sup>*\\\<^sup>* t = (u \<^sup>*\\\<^sup>* t) \<^sup>*\\\<^sup>* (t' \<^sup>*\\\<^sup>* t)"
        using assms
        by (metis con_target conI\<^sub>P con_sym resid_arr_ide)
      also have "... = (u \<^sup>*\\\<^sup>* t') \<^sup>*\\\<^sup>* (t \<^sup>*\\\<^sup>* t')"
        using cube by auto
      also have "... = u \<^sup>*\\\<^sup>* t'"
        using assms
        by (metis con_target conI\<^sub>P con_sym resid_arr_ide)
      finally show ?thesis by blast
    qed

    lemma set_Ide_subset_single_hd:
    shows "Ide T \<Longrightarrow> set T \<subseteq> {hd T}"
      apply (induct T, auto)
      using \<Lambda>.coinitial_ide_are_cong
      by (metis Arr_imp_arr_hd Ide_consE Ide_imp_Ide_hd Ide_implies_Arr Srcs_simp\<^sub>P\<^sub>W\<^sub>E Srcs_simp\<^sub>\<Lambda>\<^sub>P
          \<Lambda>.trg_ide equals0D \<Lambda>.Ide_iff_Src_self \<Lambda>.arr_char \<Lambda>.ide_char set_empty singletonD
          subset_code(1))

    text \<open>
      A single parallel reduction with \<open>Beta\<close> as the top-level operator factors,
      up to congruence, either as a path in which the top-level redex is
      contracted first, or as a path in which the top-level redex is contracted last.
    \<close>

    lemma Beta_decomp:
    assumes "\<Lambda>.Arr t" and "\<Lambda>.Arr u"
    shows "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
    and "[\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u] @ [\<^bold>\<lambda>\<^bold>[\<Lambda>.Trg t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Trg u] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
      using assms \<Lambda>.Arr_not_Nil \<Lambda>.Subst_not_Nil ide_char \<Lambda>.Ide_Subst \<Lambda>.Ide_Trg
            \<Lambda>.Arr_Subst \<Lambda>.resid_Arr_self
      by auto

    text \<open>
      If a reduction path follows an initial reduction whose top-level constructor is \<open>Lam\<close>,
      then all the terms in the path have \<open>Lam\<close> as their top-level constructor.
    \<close>

    lemma seq_Lam_Arr_implies:
    shows "\<lbrakk>seq [t] U; \<Lambda>.is_Lam t\<rbrakk> \<Longrightarrow> set U \<subseteq> Collect \<Lambda>.is_Lam"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>seq [t] []; \<Lambda>.is_Lam t\<rbrakk> \<Longrightarrow> set [] \<subseteq> Collect \<Lambda>.is_Lam"
        by simp
      fix u U t
      assume ind: "\<And>t. \<lbrakk>seq [t] U; \<Lambda>.is_Lam t\<rbrakk> \<Longrightarrow> set U \<subseteq> Collect \<Lambda>.is_Lam"
      assume uU: "seq [t] (u # U)"
      assume t: "\<Lambda>.is_Lam t"
      show "set (u # U) \<subseteq> Collect \<Lambda>.is_Lam"
      proof -
        have "\<Lambda>.is_Lam u"
          by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(1-2,4-5) \<Lambda>.Trg.simps(2) \<Lambda>.is_App_def
            \<Lambda>.is_Beta_def \<Lambda>.is_Lam_def \<Lambda>.is_Var_def \<Lambda>.lambda.disc(9) \<Lambda>.lambda.exhaust_disc
            last_ConsL list.sel(1) t uU)
        moreover have "set U \<subseteq> Collect \<Lambda>.is_Lam"
        proof (cases "U = []")
          show "U = [] \<Longrightarrow> ?thesis"
            by simp
          assume U: "U \<noteq> []"
          have "seq [u] U"
            by (metis U append_Cons arr_append_imp_seq not_Cons_self2 self_append_conv2
                seqE uU)
          thus ?thesis
            using ind calculation by simp
        qed
        ultimately show ?thesis by auto
      qed
    qed

    lemma seq_map_un_Lam:
    assumes "seq [\<^bold>\<lambda>\<^bold>[t\<^bold>]] U"
    shows "seq [t] (map \<Lambda>.un_Lam U)"
    proof -
      have "Arr (\<^bold>\<lambda>\<^bold>[t\<^bold>] # U)"
        using assms
        by (simp add: seq_char)
      hence "Arr (map \<Lambda>.un_Lam (\<^bold>\<lambda>\<^bold>[t\<^bold>] # U)) \<and> Arr U"
        using seq_Lam_Arr_implies
        by (metis Arr_map_un_Lam \<open>seq [\<^bold>\<lambda>\<^bold>[t\<^bold>]] U\<close> \<Lambda>.lambda.discI(2) mem_Collect_eq
            seq_char set_ConsD subset_code(1))
      hence "Arr (\<Lambda>.un_Lam \<^bold>\<lambda>\<^bold>[t\<^bold>] # map \<Lambda>.un_Lam U) \<and> Arr U"
        by simp
      thus ?thesis
        using seq_char
        by (metis (no_types, lifting) Arr.simps(1) Con_imp_eq_Srcs Con_implies_Arr(2)
            Con_initial_right Resid_rec(1) Resid_rec(3) Srcs_Resid \<Lambda>.lambda.sel(2)
            map_is_Nil_conv confluence_ind)
    qed

  end

  section "Developments"

  text \<open>
    A \emph{development} is a reduction path from a term in which at each step exactly one
    redex is contracted, and the only redexes that are contracted are those that are residuals
    of redexes present in the original term.  That is, no redexes are contracted that were
    newly created as a result of the previous reductions.  The main theorem about developments
    is the Finite Developments Theorem, which states that all developments are finite.
    A proof of this theorem was published by Hindley \<^cite>\<open>"hindley"\<close>, who attributes the
    result to Schroer \<^cite>\<open>"schroer"\<close>.  Other proofs were published subsequently.
    Here we follow the paper by de Vrijer \<^cite>\<open>"deVrijer"\<close>, which may in some sense be considered
    the definitive work because de Vrijer's proof gives an exact bound on the number of steps
    in a development.  Since de Vrijer used a classical, named-variable representation of
    \<open>\<lambda>\<close>-terms, for the formalization given in the present article it was necessary to find the
    correct way to adapt de Vrijer's proof to the de Bruijn index representation of terms.
    I found this to be a somewhat delicate matter and to my knowledge it has not been done
    previously.
  \<close>

  context lambda_calculus
  begin

    text \<open>
      We define an \emph{elementary reduction} defined to be a term with exactly one marked redex.
      These correspond to the most basic computational steps.
    \<close>

    fun elementary_reduction
    where "elementary_reduction \<^bold>\<sharp> \<longleftrightarrow> False"
        | "elementary_reduction (\<^bold>\<guillemotleft>_\<^bold>\<guillemotright>) \<longleftrightarrow> False"
        | "elementary_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> elementary_reduction t"
        | "elementary_reduction (t \<^bold>\<circ> u) \<longleftrightarrow>
            (elementary_reduction t \<and> Ide u) \<or> (Ide t \<and> elementary_reduction u)"
        | "elementary_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<longleftrightarrow> Ide t \<and> Ide u"

    text \<open>
      It is tempting to imagine that elementary reductions would be atoms with respect to the
      preorder \<open>\<lesssim>\<close>, but this is not necessarily the case.
      For example, suppose \<open>t = \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>)\<close> and \<open>u = \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>)\<close>.
      Then \<open>t\<close> is an elementary reduction, \<open>u \<lesssim> t\<close> (in fact \<open>u \<sim> t\<close>) but \<open>u\<close> is not an identity,
      nor is it elementary.
    \<close>

    lemma elementary_reduction_is_arr:
    shows "elementary_reduction t \<Longrightarrow> arr t"
      using Ide_implies_Arr arr_char
      by (induct t) auto

    lemma elementary_reduction_not_ide:
    shows "elementary_reduction t \<Longrightarrow> \<not> ide t"
      using ide_char
      by (induct t) auto

    lemma elementary_reduction_Raise_iff:
    shows "\<And>d n. elementary_reduction (Raise d n t) \<longleftrightarrow> elementary_reduction t"
      using Ide_Raise
      by (induct t) auto

    lemma elementary_reduction_Lam_iff:
    shows "is_Lam t \<Longrightarrow> elementary_reduction t \<longleftrightarrow> elementary_reduction (un_Lam t)"
      by (metis elementary_reduction.simps(3) lambda.collapse(2))

    lemma elementary_reduction_App_iff:
    shows "is_App t \<Longrightarrow> elementary_reduction t \<longleftrightarrow>
                        (elementary_reduction (un_App1 t) \<and> ide (un_App2 t)) \<or>
                        (ide (un_App1 t) \<and> elementary_reduction (un_App2 t))"
      using ide_char
      by (metis elementary_reduction.simps(4) lambda.collapse(3))

    lemma elementary_reduction_Beta_iff:
    shows "is_Beta t \<Longrightarrow> elementary_reduction t \<longleftrightarrow> ide (un_Beta1 t) \<and> ide (un_Beta2 t)"
      using ide_char
      by (metis elementary_reduction.simps(5) lambda.collapse(4))

    lemma cong_elementary_reductions_are_equal:
    shows "\<lbrakk>elementary_reduction t; elementary_reduction u; t \<sim> u\<rbrakk> \<Longrightarrow> t = u"
    proof (induct t arbitrary: u)
      show "\<And>u. \<lbrakk>elementary_reduction \<^bold>\<sharp>; elementary_reduction u; \<^bold>\<sharp> \<sim> u\<rbrakk> \<Longrightarrow> \<^bold>\<sharp> = u"
        by simp
      show "\<And>x u. \<lbrakk>elementary_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>; elementary_reduction u; \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<sim> u\<rbrakk> \<Longrightarrow> \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = u"
        by simp
      show "\<And>t u. \<lbrakk>\<And>u. \<lbrakk>elementary_reduction t; elementary_reduction u; t \<sim> u\<rbrakk> \<Longrightarrow> t = u;
                    elementary_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>]; elementary_reduction u; \<^bold>\<lambda>\<^bold>[t\<^bold>] \<sim> u\<rbrakk>
                     \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t\<^bold>] = u"
        by (metis elementary_reduction_Lam_iff lambda.collapse(2) lambda.inject(2) prfx_Lam_iff)
      show "\<And>t1 t2. \<lbrakk>\<And>u. \<lbrakk>elementary_reduction t1; elementary_reduction u; t1 \<sim> u\<rbrakk> \<Longrightarrow> t1 = u;
                     \<And>u. \<lbrakk>elementary_reduction t2; elementary_reduction u; t2 \<sim> u\<rbrakk> \<Longrightarrow> t2 = u;
                     elementary_reduction (t1 \<^bold>\<circ> t2); elementary_reduction u; t1 \<^bold>\<circ> t2 \<sim> u\<rbrakk>
                       \<Longrightarrow> t1 \<^bold>\<circ> t2 = u"
        for u
        using prfx_App_iff
        apply (cases u)
            apply auto[3]
         apply (metis elementary_reduction_App_iff ide_backward_stable lambda.sel(3-4)
                      weak_extensionality)
        by auto
      show "\<And>t1 t2. \<lbrakk>\<And>u. \<lbrakk>elementary_reduction t1; elementary_reduction u; t1 \<sim> u\<rbrakk> \<Longrightarrow> t1 = u;
                     \<And>u. \<lbrakk>elementary_reduction t2; elementary_reduction u; t2 \<sim> u\<rbrakk> \<Longrightarrow> t2 = u;
                     elementary_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2); elementary_reduction u; \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<sim> u\<rbrakk>
                       \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 = u"
        for u
        using prfx_App_iff
        apply (cases u, simp_all)
        by (metis (full_types) Coinitial_iff_Con Ide_iff_Src_self Ide.simps(1))
    qed

    text \<open>
      An \emph{elementary reduction path} is a path in which each step is an elementary reduction.
      It will be convenient to regard the empty list as an elementary reduction path, even though
      it is not actually a path according to our previous definition of that notion.
    \<close>

    definition (in reduction_paths) elementary_reduction_path
    where "elementary_reduction_path T \<longleftrightarrow>
           (T = [] \<or> Arr T \<and> set T \<subseteq> Collect \<Lambda>.elementary_reduction)"

    text \<open>
      In the formal definition of ``development'' given below, we represent a set of
      redexes simply by a term, in which the occurrences of \<open>Beta\<close> correspond to the redexes
      in the set.  To express the idea that an elementary reduction \<open>u\<close> is a member of
      the set of redexes represented by term \<open>t\<close>, it is not adequate to say \<open>u \<lesssim> t\<close>.
      To see this, consider the developments of a term of the form \<open>\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<close>. 
      Intuitively, such developments should consist of a (possibly empty) initial segment
      containing only transitions of the form \<open>t1 \<^bold>\<circ> t2\<close>, followed by a transition of the form
      \<open>\<^bold>\<lambda>\<^bold>[u1'\<^bold>] \<^bold>\<Zspot> u2'\<close>, followed by a development of the residual of the original \<open>\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<close>
      after what has come so far.
      The requirement \<open>u \<lesssim> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<close> is not a strong enough constraint on the
      transitions in the initial segment, because \<open>\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2 \<lesssim> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<close>
      can hold for \<open>t2\<close> and \<open>u2\<close> coinitial, but otherwise without any particular relationship
      between their sets of marked redexes.  In particular, this can occur when
      \<open>u2\<close> and \<open>t2\<close> occur as subterms that can be deleted by the contraction of an outer redex.
      So we need to introduce a notion of containment between terms that is stronger
      and more ``syntactic'' than \<open>\<lesssim>\<close>.  The notion ``subsumed by'' defined below serves
      this purpose.  Term \<open>u\<close> is subsumed by term \<open>t\<close> if both terms are arrows with exactly
      the same form except that \<open>t\<close> may contain \<open>\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<close> (a marked redex) in places
      where \<open>u\<close> contains \<open>\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<circ> t2\<close>.
    \<close>

    fun subs  (infix "\<sqsubseteq>" 50)
    where "\<^bold>\<guillemotleft>i\<^bold>\<guillemotright> \<sqsubseteq> \<^bold>\<guillemotleft>i'\<^bold>\<guillemotright> \<longleftrightarrow> i = i'"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t'\<^bold>] \<longleftrightarrow> t \<sqsubseteq> t'"
        | "t \<^bold>\<circ> u \<sqsubseteq> t' \<^bold>\<circ> u' \<longleftrightarrow> t \<sqsubseteq> t' \<and> u \<sqsubseteq> u'"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u' \<longleftrightarrow> t \<sqsubseteq> t' \<and> u \<sqsubseteq> u'"
        | "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u' \<longleftrightarrow> t \<sqsubseteq> t' \<and> u \<sqsubseteq> u'"
        | "_ \<sqsubseteq> _ \<longleftrightarrow> False"

    lemma subs_implies_prfx:
    shows "t \<sqsubseteq> u \<Longrightarrow> t \<lesssim> u"
      apply (induct t arbitrary: u)
          apply auto[1]
      using subs.elims(2)
         apply fastforce
    proof -
      show "\<And>t. \<lbrakk>\<And>u. t \<sqsubseteq> u \<Longrightarrow> t \<lesssim> u; \<^bold>\<lambda>\<^bold>[t\<^bold>] \<sqsubseteq> u\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t\<^bold>] \<lesssim> u" for u
        by (cases u, auto) fastforce
      show "\<And>t2. \<lbrakk>\<And>u1. t1 \<sqsubseteq> u1 \<Longrightarrow> t1 \<lesssim> u1;
                  \<And>u2. t2 \<sqsubseteq> u2 \<Longrightarrow> t2 \<lesssim> u2;
                  t1 \<^bold>\<circ> t2 \<sqsubseteq> u\<rbrakk>
                     \<Longrightarrow> t1 \<^bold>\<circ> t2 \<lesssim> u" for t1 u
        apply (cases t1; cases u)
                            apply simp_all
            apply fastforce+
          apply (metis Ide_Subst con_char lambda.sel(2) subs.simps(2) prfx_Lam_iff prfx_char
                       prfx_implies_con)
        by fastforce+
      show "\<And>t1 t2. \<lbrakk>\<And>u1. t1 \<sqsubseteq> u1 \<Longrightarrow> t1 \<lesssim> u1;
                     \<And>u2. t2 \<sqsubseteq> u2 \<Longrightarrow> t2 \<lesssim> u2;
                     \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<sqsubseteq> u\<rbrakk>
                        \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<lesssim> u" for u
        using Ide_Subst
        apply (cases u, simp_all)
        by (metis Ide.simps(1))
    qed

    text \<open>
      The following is an example showing that two terms can be related by \<open>\<lesssim>\<close> without being
      related by \<open>\<sqsubseteq>\<close>.
    \<close>

    lemma subs_example:
    shows "\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>) \<lesssim> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>) = True"
    and "\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>) \<sqsubseteq> \<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>1\<^bold>\<guillemotright>\<^bold>] \<^bold>\<Zspot> (\<^bold>\<lambda>\<^bold>[\<^bold>\<guillemotleft>0\<^bold>\<guillemotright>\<^bold>] \<^bold>\<circ> \<^bold>\<guillemotleft>0\<^bold>\<guillemotright>) = False"
      by auto

    lemma subs_Ide:
    shows "\<lbrakk>ide u; Src t = Src u\<rbrakk> \<Longrightarrow> u \<sqsubseteq> t"
      using Ide_Src Ide_implies_Arr Ide_iff_Src_self
      by (induct t arbitrary: u, simp_all) force+

    lemma subs_App:
    shows "u \<sqsubseteq> t1 \<^bold>\<circ> t2 \<longleftrightarrow> is_App u \<and> un_App1 u \<sqsubseteq> t1 \<and> un_App2 u \<sqsubseteq> t2"
      by (metis lambda.collapse(3) prfx_App_iff subs.simps(3) subs_implies_prfx)

  end

  context reduction_paths
  begin

    text \<open>
      We now formally define a \emph{development of \<open>t\<close>} to be an elementary reduction path \<open>U\<close>
      that is coinitial with \<open>[t]\<close>  and is such that each transition \<open>u\<close> in \<open>U\<close> is subsumed by
      the residual of \<open>t\<close> along the prefix of \<open>U\<close> coming before \<open>u\<close>.  Stated another way,
      each transition in \<open>U\<close> corresponds to the contraction of a single redex that is the residual
      of a redex originally marked in \<open>t\<close>.
    \<close>

    fun development
    where "development t [] \<longleftrightarrow> \<Lambda>.Arr t"
        | "development t (u # U) \<longleftrightarrow>
           \<Lambda>.elementary_reduction u \<and> u \<sqsubseteq> t \<and> development (t \\ u) U"

    lemma development_imp_Arr:
    assumes "development t U"
    shows "\<Lambda>.Arr t"
      using assms
      by (metis \<Lambda>.Con_implies_Arr2 \<Lambda>.Ide.simps(1) \<Lambda>.ide_char \<Lambda>.subs_implies_prfx
          development.elims(2))

    lemma development_Ide:
    shows "\<Lambda>.Ide t \<Longrightarrow> development t U \<longleftrightarrow> U = []"
      using \<Lambda>.Ide_implies_Arr
      apply (induct U arbitrary: t)
       apply auto
      by (meson \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_backward_stable \<Lambda>.ide_char
          \<Lambda>.subs_implies_prfx)

    lemma development_implies:
    shows "development t U \<Longrightarrow> elementary_reduction_path U \<and> (U \<noteq> [] \<longrightarrow> U \<^sup>*\<lesssim>\<^sup>* [t])"
      apply (induct U arbitrary: t)
      using elementary_reduction_path_def
       apply simp
    proof -
      fix t u U
      assume ind: "\<And>t. development t U \<Longrightarrow>
                       elementary_reduction_path U \<and> (U \<noteq> [] \<longrightarrow> U \<^sup>*\<lesssim>\<^sup>* [t])"
      show "development t (u # U) \<Longrightarrow>
            elementary_reduction_path (u # U) \<and> (u # U \<noteq> [] \<longrightarrow> u # U \<^sup>*\<lesssim>\<^sup>* [t])"
      proof (cases "U = []")
        assume uU: "development t (u # U)"
        show "U = [] \<Longrightarrow> ?thesis"
          using uU \<Lambda>.subs_implies_prfx ide_char \<Lambda>.elementary_reduction_is_arr
                elementary_reduction_path_def prfx_implies_con
          by force
        assume U: "U \<noteq> []"
        have "\<Lambda>.elementary_reduction u \<and> u \<sqsubseteq> t \<and> development (t \\ u) U"
          using U uU development.elims(1) by blast
        hence 1: "\<Lambda>.elementary_reduction u \<and> elementary_reduction_path U \<and> u \<sqsubseteq> t \<and>
                  (U \<noteq> [] \<longrightarrow> U \<^sup>*\<lesssim>\<^sup>* [t \\ u])"
          using U uU ind by auto
        show ?thesis
        proof (unfold elementary_reduction_path_def, intro conjI)
          show "u # U = [] \<or> Arr (u # U) \<and> set (u # U) \<subseteq> Collect \<Lambda>.elementary_reduction"
            using U 1
            by (metis Con_implies_Arr(1) Con_rec(2) con_char prfx_implies_con
                elementary_reduction_path_def insert_subset list.simps(15) mem_Collect_eq
                \<Lambda>.prfx_implies_con \<Lambda>.subs_implies_prfx)
          show "u # U \<noteq> [] \<longrightarrow> u # U \<^sup>*\<lesssim>\<^sup>* [t]"
          proof -
            have "u # U \<^sup>*\<lesssim>\<^sup>* [t] \<longleftrightarrow> ide ([u \\ t] @ U \<^sup>*\\\<^sup>* [t \\ u])"
              using 1 U Con_rec(2) Resid_rec(2) con_char prfx_implies_con
                    \<Lambda>.prfx_implies_con \<Lambda>.subs_implies_prfx
              by simp
            also have "... \<longleftrightarrow> True"
              using U 1 ide_char Ide_append_iff\<^sub>P\<^sub>W\<^sub>E [of "[u \\ t]" "U \<^sup>*\\\<^sup>* [t \\ u]"]
              by (metis Ide.simps(2) Ide_appendI\<^sub>P\<^sub>W\<^sub>E Src_resid Trg.simps(2)
                  \<Lambda>.apex_sym con_char \<Lambda>.subs_implies_prfx prfx_implies_con)
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    text \<open>
      The converse of the previous result does not hold, because there could be a stage \<open>i\<close>
      at which \<open>u\<^sub>i \<lesssim> t\<^sub>i\<close>, but \<open>t\<^sub>i\<close>  deletes the redex contracted in \<open>u\<^sub>i\<close>, so there is nothing
      forcing that redex to have been originally marked in \<open>t\<close>.  So \<open>U\<close> being a development
      of \<open>t\<close> is a stronger property than \<open>U\<close> just being an elementary reduction path such
      that \<open>U \<^sup>*\<lesssim>\<^sup>* [t]\<close>.
    \<close>

    lemma development_append:
    shows "\<lbrakk>development t U; development (t \<^sup>1\\\<^sup>* U) V\<rbrakk> \<Longrightarrow> development t (U @ V)"
      using development_imp_Arr null_char
      apply (induct U arbitrary: t V)
       apply auto
      by (metis Resid1x.simps(2-3) append_Nil neq_Nil_conv)

    lemma development_map_Lam:
    shows "development t T \<Longrightarrow> development \<^bold>\<lambda>\<^bold>[t\<^bold>] (map \<Lambda>.Lam T)"
      using \<Lambda>.Arr_not_Nil development_imp_Arr
      by (induct T arbitrary: t) auto

    lemma development_map_App_1:
    shows "\<lbrakk>development t T; \<Lambda>.Arr u\<rbrakk> \<Longrightarrow> development (t \<^bold>\<circ> u) (map (\<lambda>x. x \<^bold>\<circ> \<Lambda>.Src u) T)"
      apply (induct T arbitrary: t)
       apply (simp add: \<Lambda>.Ide_implies_Arr)
    proof -
      fix t T t'
      assume ind: "\<And>t. \<lbrakk>development t T; \<Lambda>.Arr u\<rbrakk>
                          \<Longrightarrow> development (t \<^bold>\<circ> u) (map (\<lambda>x. x \<^bold>\<circ> \<Lambda>.Src u) T)"
      assume t'T: "development t (t' # T)"
      assume u: "\<Lambda>.Arr u"
      show "development (t \<^bold>\<circ> u) (map (\<lambda>x. x \<^bold>\<circ> \<Lambda>.Src u) (t' # T))"
        using u t'T ind
        apply simp
        using \<Lambda>.Arr_not_Nil \<Lambda>.Ide_Src development_imp_Arr \<Lambda>.subs_Ide by force
    qed

    lemma development_map_App_2:
    shows "\<lbrakk>\<Lambda>.Arr t; development u U\<rbrakk> \<Longrightarrow> development (t \<^bold>\<circ> u) (map (\<lambda>x. \<Lambda>.App (\<Lambda>.Src t) x) U)"
      apply (induct U arbitrary: u)
       apply (simp add: \<Lambda>.Ide_implies_Arr)
    proof -
      fix u U u'
      assume ind: "\<And>u. \<lbrakk>\<Lambda>.Arr t; development u U\<rbrakk>
                          \<Longrightarrow> development (t \<^bold>\<circ> u) (map (\<Lambda>.App (\<Lambda>.Src t)) U)"
      assume u'U: "development u (u' # U)"
      assume t: "\<Lambda>.Arr t"
      show "development (t \<^bold>\<circ> u) (map (\<Lambda>.App (\<Lambda>.Src t)) (u' # U)) "
        using t u'U ind
        apply simp
        by (metis \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr
            development_imp_Arr \<Lambda>.ide_char \<Lambda>.resid_Arr_Ide \<Lambda>.subs_Ide)
    qed

    subsection "Finiteness of Developments"

    text \<open>
      A term \<open>t\<close> has the finite developments property if there exists a finite value
      that bounds the length of all developments of \<open>t\<close>.  The goal of this section is
      to prove the Finite Developments Theorem: every term has the finite developments
      property.
    \<close>

    definition FD
    where "FD t \<equiv> \<exists>n. \<forall>U. development t U \<longrightarrow> length U \<le> n"

  end

  text \<open>
    In \<^cite>\<open>"hindley"\<close>, Hindley proceeds by using structural induction to establish
    a bound on the length of a development of a term.
    The only case that poses any difficulty is the case of a \<open>\<beta>\<close>-redex, which is
    \<open>\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u\<close> in the notation used here.  He notes that there is an easy bound on the
    length of a development of a special form in which all the contractions of residuals of \<open>t\<close>
    occur before the contraction of the top-level redex.  The development first
    takes \<open>\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u\<close> to \<open>\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u'\<close>, then to \<open>subst u' t'\<close>, then continues with
    independent developments of \<open>u'\<close>.  The number of independent developments of \<open>u'\<close>
    is given by the number of free occurrences of \<open>Var 0\<close> in \<open>t'\<close>.  As there can be
    only finitely many such \<open>t'\<close>, we can use the maximum number of free occurrences
    of \<open>Var 0\<close> over all such \<open>t'\<close> to bound the steps in the independent developments of \<open>u'\<close>.

    In the general case, the problem is that reductions of residuals of t can
    increase the number of free occurrences of \<open>Var 0\<close>, so we can't readily count
    them at any particular stage.  Hindley shows that developments in which
    there are reductions of residuals of \<open>t\<close> that occur after the contraction of the
    top-level redex are equivalent to reductions of the special form, by a
    transformation with a bounded increase in length.  This can be considered as a
    weak form of standardization for developments.

    A later paper by de Vrijer \<^cite>\<open>"deVrijer"\<close> obtains an explicit function for the
    exact number of steps in a development of maximal length.  His proof is very
    straightforward and amenable to formalization, and it is what we follow here.
    The main issue for us is that de Vrijer uses a classical representation of \<open>\<lambda>\<close>-terms,
    with variable names and \<open>\<alpha>\<close>-equivalence, whereas here we are using de Bruijn indices.
    This means that we have to discover the correct modification of de Vrijer's definitions
    to apply to the present situation.
  \<close>

  context lambda_calculus
  begin

    text \<open>
      Our first definition is that of the ``multiplicity'' of a free variable in a term.
      This is a count of the maximum number of times a variable could occur free in a term
      reachable in a development.  The main issue in adjusting to de Bruijn indices
      is that the same variable will have different indices depending on the depth at which
      it occurs in the term.  So, we need to keep track of how the indices of variables change
      as we move through the term.  Our modified definitions adjust the parameter to the
      multiplicity function on each recursive call, to account for the contextual depth
      (\emph{i.e.}~the number of binders on a path from the root of the term).
     
      The definition of this function is readily understandable, except perhaps for the
      \<open>Beta\<close> case.  The multiplicity \<open>mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)\<close> has to be at least as large as
      \<open>mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u)\<close>, to account for developments in which the top-level redex is not
      contracted.  However, if the top-level redex \<open>\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u\<close> is contracted, then the contractum
      is \<open>subst u t\<close>, so the multiplicity has to be at least as large as \<open>mtp x (subst u t)\<close>.
      This leads to the relation:
      \begin{center}
        \<open>mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = max (mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u)) (mtp x (subst u t))\<close>
      \end{center}
      This is not directly suitable for use in a definition of the function \<open>mtp\<close>, because
      proving the termination is problematic.  Instead, we have to guess the correct
      expression for \<open>mtp x (subst u t)\<close> and use that.
    
      Now, each variable \<open>x\<close> in \<open>subst u t\<close> other than the variable \<open>0\<close> that is substituted for
      still has all the occurrences that it does in \<open>\<^bold>\<lambda>\<^bold>[t\<^bold>]\<close>.  In addition, the variable being
      substituted for (which has index \<open>0\<close> in the outermost context of \<open>t\<close>) will in general have
      multiple free occurrences in \<open>t\<close>, with a total multiplicity given by \<open>mtp 0 t\<close>.
      The substitution operation replaces each free occurrence by \<open>u\<close>, which has the effect of
      multiplying the multiplicity of a variable \<open>x\<close> in \<open>t\<close> by a factor of \<open>mtp 0 t\<close>.
      These considerations lead to the following:
      \begin{center}
       \<open>mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = max (mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp x u) (mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp x u * mtp 0 t)\<close>
      \end{center}
      However, we can simplify this to:
      \begin{center}
       \<open>mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp x u * max 1 (mtp 0 t)\<close>
      \end{center}
      and replace the \<open>mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>]\<close> by \<open>mtp (Suc x) t\<close> to simplify the ordering necessary
      for the termination proof and allow it to be done automatically.
     
      The final result is perhaps about the first thing one would think to write down,
      but there are possible ways to go wrong and it is of course still necessary to discover
      the proper form required for the various induction proofs.  I followed a long path
      of rather more complicated-looking definitions, until I eventually managed to find the
      proper inductive forms for all the lemmas and eventually arrive back at this definition.
    \<close>

    fun mtp :: "nat \<Rightarrow> lambda \<Rightarrow> nat"
    where "mtp x \<^bold>\<sharp> = 0"
        | "mtp x \<^bold>\<guillemotleft>z\<^bold>\<guillemotright> = (if z = x then 1 else 0)"
        | "mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>] = mtp (Suc x) t"
        | "mtp x (t \<^bold>\<circ> u) = mtp x t + mtp x u"
        | "mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = mtp (Suc x) t + mtp x u * max 1 (mtp 0 t)"

    text \<open>
      The multiplicity function generalizes the free variable predicate.
      This is not actually used, but is included for explanatory purposes.
    \<close>

    lemma mtp_gt_0_iff_in_FV:
    shows "mtp x t > 0 \<longleftrightarrow> x \<in> FV t"
    proof (induct t arbitrary: x)
      show "\<And>x. 0 < mtp x \<^bold>\<sharp> \<longleftrightarrow> x \<in> FV \<^bold>\<sharp>"
        by simp
      show "\<And>x z. 0 < mtp x \<^bold>\<guillemotleft>z\<^bold>\<guillemotright> \<longleftrightarrow> x \<in> FV \<^bold>\<guillemotleft>z\<^bold>\<guillemotright>"
        by auto
      show Lam: "\<And>t x. (\<And>x. 0 < mtp x t \<longleftrightarrow> x \<in> FV t)
                          \<Longrightarrow> 0 < mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> x \<in> FV \<^bold>\<lambda>\<^bold>[t\<^bold>]"
      proof -
        fix t and x :: nat
        assume ind: "\<And>x. 0 < mtp x t \<longleftrightarrow> x \<in> FV t"
        show "0 < mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> x \<in> FV \<^bold>\<lambda>\<^bold>[t\<^bold>]"
          using ind
          apply auto
          apply (metis Diff_iff One_nat_def diff_Suc_1 empty_iff imageI insert_iff
                       nat.distinct(1))
          by (metis Suc_pred neq0_conv)
      qed
      show "\<And>t u x.
              \<lbrakk>\<And>x. 0 < mtp x t \<longleftrightarrow> x \<in> FV t;
               \<And>x. 0 < mtp x u \<longleftrightarrow> x \<in> FV u\<rbrakk>
                 \<Longrightarrow> 0 < mtp x (t \<^bold>\<circ> u) \<longleftrightarrow> x \<in> FV (t \<^bold>\<circ> u)"
        by simp
      show "\<And>t u x.
              \<lbrakk>\<And>x. 0 < mtp x t \<longleftrightarrow> x \<in> FV t;
               \<And>x. 0 < mtp x u \<longleftrightarrow> x \<in> FV u\<rbrakk>
                 \<Longrightarrow> 0 < mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<longleftrightarrow> x \<in> FV (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
      proof -
        fix t u and x :: nat
        assume ind1: "\<And>x. 0 < mtp x t \<longleftrightarrow> x \<in> FV t"
        assume ind2: "\<And>x. 0 < mtp x u \<longleftrightarrow> x \<in> FV u"
        show "0 < mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<longleftrightarrow> x \<in> FV (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
          using ind1 ind2
          apply simp
          by force
      qed
    qed

    text \<open>
      We now establish a fact about commutation of multiplicity and Raise that will be
      needed subsequently.
    \<close>

    lemma mtpE_eq_Raise:
    shows "x < d \<Longrightarrow> mtp x (Raise d k t) = mtp x t"
      by (induct t arbitrary: x k d) auto

    lemma mtp_Raise_ind:
    shows "\<lbrakk>l \<le> d; size t \<le> s\<rbrakk> \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
    proof (induct s arbitrary: d x k l t)
      show "\<And>d x k l. \<lbrakk>l \<le> d; size t \<le> 0\<rbrakk> \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
              for t
        by (cases t) auto
      show "\<And>s d x k l.
               \<lbrakk>\<And>d x k l t. \<lbrakk>l \<le> d; size t \<le> s\<rbrakk> \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t;
                l \<le> d; size t \<le> Suc s\<rbrakk>
                  \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
        for t
      proof (cases t)
        show "\<And>d x k l s. t = \<^bold>\<sharp> \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
          by simp
        show "\<And>z d x k l s. \<lbrakk>l \<le> d; t = \<^bold>\<guillemotleft>z\<^bold>\<guillemotright>\<rbrakk>
                               \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
          by simp
        show "\<And>u d x k l s. \<lbrakk>l \<le> d; size t \<le> Suc s; t = \<^bold>\<lambda>\<^bold>[u\<^bold>];
                             (\<And>d x k l u. \<lbrakk>l \<le> d; size u \<le> s\<rbrakk>
                                             \<Longrightarrow> mtp (x + d + k) (Raise l k u) = mtp (x + d) u)\<rbrakk>
                               \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
        proof -
          fix u d x s and k l :: nat
          assume l: "l \<le> d" and s: "size t \<le> Suc s" and t: "t = \<^bold>\<lambda>\<^bold>[u\<^bold>]"
          assume ind: "\<And>d x k l u. \<lbrakk>l \<le> d; size u \<le> s\<rbrakk>
                                       \<Longrightarrow> mtp (x + d + k) (Raise l k u) = mtp (x + d) u"
          show "mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
          proof -
            have "mtp (x + d + k) (Raise l k t) = mtp (Suc (x + d + k)) (Raise (Suc l) k u)"
              using t by simp
            also have "... = mtp (x + Suc d) u"
            proof -
              have "size u \<le> s"
                using t s by force
              thus ?thesis
                using l s ind [of "Suc l" "Suc d"] by simp
            qed
            also have "... = mtp (x + d) t"
              using t by auto
            finally show ?thesis by blast
          qed
        qed
        show "\<And>t1 t2 d x k l s.
                \<lbrakk>\<And>d x k l t1. \<lbrakk>l \<le> d; size t1 \<le> s\<rbrakk>
                                 \<Longrightarrow> mtp (x + d + k) (Raise l k t1) = mtp (x + d) t1;
                 \<And>d x k l t2. \<lbrakk>l \<le> d; size t2 \<le> s\<rbrakk>
                                 \<Longrightarrow> mtp (x + d + k) (Raise l k t2) = mtp (x + d) t2;
                 l \<le> d; size t \<le> Suc s; t = t1 \<^bold>\<circ> t2\<rbrakk>
                    \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
        proof -
          fix t1 t2 s
          assume s: "size t \<le> Suc s" and t: "t = t1 \<^bold>\<circ> t2"
          have "size t1 \<le> s \<and> size t2 \<le> s"
            using s t by auto
          thus "\<And>d x k l.
                  \<lbrakk>\<And>d x k l t1. \<lbrakk>l \<le> d; size t1 \<le> s\<rbrakk>
                                   \<Longrightarrow> mtp (x + d + k) (Raise l k t1) = mtp (x + d) t1;
                   \<And>d x k l t2. \<lbrakk>l \<le> d; size t2 \<le> s\<rbrakk>
                                   \<Longrightarrow> mtp (x + d + k) (Raise l k t2) = mtp (x + d) t2;
                   l \<le> d; size t \<le> Suc s; t = t1 \<^bold>\<circ> t2\<rbrakk>
                      \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
            by simp
        qed
        show "\<And>t1 t2 d x k l s.
                 \<lbrakk>\<And>d x k l t1. \<lbrakk>l \<le> d; size t1 \<le> s\<rbrakk>
                                  \<Longrightarrow> mtp (x + d + k) (Raise l k t1) = mtp (x + d) t1;
                  \<And>d x k l t2. \<lbrakk>l \<le> d; size t2 \<le> s\<rbrakk>
                                  \<Longrightarrow> mtp (x + d + k) (Raise l k t2) = mtp (x + d) t2;
                  l \<le> d; size t \<le> Suc s; t = \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<rbrakk>
                     \<Longrightarrow> mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
        proof -
          fix t1 t2 d x s and k l :: nat
          assume l: "l \<le> d" and s: "size t \<le> Suc s" and t: "t = \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2"
          assume ind: "\<And>d x k l N. \<lbrakk>l \<le> d; size N \<le> s\<rbrakk>
                                      \<Longrightarrow> mtp (x + d + k) (Raise l k N) = mtp (x + d) N"
          show "mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
          proof -
            have 1: "size t1 \<le> s \<and> size t2 \<le> s"
              using s t by auto
            have "mtp (x + d + k) (Raise l k t) =
                  mtp (Suc (x + d + k)) (Raise (Suc l) k t1) +
                    mtp (x + d + k) (Raise l k t2) * max 1 (mtp 0 (Raise (Suc l) k t1))"
              using t l by simp
            also have "... = mtp (Suc (x + d + k)) (Raise (Suc l) k t1) +
                             mtp (x + d) t2 * max 1 (mtp 0 (Raise (Suc l) k t1))"
              using l 1 ind by auto
            also have "... = mtp (x + Suc d) t1 + mtp (x + d) t2 * max 1 (mtp 0 t1)"
            proof -
              have "mtp (x + Suc d + k) (Raise (Suc l) k t1) = mtp (x + Suc d) t1"
                using l 1 ind [of "Suc l" "Suc d" t1] by simp
              moreover have "mtp 0 (Raise (Suc l) k t1) = mtp 0 t1"
                (* Raising indices already > 0 does not affect mtp\<^sub>0. *)
                using l 1 ind [of "Suc l" "Suc d" t1 k] mtpE_eq_Raise by simp
              ultimately show ?thesis
                by simp
            qed
            also have "... = mtp (x + d) t"
              using t by auto
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma mtp_Raise:
    assumes "l \<le> d"
    shows "mtp (x + d + k) (Raise l k t) = mtp (x + d) t"
      using assms mtp_Raise_ind by blast

    lemma mtp_Raise':
    shows "mtp l (Raise l (Suc k) t) = 0"
      by (induct t arbitrary: k l) auto

    lemma mtp_raise:
    shows "mtp (x + Suc d) (raise d t) = mtp (Suc x) t"
       by (metis Suc_eq_plus1 add.assoc le_add2 le_add_same_cancel2 mtp_Raise plus_1_eq_Suc)

    lemma mtp_Subst_cancel:
    shows "mtp k (Subst (Suc d + k) u t) = mtp k t"
    proof (induct t arbitrary: k d)
      show "\<And>k d. mtp k (Subst (Suc d + k) u \<^bold>\<sharp>) = mtp k \<^bold>\<sharp>"
        by simp
      show "\<And>k z d. mtp k (Subst (Suc d + k) u \<^bold>\<guillemotleft>z\<^bold>\<guillemotright>) = mtp k \<^bold>\<guillemotleft>z\<^bold>\<guillemotright>"
      using mtp_Raise'
        apply auto
        by (metis add_Suc_right add_Suc_shift order_refl raise_plus)
      show "\<And>t k d. (\<And>k d. mtp k (Subst (Suc d + k) u t) = mtp k t)
                        \<Longrightarrow> mtp k (Subst (Suc d + k) u \<^bold>\<lambda>\<^bold>[t\<^bold>]) = mtp k \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        by (metis Subst.simps(3) add_Suc_right mtp.simps(3))
      show "\<And>t1 t2 k d.
               \<lbrakk>\<And>k d. mtp k (Subst (Suc d + k) u t1) = mtp k t1;
                \<And>k d. mtp k (Subst (Suc d + k) u t2) = mtp k t2\<rbrakk>
                   \<Longrightarrow> mtp k (Subst (Suc d + k) u (t1 \<^bold>\<circ> t2)) = mtp k (t1 \<^bold>\<circ> t2)"
        by auto
      show "\<And>t1 t2 k d.
         \<lbrakk>\<And>k d. mtp k (Subst (Suc d + k) u t1) = mtp k t1;
          \<And>k d. mtp k (Subst (Suc d + k) u t2) = mtp k t2\<rbrakk>
             \<Longrightarrow> mtp k (Subst (Suc d + k) u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) = mtp k (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        using mtp_Raise'
        apply auto
        by (metis Nat.add_0_right add_Suc_right)
    qed

    lemma mtp\<^sub>0_Subst_cancel:
    shows "mtp 0 (Subst (Suc d) u t) = mtp 0 t"
      using mtp_Subst_cancel [of 0] by simp

    text \<open>
      We can now (!) prove the desired generalization of de Vrijer's formula for the
      commutation of multiplicity and substitution.  This is the main lemma whose form
      is difficult to find.  To get this right, the proper relationships have to exist
      between the various depth parameters to \<open>Subst\<close> and the arguments to \<open>mtp\<close>.
    \<close>

    lemma mtp_Subst':
    shows "mtp (x + Suc d) (Subst d u t) = mtp (x + Suc (Suc d)) t + mtp (Suc x) u * mtp d t"
    proof (induct t arbitrary: d x u)
      show "\<And>d x u. mtp (x + Suc d) (Subst d u \<^bold>\<sharp>) =
            mtp (x + Suc (Suc d)) \<^bold>\<sharp> + mtp (Suc x) u * mtp d \<^bold>\<sharp>"
        by simp
      show "\<And>z d x u. mtp (x + Suc d) (Subst d u \<^bold>\<guillemotleft>z\<^bold>\<guillemotright>) =
                       mtp (x + Suc (Suc d)) \<^bold>\<guillemotleft>z\<^bold>\<guillemotright> + mtp (Suc x) u * mtp d \<^bold>\<guillemotleft>z\<^bold>\<guillemotright>"
        using mtp_raise by auto
      show "\<And>t d x u.
              (\<And>d x u. mtp (x + Suc d) (Subst d u t) =
                        mtp (x + Suc (Suc d)) t + mtp (Suc x) u * mtp d t)
                          \<Longrightarrow> mtp (x + Suc d) (Subst d u \<^bold>\<lambda>\<^bold>[t\<^bold>]) =
                              mtp (x + Suc (Suc d)) \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp (Suc x) u * mtp d \<^bold>\<lambda>\<^bold>[t\<^bold>]"
      proof -
        fix t u d x
        assume ind: "\<And>d x N. mtp (x + Suc d) (Subst d N t) =
                              mtp (x + Suc (Suc d)) t + mtp (Suc x) N * mtp d t"
        have "mtp (x + Suc d) (Subst d u \<^bold>\<lambda>\<^bold>[t\<^bold>]) =
              mtp (Suc x + Suc (Suc d)) t +
              mtp (x + Suc (Suc d)) (raise (Suc d) u) * mtp (Suc d) t"
          using ind mtp_raise add_Suc_shift
          by (metis Subst.simps(3) add_Suc_right mtp.simps(3))
        also have "... = mtp (x + Suc (Suc d)) \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp (Suc x) u * mtp d \<^bold>\<lambda>\<^bold>[t\<^bold>]"
          using Raise_Suc
          by (metis add_Suc_right add_Suc_shift mtp.simps(3) mtp_raise)
        finally show "mtp (x + Suc d) (Subst d u \<^bold>\<lambda>\<^bold>[t\<^bold>]) =
                      mtp (x + Suc (Suc d)) \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp (Suc x) u * mtp d \<^bold>\<lambda>\<^bold>[t\<^bold>]"
          by blast
      qed
      show "\<And>t1 t2 u d x.
               \<lbrakk>\<And>d x u. mtp (x + Suc d) (Subst d u t1) =
                        mtp (x + Suc (Suc d)) t1 + mtp (Suc x) u * mtp d t1;
                \<And>d x u. mtp (x + Suc d) (Subst d u t2) =
                         mtp (x + Suc (Suc d)) t2 + mtp (Suc x) u * mtp d t2\<rbrakk>
                  \<Longrightarrow> mtp (x + Suc d) (Subst d u (t1 \<^bold>\<circ> t2)) =
                      mtp (x + Suc (Suc d)) (t1 \<^bold>\<circ> t2) + mtp (Suc x) u * mtp d (t1 \<^bold>\<circ> t2)"
        by (simp add: add_mult_distrib2)
      show "\<And>t1 t2 u d x.
              \<lbrakk>\<And>d x N. mtp (x + Suc d) (Subst d N t1) =
                       mtp (x + Suc (Suc d)) t1 + mtp (Suc x) N * mtp d t1;
              \<And>d x N. mtp (x + Suc d) (Subst d N t2) =
                       mtp (x + Suc (Suc d)) t2 + mtp (Suc x) N * mtp d t2\<rbrakk>
                 \<Longrightarrow> mtp (x + Suc d) (Subst d u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) =
                     mtp (x + Suc (Suc d)) (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + mtp (Suc x) u * mtp d (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      proof -
        fix t1 t2 u d x
        assume ind1: "\<And>d x N. mtp (x + Suc d) (Subst d N t1) =
                               mtp (x + Suc (Suc d)) t1 + mtp (Suc x) N * mtp d t1"
        assume ind2: "\<And>d x N. mtp (x + Suc d) (Subst d N t2) =
                               mtp (x + Suc (Suc d)) t2 + mtp (Suc x) N * mtp d t2"
        show "mtp (x + Suc d) (Subst d u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) =
              mtp (x + Suc (Suc d)) (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + mtp (Suc x) u * mtp d (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          let ?A = "mtp (Suc x + Suc (Suc d)) t1"
          let ?B = "mtp (Suc x + Suc d) t2"
          let ?M1 = "mtp (Suc d) t1"
          let ?M2 = "mtp d t2"
          let ?M1\<^sub>0 = "mtp 0 (Subst (Suc d) u t1)"
          let ?M1\<^sub>0' = "mtp 0 t1"
          let ?N = "mtp (Suc x) u"
          have "mtp (x + Suc d) (Subst d u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) =
                mtp (x + Suc d) (\<^bold>\<lambda>\<^bold>[Subst (Suc d) u t1\<^bold>] \<^bold>\<Zspot> Subst d u t2)"
             by simp
          also have "... = mtp (x + Suc (Suc d)) (Subst (Suc d) u t1) +
                           mtp (x + Suc d) (Subst d u t2) *
                             max 1 (mtp 0 (Subst (Suc d) u t1))"
            by simp
          also have "... = (?A + ?N * ?M1) + (?B + ?N * ?M2) * max 1 ?M1\<^sub>0"
            using ind1 ind2 add_Suc_shift by presburger
          also have "... = ?A + ?N * ?M1 + ?B * max 1 ?M1\<^sub>0 + ?N * ?M2 * max 1 ?M1\<^sub>0"
            by algebra
          also have "... = ?A + ?B * max 1 ?M1\<^sub>0' + ?N * ?M1 + ?N * ?M2 * max 1 ?M1\<^sub>0'"
          proof -
            have "?M1\<^sub>0 = ?M1\<^sub>0'"
            (* The u-dependence on the LHS is via raise (Suc d) u, which does not have
               any free occurrences of 0.  So mtp 0 0 yields the same on both. *)
              using mtp\<^sub>0_Subst_cancel by blast
            thus ?thesis by auto
          qed
          also have "... = ?A + ?B * max 1 ?M1\<^sub>0' + ?N * (?M1 + ?M2 * max 1 ?M1\<^sub>0')"
            by algebra
          also have "... =  mtp (Suc x + Suc d) (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + mtp (Suc x) u * mtp d (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by simp
          finally show ?thesis by simp
        qed
      qed
    qed

    text \<open>
      The following lemma provides expansions that apply when the parameter to \<open>mtp\<close> is \<open>0\<close>,
      as opposed to the previous lemma, which only applies for parameters greater than \<open>0\<close>.
    \<close>

    lemma mtp_Subst:
    shows "mtp k (Subst k u t) = mtp (Suc k) t + mtp k (raise k u) * mtp k t"
    proof (induct t arbitrary: u k)
      show "\<And>u k. mtp k (Subst k u \<^bold>\<sharp>) = mtp (Suc k) \<^bold>\<sharp> + mtp k (raise k u) * mtp k \<^bold>\<sharp>"
        by simp
      show "\<And>x u k. mtp k (Subst k u \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>) =
                     mtp (Suc k) \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> + mtp k (raise k u) * mtp k \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        by auto
      show "\<And>t u k. (\<And>u k. mtp k (Subst k u t) = mtp (Suc k) t + mtp k (raise k u) * mtp k t)
                              \<Longrightarrow> mtp k (Subst k u \<^bold>\<lambda>\<^bold>[t\<^bold>]) =
                                  mtp (Suc k) \<^bold>\<lambda>\<^bold>[t\<^bold>] + mtp k (Raise 0 k u) * mtp k \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        using mtp_Raise [of 0]
        apply auto
        by (metis add.left_neutral)
      show "\<And>t1 t2 u k.
              \<lbrakk>\<And>u k. mtp k (Subst k u t1) = mtp (Suc k) t1 + mtp k (raise k u) * mtp k t1;
               \<And>u k. mtp k (Subst k u t2) = mtp (Suc k) t2 + mtp k (raise k u) * mtp k t2\<rbrakk>
                   \<Longrightarrow> mtp k (Subst k u (t1 \<^bold>\<circ> t2)) =
                       mtp (Suc k) (t1 \<^bold>\<circ> t2) + mtp k (raise k u) * mtp k (t1 \<^bold>\<circ> t2)"
        by (auto simp add: distrib_left)
      show "\<And>t1 t2 u k.
              \<lbrakk>\<And>u k. mtp k (Subst k u t1) = mtp (Suc k) t1 + mtp k (raise k u) * mtp k t1;
               \<And>u k. mtp k (Subst k u t2) = mtp (Suc k) t2 + mtp k (raise k u) * mtp k t2\<rbrakk>
                  \<Longrightarrow> mtp k (Subst k u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) =
                      mtp (Suc k) (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + mtp k (raise k u) * mtp k (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      proof -
        fix t1 t2 u k
        assume ind1: "\<And>u k. mtp k (Subst k u t1) =
                             mtp (Suc k) t1 + mtp k (raise k u) * mtp k t1"
        assume ind2: "\<And>u k. mtp k (Subst k u t2) =
                             mtp (Suc k) t2 + mtp k (raise k u) * mtp k t2"
        show "mtp k (Subst k u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) =
              mtp (Suc k) (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + mtp k (raise k u) * mtp k (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          have "mtp (Suc k) (Raise 0 (Suc k) u) * mtp (Suc k) t1 +
                  (mtp (Suc k) t2 + mtp k (Raise 0 k u) * mtp k t2) * max (Suc 0) (mtp 0 t1) =
                mtp (Suc k) t2 * max (Suc 0) (mtp 0 t1) +
                  mtp k (Raise 0 k u) * (mtp (Suc k) t1 + mtp k t2 * max (Suc 0) (mtp 0 t1))"
          proof -
            have "mtp (Suc k) (Raise 0 (Suc k) u) * mtp (Suc k) t1 +
                    (mtp (Suc k) t2 + mtp k (Raise 0 k u) * mtp k t2) * max (Suc 0) (mtp 0 t1) =
                  mtp (Suc k) t2 * max (Suc 0) (mtp 0 t1) +
                    mtp (Suc k) (Raise 0 (Suc k) u) * mtp (Suc k) t1 +
                      mtp k (Raise 0 k u) * mtp k t2 * max (Suc 0) (mtp 0 t1)"
              by algebra
            also have "... = mtp (Suc k) t2 * max (Suc 0) (mtp 0 t1) +
                               mtp (Suc k) (Raise 0 (Suc k) u) * mtp (Suc k) t1 +
                                  mtp 0 u * mtp k t2 * max (Suc 0) (mtp 0 t1)"
              using mtp_Raise [of 0 0 0 k u] by auto
            also have "... = mtp (Suc k) t2 * max (Suc 0) (mtp 0 t1) +
                               mtp k (Raise 0 k u) *
                                 (mtp (Suc k) t1 + mtp k t2 * max (Suc 0) (mtp 0 t1))"
              by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1)
                  ab_semigroup_mult_class.mult_ac(1) add_mult_distrib2 le_add1 mtp_Raise
                  plus_nat.add_0)
            finally show ?thesis by blast
          qed
          thus ?thesis
            using ind1 ind2 mtp\<^sub>0_Subst_cancel by auto
        qed
      qed
    qed

    lemma mtp0_subst_le:
    shows "mtp 0 (subst u t) \<le> mtp 1 t + mtp 0 u * max 1 (mtp 0 t)"
    proof (cases t)
      show "t = \<^bold>\<sharp> \<Longrightarrow> mtp 0 (subst u t) \<le> mtp 1 t + mtp 0 u * max 1 (mtp 0 t)"
        by auto
      show "\<And>z. t = \<^bold>\<guillemotleft>z\<^bold>\<guillemotright> \<Longrightarrow> mtp 0 (subst u t) \<le> mtp 1 t + mtp 0 u * max 1 (mtp 0 t)"
        using Raise_0 by force
      show "\<And>P. t = \<^bold>\<lambda>\<^bold>[P\<^bold>] \<Longrightarrow> mtp 0 (subst u t) \<le> mtp 1 t + mtp 0 u * max 1 (mtp 0 t)"
        using mtp_Subst [of 0 u t] Raise_0 by force
      show "\<And>t1 t2. t = t1 \<^bold>\<circ> t2 \<Longrightarrow> mtp 0 (subst u t) \<le> mtp 1 t + mtp 0 u * max 1 (mtp 0 t)"
        using mtp_Subst Raise_0 add_mult_distrib2 nat_mult_max_right by auto
      show "\<And>t1 t2. t = \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<Longrightarrow> mtp 0 (subst u t) \<le> mtp 1 t + mtp 0 u * max 1 (mtp 0 t)"
        using mtp_Subst Raise_0
        by (metis Nat.add_0_right dual_order.eq_iff max_def mult.commute mult_zero_left
            not_less_eq_eq plus_1_eq_Suc trans_le_add1)
    qed

    lemma elementary_reduction_nonincreases_mtp:
    shows "\<lbrakk>elementary_reduction u; u \<sqsubseteq> t\<rbrakk> \<Longrightarrow> mtp x (resid t u) \<le> mtp x t"
    proof (induct t arbitrary: u x)
      show "\<And>u x. \<lbrakk>elementary_reduction u; u \<sqsubseteq> \<^bold>\<sharp>\<rbrakk> \<Longrightarrow> mtp x (resid \<^bold>\<sharp> u) \<le> mtp x \<^bold>\<sharp>"
        by simp
      show "\<And>x u i. \<lbrakk>elementary_reduction u; u \<sqsubseteq> \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>\<rbrakk>
                          \<Longrightarrow> mtp x (resid \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> u) \<le> mtp x \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>"
        by (meson Ide.simps(2) elementary_reduction_not_ide ide_backward_stable ide_char
            subs_implies_prfx)
      fix u
      show "\<And>t x. \<lbrakk>\<And>u x. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t\<rbrakk> \<Longrightarrow> mtp x (resid t u) \<le> mtp x t;
                   elementary_reduction u; u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t\<^bold>]\<rbrakk>
                     \<Longrightarrow> mtp x (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u) \<le> mtp x \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        by (cases u) auto
      show "\<And>t1 t2 x.
               \<lbrakk>\<And>u x. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t1\<rbrakk> \<Longrightarrow> mtp x (resid t1 u) \<le> mtp x t1;
                \<And>u x. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t2\<rbrakk> \<Longrightarrow> mtp x (resid t2 u) \<le> mtp x t2;
                elementary_reduction u; u \<sqsubseteq> t1 \<^bold>\<circ> t2\<rbrakk>
                  \<Longrightarrow> mtp x (resid (t1 \<^bold>\<circ> t2) u) \<le> mtp x (t1 \<^bold>\<circ> t2)"
        apply (cases u)
            apply auto
         apply (metis Coinitial_iff_Con add_mono_thms_linordered_semiring(3) resid_Arr_Ide)
        by (metis Coinitial_iff_Con add_mono_thms_linordered_semiring(2) resid_Arr_Ide)
      (*
       * TODO: Isabelle is sensitive to the order of assumptions in the induction hypotheses
       * stated in the "show". Why?
       *)
      show "\<And>t1 t2 x.
               \<lbrakk>\<And>u1 x. \<lbrakk>elementary_reduction u1; u1 \<sqsubseteq> t1\<rbrakk> \<Longrightarrow> mtp x (resid t1 u1) \<le> mtp x t1;
                \<And>u2 x. \<lbrakk>elementary_reduction u2; u2 \<sqsubseteq> t2\<rbrakk> \<Longrightarrow> mtp x (resid t2 u2) \<le> mtp x t2;
                elementary_reduction u; u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<rbrakk>
                  \<Longrightarrow> mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) \<le> mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      proof -
        fix t1 t2 x
        assume ind1: "\<And>u1 x. \<lbrakk>elementary_reduction u1; u1 \<sqsubseteq> t1\<rbrakk>
                                \<Longrightarrow> mtp x (t1 \\ u1) \<le> mtp x t1"
        assume ind2: "\<And>u2 x. \<lbrakk>elementary_reduction u2; u2 \<sqsubseteq> t2\<rbrakk>
                                \<Longrightarrow> mtp x (t2 \\ u2) \<le> mtp x t2"
        assume u: "elementary_reduction u"
        assume subs: "u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2"
        have 1: "is_App u \<or> is_Beta u"
          using subs by (metis prfx_Beta_iff subs_implies_prfx)
        have "is_App u \<Longrightarrow> mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) \<le> mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          assume 2: "is_App u"
          obtain u1 u2 where u1u2: "u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<circ> u2"
            using 2 u
            by (metis ConD(3) Con_implies_is_Lam_iff_is_Lam Con_sym con_def is_App_def is_Lam_def
                      lambda.disc(8) null_char prfx_implies_con subs subs_implies_prfx)
          have "mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) = mtp x (\<^bold>\<lambda>\<^bold>[t1 \\ u1\<^bold>] \<^bold>\<Zspot> (t2 \\ u2))"
            using u1u2 subs
            by (metis Con_sym Ide.simps(1) ide_char resid.simps(6) subs_implies_prfx)
          also have "... = mtp (Suc x) (resid t1 u1) +
                           mtp x (resid t2 u2) * max 1 (mtp 0 (resid t1 u1))"
            by simp
          also have "... \<le> mtp (Suc x) t1 + mtp x (resid t2 u2) * max 1 (mtp 0 (resid t1 u1))"
            using u1u2 ind1 [of u1 "Suc x"] con_sym ide_char resid_arr_ide prfx_implies_con
                  subs subs_implies_prfx u
            by force
          also have "... \<le> mtp (Suc x) t1 + mtp x t2 * max 1 (mtp 0 (resid t1 u1))"
            using u1u2 ind2 [of u2 x]
            by (metis (no_types, lifting) Con_implies_Coinitial_ind add_left_mono
                dual_order.eq_iff elementary_reduction.simps(4) lambda.disc(11)
                mult_le_cancel2 prfx_App_iff resid.simps(31) resid_Arr_Ide subs subs.simps(4)
                subs_implies_prfx u)
          also have "... \<le> mtp (Suc x) t1 + mtp x t2 * max 1 (mtp 0 t1)"
            using ind1 [of u1 0]
            by (metis Con_implies_Coinitial_ind Ide.simps(3) elementary_reduction.simps(3)
                elementary_reduction.simps(4) lambda.disc(11) max.mono mult_le_mono
                nat_add_left_cancel_le nat_le_linear prfx_App_iff resid.simps(31) resid_Arr_Ide
                subs subs.simps(4) subs_implies_prfx u u1u2)
          also have "... = mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by auto
          finally show "mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) \<le> mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)" by blast
        qed
        moreover have "is_Beta u \<Longrightarrow> mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) \<le> mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          assume 2: "is_Beta u"
          obtain u1 u2 where u1u2: "u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2"
            using 2 u is_Beta_def by auto
          have "mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) = mtp x (subst (t2 \\ u2) (t1 \\ u1))"
            using u1u2 subs
            by (metis con_def con_sym null_char prfx_implies_con resid.simps(4) subs_implies_prfx)
          also have "... \<le> mtp (Suc x) (resid t1 u1) +
                             mtp x (resid t2 u2) * max 1 (mtp 0 (resid t1 u1))"
            apply (cases "x = 0")
            using mtp0_subst_le Raise_0 mtp_Subst' [of "x - 1" 0 "resid t2 u2" "resid t1 u1"]
            by auto
          also have "... \<le> mtp (Suc x) t1 + mtp x t2 * max 1 (mtp 0 t1)"
            using ind1 ind2
            apply simp
            by (metis Coinitial_iff_Con Ide.simps(1) dual_order.eq_iff elementary_reduction.simps(5)
                ide_char resid.simps(4) resid_Arr_Ide subs subs_implies_prfx u u1u2)
          also have "... = mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by simp
          finally show "mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) \<le> mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)" by blast
        qed
        ultimately show "mtp x ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) \<le> mtp x (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
          using 1 by blast
      qed
    qed

    text \<open>
      Next we define the ``height'' of a term.  This counts the number of steps in a development
      of maximal length of the given term.
    \<close>

    fun hgt
    where "hgt \<^bold>\<sharp> = 0"
        | "hgt \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> = 0"
        | "hgt \<^bold>\<lambda>\<^bold>[t\<^bold>] = hgt t"
        | "hgt (t \<^bold>\<circ> u) = hgt t + hgt u"
        | "hgt (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = Suc (hgt t + hgt u * max 1 (mtp 0 t))"

    lemma hgt_resid_ide:
    shows "\<lbrakk>ide u; u \<sqsubseteq> t\<rbrakk> \<Longrightarrow> hgt (resid t u) \<le> hgt t"
      by (metis con_sym eq_imp_le resid_arr_ide prfx_implies_con subs_implies_prfx)

    lemma hgt_Raise:
    shows "hgt (Raise l k t) = hgt t"
      using mtpE_eq_Raise
      by (induct t arbitrary: l k) auto

    lemma hgt_Subst:
    shows "Arr u \<Longrightarrow> hgt (Subst k u t) = hgt t + hgt u * mtp k t"
    proof (induct t arbitrary: u k)
      show "\<And>u k. Arr u \<Longrightarrow> hgt (Subst k u \<^bold>\<sharp>) = hgt \<^bold>\<sharp> + hgt u * mtp k \<^bold>\<sharp>"
        by simp
      show "\<And>x u k. Arr u \<Longrightarrow> hgt (Subst k u \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>) = hgt \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> + hgt u * mtp k \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        using hgt_Raise by auto
      show "\<And>t u k. \<lbrakk>\<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t) = hgt t + hgt u * mtp k t; Arr u\<rbrakk>
                       \<Longrightarrow> hgt (Subst k u \<^bold>\<lambda>\<^bold>[t\<^bold>]) = hgt \<^bold>\<lambda>\<^bold>[t\<^bold>] + hgt u * mtp k \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        by auto
      show "\<And>t1 t2 u k.
              \<lbrakk>\<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t1) = hgt t1 + hgt u * mtp k t1;
               \<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t2) = hgt t2 + hgt u * mtp k t2; Arr u\<rbrakk>
                   \<Longrightarrow> hgt (Subst k u (t1 \<^bold>\<circ> t2)) = hgt (t1 \<^bold>\<circ> t2) + hgt u * mtp k (t1 \<^bold>\<circ> t2)"
        by (simp add: distrib_left)
      show "\<And>t1 t2 u k.
               \<lbrakk>\<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t1) = hgt t1 + hgt u * mtp k t1;
                \<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t2) = hgt t2 + hgt u * mtp k t2; Arr u\<rbrakk>
                  \<Longrightarrow> hgt (Subst k u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) = hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + hgt u * mtp k (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      proof -
        fix t1 t2 u k
        assume ind1: "\<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t1) = hgt t1 + hgt u * mtp k t1"
        assume ind2: "\<And>u k. Arr u \<Longrightarrow> hgt (Subst k u t2) = hgt t2 + hgt u * mtp k t2"
        assume u: "Arr u"
        show "hgt (Subst k u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) = hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + hgt u * mtp k (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          have "hgt (Subst k u (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) =
                Suc (hgt (Subst (Suc k) u t1) +
                  hgt (Subst k u t2) * max 1 (mtp 0 (Subst (Suc k) u t1)))"
            by simp
          also have "... = Suc ((hgt t1 + hgt u * mtp (Suc k) t1) +
                                (hgt t2 + hgt u * mtp k t2) * max 1 (mtp 0 (Subst (Suc k) u t1)))"
            using u ind1 [of u "Suc k"] ind2 [of u k] by simp
          also have "... = Suc (hgt t1 + hgt t2 * max 1 (mtp 0 (Subst (Suc k) u t1)) +
                                hgt u * mtp (Suc k) t1) +
                                hgt u * mtp k t2 * max 1 (mtp 0 (Subst (Suc k) u t1))"
            using comm_semiring_class.distrib by force
          also have "... = Suc (hgt t1 + hgt t2 * max 1 (mtp 0 (Subst (Suc k) u t1)) +
                                hgt u * (mtp (Suc k) t1 +
                                           mtp k t2 * max 1 (mtp 0 (Subst (Suc k) u t1))))"
            by (simp add: distrib_left)
          also have "... = Suc (hgt t1 + hgt t2 * max 1 (mtp 0 t1) +
                                hgt u * (mtp (Suc k) t1 +
                                           mtp k t2 * max 1 (mtp 0 t1)))"
          proof -
            have "mtp 0 (Subst (Suc k) u t1) = mtp 0 t1"
              using mtp\<^sub>0_Subst_cancel by auto
            thus ?thesis by simp
          qed
          also have "... = hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) + hgt u * mtp k (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by simp
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma elementary_reduction_decreases_hgt:
    shows "\<lbrakk>elementary_reduction u; u \<sqsubseteq> t\<rbrakk> \<Longrightarrow> hgt (t \\ u) < hgt t"
    proof (induct t arbitrary: u)
      show "\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> \<^bold>\<sharp>\<rbrakk> \<Longrightarrow> hgt (\<^bold>\<sharp> \\ u) < hgt \<^bold>\<sharp>"
        by simp
      show "\<And>u x. \<lbrakk>elementary_reduction u; u \<sqsubseteq> \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>\<rbrakk> \<Longrightarrow> hgt (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \\ u) < hgt \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        using Ide.simps(2) elementary_reduction_not_ide ide_backward_stable ide_char
              subs_implies_prfx
        by blast
      show "\<And>t u. \<lbrakk>\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t\<rbrakk> \<Longrightarrow> hgt (t \\ u) < hgt t;
                   elementary_reduction u; u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t\<^bold>]\<rbrakk>
                     \<Longrightarrow> hgt (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u) < hgt \<^bold>\<lambda>\<^bold>[t\<^bold>]"
      proof -
        fix t u
        assume ind: "\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t\<rbrakk> \<Longrightarrow> hgt (t \\ u) < hgt t"
        assume u: "elementary_reduction u"
        assume subs: "u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        show "hgt (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u) < hgt \<^bold>\<lambda>\<^bold>[t\<^bold>]"
          using u subs ind
          apply (cases u)
              apply simp_all
          by fastforce
      qed
      show "\<And>t1 t2 u.
              \<lbrakk>\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t1\<rbrakk> \<Longrightarrow> hgt (t1 \\ u) < hgt t1;
               \<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t2\<rbrakk> \<Longrightarrow> hgt (t2 \\ u) < hgt t2;
               elementary_reduction u; u \<sqsubseteq> t1 \<^bold>\<circ> t2\<rbrakk>
                  \<Longrightarrow> hgt ((t1 \<^bold>\<circ> t2) \\ u) < hgt (t1 \<^bold>\<circ> t2)"
      proof -
        fix t1 t2 u
        assume ind1: "\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t1\<rbrakk> \<Longrightarrow> hgt (t1 \\ u) < hgt t1"
        assume ind2: "\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t2\<rbrakk> \<Longrightarrow> hgt (t2 \\ u) < hgt t2"
        assume u: "elementary_reduction u"
        assume subs: "u \<sqsubseteq> t1 \<^bold>\<circ> t2"
        show "hgt ((t1 \<^bold>\<circ> t2) \\ u) < hgt (t1 \<^bold>\<circ> t2)"
          using u subs ind1 ind2
          apply (cases u)
              apply simp_all
          by (metis add_le_less_mono add_less_le_mono hgt_resid_ide ide_char not_less0
                    zero_less_iff_neq_zero)
      qed
      show "\<And>t1 t2 u.
              \<lbrakk>\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t1\<rbrakk> \<Longrightarrow> hgt (t1 \\ u) < hgt t1;
               \<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t2\<rbrakk> \<Longrightarrow> hgt (t2 \\ u) < hgt t2;
               elementary_reduction u; u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2\<rbrakk>
                  \<Longrightarrow> hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      proof -
        fix t1 t2 u
        assume ind1: "\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t1\<rbrakk> \<Longrightarrow> hgt (t1 \\ u) < hgt t1"
        assume ind2: "\<And>u. \<lbrakk>elementary_reduction u; u \<sqsubseteq> t2\<rbrakk> \<Longrightarrow> hgt (t2 \\ u) < hgt t2"
        assume u: "elementary_reduction u"
        assume subs: "u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2"
        have "is_App u \<or> is_Beta u"
          using subs by (metis prfx_Beta_iff subs_implies_prfx)
        moreover have "is_App u \<Longrightarrow> hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          fix u1 u2
          assume 0: "is_App u"
          obtain u1 u1' u2 where 1: "u = u1 \<^bold>\<circ> u2 \<and> u1 = \<^bold>\<lambda>\<^bold>[u1'\<^bold>]"
            using u 0
            by (metis ConD(3) Con_implies_is_Lam_iff_is_Lam Con_sym con_def is_App_def is_Lam_def
                      null_char prfx_implies_con subs subs_implies_prfx)
          have "hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) = hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ (u1 \<^bold>\<circ> u2))"
            using 1 by simp
          also have "... = hgt (\<^bold>\<lambda>\<^bold>[t1 \\ u1'\<^bold>] \<^bold>\<Zspot> t2 \\ u2)"
            by (metis "1" Con_sym Ide.simps(1) ide_char resid.simps(6) subs subs_implies_prfx)
          also have "... = Suc (hgt (t1 \\ u1') + hgt (t2 \\ u2) * max (Suc 0) (mtp 0 (t1 \\ u1')))"
            by auto
          also have "... < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
          proof -
            have "elementary_reduction (un_App1 u) \<and> ide (un_App2 u) \<or>
                  ide (un_App1 u) \<and> elementary_reduction (un_App2 u)"
              using u 1 elementary_reduction_App_iff [of u] by simp
            moreover have "elementary_reduction (un_App1 u) \<and> ide (un_App2 u) \<Longrightarrow> ?thesis"
            proof -
              assume 2: "elementary_reduction (un_App1 u) \<and> ide (un_App2 u)"
              have "elementary_reduction u1' \<and> ide (un_App2 u)"
                using 1 2 u elementary_reduction_Lam_iff by force
              moreover have "mtp 0 (t1 \\ u1') \<le> mtp 0 t1"
                using 1 calculation elementary_reduction_nonincreases_mtp subs
                      subs.simps(4)
                by blast
              moreover have "mtp 0 (t2 \\ u2) \<le> mtp 0 t2"
                using 1 hgt_resid_ide [of u2 t2]
                by (metis calculation(1) con_sym eq_refl resid_arr_ide lambda.sel(4)
                    prfx_implies_con subs subs.simps(4) subs_implies_prfx)
              ultimately show ?thesis
                using 1 2 ind1 [of u1'] hgt_resid_ide
                apply simp
                by (metis "1" Suc_le_mono \<open>mtp 0 (t1 \ u1') \<le> mtp 0 t1\<close> add_less_le_mono
                    le_add1 le_add_same_cancel1 max.mono mult_le_mono subs subs.simps(4))
            qed
            moreover have "ide (un_App1 u) \<and> elementary_reduction (un_App2 u) \<Longrightarrow> ?thesis"
            proof -
              assume 2: "ide (un_App1 u) \<and> elementary_reduction (un_App2 u)"
              have "ide (un_App1 u) \<and> elementary_reduction u2"
                using 1 2 u elementary_reduction_Lam_iff by force
              moreover have "mtp 0 (t1 \\ u1') \<le> mtp 0 t1"
                using 1 hgt_resid_ide [of u1' t1]
                by (metis Ide.simps(3) calculation con_sym eq_refl ide_char resid_arr_ide
                    lambda.sel(3) prfx_implies_con subs subs.simps(4) subs_implies_prfx)
              moreover have "mtp 0 (t2 \\ u2) \<le> mtp 0 t2"
                using 1 elementary_reduction_nonincreases_mtp subs calculation(1) subs.simps(4)
                by blast
              ultimately show ?thesis
                using 1 2 ind2 [of u2]
                apply simp
                by (metis Coinitial_iff_Con Ide_iff_Src_self Nat.add_0_right add_le_less_mono
                          ide_char Ide.simps(1) subs.simps(4) le_add1 max_nat.neutr_eq_iff
                          mult_less_cancel2 nat.distinct(1) neq0_conv resid_Arr_Src subs
                          subs_implies_prfx)
            qed
            ultimately show ?thesis by blast
          qed
          also have "... = Suc (hgt t1 + hgt t2 * max 1 (mtp 0 t1))"
            by simp
          also have "... = hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by simp
          finally show "hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by blast
        qed
        moreover have "is_Beta u \<Longrightarrow> hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        proof -
          fix u1 u2
          assume 0: "is_Beta u"
          obtain u1 u2 where 1: "u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2"
            using u 0 by (metis lambda.collapse(4))
          have "hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) = hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2))"
            using 1 by simp
          also have "... = hgt (subst (resid t2 u2) (resid t1 u1))"
            by (metis "1" con_def con_sym null_char prfx_implies_con resid.simps(4)
                subs subs_implies_prfx)
          also have "... = hgt (resid t1 u1) + hgt (resid t2 u2) * mtp 0 (resid t1 u1)"
          proof -
            have "Arr (resid t2 u2)"
              by (metis "1" Coinitial_resid_resid Con_sym Ide.simps(1) ide_char resid.simps(4)
                  subs subs_implies_prfx)
            thus ?thesis
              using hgt_Subst [of "resid t2 u2" 0 "resid t1 u1"] by simp
          qed
          also have "... < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
          proof -
            have "ide u1 \<and> ide u2"
              using u 1 elementary_reduction_Beta_iff [of u] by auto
           thus ?thesis
             using 1 hgt_resid_ide
             by (metis add_le_mono con_sym hgt.simps(5) resid_arr_ide less_Suc_eq_le
                 max.cobounded2 nat_mult_max_right prfx_implies_con subs subs.simps(5)
                 subs_implies_prfx)
          qed
          finally show "hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
            by blast
        qed
        ultimately show "hgt ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u) < hgt (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)" by blast
      qed
    qed

  end

  context reduction_paths
  begin

    lemma length_devel_le_hgt:
    shows "development t U \<Longrightarrow> length U \<le> \<Lambda>.hgt t"
      using \<Lambda>.elementary_reduction_decreases_hgt
      by (induct U arbitrary: t, auto, fastforce)

    text \<open>
      We finally arrive at the main result of this section:
      the Finite Developments Theorem.
    \<close>

    theorem finite_developments:
    shows "FD t"
      using length_devel_le_hgt [of t] FD_def by auto

    subsection "Complete Developments"

    text \<open>
      A \emph{complete development} is a development in which there are no residuals of originally
      marked redexes left to contract.
    \<close>

    definition complete_development
    where "complete_development t U \<equiv> development t U \<and> (\<Lambda>.Ide t \<or> [t] \<^sup>*\<lesssim>\<^sup>* U)"

    lemma complete_development_Ide_iff:
    shows "complete_development t U \<Longrightarrow> \<Lambda>.Ide t \<longleftrightarrow> U = []"
      using complete_development_def development_Ide Ide.simps(1) ide_char
      by (induct t) auto

    lemma complete_development_cons:
    assumes "complete_development t (u # U)"
    shows "complete_development (t \\ u) U"
      using assms complete_development_def
      by (metis Ide.simps(1) Ide.simps(2) Resid_rec(1) Resid_rec(3)
          complete_development_Ide_iff ide_char development.simps(2)
          \<Lambda>.ide_char list.simps(3))

    lemma complete_development_cong:
    shows "\<lbrakk>complete_development t U; \<not> \<Lambda>.Ide t\<rbrakk> \<Longrightarrow> [t] \<^sup>*\<sim>\<^sup>* U"
      using complete_development_def development_implies
      by (induct U) auto

    lemma complete_developments_cong:
    assumes "\<not> \<Lambda>.Ide t" and "complete_development t U" and "complete_development t V"
    shows "U \<^sup>*\<sim>\<^sup>* V"
      using assms complete_development_cong [of "t"] cong_symmetric cong_transitive
      by blast

    lemma Trgs_complete_development:
    shows "\<lbrakk>complete_development t U; \<not> \<Lambda>.Ide t\<rbrakk> \<Longrightarrow> Trgs U = {\<Lambda>.Trg t}"
      using complete_development_cong Ide.simps(1) Srcs_Resid Trgs.simps(2)
            Trgs_Resid_sym ide_char complete_development_def development_imp_Arr \<Lambda>.targets_char\<^sub>\<Lambda>
      apply simp
      by (metis Srcs_Resid Trgs.simps(2) con_char ide_def)

    text \<open>
      Now that we know all developments are finite, it is easy to construct a complete development
      by an iterative process that at each stage contracts one of the remaining marked redexes
      at each stage.  It is also possible to construct a complete development by structural
      induction without using the finite developments property, but it is more work to prove the
      correctness.
    \<close>

    fun (in lambda_calculus) bottom_up_redex
    where "bottom_up_redex \<^bold>\<sharp> = \<^bold>\<sharp>"
        | "bottom_up_redex \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        | "bottom_up_redex \<^bold>\<lambda>\<^bold>[M\<^bold>] = \<^bold>\<lambda>\<^bold>[bottom_up_redex M\<^bold>]"
        | "bottom_up_redex (M \<^bold>\<circ> N) =
             (if \<not> Ide M then bottom_up_redex M \<^bold>\<circ> Src N else M \<^bold>\<circ> bottom_up_redex N)"
        | "bottom_up_redex (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) =
             (if \<not> Ide M then \<^bold>\<lambda>\<^bold>[bottom_up_redex M\<^bold>] \<^bold>\<circ> Src N
              else if \<not> Ide N then \<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> bottom_up_redex N
              else \<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N)"

    lemma (in lambda_calculus) elementary_reduction_bottom_up_redex:
    shows "\<lbrakk>Arr t; \<not> Ide t\<rbrakk> \<Longrightarrow> elementary_reduction (bottom_up_redex t)"
      using Ide_Src
      by (induct t) auto

    lemma (in lambda_calculus) subs_bottom_up_redex:
    shows "Arr t \<Longrightarrow> bottom_up_redex t \<sqsubseteq> t"
      apply (induct t)
          apply auto[3]
       apply (metis Arr.simps(4) Ide.simps(4) Ide_Src Ide_iff_Src_self Ide_implies_Arr
                    bottom_up_redex.simps(4) ide_char lambda.disc(14) lambda.sel(3) lambda.sel(4)
                    subs_App subs_Ide)
      by (metis Arr.simps(5) Ide_Src Ide_iff_Src_self Ide_implies_Arr bottom_up_redex.simps(5)
                ide_char subs.simps(4) subs.simps(5) subs_Ide)

    function (sequential) bottom_up_development
    where "bottom_up_development t =
           (if \<not> \<Lambda>.Arr t \<or> \<Lambda>.Ide t then []
            else \<Lambda>.bottom_up_redex t # (bottom_up_development (t \\ \<Lambda>.bottom_up_redex t)))"
      by pat_completeness auto

    termination bottom_up_development
      using \<Lambda>.elementary_reduction_decreases_hgt \<Lambda>.elementary_reduction_bottom_up_redex
            \<Lambda>.subs_bottom_up_redex
      by (relation "measure \<Lambda>.hgt") auto

    lemma complete_development_bottom_up_development_ind:
    shows "\<lbrakk>\<Lambda>.Arr t; length (bottom_up_development t) \<le> n\<rbrakk>
              \<Longrightarrow> complete_development t (bottom_up_development t)"
    proof (induct n arbitrary: t)
      show "\<And>t. \<lbrakk>\<Lambda>.Arr t; length (bottom_up_development t) \<le> 0\<rbrakk>
                   \<Longrightarrow> complete_development t (bottom_up_development t)"
        using complete_development_def development_Ide by auto
      show "\<And>n t. \<lbrakk>\<And>t. \<lbrakk>\<Lambda>.Arr t; length (bottom_up_development t) \<le> n\<rbrakk>
                           \<Longrightarrow> complete_development t (bottom_up_development t);
                   \<Lambda>.Arr t; length (bottom_up_development t) \<le> Suc n\<rbrakk>
                     \<Longrightarrow> complete_development t (bottom_up_development t)"
      proof -
        fix n t
        assume t: "\<Lambda>.Arr t"
        assume n: "length (bottom_up_development t) \<le> Suc n"
        assume ind: "\<And>t. \<lbrakk>\<Lambda>.Arr t; length (bottom_up_development t) \<le> n\<rbrakk>
                           \<Longrightarrow> complete_development t (bottom_up_development t)"
        show "complete_development t (bottom_up_development t)"
        proof (cases "bottom_up_development t")
          show "bottom_up_development t = [] \<Longrightarrow> ?thesis"
            using ind t by force
          fix u U
          assume uU: "bottom_up_development t = u # U"
          have 1: "\<Lambda>.elementary_reduction u \<and> u \<sqsubseteq> t"
            using t uU
            by (metis bottom_up_development.simps \<Lambda>.elementary_reduction_bottom_up_redex
                list.inject list.simps(3) \<Lambda>.subs_bottom_up_redex)
          moreover have "complete_development (\<Lambda>.resid t u) U"
            using 1 ind
            by (metis Suc_le_length_iff \<Lambda>.arr_char \<Lambda>.arr_resid_iff_con bottom_up_development.simps
                      list.discI list.inject n not_less_eq_eq \<Lambda>.prfx_implies_con
                      \<Lambda>.con_sym \<Lambda>.subs_implies_prfx uU)
          ultimately show ?thesis
            by (metis Con_sym Ide.simps(2) Resid_rec(1) Resid_rec(3)
                complete_development_Ide_iff complete_development_def ide_char
                development.simps(2) development_implies \<Lambda>.ide_char list.simps(3) uU)
        qed
      qed
    qed

    lemma complete_development_bottom_up_development:
    assumes "\<Lambda>.Arr t"
    shows "complete_development t (bottom_up_development t)"
      using assms complete_development_bottom_up_development_ind by blast

  end

  section "Reduction Strategies"

  context lambda_calculus
  begin

    text \<open>
      A \emph{reduction strategy} is a function taking an identity term to an arrow having that
      identity as its source.
    \<close>

    definition reduction_strategy
    where "reduction_strategy f \<longleftrightarrow> (\<forall>t. Ide t \<longrightarrow> Coinitial (f t) t)"

    text \<open>
      The following defines the iterated application of a reduction strategy to an identity term.
    \<close>

    fun reduce
    where "reduce f a 0 = a"
        | "reduce f a (Suc n) = reduce f (Trg (f a)) n"

    lemma red_reduce:
    assumes "reduction_strategy f"
    shows "Ide a \<Longrightarrow> red a (reduce f a n)"
      apply (induct n arbitrary: a, auto)
       apply (metis Ide_iff_Src_self Ide_iff_Trg_self Ide_implies_Arr red.simps)
      by (metis Ide_Trg Ide_iff_Src_self assms red.intros(1) red.intros(2) reduction_strategy_def)

    text \<open>
      A reduction strategy is \emph{normalizing} if iterated application of it to a normalizable
      term eventually yields a normal form.
    \<close>

    definition normalizing_strategy
    where "normalizing_strategy f \<longleftrightarrow> (\<forall>a. normalizable a \<longrightarrow> (\<exists>n. NF (reduce f a n)))"

  end

  context reduction_paths
  begin

    text \<open>
      The following function constructs the reduction path that results by iterating the
      application of a reduction strategy to a term.
    \<close>

    fun apply_strategy
    where "apply_strategy f a 0 = []"
        | "apply_strategy f a (Suc n) = f a # apply_strategy f (\<Lambda>.Trg (f a)) n"

    lemma apply_strategy_gives_path_ind:
    assumes "\<Lambda>.reduction_strategy f"
    shows "\<lbrakk>\<Lambda>.Ide a; n > 0\<rbrakk> \<Longrightarrow> Arr (apply_strategy f a n) \<and>
                                length (apply_strategy f a n) = n \<and>
                                Src (apply_strategy f a n) = a \<and>
                                Trg (apply_strategy f a n) = \<Lambda>.reduce f a n"
    proof (induct n arbitrary: a, simp)
      fix n a
      assume ind: "\<And>a. \<lbrakk>\<Lambda>.Ide a; 0 < n\<rbrakk> \<Longrightarrow> Arr (apply_strategy f a n) \<and>
                                            length (apply_strategy f a n) = n \<and>
                                            Src (apply_strategy f a n) = a \<and>
                                            Trg (apply_strategy f a n) = \<Lambda>.reduce f a n"
      assume a: "\<Lambda>.Ide a"
      show "Arr (apply_strategy f a (Suc n)) \<and>
            length (apply_strategy f a (Suc n)) = Suc n \<and>
            Src (apply_strategy f a (Suc n)) = a \<and>
            Trg (apply_strategy f a (Suc n)) = \<Lambda>.reduce f a (Suc n)"
      proof (intro conjI)
        have 1: "\<Lambda>.Arr (f a) \<and> \<Lambda>.Src (f a) = a"
          using assms a \<Lambda>.reduction_strategy_def
          by (metis \<Lambda>.Ide_iff_Src_self)
        show "Arr (apply_strategy f a (Suc n))"
          using "1" Arr.elims(3) ind \<Lambda>.targets_char\<^sub>\<Lambda> \<Lambda>.Ide_Trg by fastforce
        show "Src (apply_strategy f a (Suc n)) = a"
          by (simp add: "1")
        show "length (apply_strategy f a (Suc n)) = Suc n"
          by (metis "1" \<Lambda>.Ide_Trg One_nat_def Suc_eq_plus1 ind list.size(3) list.size(4)
              neq0_conv apply_strategy.simps(1) apply_strategy.simps(2))
        show "Trg (apply_strategy f a (Suc n)) = \<Lambda>.reduce f a (Suc n)"
        proof (cases "apply_strategy f (\<Lambda>.Trg (f a)) n = []")
          show "apply_strategy f (\<Lambda>.Trg (f a)) n = [] \<Longrightarrow> ?thesis"
            using a 1 ind [of "\<Lambda>.Trg (f a)"] \<Lambda>.Ide_Trg \<Lambda>.targets_char\<^sub>\<Lambda> by force
          assume 2: "apply_strategy f (\<Lambda>.Trg (f a)) n \<noteq> []"
          have "Trg (apply_strategy f a (Suc n)) = Trg (apply_strategy f (\<Lambda>.Trg (f a)) n)"
            using a 1 ind [of "\<Lambda>.Trg (f a)"]
            by (simp add: "2")
          also have "... = \<Lambda>.reduce f a (Suc n)"
            using 1 2 \<Lambda>.Ide_Trg ind [of "\<Lambda>.Trg (f a)"] by fastforce
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma apply_strategy_gives_path:
    assumes "\<Lambda>.reduction_strategy f" and "\<Lambda>.Ide a" and "n > 0"
    shows "Arr (apply_strategy f a n)"
    and "length (apply_strategy f a n) = n"
    and "Src (apply_strategy f a n) = a"
    and "Trg (apply_strategy f a n) = \<Lambda>.reduce f a n"
      using assms apply_strategy_gives_path_ind by auto

    lemma reduce_eq_Trg_apply_strategy:
    assumes "\<Lambda>.reduction_strategy S" and "\<Lambda>.Ide a"
    shows "n > 0 \<Longrightarrow> \<Lambda>.reduce S a n = Trg (apply_strategy S a n)"
      using assms
      apply (induct n)
       apply simp_all
      by (metis Arr.simps(1) Trg_simp apply_strategy_gives_path_ind \<Lambda>.Ide_Trg
          \<Lambda>.reduce.simps(1) \<Lambda>.reduction_strategy_def \<Lambda>.trg_char neq0_conv
          apply_strategy.simps(1))

  end

  subsection "Parallel Reduction"

  context lambda_calculus
  begin

    text \<open>
       \emph{Parallel reduction} is the strategy that contracts all available redexes at each step.
    \<close>

    fun parallel_strategy
    where "parallel_strategy \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>"
        | "parallel_strategy \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[parallel_strategy t\<^bold>]"
        | "parallel_strategy (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) = \<^bold>\<lambda>\<^bold>[parallel_strategy t\<^bold>] \<^bold>\<Zspot> parallel_strategy u"
        | "parallel_strategy (t \<^bold>\<circ> u) = parallel_strategy t \<^bold>\<circ> parallel_strategy u"
        | "parallel_strategy (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = \<^bold>\<lambda>\<^bold>[parallel_strategy t\<^bold>] \<^bold>\<Zspot> parallel_strategy u"
        | "parallel_strategy \<^bold>\<sharp> = \<^bold>\<sharp>"

    lemma parallel_strategy_is_reduction_strategy:
    shows "reduction_strategy parallel_strategy"
    proof (unfold reduction_strategy_def, intro allI impI)
      fix t
      show "Ide t \<Longrightarrow> Coinitial (parallel_strategy t) t"
        using Ide_implies_Arr
        apply (induct t, auto)
        by force+
    qed

    lemma parallel_strategy_Src_eq:
    shows "Arr t \<Longrightarrow> parallel_strategy (Src t) = parallel_strategy t"
      by (induct t) auto

    lemma subs_parallel_strategy_Src:
    shows "Arr t \<Longrightarrow> t \<sqsubseteq> parallel_strategy (Src t)"
      by (induct t) auto

  end

  context reduction_paths
  begin

    text \<open>
     Parallel reduction is a universal strategy in the sense that every reduction path is
     \<open>\<^sup>*\<lesssim>\<^sup>*\<close>-below the path generated by the parallel reduction strategy.
    \<close>

    lemma parallel_strategy_is_universal:
    shows "\<lbrakk>n > 0; n \<le> length U; Arr U\<rbrakk>
              \<Longrightarrow> take n U \<^sup>*\<lesssim>\<^sup>* apply_strategy \<Lambda>.parallel_strategy (Src U) n"
    proof (induct n arbitrary: U, simp)
      fix n a and U :: "\<Lambda>.lambda list"
      assume n: "Suc n \<le> length U"
      assume U: "Arr U"
      assume ind: "\<And>U. \<lbrakk>0 < n; n \<le> length U; Arr U\<rbrakk>
                          \<Longrightarrow> take n U \<^sup>*\<lesssim>\<^sup>* apply_strategy \<Lambda>.parallel_strategy (Src U) n"
      have 1: "take (Suc n) U = hd U # take n (tl U)"
        by (metis U Arr.simps(1) take_Suc)
      have 2: "hd U \<sqsubseteq> \<Lambda>.parallel_strategy (Src U)"
        by (metis Arr_imp_arr_hd Con_single_ideI(2) Resid_Arr_Src Src_resid Srcs_simp\<^sub>\<Lambda>\<^sub>P
            Trg.simps(2) U \<Lambda>.source_is_ide \<Lambda>.trg_ide empty_set \<Lambda>.arr_char \<Lambda>.sources_char\<^sub>\<Lambda>
            \<Lambda>.subs_parallel_strategy_Src list.set_intros(1) list.simps(15))
      show "take (Suc n) U \<^sup>*\<lesssim>\<^sup>* apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n)"
      proof (cases "apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n)")
        show "apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n) = [] \<Longrightarrow>
                take (Suc n) U \<^sup>*\<lesssim>\<^sup>* apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n)"
          by simp
        fix v V
        assume 3: "apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n) = v # V"
        show "take (Suc n) U \<^sup>*\<lesssim>\<^sup>* apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n)"
        proof (cases "V = []")
          show "V = [] \<Longrightarrow> ?thesis"
            using 1 2 3 ind ide_char
            by (metis Suc_inject Ide.simps(2) Resid.simps(3) list.discI list.inject
                      \<Lambda>.prfx_implies_con apply_strategy.elims \<Lambda>.subs_implies_prfx take0)
          assume V: "V \<noteq> []"
          have 4: "Arr (v # V)"
            using 3 apply_strategy_gives_path(1)
            by (metis Arr_imp_arr_hd Srcs_simp\<^sub>P\<^sub>W\<^sub>E Srcs_simp\<^sub>\<Lambda>\<^sub>P U \<Lambda>.Ide_Src \<Lambda>.arr_iff_has_target
                \<Lambda>.parallel_strategy_is_reduction_strategy \<Lambda>.targets_char\<^sub>\<Lambda> singleton_insert_inj_eq'
                zero_less_Suc)
          have 5: "Arr (hd U # take n (tl U))"
            by (metis 1 U Arr_append_iff\<^sub>P id_take_nth_drop list.discI not_less take_all_iff)
          have 6: "Srcs (hd U # take n (tl U)) = Srcs (v # V)"
            by (metis 2 3 \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide.simps(1) Srcs.simps(2) Srcs.simps(3)
                \<Lambda>.ide_char list.exhaust_sel list.inject apply_strategy.simps(2) \<Lambda>.sources_char\<^sub>\<Lambda>
                \<Lambda>.subs_implies_prfx)
          have "take (Suc n) U \<^sup>*\\\<^sup>* apply_strategy \<Lambda>.parallel_strategy (Src U) (Suc n) =
                [hd U \\ v] \<^sup>*\\\<^sup>* V @ (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* [hd U \\ v])"
            using U V 1 3 4 5 6
            by (metis Resid.simps(1) Resid_cons(1) Resid_rec(3-4) confluence_ind)
          moreover have "Ide ..."
          proof
            have 7: "v = \<Lambda>.parallel_strategy (Src U) \<and>
                      V = apply_strategy \<Lambda>.parallel_strategy (Src U \\ v) n"
              using 3 \<Lambda>.subs_implies_prfx \<Lambda>.subs_parallel_strategy_Src
              apply simp
              by (metis (full_types) \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide.simps(1) \<Lambda>.Trg.simps(5)
                  \<Lambda>.parallel_strategy.simps(9) \<Lambda>.resid_Src_Arr)
            show 8: "Ide ([hd U \\ v] \<^sup>*\\\<^sup>* V)"
              by (metis 2 4 5 6 7 V Con_initial_left Ide.simps(2)
                  confluence_ind Con_rec(3) Resid_Ide_Arr_ind \<Lambda>.subs_implies_prfx)
            show 9: "Ide ((take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* [hd U \\ v]))"
            proof -
              have 10: "\<Lambda>.Ide (hd U \\ v)"
                using 2 7 \<Lambda>.ide_char \<Lambda>.subs_implies_prfx by presburger
              have 11: "V = apply_strategy \<Lambda>.parallel_strategy (\<Lambda>.Trg v) n"
                using 3 by auto
              have "(take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* [hd U \\ v]) =
                    (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) \<^sup>*\\\<^sup>*
                       apply_strategy \<Lambda>.parallel_strategy (\<Lambda>.Trg v) n"
                by (metis 8 10 11 Ide.simps(1) Resid_single_ide(2) \<Lambda>.prfx_char)
              moreover have "Ide ..."
              proof -
                have "Ide (take n (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) \<^sup>*\\\<^sup>*
                             apply_strategy \<Lambda>.parallel_strategy (\<Lambda>.Trg v) n)"
                proof -
                  have "0 < n"
                  proof -
                    have "length V = n"
                      using apply_strategy_gives_path
                      by (metis 10 11 V \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Trg \<Lambda>.Arr_not_Nil
                          \<Lambda>.Ide_implies_Arr \<Lambda>.parallel_strategy_is_reduction_strategy neq0_conv
                          apply_strategy.simps(1))
                    thus ?thesis
                      using V by blast
                  qed
                  moreover have "n \<le> length (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U])"
                  proof -
                    have "length (take n (tl U)) = n"
                      using n by force
                    thus ?thesis
                      using n U length_Resid [of "take n (tl U)" "[v \\ hd U]"]
                      by (metis 4 5 6 Arr.simps(1) Con_cons(2) Con_rec(2)
                          confluence_ind dual_order.eq_iff)
                  qed
                  moreover have "\<Lambda>.Trg v = Src (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U])"
                  proof -
                    have "Src (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) = Trg [v \\ hd U]"
                      by (metis Src_resid calculation(1-2) linorder_not_less list.size(3))
                    also have "... = \<Lambda>.Trg v"
                      by (metis 10 Trg.simps(2) \<Lambda>.Arr_not_Nil \<Lambda>.apex_sym \<Lambda>.trg_ide
                          \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src_resid \<Lambda>.prfx_char)
                    finally show ?thesis by simp
                  qed
                  ultimately show ?thesis
                    using ind [of "Resid (take n (tl U)) [\<Lambda>.resid v (hd U)]"] ide_char
                    by (metis Con_imp_Arr_Resid le_zero_eq less_not_refl list.size(3))
                qed
                moreover have "take n (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) =
                               take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]"
                proof -
                  have "Arr (take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U])"
                    by (metis Con_imp_Arr_Resid Con_implies_Arr(1) Ide.simps(1) calculation
                        take_Nil)
                  thus ?thesis
                    by (metis 1 Arr.simps(1) length_Resid dual_order.eq_iff length_Cons
                              length_take min.absorb2 n old.nat.inject take_all)
                qed
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis by auto
            qed
            show "Trg ([hd U \\ v] \<^sup>*\\\<^sup>* V) =
                  Src ((take n (tl U) \<^sup>*\\\<^sup>* [v \\ hd U]) \<^sup>*\\\<^sup>* (V \<^sup>*\\\<^sup>* [hd U \\ v]))"
              by (metis 9 Ide.simps(1) Src_resid Trg_resid_sym)
          qed
          ultimately show ?thesis
            using ide_char by presburger
        qed
      qed
    qed

  end

  context lambda_calculus
  begin

    text \<open>
      Parallel reduction is a normalizing strategy.
    \<close>

    lemma parallel_strategy_is_normalizing:
    shows "normalizing_strategy parallel_strategy"
    proof -
      interpret \<Lambda>x: reduction_paths .
      (* TODO: Notation is not inherited here. *)
      have "\<And>a. normalizable a \<Longrightarrow> \<exists>n. NF (reduce parallel_strategy a n)"
      proof -
        fix a
        assume 1: "normalizable a"
        obtain U b where U: "\<Lambda>x.Arr U \<and> \<Lambda>x.Src U = a \<and> \<Lambda>x.Trg U = b \<and> NF b"
          using 1 normalizable_def \<Lambda>x.red_iff by blast
        have 2: "\<And>n. \<lbrakk>0 < n; n \<le> length U\<rbrakk>
                        \<Longrightarrow> \<Lambda>x.Ide (\<Lambda>x.Resid (take n U) (\<Lambda>x.apply_strategy parallel_strategy a n))"
          using U \<Lambda>x.parallel_strategy_is_universal \<Lambda>x.ide_char by blast
        let ?PR = "\<Lambda>x.apply_strategy parallel_strategy a (length U)"
        have "\<Lambda>x.Trg ?PR = b"
        proof -
          have 3: "\<Lambda>x.Ide (\<Lambda>x.Resid U ?PR)"
            using U 2 [of "length U"] by force
          have "\<Lambda>x.Trg (\<Lambda>x.Resid ?PR U) = b"
            by (metis "3" NF_reduct_is_trivial U \<Lambda>x.Con_imp_Arr_Resid \<Lambda>x.Con_sym \<Lambda>x.Ide.simps(1)
                \<Lambda>x.Src_resid reduction_paths.red_iff)
          thus ?thesis
            by (metis 3 \<Lambda>x.Con_Arr_self \<Lambda>x.Ide_implies_Arr \<Lambda>x.Resid_Arr_Ide_ind
                \<Lambda>x.Src_resid \<Lambda>x.Trg_resid_sym)
        qed
        hence "reduce parallel_strategy a (length U) = b"
          using 1 U
          by (metis \<Lambda>x.Arr.simps(1) length_greater_0_conv normalizable_def
              \<Lambda>x.apply_strategy_gives_path(4) parallel_strategy_is_reduction_strategy)
        thus "\<exists>n. NF (reduce parallel_strategy a n)"
          using U by blast
      qed
      thus ?thesis
        using normalizing_strategy_def by blast
    qed

    text \<open>
      An alternative characterization of a normal form is a term on which the parallel
      reduction strategy yields an identity.
    \<close>

    abbreviation has_redex
    where "has_redex t \<equiv> Arr t \<and> \<not> Ide (parallel_strategy t)"

    lemma NF_iff_has_no_redex:
    shows "Arr t \<Longrightarrow> NF t \<longleftrightarrow> \<not> has_redex t"
    proof (induct t)
      show "Arr \<^bold>\<sharp> \<Longrightarrow> NF \<^bold>\<sharp> \<longleftrightarrow> \<not> has_redex \<^bold>\<sharp>"
        using NF_def by simp
      show "\<And>x. Arr \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> NF \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<longleftrightarrow> \<not> has_redex \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        using NF_def by force
      show "\<And>t. \<lbrakk>Arr t \<Longrightarrow> NF t \<longleftrightarrow> \<not> has_redex t; Arr \<^bold>\<lambda>\<^bold>[t\<^bold>]\<rbrakk> \<Longrightarrow> NF \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> \<not> has_redex \<^bold>\<lambda>\<^bold>[t\<^bold>]"
      proof -
        fix t
        assume ind: "Arr t \<Longrightarrow> NF t \<longleftrightarrow> \<not> has_redex t"
        assume t: "Arr \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        show "NF \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> \<not> has_redex \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        proof
          show "NF \<^bold>\<lambda>\<^bold>[t\<^bold>] \<Longrightarrow> \<not> has_redex \<^bold>\<lambda>\<^bold>[t\<^bold>]"
            using t ind
            by (metis NF_def Arr.simps(3) Ide.simps(3) Src.simps(3) parallel_strategy.simps(2))
          show "\<not> has_redex \<^bold>\<lambda>\<^bold>[t\<^bold>] \<Longrightarrow> NF \<^bold>\<lambda>\<^bold>[t\<^bold>]"
            using t ind
            by (metis NF_def ide_backward_stable ide_char parallel_strategy_Src_eq
                subs_implies_prfx subs_parallel_strategy_Src)
        qed
      qed
      show "\<And>t1 t2. \<lbrakk>Arr t1 \<Longrightarrow> NF t1 \<longleftrightarrow> \<not> has_redex t1;
                     Arr t2 \<Longrightarrow> NF t2 \<longleftrightarrow> \<not> has_redex t2;
                     Arr (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)\<rbrakk>
                        \<Longrightarrow> NF (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \<longleftrightarrow> \<not> has_redex (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        using NF_def Ide.simps(5) parallel_strategy.simps(8) by presburger
      show "\<And>t1 t2. \<lbrakk>Arr t1 \<Longrightarrow> NF t1 \<longleftrightarrow> \<not> has_redex t1;
                     Arr t2 \<Longrightarrow> NF t2 \<longleftrightarrow> \<not> has_redex t2;
                     Arr (t1 \<^bold>\<circ> t2)\<rbrakk>
                        \<Longrightarrow> NF (t1 \<^bold>\<circ> t2) \<longleftrightarrow> \<not> has_redex (t1 \<^bold>\<circ> t2)"
      proof -
        fix t1 t2
        assume ind1: "Arr t1 \<Longrightarrow> NF t1 \<longleftrightarrow> \<not> has_redex t1"
        assume ind2: "Arr t2 \<Longrightarrow> NF t2 \<longleftrightarrow> \<not> has_redex t2"
        assume t: "Arr (t1 \<^bold>\<circ> t2)"
        show "NF (t1 \<^bold>\<circ> t2) \<longleftrightarrow> \<not> has_redex (t1 \<^bold>\<circ> t2)"
          using t ind1 ind2 NF_def
          apply (intro iffI)
           apply (metis Ide_iff_Src_self parallel_strategy_is_reduction_strategy
              reduction_strategy_def)
          apply (cases t1)
              apply simp_all
           apply (metis Ide_iff_Src_self ide_char parallel_strategy.simps(1,5)
              parallel_strategy_is_reduction_strategy reduction_strategy_def resid_Arr_Src
              subs_implies_prfx subs_parallel_strategy_Src)
          by (metis Ide_iff_Src_self ide_char ind1 Arr.simps(4) parallel_strategy.simps(6)
              parallel_strategy_is_reduction_strategy reduction_strategy_def resid_Arr_Src
              subs_implies_prfx subs_parallel_strategy_Src)
      qed
    qed

    lemma (in lambda_calculus) not_NF_elim:
    assumes "\<not> NF t" and "Ide t"
    obtains u where "coinitial t u \<and> \<not> Ide u"
      using assms NF_def by auto

    lemma (in lambda_calculus) NF_Lam_iff:
    shows "NF \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> NF t"
      using NF_def
      by (metis Ide_implies_Arr NF_iff_has_no_redex Ide.simps(3) parallel_strategy.simps(2))

    lemma (in lambda_calculus) NF_App_iff:
    shows "NF (t1 \<^bold>\<circ> t2) \<longleftrightarrow> \<not> is_Lam t1 \<and> NF t1 \<and> NF t2"
    proof -
      have "\<not> NF (t1 \<^bold>\<circ> t2) \<Longrightarrow> is_Lam t1 \<or> \<not> NF t1 \<or> \<not> NF t2"
        apply (cases "is_Lam t1")
         apply simp_all
        apply (cases t1)
            apply simp_all
        using NF_def Ide.simps(1) apply presburger
          apply (metis Ide_implies_Arr NF_def NF_iff_has_no_redex Ide.simps(4)
            parallel_strategy.simps(5))
        apply (metis Ide_implies_Arr NF_def NF_iff_has_no_redex Ide.simps(4)
            parallel_strategy.simps(6))
        using NF_def Ide.simps(5) by presburger
      moreover have "is_Lam t1 \<or> \<not> NF t1 \<or> \<not> NF t2 \<Longrightarrow> \<not> NF (t1 \<^bold>\<circ> t2)"
      proof -
        have "is_Lam t1 \<Longrightarrow> \<not>NF (t1 \<^bold>\<circ> t2)"
          by (metis Ide_implies_Arr NF_def NF_iff_has_no_redex Ide.simps(5) lambda.collapse(2)
              parallel_strategy.simps(3,8))
        moreover have "\<not> NF t1 \<Longrightarrow> \<not>NF (t1 \<^bold>\<circ> t2)"
          using NF_def Ide_iff_Src_self Ide_implies_Arr
          apply auto
          by (metis (full_types) Arr.simps(4) Ide.simps(4) Src.simps(4))
        moreover have "\<not> NF t2 \<Longrightarrow> \<not>NF (t1 \<^bold>\<circ> t2)"
          using NF_def Ide_iff_Src_self Ide_implies_Arr
          apply auto
          by (metis (full_types) Arr.simps(4) Ide.simps(4) Src.simps(4))
        ultimately show "is_Lam t1 \<or> \<not> NF t1 \<or> \<not> NF t2 \<Longrightarrow> \<not> NF (t1 \<^bold>\<circ> t2)"
          by auto
      qed
      ultimately show ?thesis by blast
    qed

    subsection "Head Reduction"

    text \<open>
      \emph{Head reduction} is the strategy that only contracts a redex at the ``head'' position,
      which is found at the end of the ``left spine'' of applications, and does nothing if there is
      no such redex.

      The following function applies to an arbitrary arrow \<open>t\<close>, and it marks the redex at
      the head position, if any, otherwise it yields \<open>Src t\<close>.
    \<close>

    fun head_strategy
    where "head_strategy \<^bold>\<guillemotleft>i\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>i\<^bold>\<guillemotright>"
        | "head_strategy \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[head_strategy t\<^bold>]"
        | "head_strategy (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) = \<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u"
        | "head_strategy (t \<^bold>\<circ> u) = head_strategy t \<^bold>\<circ> Src u"
        | "head_strategy (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = \<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u"
        | "head_strategy \<^bold>\<sharp> = \<^bold>\<sharp>"

    lemma Arr_head_strategy:
    shows "Arr t \<Longrightarrow> Arr (head_strategy t)"
      apply (induct t)
          apply auto
    proof -
      fix t u
      assume ind: "Arr (head_strategy t)"
      assume t: "Arr t" and u: "Arr u"
      show "Arr (head_strategy (t \<^bold>\<circ> u))"
        using t u ind
        by (cases t) auto
    qed

    lemma Src_head_strategy:
    shows "Arr t \<Longrightarrow> Src (head_strategy t) = Src t"
      apply (induct t)
          apply auto
    proof -
      fix t u
      assume ind: "Src (head_strategy t) = Src t"
      assume t: "Arr t" and u: "Arr u"
      have "Src (head_strategy (t \<^bold>\<circ> u)) = Src (head_strategy t \<^bold>\<circ> Src u)"
        using t ind
        by (cases t) auto
      also have "... = Src t \<^bold>\<circ> Src u"
        using t u ind by auto
      finally show "Src (head_strategy (t \<^bold>\<circ> u)) = Src t \<^bold>\<circ> Src u" by simp
    qed

    lemma Con_head_strategy:
    shows "Arr t \<Longrightarrow> Con t (head_strategy t)"
      apply (induct t)
          apply auto
       apply (simp add: Arr_head_strategy Src_head_strategy)
      using Arr_Subst Arr_not_Nil by auto

    lemma head_strategy_Src:
    shows "Arr t \<Longrightarrow> head_strategy (Src t) = head_strategy t"
      apply (induct t)
          apply auto
      using Arr.elims(2) by fastforce

    lemma head_strategy_is_elementary:
    shows "\<lbrakk>Arr t; \<not> Ide (head_strategy t)\<rbrakk> \<Longrightarrow> elementary_reduction (head_strategy t)"
      using Ide_Src
      apply (induct t)
          apply auto
    proof -
      fix t1 t2
      assume t1: "Arr t1" and t2: "Arr t2"
      assume t: "\<not> Ide (head_strategy (t1 \<^bold>\<circ> t2))"
      assume 1: "\<not> Ide (head_strategy t1) \<Longrightarrow> elementary_reduction (head_strategy t1)"
      assume 2: "\<not> Ide (head_strategy t2) \<Longrightarrow> elementary_reduction (head_strategy t2)"
      show "elementary_reduction (head_strategy (t1 \<^bold>\<circ> t2))"
        using t t1 t2 1 2 Ide_Src Ide_implies_Arr
        by (cases t1) auto
    qed

    lemma head_strategy_is_reduction_strategy:
    shows "reduction_strategy head_strategy"
    proof (unfold reduction_strategy_def, intro allI impI)
      fix t
      show "Ide t \<Longrightarrow> Coinitial (head_strategy t) t"
      proof (induct t)
        show "Ide \<^bold>\<sharp> \<Longrightarrow> Coinitial (head_strategy \<^bold>\<sharp>) \<^bold>\<sharp>"
          by simp
        show "\<And>x. Ide \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> Coinitial (head_strategy \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>) \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
          by simp
        show "\<And>t. \<lbrakk>Ide t \<Longrightarrow> Coinitial (head_strategy t) t; Ide \<^bold>\<lambda>\<^bold>[t\<^bold>]\<rbrakk>
                      \<Longrightarrow> Coinitial (head_strategy \<^bold>\<lambda>\<^bold>[t\<^bold>]) \<^bold>\<lambda>\<^bold>[t\<^bold>]"
          by simp
        fix t1 t2
          assume ind1: "Ide t1 \<Longrightarrow> Coinitial (head_strategy t1) t1"
        assume ind2: "Ide t2 \<Longrightarrow> Coinitial (head_strategy t2) t2"
        assume t: "Ide (t1 \<^bold>\<circ> t2)"
        show "Coinitial (head_strategy (t1 \<^bold>\<circ> t2)) (t1 \<^bold>\<circ> t2)"
          using t ind1 Ide_implies_Arr Ide_iff_Src_self
          by (cases t1) simp_all
        next
        fix t1 t2
        assume ind1: "Ide t1 \<Longrightarrow> Coinitial (head_strategy t1) t1"
        assume ind2: "Ide t2 \<Longrightarrow> Coinitial (head_strategy t2) t2"
        assume t: "Ide (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        show "Coinitial (head_strategy (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
          using t by auto
      qed
    qed

    text \<open>
      The following function tests whether a term is an elementary reduction of the head redex.
    \<close>

    fun is_head_reduction
    where "is_head_reduction \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> \<longleftrightarrow> False"
        | "is_head_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> is_head_reduction t"
        | "is_head_reduction (\<^bold>\<lambda>\<^bold>[_\<^bold>] \<^bold>\<circ> _) \<longleftrightarrow> False"
        | "is_head_reduction (t \<^bold>\<circ> u) \<longleftrightarrow> is_head_reduction t \<and> Ide u"
        | "is_head_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<longleftrightarrow> Ide t \<and> Ide u"
        | "is_head_reduction \<^bold>\<sharp> \<longleftrightarrow> False"

    lemma is_head_reduction_char:
    shows "is_head_reduction t \<longleftrightarrow> elementary_reduction t \<and> head_strategy (Src t) = t"
      apply (induct t)
          apply simp_all
    proof -
      fix t1 t2
      assume ind: "is_head_reduction t1 \<longleftrightarrow>
                   elementary_reduction t1 \<and> head_strategy (Src t1) = t1"
      show "is_head_reduction (t1 \<^bold>\<circ> t2) \<longleftrightarrow>
             (elementary_reduction t1 \<and> Ide t2 \<or> Ide t1 \<and> elementary_reduction t2) \<and>
              head_strategy (Src t1 \<^bold>\<circ> Src t2) = t1 \<^bold>\<circ> t2"
        using ind Ide_implies_Arr Ide_iff_Src_self Ide_Src elementary_reduction_not_ide
              ide_char
        apply (cases t1)
            apply simp_all
          apply (metis Ide_Src arr_char elementary_reduction_is_arr)
         apply (metis Ide_Src arr_char elementary_reduction_is_arr)
        by metis
      next
      fix t1 t2
      show "Ide t1 \<and> Ide t2 \<longleftrightarrow> Ide t1 \<and> Ide t2 \<and> Src (Src t1) = t1 \<and> Src (Src t2) = t2"
        by (metis Ide_iff_Src_self Ide_implies_Arr)
    qed

    lemma is_head_reductionI:
    assumes "Arr t" and "elementary_reduction t" and "head_strategy (Src t) = t"
    shows "is_head_reduction t"
      using assms is_head_reduction_char by blast

    text \<open>
      The following function tests whether a redex in the head position of a term is marked.
    \<close>

    fun contains_head_reduction
    where "contains_head_reduction \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> \<longleftrightarrow> False"
        | "contains_head_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> contains_head_reduction t"
        | "contains_head_reduction (\<^bold>\<lambda>\<^bold>[_\<^bold>] \<^bold>\<circ> _) \<longleftrightarrow> False"
        | "contains_head_reduction (t \<^bold>\<circ> u) \<longleftrightarrow> contains_head_reduction t \<and> Arr u"
        | "contains_head_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<longleftrightarrow> Arr t \<and> Arr u"
        | "contains_head_reduction \<^bold>\<sharp> \<longleftrightarrow> False"

    lemma is_head_reduction_imp_contains_head_reduction:
    shows "is_head_reduction t \<Longrightarrow> contains_head_reduction t"
      using Ide_implies_Arr
      apply (induct t)
          apply auto
    proof -
      fix t1 t2
      assume ind1: "is_head_reduction t1 \<Longrightarrow> contains_head_reduction t1"
      assume ind2: "is_head_reduction t2 \<Longrightarrow> contains_head_reduction t2"
      assume t: "is_head_reduction (t1 \<^bold>\<circ> t2)"
      show "contains_head_reduction (t1 \<^bold>\<circ> t2)"
        using t ind1 ind2 Ide_implies_Arr
        by (cases t1) auto
    qed

    text \<open>
      An \emph{internal reduction} is one that does not contract any redex at the head position.
    \<close>

    fun is_internal_reduction
    where "is_internal_reduction \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> \<longleftrightarrow> True"
        | "is_internal_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longleftrightarrow> is_internal_reduction t"
        | "is_internal_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) \<longleftrightarrow> Arr t \<and> Arr u"
        | "is_internal_reduction (t \<^bold>\<circ> u) \<longleftrightarrow> is_internal_reduction t \<and> Arr u"
        | "is_internal_reduction (\<^bold>\<lambda>\<^bold>[_\<^bold>] \<^bold>\<Zspot> _) \<longleftrightarrow> False"
        | "is_internal_reduction \<^bold>\<sharp> \<longleftrightarrow> False"

    lemma is_internal_reduction_iff:
    shows "is_internal_reduction t \<longleftrightarrow> Arr t \<and> \<not> contains_head_reduction t"
      apply (induct t)
          apply simp_all
    proof -
      fix t1 t2
      assume ind1: "is_internal_reduction t1 \<longleftrightarrow> Arr t1 \<and> \<not> contains_head_reduction t1"
      assume ind2: "is_internal_reduction t2 \<longleftrightarrow> Arr t2 \<and> \<not> contains_head_reduction t2"
      show "is_internal_reduction (t1 \<^bold>\<circ> t2) \<longleftrightarrow>
            Arr t1 \<and> Arr t2 \<and> \<not> contains_head_reduction (t1 \<^bold>\<circ> t2)"
        using ind1 ind2
        apply (cases t1)
            apply simp_all
        by blast
    qed

    text \<open>
      Head reduction steps are either \<open>\<lesssim>\<close>-prefixes of, or are preserved by, residuation along
      arbitrary reductions.
    \<close>

    lemma is_head_reduction_resid:
    shows "\<lbrakk>is_head_reduction t; Arr u; Src t = Src u\<rbrakk> \<Longrightarrow> t \<lesssim> u \<or> is_head_reduction (t \\ u)"
    proof (induct t arbitrary: u)
      show "\<And>u. \<lbrakk>is_head_reduction \<^bold>\<sharp>; Arr u; Src \<^bold>\<sharp> = Src u\<rbrakk>
                   \<Longrightarrow> \<^bold>\<sharp> \<lesssim> u \<or> is_head_reduction (\<^bold>\<sharp> \\ u)"
        by auto
      show "\<And>x u. \<lbrakk>is_head_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>; Arr u; Src \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = Src u\<rbrakk>
                     \<Longrightarrow> \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<lesssim> u \<or> is_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \\ u)"
        by auto
      fix t u
      assume ind: "\<And>u. \<lbrakk>is_head_reduction t; Arr u; Src t = Src u\<rbrakk>
                          \<Longrightarrow> t \<lesssim> u \<or> is_head_reduction (t \\ u)"
      assume t: "is_head_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>]"
      assume u: "Arr u"
      assume tu: "Src \<^bold>\<lambda>\<^bold>[t\<^bold>] = Src u"
      have 1: "Arr t"
        by (metis Arr_head_strategy head_strategy_Src is_head_reduction_char Arr.simps(3) t tu u)
      show " \<^bold>\<lambda>\<^bold>[t\<^bold>] \<lesssim> u \<or> is_head_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u)"
        using t u tu 1 ind
        by (cases u) auto
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. \<lbrakk>is_head_reduction t1; Arr u1; Src t1 = Src u1\<rbrakk>
                           \<Longrightarrow> t1 \<lesssim> u1 \<or> is_head_reduction (t1 \\ u1)"
      assume ind2: "\<And>u2. \<lbrakk>is_head_reduction t2; Arr u2; Src t2 = Src u2\<rbrakk>
                           \<Longrightarrow> t2 \<lesssim> u2 \<or> is_head_reduction (t2 \\ u2)"
      assume t: "is_head_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      assume u: "Arr u"
      assume tu: "Src (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) = Src u"
      show "\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 \<lesssim> u \<or> is_head_reduction ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u)"
        using t u tu ind1 ind2 Coinitial_iff_Con Ide_implies_Arr ide_char resid_Ide_Arr Ide_Subst
        by (cases u; cases "un_App1 u") auto
      next
      fix t1 t2 u
      assume ind1: "\<And>u1. \<lbrakk>is_head_reduction t1; Arr u1; Src t1 = Src u1\<rbrakk>
                           \<Longrightarrow> t1 \<lesssim> u1 \<or> is_head_reduction (t1 \\ u1)"
      assume ind2: "\<And>u2. \<lbrakk>is_head_reduction t2; Arr u2; Src t2 = Src u2\<rbrakk>
                           \<Longrightarrow> t2 \<lesssim> u2 \<or> is_head_reduction (t2 \\ u2)"
      assume t: "is_head_reduction (t1 \<^bold>\<circ> t2)"
      assume u: "Arr u"
      assume tu: "Src (t1 \<^bold>\<circ> t2) = Src u"
      have "Arr (t1 \<^bold>\<circ> t2)"
        using is_head_reduction_char elementary_reduction_is_arr t by blast
      hence t1: "Arr t1" and t2: "Arr t2"
        by auto
      have 0: "\<not> is_Lam t1"
        using t is_Lam_def by fastforce
      have 1: "is_head_reduction t1"
        using t t1 by force
      show "t1 \<^bold>\<circ> t2 \<lesssim> u \<or> is_head_reduction ((t1 \<^bold>\<circ> t2) \\ u) "
      proof -
        have "\<not> Ide ((t1 \<^bold>\<circ> t2) \\ u) \<Longrightarrow> is_head_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
        proof (intro is_head_reductionI)
          assume 2: "\<not> Ide ((t1 \<^bold>\<circ> t2) \\ u)"
          have 3: "is_App u \<Longrightarrow> \<not> Ide (t1 \\ un_App1 u) \<or> \<not> Ide (t2 \\ un_App2 u)"
            by (metis "2" ide_char lambda.collapse(3) lambda.discI(3) lambda.sel(3-4) prfx_App_iff)
          have 4: "is_Beta u \<Longrightarrow> \<not> Ide (t1 \\ un_Beta1 u) \<or> \<not> Ide (t2 \\ un_Beta2 u)"
            using u tu 2
            by (metis "0" ConI Con_implies_is_Lam_iff_is_Lam \<open>Arr (t1 \<^bold>\<circ> t2)\<close>
                ConD(4) lambda.collapse(4) lambda.disc(8))
          show 5: "Arr ((t1 \<^bold>\<circ> t2) \\ u)"
            using Arr_resid \<open>Arr (t1 \<^bold>\<circ> t2)\<close> tu u by auto
          show "head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
          proof (cases u)
            show "u = \<^bold>\<sharp> \<Longrightarrow> head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
              by simp
            show "\<And>x. u = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
              by auto
            show "\<And>v. u = \<^bold>\<lambda>\<^bold>[v\<^bold>] \<Longrightarrow> head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
              by simp
            show "\<And>u1 u2. u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2 \<Longrightarrow> head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
              by (metis "0" "5" Arr_not_Nil ConD(4) Con_implies_is_Lam_iff_is_Lam lambda.disc(8))
            show "\<And>u1 u2. u = App u1 u2 \<Longrightarrow> head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
            proof -
              fix u1 u2
              assume u1u2: "u = u1 \<^bold>\<circ> u2"
              have "head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) =
                    head_strategy (Src (t1 \\ u1) \<^bold>\<circ> Src (t2 \\ u2))"
                using u u1u2 tu t1 t2 Coinitial_iff_Con by auto
              also have "... = head_strategy (Trg u1 \<^bold>\<circ> Trg u2)"
                using 5 u1u2 Src_resid
                by (metis Arr_not_Nil ConD(1))
              also have "... = (t1 \<^bold>\<circ> t2) \\ u"
              proof (cases "Trg u1")
                show "Trg u1 = \<^bold>\<sharp> \<Longrightarrow> head_strategy (Trg u1 \<^bold>\<circ> Trg u2) = (t1 \<^bold>\<circ> t2) \\ u"
                  using Arr_not_Nil u u1u2 by force
                show "\<And>x. Trg u1 = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> head_strategy (Trg u1 \<^bold>\<circ> Trg u2) = (t1 \<^bold>\<circ> t2) \\ u"
                  using tu t u t1 t2 u1u2 Arr_not_Nil Ide_iff_Src_self
                  by (cases u1; cases t1) auto
                show "\<And>v. Trg u1 = \<^bold>\<lambda>\<^bold>[v\<^bold>] \<Longrightarrow> head_strategy (Trg u1 \<^bold>\<circ> Trg u2) = (t1 \<^bold>\<circ> t2) \\ u"
                  using tu t u t1 t2 u1u2 Arr_not_Nil Ide_iff_Src_self
                  apply (cases u1; cases t1)
                                      apply auto
                  by (metis 2 5 Src_resid Trg.simps(3-4) resid.simps(3-4) resid_Src_Arr)
                show "\<And>u11 u12. Trg u1 = u11 \<^bold>\<circ> u12
                                   \<Longrightarrow> head_strategy (Trg u1 \<^bold>\<circ> Trg u2) = (t1 \<^bold>\<circ> t2) \\ u"
                proof -
                  fix u11 u12
                  assume u1: "Trg u1 = u11 \<^bold>\<circ> u12"
                  show "head_strategy (Trg u1 \<^bold>\<circ> Trg u2) = (t1 \<^bold>\<circ> t2) \\ u"
                  proof (cases "Trg u1")
                    show "Trg u1 = \<^bold>\<sharp> \<Longrightarrow> ?thesis"
                      using u1 by simp
                    show "\<And>x. Trg u1 = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> ?thesis"
                      apply simp
                      using u1 by force
                    show "\<And>v. Trg u1 = \<^bold>\<lambda>\<^bold>[v\<^bold>] \<Longrightarrow> ?thesis"
                      using u1 by simp
                    show "\<And>u11 u12. Trg u1 = u11 \<^bold>\<circ> u12 \<Longrightarrow> ?thesis"
                      using t u tu u1u2 1 2 ind1 elementary_reduction_not_ide
                            is_head_reduction_char Src_resid Ide_iff_Src_self
                            \<open>Arr (t1 \<^bold>\<circ> t2)\<close> Coinitial_iff_Con
                      by fastforce
                    show "\<And>u11 u12. Trg u1 = \<^bold>\<lambda>\<^bold>[u11\<^bold>] \<^bold>\<Zspot> u12 \<Longrightarrow> ?thesis"
                      using u1 by simp
                  qed
                qed
                show "\<And>u11 u12. Trg u1 = \<^bold>\<lambda>\<^bold>[u11\<^bold>] \<^bold>\<Zspot> u12 \<Longrightarrow> ?thesis"
                  using u1u2 u Ide_Trg by fastforce
              qed
              finally show "head_strategy (Src ((t1 \<^bold>\<circ> t2) \\ u)) = (t1 \<^bold>\<circ> t2) \\ u"
                by simp
            qed
          qed
          thus "elementary_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
            by (metis 2 5 Ide_Src Ide_implies_Arr head_strategy_is_elementary)
        qed
        thus ?thesis by blast
      qed
    qed

    text \<open>
       Internal reductions are closed under residuation.
    \<close>

    lemma is_internal_reduction_resid:
    shows "\<lbrakk>is_internal_reduction t; is_internal_reduction u; Src t = Src u\<rbrakk>
              \<Longrightarrow> is_internal_reduction (t \\ u)"
      apply (induct t arbitrary: u)
          apply auto
      apply (metis Con_implies_Arr2 con_char weak_extensionality Arr.simps(2) Src.simps(2)
                   parallel_strategy.simps(1) prfx_implies_con resid_Arr_Src subs_Ide
                   subs_implies_prfx subs_parallel_strategy_Src)
    proof -
      fix t u
      assume ind: "\<And>u. \<lbrakk>is_internal_reduction u; Src t = Src u\<rbrakk> \<Longrightarrow> is_internal_reduction (t \\ u)"
      assume t: "is_internal_reduction t"
      assume u: "is_internal_reduction u"
      assume tu: "\<^bold>\<lambda>\<^bold>[Src t\<^bold>] = Src u"
      show "is_internal_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u)"
        using t u tu ind
        apply (cases u)
        by auto fastforce
      next
      fix t1 t2 u
      assume ind1: "\<And>u. \<lbrakk>is_internal_reduction t1; is_internal_reduction u; Src t1 = Src u\<rbrakk>
                            \<Longrightarrow> is_internal_reduction (t1 \\ u)"
      assume t: "is_internal_reduction (t1 \<^bold>\<circ> t2)"
      assume u: "is_internal_reduction u"
      assume tu: "Src t1 \<^bold>\<circ> Src t2 = Src u"
      show "is_internal_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
        using t u tu ind1 Coinitial_resid_resid Coinitial_iff_Con Arr_Src
              is_internal_reduction_iff
        apply auto
         apply (metis Arr.simps(4) Src.simps(4))
      proof -
        assume t1: "Arr t1" and t2: "Arr t2" and u: "Arr u"
        assume tu: "Src t1 \<^bold>\<circ> Src t2 = Src u"
        assume 1: "\<not> contains_head_reduction u"
        assume 2: "\<not> contains_head_reduction (t1 \<^bold>\<circ> t2)"
        assume 3: "contains_head_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
        show False
          using t1 t2 u tu 1 2 3 is_internal_reduction_iff
          apply (cases u)
              apply simp_all
          apply (cases t1; cases "un_App1 u")
                              apply simp_all
          by (metis Coinitial_iff_Con ind1 Arr.simps(4) Src.simps(4) resid.simps(3))
      qed
    qed

    text \<open>
      A head reduction is preserved by residuation along an internal reduction,
      so a head reduction can only be canceled by a transition that contains a head reduction.
    \<close>

    lemma is_head_reduction_resid':
    shows "\<lbrakk>is_head_reduction t; is_internal_reduction u; Src t = Src u\<rbrakk>
               \<Longrightarrow> is_head_reduction (t \\ u)"
    proof (induct t arbitrary: u)
      show "\<And>u. \<lbrakk>is_head_reduction \<^bold>\<sharp>; is_internal_reduction u; Src \<^bold>\<sharp> = Src u\<rbrakk>
                   \<Longrightarrow> is_head_reduction (\<^bold>\<sharp> \\ u)"
        by simp
      show "\<And>x u. \<lbrakk>is_head_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>; is_internal_reduction u; Src \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = Src u\<rbrakk>
                     \<Longrightarrow> is_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \\ u)"
        by simp
      show "\<And>t. \<lbrakk>\<And>u. \<lbrakk>is_head_reduction t; is_internal_reduction u; Src t = Src u\<rbrakk>
                         \<Longrightarrow> is_head_reduction (t \\ u);
                       is_head_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>]; is_internal_reduction u; Src \<^bold>\<lambda>\<^bold>[t\<^bold>] = Src u\<rbrakk>
                    \<Longrightarrow> is_head_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u)"
        for u
        by (cases u, simp_all) fastforce
      fix t1 t2 u
      assume ind1: "\<And>u. \<lbrakk>is_head_reduction t1; is_internal_reduction u; Src t1 = Src u\<rbrakk>
                            \<Longrightarrow> is_head_reduction (t1 \\ u)"
      assume t: "is_head_reduction (t1 \<^bold>\<circ> t2)"
      assume u: "is_internal_reduction u"
      assume tu: "Src (t1 \<^bold>\<circ> t2) = Src u"
      show "is_head_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
        using t u tu ind1
        apply (cases u)
           apply simp_all
      proof (intro conjI impI)
        fix u1 u2
        assume u1u2: "u = u1 \<^bold>\<circ> u2"
        show 1: "Con t1 u1"
          using Coinitial_iff_Con tu u1u2 ide_char
          by (metis ConD(1) Ide.simps(1) is_head_reduction.simps(9) is_head_reduction_resid
              is_internal_reduction.simps(9) is_internal_reduction_resid t u)
        show "Con t2 u2"
          using Coinitial_iff_Con tu u1u2 ide_char
          by (metis ConD(1) Ide.simps(1) is_head_reduction.simps(9) is_head_reduction_resid
              is_internal_reduction.simps(9) is_internal_reduction_resid t u)
        show "is_head_reduction (t1 \\ u1 \<^bold>\<circ> t2 \\ u2)"
          using t u u1u2 1 Coinitial_iff_Con \<open>Con t2 u2\<close> ide_char ind1 resid_Ide_Arr
          apply (cases t1; simp_all; cases u1; simp_all; cases "un_App1 u1")
                   apply auto
          by (metis 1 ind1 is_internal_reduction.simps(6) resid.simps(3))
      qed
      next
      fix t1 t2 u
      assume ind1: "\<And>u. \<lbrakk>is_head_reduction t1; is_internal_reduction u; Src t1 = Src u\<rbrakk>
                            \<Longrightarrow> is_head_reduction (t1 \\ u)"
      assume t: "is_head_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
      assume u: "is_internal_reduction u"
      assume tu: "Src (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) = Src u"
      show "is_head_reduction ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u)"
        using t u tu ind1
        apply (cases u)
            apply simp_all
        by (metis Con_implies_Arr1 is_head_reduction_resid is_internal_reduction.simps(9)
            is_internal_reduction_resid lambda.disc(15) prfx_App_iff t tu)
    qed

    text \<open>
      The following function differs from \<open>head_strategy\<close> in that it only selects an already-marked
      redex, whereas \<open>head_strategy\<close> marks the redex at the head position.
    \<close>

    fun head_redex
    where "head_redex \<^bold>\<sharp> = \<^bold>\<sharp>"
        | "head_redex \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        | "head_redex \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[head_redex t\<^bold>]"
        | "head_redex (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) = \<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<circ> Src u"
        | "head_redex (t \<^bold>\<circ> u) = head_redex t \<^bold>\<circ> Src u"
        | "head_redex (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = (\<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u)"

    lemma elementary_reduction_head_redex:
    shows "\<lbrakk>Arr t; \<not> Ide (head_redex t)\<rbrakk> \<Longrightarrow> elementary_reduction (head_redex t)"
      using Ide_Src
      apply (induct t)
          apply auto
    proof -
      show "\<And>t2. \<lbrakk>\<not> Ide (head_redex t1) \<Longrightarrow> elementary_reduction (head_redex t1);
                  \<not> Ide (head_redex (t1 \<^bold>\<circ> t2));
                  \<And>t. Arr t \<Longrightarrow> Ide (Src t); Arr t1; Arr t2\<rbrakk>
                     \<Longrightarrow> elementary_reduction (head_redex (t1 \<^bold>\<circ> t2))"
        for t1
        using Ide_Src
        by (cases t1) auto
    qed

    lemma subs_head_redex:
    shows "Arr t \<Longrightarrow> head_redex t \<sqsubseteq> t"
      using Ide_Src subs_Ide
      apply (induct t)
          apply simp_all
    proof -
      show "\<And>t2. \<lbrakk>head_redex t1 \<sqsubseteq> t1; head_redex t2 \<sqsubseteq> t2;
                  Arr t1 \<and> Arr t2; \<And>t. Arr t \<Longrightarrow> Ide (Src t);
                  \<And>u t. \<lbrakk>Ide u; Src t = Src u\<rbrakk> \<Longrightarrow> u \<sqsubseteq> t\<rbrakk>
                    \<Longrightarrow> head_redex (t1 \<^bold>\<circ> t2) \<sqsubseteq> t1 \<^bold>\<circ> t2"
        for t1
        using Ide_Src subs_Ide
        by (cases t1) auto
    qed

    lemma contains_head_reduction_iff:
    shows "contains_head_reduction t \<longleftrightarrow> Arr t \<and> \<not> Ide (head_redex t)"
      apply (induct t)
          apply simp_all
    proof -
      show "\<And>t2. contains_head_reduction t1 = (Arr t1 \<and> \<not> Ide (head_redex t1))
                    \<Longrightarrow> contains_head_reduction (t1 \<^bold>\<circ> t2) =
                        (Arr t1 \<and> Arr t2 \<and> \<not> Ide (head_redex (t1 \<^bold>\<circ> t2)))"
        for t1
        using Ide_Src
        by (cases t1) auto
    qed

    lemma head_redex_is_head_reduction:
    shows "\<lbrakk>Arr t; contains_head_reduction t\<rbrakk> \<Longrightarrow> is_head_reduction (head_redex t)"
      using Ide_Src
      apply (induct t)
          apply simp_all
    proof -
      show "\<And>t2. \<lbrakk>contains_head_reduction t1 \<Longrightarrow> is_head_reduction (head_redex t1);
                  Arr t1 \<and> Arr t2;
                  contains_head_reduction (t1 \<^bold>\<circ> t2); \<And>t. Arr t \<Longrightarrow> Ide (Src t)\<rbrakk>
                    \<Longrightarrow> is_head_reduction (head_redex (t1 \<^bold>\<circ> t2))"
        for t1
        using Ide_Src contains_head_reduction_iff subs_implies_prfx
        by (cases t1) auto
    qed

    lemma Arr_head_redex:
    assumes "Arr t"
    shows "Arr (head_redex t)"
      using assms Ide_implies_Arr elementary_reduction_head_redex elementary_reduction_is_arr
      by blast

    lemma Src_head_redex:
    assumes "Arr t"
    shows "Src (head_redex t) = Src t"
      using assms
      by (metis Coinitial_iff_Con Ide.simps(1) ide_char subs_head_redex subs_implies_prfx)

    lemma Con_Arr_head_redex:
    assumes "Arr t"
    shows "Con t (head_redex t)"
      using assms
      by (metis Con_sym Ide.simps(1) ide_char subs_head_redex subs_implies_prfx)

    lemma is_head_reduction_if:
    shows "\<lbrakk>contains_head_reduction u; elementary_reduction u\<rbrakk> \<Longrightarrow> is_head_reduction u"
      apply (induct u)
          apply auto
      using contains_head_reduction.elims(2)
       apply fastforce
    proof -
      fix u1 u2
      assume u1: "Ide u1"
      assume u2: "elementary_reduction u2"
      assume 1: "contains_head_reduction (u1 \<^bold>\<circ> u2)"
      have False
        using u1 u2 1
        apply (cases u1)
            apply auto
        by (metis Arr_head_redex Ide_iff_Src_self Src_head_redex contains_head_reduction_iff
            ide_char resid_Arr_Src subs_head_redex subs_implies_prfx u1)
      thus "is_head_reduction (u1 \<^bold>\<circ> u2)"
        by blast
    qed

    lemma (in reduction_paths) head_redex_decomp:
    assumes "\<Lambda>.Arr t"
    shows "[\<Lambda>.head_redex t] @ [t \\ \<Lambda>.head_redex t] \<^sup>*\<sim>\<^sup>* [t]"
      using assms prfx_decomp \<Lambda>.subs_head_redex \<Lambda>.subs_implies_prfx
      by (metis Ide.simps(2) Resid.simps(3) \<Lambda>.prfx_implies_con ide_char)

    text \<open>
      An internal reduction cannot create a new head redex.
    \<close>

    lemma internal_reduction_preserves_no_head_redex:
    shows "\<lbrakk>is_internal_reduction u; Ide (head_strategy (Src u))\<rbrakk>
              \<Longrightarrow> Ide (head_strategy (Trg u))"
      apply (induct u)
          apply simp_all
    proof -
      fix u1 u2
      assume ind1: "\<lbrakk>is_internal_reduction u1; Ide (head_strategy (Src u1))\<rbrakk>
                       \<Longrightarrow> Ide (head_strategy (Trg u1))"
      assume ind2: "\<lbrakk>is_internal_reduction u2; Ide (head_strategy (Src u2))\<rbrakk>
                       \<Longrightarrow> Ide (head_strategy (Trg u2))"
      assume u: "is_internal_reduction (u1 \<^bold>\<circ> u2)"
      assume 1: "Ide (head_strategy (Src u1 \<^bold>\<circ> Src u2))"
      show "Ide (head_strategy (Trg u1 \<^bold>\<circ> Trg u2))"
        using u 1 ind1 ind2 Ide_Src Ide_Trg Ide_implies_Arr
        by (cases u1) auto
    qed

    lemma head_reduction_unique:
    shows "\<lbrakk>is_head_reduction t; is_head_reduction u; coinitial t u\<rbrakk> \<Longrightarrow> t = u"
      by (metis Coinitial_iff_Con con_def confluence is_head_reduction_char null_char)

    text \<open>
      Residuation along internal reductions preserves head reductions.
    \<close>

    lemma resid_head_strategy_internal:
    shows "is_internal_reduction u \<Longrightarrow> head_strategy (Src u) \\ u = head_strategy (Trg u)"
      using internal_reduction_preserves_no_head_redex Arr_head_strategy Ide_iff_Src_self
          Src_head_strategy Src_resid head_strategy_is_elementary is_head_reduction_char
          is_head_reduction_resid' is_internal_reduction_iff
      apply (cases u)
          apply simp_all
        apply (metis head_strategy_Src resid_Src_Arr)
       apply (metis head_strategy_Src Arr.simps(4) Src.simps(4) Trg.simps(3) resid_Src_Arr)
      by blast

    text \<open>
      An internal reduction followed by a head reduction can be expressed
      as a join of the internal reduction with a head reduction.
    \<close>

    lemma resid_head_strategy_Src:
    assumes "is_internal_reduction t" and "is_head_reduction u"
    and "seq t u"
    shows "head_strategy (Src t) \\ t = u"
    and "composite_of t u (Join (head_strategy (Src t)) t)"
    proof -
      show 1: "head_strategy (Src t) \\ t = u"
        using assms internal_reduction_preserves_no_head_redex resid_head_strategy_internal
              elementary_reduction_not_ide ide_char is_head_reduction_char seq_char
        by force
      show "composite_of t u (Join (head_strategy (Src t)) t)"
        using assms(3) 1 Arr_head_strategy Src_head_strategy join_of_Join join_of_def seq_char
        by force
    qed

    lemma App_Var_contains_no_head_reduction:
    shows "\<not> contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> u)"
      by simp

    lemma hgt_resid_App_head_redex:
    assumes "Arr (t \<^bold>\<circ> u)" and "\<not> Ide (head_redex (t \<^bold>\<circ> u))"
    shows "hgt ((t \<^bold>\<circ> u) \\ head_redex (t \<^bold>\<circ> u)) < hgt (t \<^bold>\<circ> u)"
      using assms contains_head_reduction_iff elementary_reduction_decreases_hgt
            elementary_reduction_head_redex subs_head_redex
      by blast

    subsection "Leftmost Reduction"

    text \<open>
      Leftmost (or normal-order) reduction is the strategy that produces an elementary
      reduction path by contracting the leftmost redex at each step.  It agrees with
      head reduction as long as there is a head redex, otherwise it continues on with the next
      subterm to the right.
    \<close>

    fun leftmost_strategy
    where "leftmost_strategy \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        | "leftmost_strategy \<^bold>\<lambda>\<^bold>[t\<^bold>] = \<^bold>\<lambda>\<^bold>[leftmost_strategy t\<^bold>]"
        | "leftmost_strategy (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) = \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u"
        | "leftmost_strategy (t \<^bold>\<circ> u) =
             (if \<not> Ide (leftmost_strategy t)
              then leftmost_strategy t \<^bold>\<circ> u
              else t \<^bold>\<circ> leftmost_strategy u)"
        | "leftmost_strategy (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u"
        | "leftmost_strategy \<^bold>\<sharp> = \<^bold>\<sharp>"

    (* TODO: Consider if is_head_reduction should be done this way. *)
    definition is_leftmost_reduction
    where "is_leftmost_reduction t \<longleftrightarrow> elementary_reduction t \<and> leftmost_strategy (Src t) = t"

    lemma leftmost_strategy_is_reduction_strategy:
    shows "reduction_strategy leftmost_strategy"
    proof (unfold reduction_strategy_def, intro allI impI)
      fix t
      show "Ide t \<Longrightarrow> Coinitial (leftmost_strategy t) t"
      proof (induct t, auto)
        show "\<And>t2. \<lbrakk>Arr (leftmost_strategy t1); Arr (leftmost_strategy t2);
                    Ide t1; Ide t2;
                    Arr t1; Src (leftmost_strategy t1) = Src t1;
                    Arr t2; Src (leftmost_strategy t2) = Src t2\<rbrakk>
                      \<Longrightarrow> Arr (leftmost_strategy (t1 \<^bold>\<circ> t2))"
              for t1
          by (cases t1) auto
      qed
    qed

    lemma elementary_reduction_leftmost_strategy:
    shows "Ide t \<Longrightarrow> elementary_reduction (leftmost_strategy t) \<or> Ide (leftmost_strategy t)"
      apply (induct t)
          apply simp_all
    proof -
      fix t1 t2
      show "\<lbrakk>elementary_reduction (leftmost_strategy t1) \<or> Ide (leftmost_strategy t1);
             elementary_reduction (leftmost_strategy t2) \<or> Ide (leftmost_strategy t2);
             Ide t1 \<and> Ide t2\<rbrakk>
                \<Longrightarrow> elementary_reduction (leftmost_strategy (t1 \<^bold>\<circ> t2)) \<or>
                    Ide (leftmost_strategy (t1 \<^bold>\<circ> t2))"
        by (cases t1) auto
    qed

    lemma (in lambda_calculus) leftmost_strategy_selects_head_reduction:
    shows "is_head_reduction t \<Longrightarrow> t = leftmost_strategy (Src t)"
    proof (induct t)
      show "\<And>t1 t2. \<lbrakk>is_head_reduction t1 \<Longrightarrow> t1 = leftmost_strategy (Src t1);
                     is_head_reduction (t1 \<^bold>\<circ> t2)\<rbrakk>
                       \<Longrightarrow> t1 \<^bold>\<circ> t2 = leftmost_strategy (Src (t1 \<^bold>\<circ> t2))"
      proof -
        fix t1 t2
        assume ind1: "is_head_reduction t1 \<Longrightarrow> t1 = leftmost_strategy (Src t1)"
        assume t: "is_head_reduction (t1 \<^bold>\<circ> t2)"
        show "t1 \<^bold>\<circ> t2 = leftmost_strategy (Src (t1 \<^bold>\<circ> t2))"
          using t ind1
          apply (cases t1)
              apply simp_all
           apply (cases "Src t1")
               apply simp_all
          using ind1
               apply force
          using ind1
              apply force
          using ind1
             apply force
            apply (metis Ide_iff_Src_self Ide_implies_Arr elementary_reduction_not_ide
              ide_char ind1 is_head_reduction_char)
          using ind1
           apply force
          by (metis Ide_iff_Src_self Ide_implies_Arr)
      qed
      show "\<And>t1 t2. \<lbrakk>is_head_reduction t1 \<Longrightarrow> t1 = leftmost_strategy (Src t1);
                     is_head_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)\<rbrakk>
                       \<Longrightarrow> \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2 = leftmost_strategy (Src (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2))"
        by (metis Ide_iff_Src_self Ide_implies_Arr Src.simps(5)
            is_head_reduction.simps(8) leftmost_strategy.simps(3))
    qed auto

    lemma has_redex_iff_not_Ide_leftmost_strategy:
    shows "Arr t \<Longrightarrow> has_redex t \<longleftrightarrow> \<not> Ide (leftmost_strategy (Src t))"
      apply (induct t)
          apply simp_all
    proof -
      fix t1 t2
      assume ind1: "Ide (parallel_strategy t1) \<longleftrightarrow> Ide (leftmost_strategy (Src t1))"
      assume ind2: "Ide (parallel_strategy t2) \<longleftrightarrow> Ide (leftmost_strategy (Src t2))"
      assume t: "Arr t1 \<and> Arr t2"
      show "Ide (parallel_strategy (t1 \<^bold>\<circ> t2)) \<longleftrightarrow>
            Ide (leftmost_strategy (Src t1 \<^bold>\<circ> Src t2))"
        using t ind1 ind2 Ide_Src Ide_iff_Src_self
        by (cases t1) auto
    qed

    lemma leftmost_reduction_preservation:
    shows "\<lbrakk>is_leftmost_reduction t; elementary_reduction u; \<not> is_leftmost_reduction u;
            coinitial t u\<rbrakk> \<Longrightarrow> is_leftmost_reduction (t \\ u)"
    proof (induct t arbitrary: u)
      show "\<And>u. coinitial \<^bold>\<sharp> u \<Longrightarrow> is_leftmost_reduction (\<^bold>\<sharp> \\ u)"
        by simp
      show "\<And>x u. is_leftmost_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> is_leftmost_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \\ u)"
        by (simp add: is_leftmost_reduction_def)
      fix t u
      show "\<lbrakk>\<And>u. \<lbrakk>is_leftmost_reduction t; elementary_reduction u;
                   \<not> is_leftmost_reduction u; coinitial t u\<rbrakk> \<Longrightarrow> is_leftmost_reduction (t \\ u);
             is_leftmost_reduction (Lam t); elementary_reduction u;
             \<not> is_leftmost_reduction u; coinitial \<^bold>\<lambda>\<^bold>[t\<^bold>] u\<rbrakk>
                \<Longrightarrow> is_leftmost_reduction (\<^bold>\<lambda>\<^bold>[t\<^bold>] \\ u)"
        using is_leftmost_reduction_def
        by (cases u) auto
      next
      fix t1 t2 u
      show "\<lbrakk>is_leftmost_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2); elementary_reduction u; \<not> is_leftmost_reduction u;
             coinitial (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u\<rbrakk>
               \<Longrightarrow> is_leftmost_reduction ((\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \\ u)"
        using is_leftmost_reduction_def Src_resid Ide_Trg Ide_iff_Src_self Arr_Trg Arr_not_Nil
        apply (cases u)
            apply simp_all
        by (cases "un_App1 u") auto
      assume ind1: "\<And>u. \<lbrakk>is_leftmost_reduction t1; elementary_reduction u;
                          \<not> is_leftmost_reduction u; coinitial t1 u\<rbrakk>
                            \<Longrightarrow> is_leftmost_reduction (t1 \\ u)"
      assume ind2: "\<And>u. \<lbrakk>is_leftmost_reduction t2; elementary_reduction u;
                         \<not> is_leftmost_reduction u; coinitial t2 u\<rbrakk>
                            \<Longrightarrow> is_leftmost_reduction (t2 \\ u)"
      assume 1: "is_leftmost_reduction (t1 \<^bold>\<circ> t2)"
      assume 2: "elementary_reduction u"
      assume 3: "\<not> is_leftmost_reduction u"
      assume 4: "coinitial (t1 \<^bold>\<circ> t2) u"
      show "is_leftmost_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
        using 1 2 3 4 ind1 ind2 is_leftmost_reduction_def Src_resid
        apply (cases u)
            apply auto[3]
      proof -
        show "\<And>u1 u2. u = \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2 \<Longrightarrow> is_leftmost_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
          by (metis 2 3 is_leftmost_reduction_def elementary_reduction.simps(5)
              is_head_reduction.simps(8) leftmost_strategy_selects_head_reduction)
        fix u1 u2
        assume u: "u = u1 \<^bold>\<circ> u2"
        show "is_leftmost_reduction ((t1 \<^bold>\<circ> t2) \\ u)"
          using u 1 2 3 4 ind1 ind2 is_leftmost_reduction_def Src_resid Ide_Trg
                elementary_reduction_not_ide
          apply (cases u)
              apply simp_all
          apply (cases u1)
              apply simp_all
            apply auto[1]
          using Ide_iff_Src_self
           apply simp_all
        proof -
          fix u11 u12
          assume u: "u = u11 \<^bold>\<circ> u12 \<^bold>\<circ> u2"
          assume u1: "u1 = u11 \<^bold>\<circ> u12"
          have A: "(elementary_reduction t1 \<and> Src u2 = t2 \<or>
                      Src u11 \<^bold>\<circ> Src u12 = t1 \<and> elementary_reduction t2) \<and>
                     (if \<not> Ide (leftmost_strategy (Src u11 \<^bold>\<circ> Src u12))
                      then leftmost_strategy (Src u11 \<^bold>\<circ> Src u12) \<^bold>\<circ> Src u2
                      else Src u11 \<^bold>\<circ> Src u12 \<^bold>\<circ> leftmost_strategy (Src u2)) = t1 \<^bold>\<circ> t2"
            using 1 4 Ide_iff_Src_self is_leftmost_reduction_def u by auto
          have B: "(elementary_reduction u11 \<and> Src u12 = u12 \<or>
                      Src u11 = u11 \<and> elementary_reduction u12) \<and> Src u2 = u2 \<or>
                      Src u11 = u11 \<and> Src u12 = u12 \<and> elementary_reduction u2"
            using "2" "4" Ide_iff_Src_self u by force
          have C: "t1 = u11 \<^bold>\<circ> u12 \<longrightarrow> t2 \<noteq> u2"
            using 1 3 u by fastforce
          have D: "Arr t1 \<and> Arr t2 \<and> Arr u11 \<and> Arr u12 \<and> Arr u2 \<and>
                     Src t1 = Src u11 \<^bold>\<circ> Src u12 \<and> Src t2 = Src u2"
            using 4 u by force
          have E: "\<And>u. \<lbrakk>elementary_reduction t1 \<and> leftmost_strategy (Src u) = t1;
                          elementary_reduction u;
                          t1 \<noteq> u;
                          Arr u \<and> Src u11 \<^bold>\<circ> Src u12 = Src u\<rbrakk>
                            \<Longrightarrow> elementary_reduction (t1 \\ u) \<and>
                                leftmost_strategy (Trg u) = t1 \\ u"
            using D Src_resid ind1 is_leftmost_reduction_def by auto
          have F: "\<And>u. \<lbrakk>elementary_reduction t2 \<and> leftmost_strategy (Src u) = t2;
                          elementary_reduction u;
                          t2 \<noteq> u;
                          Arr u \<and> Src u2 = Src u\<rbrakk>
                            \<Longrightarrow> elementary_reduction (t2 \\ u) \<and>
                                leftmost_strategy (Trg u) = t2 \\ u"
            using D Src_resid ind2 is_leftmost_reduction_def by auto
          have G: "\<And>t. elementary_reduction t \<Longrightarrow> \<not> Ide t"
            using elementary_reduction_not_ide ide_char by blast
          have H: "elementary_reduction (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> Ide (t2 \\ u2) \<or>
                     Ide (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> elementary_reduction (t2 \\ u2)"
          proof (cases "Ide (t2 \\ u2)")
            assume 1: "Ide (t2 \\ u2)"
            hence "elementary_reduction (t1 \\ (u11 \<^bold>\<circ> u12))"
              by (metis A B C D E F G Ide_Src Arr.simps(4) Src.simps(4)
                  elementary_reduction.simps(4) lambda.inject(3) resid_Arr_Src)
            thus ?thesis
              using 1 by auto
            next
            assume 1: "\<not> Ide (t2 \\ u2)"
            hence "Ide (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> elementary_reduction (t2 \\ u2)"
              apply (intro conjI)
               apply (metis 1 A D Ide_Src Arr.simps(4) Src.simps(4) resid_Ide_Arr)
              by (metis A B C D F Ide_iff_Src_self lambda.inject(3) resid_Arr_Src resid_Ide_Arr)
            thus ?thesis by simp
          qed
          show "(\<not> Ide (leftmost_strategy (Trg u11 \<^bold>\<circ> Trg u12)) \<longrightarrow>
                  (elementary_reduction (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> Ide (t2 \\ u2) \<or>
                   Ide (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> elementary_reduction (t2 \\ u2)) \<and>
                   leftmost_strategy (Trg u11 \<^bold>\<circ> Trg u12) = t1 \\ (u11 \<^bold>\<circ> u12) \<and> Trg u2 = t2 \\ u2) \<and>
                (Ide (leftmost_strategy (Trg u11 \<^bold>\<circ> Trg u12)) \<longrightarrow>
                  (elementary_reduction (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> Ide (t2 \\ u2) \<or>
                   Ide (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> elementary_reduction (t2 \\ u2)) \<and>
                   Trg u11 \<^bold>\<circ> Trg u12 = t1 \\ (u11 \<^bold>\<circ> u12) \<and> leftmost_strategy (Trg u2) = t2 \\ u2)"
          proof (intro conjI impI)
            show H: "elementary_reduction (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> Ide (t2 \\ u2) \<or>
                       Ide (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> elementary_reduction (t2 \\ u2)"
              by fact
            show H: "elementary_reduction (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> Ide (t2 \\ u2) \<or>
                       Ide (t1 \\ (u11 \<^bold>\<circ> u12)) \<and> elementary_reduction (t2 \\ u2)"
              by fact
            assume K: "\<not> Ide (leftmost_strategy (Trg u11 \<^bold>\<circ> Trg u12))"
            show J: "Trg u2 = t2 \\ u2"
              using A B D G K has_redex_iff_not_Ide_leftmost_strategy
                    NF_def NF_iff_has_no_redex NF_App_iff resid_Arr_Src resid_Src_Arr
              by (metis lambda.inject(3))
            show "leftmost_strategy (Trg u11 \<^bold>\<circ> Trg u12) = t1 \\ (u11 \<^bold>\<circ> u12)"
              using 2 A B C D E G H J u Ide_Trg Src_Src
                  has_redex_iff_not_Ide_leftmost_strategy resid_Arr_Ide resid_Src_Arr
              by (metis Arr.simps(4) Ide.simps(4) Src.simps(4) Trg.simps(3)
                  elementary_reduction.simps(4) lambda.inject(3))
            next
            assume K: "Ide (leftmost_strategy (Trg u11 \<^bold>\<circ> Trg u12))"
            show I: "Trg u11 \<^bold>\<circ> Trg u12 = t1 \\ (u11 \<^bold>\<circ> u12)"
              using 2 A D E K u Coinitial_resid_resid ConI resid_Arr_self resid_Ide_Arr
                    resid_Arr_Ide Ide_iff_Src_self Src_resid
              apply (cases "Ide (leftmost_strategy (Src u11 \<^bold>\<circ> Src u12))")
               apply simp
              using lambda_calculus.Con_Arr_Src(2)
               apply force
              apply simp
              using u1 G H Coinitial_iff_Con
              apply (cases "elementary_reduction u11";
                     cases "elementary_reduction u12")
                 apply simp_all
                 apply metis
                apply (metis Src.simps(4) Trg.simps(3) elementary_reduction.simps(1,4))
               apply (metis Src.simps(4) Trg.simps(3) elementary_reduction.simps(1,4))
              by (metis Trg_Src)
            show "leftmost_strategy (Trg u2) = t2 \\ u2"
              using 2 A C D F G H I u Ide_Trg Ide_iff_Src_self NF_def NF_iff_has_no_redex
                    has_redex_iff_not_Ide_leftmost_strategy resid_Ide_Arr
              by (metis Arr.simps(4) Src.simps(4) Trg.simps(3) elementary_reduction.simps(4)
                  lambda.inject(3))
          qed
        qed
      qed
    qed

  end

  section "Standard Reductions"

    text \<open>
      In this section, we define the notion of a \emph{standard reduction}, which is an
      elementary reduction path that performs reductions from left to right, possibly
      skipping some redexes that could be contracted.  Once a redex has been skipped,
      neither that redex nor any redex to its left will subsequently be contracted.
      We then define and prove correct a function that transforms an arbitrary
      elementary reduction path into a congruent standard reduction path.
      Using this function, we prove the Standardization Theorem, which says that
      every elementary reduction path is congruent to a standard reduction path.
      We then show that a standard reduction path that reaches a normal form is in
      fact a leftmost reduction path.  From this fact and the Standardization Theorem
      we prove the Leftmost Reduction Theorem: leftmost reduction is a normalizing
      strategy.

      The Standardization Theorem was first proved by Curry and Feys \<^cite>\<open>"curry-and-feys"\<close>,
      with subsequent proofs given by a number of authors.  Formalized proofs have also
      been given; a recent one (using Agda) is presented in \<^cite>\<open>"copes"\<close>, with references
      to earlier work.  The version of the theorem that we formalize here is a ``strong''
      version, which asserts the existence of a standard reduction path congruent to a
      a given elementary reduction path.  At the core of the proof is a function that
      directly transforms a given reduction path into a standard one, using an algorithm
      roughly analogous to insertion sort.  The Finite Development Theorem is used in the
      proof of termination.  The proof of correctness is long, due to the number of cases that
      have to be considered, but the use of a proof assistant makes this manageable.
    \<close>

  subsection "Standard Reduction Paths"

  subsubsection "`Standardly Sequential' Reductions"

    text \<open>
      We first need to define the notion of a ``standard reduction''.  In contrast to what
      is typically done by other authors, we define this notion by direct comparison of adjacent
      terms in an elementary reduction path, rather than by using devices such as a numbering
      of subterms from left to right.

      The following function decides when two terms \<open>t\<close> and \<open>u\<close> are elementary reductions that are
      ``standardly sequential''.  This means that \<open>t\<close> and \<open>u\<close> are sequential, but in addition
      no marked redex in \<open>u\<close> is the residual of an (unmarked) redex ``to the left of'' any
      marked redex in \<open>t\<close>.  Some care is required to make sure that the recursive definition
      captures what we intend.  Most of the clauses are readily understandable.
      One clause that perhaps could use some explanation is the one for
      \<open>sseq ((\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<^bold>\<circ> v) w\<close>.  Referring to the previously proved fact \<open>seq_cases\<close>,
      which classifies the way in which two terms \<open>t\<close> and \<open>u\<close> can be sequential,
      we see that one case that must be covered is when \<open>t\<close> has the form \<open>\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> v) \<^bold>\<circ> w\<close>
      and the top-level constructor of \<open>u\<close> is \<open>Beta\<close>.  In this case, it is the reduction
      of \<open>t\<close> that creates the top-level redex contracted in \<open>u\<close>, so it is impossible for \<open>u\<close> to
      be a residual of a redex that already exists in \<open>Src t\<close>.
    \<close>

  context lambda_calculus
  begin

    fun sseq
    where "sseq _ \<^bold>\<sharp> = False"
        | "sseq \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> = False"
        | "sseq \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<lambda>\<^bold>[t'\<^bold>] = sseq t t'"
        | "sseq (t \<^bold>\<circ> u) (t' \<^bold>\<circ> u') =
                ((sseq t t' \<and> Ide u \<and> u = u') \<or>
                 (Ide t \<and> t = t' \<and> sseq u u') \<or>
                 (elementary_reduction t \<and> Trg t = t' \<and>
                  (u = Src u' \<and> elementary_reduction u')))"
        | "sseq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) (\<^bold>\<lambda>\<^bold>[t'\<^bold>] \<^bold>\<Zspot> u') = False"
        | "sseq ((\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<^bold>\<circ> v) w =
                (Ide t \<and> Ide u \<and> Ide v \<and> elementary_reduction w \<and> seq ((\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<^bold>\<circ> v) w)"
        | "sseq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) v = (Ide t \<and> Ide u \<and> elementary_reduction v \<and> seq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) v)"
        | "sseq _ _ = False"

    lemma sseq_imp_seq:
    shows "sseq t u \<Longrightarrow> seq t u"
    proof (induct t arbitrary: u)
      show "\<And>u. sseq \<^bold>\<sharp> u \<Longrightarrow> seq \<^bold>\<sharp> u"
        using sseq.elims(1) by blast
      fix u
      show "\<And>x. sseq \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u \<Longrightarrow> seq \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u"
        using sseq.elims(1) by blast
      show "\<And>t. \<lbrakk>\<And>u. sseq t u \<Longrightarrow> seq t u; sseq \<^bold>\<lambda>\<^bold>[t\<^bold>] u\<rbrakk> \<Longrightarrow> seq \<^bold>\<lambda>\<^bold>[t\<^bold>] u"
        using seq_char by (cases u) auto
      show "\<And>t1 t2. \<lbrakk>\<And>u. sseq t1 u \<Longrightarrow> seq t1 u; \<And>u. sseq t2 u \<Longrightarrow> seq t2 u;
                     sseq (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u\<rbrakk>
                        \<Longrightarrow> seq (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u"
        using seq_char Ide_implies_Arr
        by (cases u) auto
      fix t1 t2
      show "\<lbrakk>\<And>u. sseq t1 u \<Longrightarrow> seq t1 u; \<And>u. sseq t2 u \<Longrightarrow> seq t2 u; sseq (t1 \<^bold>\<circ> t2) u\<rbrakk>
                  \<Longrightarrow> seq (t1 \<^bold>\<circ> t2) u"
      proof -
        assume ind1: "\<And>u. sseq t1 u \<Longrightarrow> seq t1 u"
        assume ind2: "\<And>u. sseq t2 u \<Longrightarrow> seq t2 u"
        assume 1: "sseq (t1 \<^bold>\<circ> t2) u"
        show ?thesis
          using 1 ind1 ind2 seq_char arr_char elementary_reduction_is_arr
                Ide_Src Ide_Trg Ide_implies_Arr Coinitial_iff_Con resid_Arr_self
          apply (cases u, simp_all)
             apply (cases t1, simp_all)
            apply (cases t1, simp_all)
           apply (cases "Ide t1"; cases "Ide t2")
              apply simp_all
             apply (metis Ide_iff_Src_self Ide_iff_Trg_self)
            apply (metis Ide_iff_Src_self Ide_iff_Trg_self)
           apply (metis Ide_iff_Trg_self Src_Trg)
          by (cases t1) auto
      qed
    qed

    lemma sseq_imp_elementary_reduction1:
    shows "sseq t u \<Longrightarrow> elementary_reduction t"
    proof (induct u arbitrary: t)
      show "\<And>t. sseq t \<^bold>\<sharp> \<Longrightarrow> elementary_reduction t"
        by simp
      show "\<And>x t. sseq t \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> elementary_reduction t"
        using elementary_reduction.simps(2) sseq.elims(1) by blast
      show "\<And>u. \<lbrakk>\<And>t. sseq t u \<Longrightarrow> elementary_reduction t; sseq t \<^bold>\<lambda>\<^bold>[u\<^bold>]\<rbrakk>
                    \<Longrightarrow> elementary_reduction t" for t
        using seq_cases sseq_imp_seq
        apply (cases t, simp_all)
        by force
      show "\<And>u1 u2. \<lbrakk>\<And>t. sseq t u1 \<Longrightarrow> elementary_reduction t;
                     \<And>t. sseq t u2 \<Longrightarrow> elementary_reduction t;
                     sseq t (u1 \<^bold>\<circ> u2)\<rbrakk>
                       \<Longrightarrow> elementary_reduction t" for t
        using seq_cases sseq_imp_seq Ide_Src elementary_reduction_is_arr
        apply (cases t, simp_all)
        by blast
      show "\<And>u1 u2.
       \<lbrakk>\<And>t. sseq t u1 \<Longrightarrow> elementary_reduction t; \<And>t. sseq t u2 \<Longrightarrow> elementary_reduction t;
        sseq t (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)\<rbrakk>
       \<Longrightarrow> elementary_reduction t" for t
        using seq_cases sseq_imp_seq
        apply (cases t, simp_all)
        by fastforce
    qed

    lemma sseq_imp_elementary_reduction2:
    shows "sseq t u \<Longrightarrow> elementary_reduction u"
    proof (induct u arbitrary: t)
      show "\<And>t. sseq t \<^bold>\<sharp> \<Longrightarrow> elementary_reduction \<^bold>\<sharp>"
        by simp
      show "\<And>x t. sseq t \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<Longrightarrow> elementary_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        using elementary_reduction.simps(2) sseq.elims(1) by blast
      show "\<And>u. \<lbrakk>\<And>t. sseq t u \<Longrightarrow> elementary_reduction u; sseq t \<^bold>\<lambda>\<^bold>[u\<^bold>]\<rbrakk>
                   \<Longrightarrow> elementary_reduction \<^bold>\<lambda>\<^bold>[u\<^bold>]" for t
        using seq_cases sseq_imp_seq
        apply (cases t, simp_all)
        by force
      show "\<And>u1 u2. \<lbrakk>\<And>t. sseq t u1 \<Longrightarrow> elementary_reduction u1;
                     \<And>t. sseq t u2 \<Longrightarrow> elementary_reduction u2;
                     sseq t (u1 \<^bold>\<circ> u2)\<rbrakk>
                       \<Longrightarrow> elementary_reduction (u1 \<^bold>\<circ> u2)" for t
        using seq_cases sseq_imp_seq Ide_Trg elementary_reduction_is_arr
        by (cases t) auto
      show "\<And>u1 u2. \<lbrakk>\<And>t. sseq t u1 \<Longrightarrow> elementary_reduction u1;
                     \<And>t. sseq t u2 \<Longrightarrow> elementary_reduction u2;
                     sseq t (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)\<rbrakk>
                       \<Longrightarrow> elementary_reduction (\<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2)" for t
        using seq_cases sseq_imp_seq
        apply (cases t, simp_all)
        by fastforce
    qed

    lemma sseq_Beta:
    shows "sseq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) v \<longleftrightarrow> Ide t \<and> Ide u \<and> elementary_reduction v \<and> seq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) v"
      by (cases v) auto

    lemma sseq_BetaI [intro]:
    assumes "Ide t" and "Ide u" and "elementary_reduction v" and "seq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) v"
    shows "sseq (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) v"
      using assms sseq_Beta by simp

    text \<open>
      A head reduction is standardly sequential with any elementary reduction that
      can be performed after it.
    \<close>

    lemma sseq_head_reductionI:
    shows "\<lbrakk>is_head_reduction t; elementary_reduction u; seq t u\<rbrakk> \<Longrightarrow> sseq t u"
    proof (induct t arbitrary: u)
      show "\<And>u. \<lbrakk>is_head_reduction \<^bold>\<sharp>; elementary_reduction u; seq \<^bold>\<sharp> u\<rbrakk> \<Longrightarrow> sseq \<^bold>\<sharp> u"
        by simp
      show "\<And>x u. \<lbrakk>is_head_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>; elementary_reduction u; seq \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u\<rbrakk> \<Longrightarrow> sseq \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u"
        by auto
      show "\<And>t. \<lbrakk>\<And>u. \<lbrakk>is_head_reduction t; elementary_reduction u; seq t u\<rbrakk> \<Longrightarrow> sseq t u;
                 is_head_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>]; elementary_reduction u; seq \<^bold>\<lambda>\<^bold>[t\<^bold>] u\<rbrakk>
                    \<Longrightarrow> sseq \<^bold>\<lambda>\<^bold>[t\<^bold>] u" for u
        by (cases u) auto
      show "\<And>t2. \<lbrakk>\<And>u. \<lbrakk>is_head_reduction t1; elementary_reduction u; seq t1 u\<rbrakk> \<Longrightarrow> sseq t1 u;
                  \<And>u. \<lbrakk>is_head_reduction t2; elementary_reduction u; seq t2 u\<rbrakk> \<Longrightarrow> sseq t2 u;
                  is_head_reduction (t1 \<^bold>\<circ> t2); elementary_reduction u; seq (t1 \<^bold>\<circ> t2) u\<rbrakk>
                     \<Longrightarrow> sseq (t1 \<^bold>\<circ> t2) u" for t1 u
        using seq_char
        apply (cases u)
            apply simp_all
        apply (metis ArrE Ide_iff_Src_self Ide_iff_Trg_self App_Var_contains_no_head_reduction
            is_head_reduction_char is_head_reduction_imp_contains_head_reduction
            is_head_reduction.simps(3,6-7))
        by (cases t1) auto
      show "\<And>t1 t2 u. \<lbrakk>\<And>u. \<lbrakk>is_head_reduction t1; elementary_reduction u; seq t1 u\<rbrakk> \<Longrightarrow> sseq t1 u;
                       \<And>u. \<lbrakk>is_head_reduction t2; elementary_reduction u; seq t2 u\<rbrakk> \<Longrightarrow> sseq t2 u;
                       is_head_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2); elementary_reduction u; seq (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u\<rbrakk>
                         \<Longrightarrow> sseq (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u"
        by auto
    qed

    text \<open>
      Once a head reduction is skipped in an application, then all terms that follow it
      in a standard reduction path are also applications that do not contain head reductions.
    \<close>

    lemma sseq_preserves_App_and_no_head_reduction:
    shows "\<lbrakk>sseq t u; is_App t \<and> \<not> contains_head_reduction t\<rbrakk>
               \<Longrightarrow> is_App u \<and> \<not> contains_head_reduction u"
      apply (induct t arbitrary: u)
          apply simp_all
    proof -
      fix t1 t2 u
      assume ind1: "\<And>u. \<lbrakk>sseq t1 u; is_App t1 \<and> \<not> contains_head_reduction t1\<rbrakk>
                          \<Longrightarrow> is_App u \<and> \<not> contains_head_reduction u"
      assume ind2: "\<And>u. \<lbrakk>sseq t2 u; is_App t2 \<and> \<not> contains_head_reduction t2\<rbrakk>
                          \<Longrightarrow> is_App u \<and> \<not> contains_head_reduction u"
      assume sseq: "sseq (t1 \<^bold>\<circ> t2) u"
      assume t: "\<not> contains_head_reduction (t1 \<^bold>\<circ> t2)"
      have u: "\<not> is_Beta u"
       using sseq t sseq_imp_seq seq_cases
       by (cases t1; cases u) auto
      have 1: "is_App u"
        using u sseq sseq_imp_seq
        apply (cases u)
            apply simp_all
        by fastforce+
      moreover have "\<not> contains_head_reduction u"
      proof (cases u)
        show "\<And>v. u = \<^bold>\<lambda>\<^bold>[v\<^bold>] \<Longrightarrow> \<not> contains_head_reduction u"
          using 1 by auto
        show "\<And>v w. u = \<^bold>\<lambda>\<^bold>[v\<^bold>] \<^bold>\<Zspot> w \<Longrightarrow> \<not> contains_head_reduction u"
          using u by auto
        fix u1 u2
        assume u: "u = u1 \<^bold>\<circ> u2"
        have 1: "(sseq t1 u1 \<and> Ide t2 \<and> t2 = u2) \<or> (Ide t1 \<and> t1 = u1 \<and> sseq t2 u2) \<or>
                 (elementary_reduction t1 \<and> u1 = Trg t1 \<and> t2 = Src u2 \<and> elementary_reduction u2)"
          using sseq u by force
        moreover have "Ide t1 \<and> t1 = u1 \<and> sseq t2 u2 \<Longrightarrow> ?thesis"
          using Ide_implies_Arr ide_char sseq_imp_seq t u by fastforce
        moreover have "elementary_reduction t1 \<and> u1 = Trg t1 \<and> t2 = Src u2 \<and>
                       elementary_reduction u2
                         \<Longrightarrow> ?thesis"
        proof -
          assume 2: "elementary_reduction t1 \<and> u1 = Trg t1 \<and> t2 = Src u2 \<and>
                     elementary_reduction u2"
          have "contains_head_reduction u \<Longrightarrow> contains_head_reduction u1"
            using u
            apply simp
            using contains_head_reduction.elims(2) by fastforce
          hence "contains_head_reduction u \<Longrightarrow> \<not> Ide u1"
            using contains_head_reduction_iff
            by (metis Coinitial_iff_Con Ide_iff_Src_self Ide_implies_Arr ide_char resid_Arr_Src
                subs_head_redex subs_implies_prfx)
          thus ?thesis
            using 2
            by (metis Arr.simps(4) Ide_Trg seq_char sseq sseq_imp_seq)
        qed
        moreover have "sseq t1 u1 \<and> Ide t2 \<and> t2 = u2 \<Longrightarrow> ?thesis"
          using t u ind1 [of u1] Ide_implies_Arr sseq_imp_elementary_reduction1
          apply (cases t1, simp_all)
          using elementary_reduction.simps(1)
              apply blast
          using elementary_reduction.simps(2)
             apply blast
          using contains_head_reduction.elims(2)
            apply fastforce
           apply (metis contains_head_reduction.simps(6) is_App_def)
          using sseq_Beta by blast
        ultimately show ?thesis by blast
      qed auto
      ultimately show "is_App u \<and> \<not> contains_head_reduction u"
        by blast
    qed

  end

  subsubsection "Standard Reduction Paths"

  context reduction_paths
  begin

    text \<open>
      A \emph{standard reduction path} is an elementary reduction path in which
      successive reductions are standardly sequential.
    \<close>

    fun Std
    where "Std [] = True"
        | "Std [t] = \<Lambda>.elementary_reduction t"
        | "Std (t # U) = (\<Lambda>.sseq t (hd U) \<and> Std U)"

    lemma Std_consE [elim]:
    assumes "Std (t # U)"
    and "\<lbrakk>\<Lambda>.Arr t; U \<noteq> [] \<Longrightarrow> \<Lambda>.sseq t (hd U); Std U\<rbrakk> \<Longrightarrow> thesis"
    shows thesis
      using assms
      by (metis \<Lambda>.arr_char \<Lambda>.elementary_reduction_is_arr \<Lambda>.seq_char \<Lambda>.sseq_imp_seq
          list.exhaust_sel list.sel(1) Std.simps(1-3))

    lemma Std_imp_Arr [simp]:
    shows "\<lbrakk>Std T; T \<noteq> []\<rbrakk> \<Longrightarrow> Arr T"
    proof (induct T)
      show "[] \<noteq> [] \<Longrightarrow> Arr []"
        by simp
      fix t U
      assume ind: "\<lbrakk>Std U; U \<noteq> []\<rbrakk> \<Longrightarrow> Arr U"
      assume tU: "Std (t # U)"
      show "Arr (t # U)"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> Arr (t # U)"
          using \<Lambda>.elementary_reduction_is_arr tU \<Lambda>.Ide_implies_Arr Std.simps(2) Arr.simps(2)
          by blast
        assume U: "U \<noteq> []"
        show "Arr (t # U)"
        proof -
          have "\<Lambda>.sseq t (hd U)"
            using tU U
            by (metis list.exhaust_sel reduction_paths.Std.simps(3))
          thus ?thesis
            using U ind \<Lambda>.sseq_imp_seq
            apply auto
            using reduction_paths.Std.elims(3) tU
            by fastforce
        qed
      qed
    qed

    lemma Std_imp_sseq_last_hd:
    shows "\<lbrakk>Std (T @ U); T \<noteq> []; U \<noteq> []\<rbrakk> \<Longrightarrow> \<Lambda>.sseq (last T) (hd U)"
      apply (induct T arbitrary: U)
       apply simp_all
      by (metis Std.elims(3) Std.simps(3) append_self_conv2 neq_Nil_conv)

    lemma Std_implies_set_subset_elementary_reduction:
    shows "Std U \<Longrightarrow> set U \<subseteq> Collect \<Lambda>.elementary_reduction"
      apply (induct U)
        apply auto
      by (metis Std.simps(2) Std.simps(3) neq_Nil_conv \<Lambda>.sseq_imp_elementary_reduction1)

    lemma Std_map_Lam:
    shows "Std T \<Longrightarrow> Std (map \<Lambda>.Lam T)"
    proof (induct T)
      show "Std [] \<Longrightarrow> Std (map \<Lambda>.Lam [])"
        by simp
      fix t U
      assume ind: "Std U \<Longrightarrow> Std (map \<Lambda>.Lam U)"
      assume tU: "Std (t # U)"
      have "Std (map \<Lambda>.Lam (t # U)) \<longleftrightarrow> Std (\<^bold>\<lambda>\<^bold>[t\<^bold>] # map \<Lambda>.Lam U)"
        by auto
      also have "... = True"
        apply (cases "U = []")
         apply simp_all
        using Arr.simps(3) Std.simps(2) arr_char tU
         apply presburger
      proof -
        assume U: "U \<noteq> []"
        have "Std (\<^bold>\<lambda>\<^bold>[t\<^bold>] # map \<Lambda>.Lam U) \<longleftrightarrow> \<Lambda>.sseq \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<lambda>\<^bold>[hd U\<^bold>] \<and> Std (map \<Lambda>.Lam U)"
          using U
          by (metis Nil_is_map_conv Std.simps(3) hd_map list.exhaust_sel)
        also have "... \<longleftrightarrow> \<Lambda>.sseq t (hd U) \<and> Std (map \<Lambda>.Lam U)"
          by auto
        also have "... = True"
          using ind tU U
          by (metis Std.simps(3) list.exhaust_sel)
        finally show "Std (\<^bold>\<lambda>\<^bold>[t\<^bold>] # map \<Lambda>.Lam U)" by blast
      qed
      finally show "Std (map \<Lambda>.Lam (t # U))" by blast
    qed

    lemma Std_map_App1:
    shows "\<lbrakk>\<Lambda>.Ide b; Std T\<rbrakk> \<Longrightarrow> Std (map (\<lambda>X. X \<^bold>\<circ> b) T)"
    proof (induct T)
      show "\<lbrakk>\<Lambda>.Ide b; Std []\<rbrakk> \<Longrightarrow> Std (map (\<lambda>X. X \<^bold>\<circ> b) [])"
        by simp
      fix t U
      assume ind: "\<lbrakk>\<Lambda>.Ide b; Std U\<rbrakk> \<Longrightarrow> Std (map (\<lambda>X. X \<^bold>\<circ> b) U)"
      assume b: "\<Lambda>.Ide b"
      assume tU: "Std (t # U)"
      show "Std (map (\<lambda>v. v \<^bold>\<circ> b) (t # U))"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using Ide_implies_Arr b \<Lambda>.arr_char tU by force
        assume U: "U \<noteq> []"
        have "Std (map (\<lambda>v. v \<^bold>\<circ> b) (t # U)) = Std ((t \<^bold>\<circ> b) # map (\<lambda>X. X \<^bold>\<circ> b) U)"
          by simp
        also have "... = (\<Lambda>.sseq (t \<^bold>\<circ> b) (hd U \<^bold>\<circ> b) \<and> Std (map (\<lambda>X. X \<^bold>\<circ> b) U))"
          using U reduction_paths.Std.simps(3) hd_map
          by (metis Nil_is_map_conv neq_Nil_conv)
        also have "... = True"
          using b tU U ind
          by (metis Std.simps(3) list.exhaust_sel \<Lambda>.sseq.simps(4))
        finally show "Std (map (\<lambda>v. v \<^bold>\<circ> b) (t # U))" by blast
      qed
    qed

    lemma Std_map_App2:
    shows "\<lbrakk>\<Lambda>.Ide a; Std T\<rbrakk> \<Longrightarrow> Std (map (\<lambda>u. a \<^bold>\<circ> u) T)"
    proof (induct T)
      show "\<lbrakk>\<Lambda>.Ide a; Std []\<rbrakk> \<Longrightarrow> Std (map (\<lambda>u. a \<^bold>\<circ> u) [])"
        by simp
      fix t U
      assume ind: "\<lbrakk>\<Lambda>.Ide a; Std U\<rbrakk> \<Longrightarrow> Std (map (\<lambda>u. a \<^bold>\<circ> u) U)"
      assume a: "\<Lambda>.Ide a"
      assume tU: "Std (t # U)"
      show "Std (map (\<lambda>u. a \<^bold>\<circ> u) (t # U))"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          using a tU by force
        assume U: "U \<noteq> []"
        have "Std (map (\<lambda>u. a \<^bold>\<circ> u) (t # U)) = Std ((a \<^bold>\<circ> t) # map (\<lambda>u. a \<^bold>\<circ> u) U)"
          by simp
        also have "... = (\<Lambda>.sseq (a \<^bold>\<circ> t) (a \<^bold>\<circ> hd U) \<and> Std (map (\<lambda>u. a \<^bold>\<circ> u) U))"
          using U
          by (metis Nil_is_map_conv Std.simps(3) hd_map list.exhaust_sel)
        also have "... = True"
          using a tU U ind
          by (metis Std.simps(3) list.exhaust_sel \<Lambda>.sseq.simps(4))
        finally show "Std (map (\<lambda>u. a \<^bold>\<circ> u) (t # U))" by blast
      qed
    qed

    lemma Std_map_un_Lam:
    shows "\<lbrakk>Std T; set T \<subseteq> Collect \<Lambda>.is_Lam\<rbrakk> \<Longrightarrow> Std (map \<Lambda>.un_Lam T)"
    proof (induct T)
      show "\<lbrakk>Std []; set [] \<subseteq> Collect \<Lambda>.is_Lam\<rbrakk> \<Longrightarrow> Std (map \<Lambda>.un_Lam [])"
        by simp
      fix t T
      assume ind: "\<lbrakk>Std T; set T \<subseteq> Collect \<Lambda>.is_Lam\<rbrakk> \<Longrightarrow> Std (map \<Lambda>.un_Lam T)"
      assume tT: "Std (t # T)"
      assume 1: "set (t # T) \<subseteq> Collect \<Lambda>.is_Lam"
      show "Std (map \<Lambda>.un_Lam (t # T))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> Std (map \<Lambda>.un_Lam (t # T))"
        by (metis "1" Std.simps(2) \<Lambda>.elementary_reduction.simps(3) \<Lambda>.lambda.collapse(2)
            list.set_intros(1) list.simps(8) list.simps(9) mem_Collect_eq subset_code(1) tT)
        assume T: "T \<noteq> []"
        show "Std (map \<Lambda>.un_Lam (t # T))"
          using T tT 1 ind Std.simps(3) [of "\<Lambda>.un_Lam t" "\<Lambda>.un_Lam (hd T)" "map \<Lambda>.un_Lam (tl T)"]
          by (metis \<Lambda>.lambda.collapse(2) \<Lambda>.sseq.simps(3) list.exhaust_sel list.sel(1)
              list.set_intros(1) map_eq_Cons_conv mem_Collect_eq reduction_paths.Std.simps(3)
              set_subset_Cons subset_code(1))
      qed
    qed

    lemma Std_append_single:
    shows "\<lbrakk>Std T; T \<noteq> []; \<Lambda>.sseq (last T) u\<rbrakk> \<Longrightarrow> Std (T @ [u])"
    proof (induct T)
      show "\<lbrakk>Std []; [] \<noteq> []; \<Lambda>.sseq (last []) u\<rbrakk> \<Longrightarrow> Std ([] @ [u])"
        by blast
      fix t T
      assume ind: "\<lbrakk>Std T; T \<noteq> []; \<Lambda>.sseq (last T) u\<rbrakk> \<Longrightarrow> Std (T @ [u])"
      assume tT: "Std (t # T)"
      assume sseq: "\<Lambda>.sseq (last (t # T)) u"
      have "Std (t # (T @ [u]))"
        using \<Lambda>.sseq_imp_elementary_reduction2 sseq ind tT
        apply (cases "T = []")
         apply simp
        by (metis append_Cons last_ConsR list.sel(1) neq_Nil_conv reduction_paths.Std.simps(3))
      thus "Std ((t # T) @ [u])" by simp
    qed

    lemma Std_append:
    shows "\<lbrakk>Std T; Std U; T = [] \<or> U = [] \<or> \<Lambda>.sseq (last T) (hd U)\<rbrakk> \<Longrightarrow> Std (T @ U)"
    proof (induct U arbitrary: T)
      show "\<And>T. \<lbrakk>Std T; Std []; T = [] \<or> [] = [] \<or> \<Lambda>.sseq (last T) (hd [])\<rbrakk> \<Longrightarrow> Std (T @ [])"
        by simp
      fix u T U
      assume ind: "\<And>T. \<lbrakk>Std T; Std U; T = [] \<or> U = [] \<or> \<Lambda>.sseq (last T) (hd U)\<rbrakk>
                          \<Longrightarrow> Std (T @ U)"
      assume T: "Std T"
      assume uU: "Std (u # U)"
      have U: "Std U"
        using uU Std.elims(3) by fastforce
      assume seq: "T = [] \<or> u # U = [] \<or> \<Lambda>.sseq (last T) (hd (u # U))"
      show "Std (T @ (u # U))"
        by (metis Std_append_single T U append.assoc append.left_neutral append_Cons
            ind last_snoc list.distinct(1) list.exhaust_sel list.sel(1) Std.simps(3) seq uU)
    qed

    subsubsection "Projections of Standard `App Paths'"

    text \<open>
      Given a standard reduction path, all of whose transitions have App as their top-level
      constructor, we can apply \<open>un_App1\<close> or \<open>un_App2\<close> to each transition to project the path
      onto paths formed from the ``rator'' and the ``rand'' of each application.  These projected
      paths are not standard, since the projection operation will introduce identities,
      in general.  However, in this section we show that if we remove the identities, then
      in fact we do obtain standard reduction paths.
    \<close>

    abbreviation notIde
    where "notIde \<equiv> \<lambda>u. \<not> \<Lambda>.Ide u"

    lemma filter_notIde_Ide:
    shows "Ide U \<Longrightarrow> filter notIde U = []"
      by (induct U) auto

    lemma cong_filter_notIde:
    shows "\<lbrakk>Arr U; \<not> Ide U\<rbrakk> \<Longrightarrow> filter notIde U \<^sup>*\<sim>\<^sup>* U"
    proof (induct U)
      show "\<lbrakk>Arr []; \<not> Ide []\<rbrakk> \<Longrightarrow> filter notIde [] \<^sup>*\<sim>\<^sup>* []"
        by simp
      fix u U
      assume ind: "\<lbrakk>Arr U; \<not> Ide U\<rbrakk> \<Longrightarrow> filter notIde U \<^sup>*\<sim>\<^sup>* U"
      assume Arr: "Arr (u # U)"
      assume 1: "\<not> Ide (u # U)"
      show "filter notIde (u # U) \<^sup>*\<sim>\<^sup>* (u # U)"
      proof (cases "\<Lambda>.Ide u")
        assume u: "\<Lambda>.Ide u"
        have U: "Arr U \<and> \<not> Ide U"
          using Arr u 1 Ide.elims(3) by fastforce
        have "filter notIde (u # U) = filter notIde U"
          using u by simp
        also have "... \<^sup>*\<sim>\<^sup>* U"
          using U ind by blast
        also have "U \<^sup>*\<sim>\<^sup>* [u] @ U"
          using u
          by (metis (full_types) Arr Arr_has_Src Cons_eq_append_conv Ide.elims(3) Ide.simps(2)
              Srcs.simps(1) U arrI\<^sub>P arr_append_imp_seq cong_append_ideI(3) ide_char
              \<Lambda>.ide_char not_Cons_self2)
        also have "[u] @ U = u # U"
          by simp
        finally show ?thesis by blast
        next
        assume u: "\<not> \<Lambda>.Ide u"
        show ?thesis
        proof (cases "Ide U")
          assume U: "Ide U"
          have "filter notIde (u # U) = [u]"
            using u U filter_notIde_Ide by simp
          moreover have "[u] \<^sup>*\<sim>\<^sup>* [u] @ U"
            using u U cong_append_ideI(4) [of "[u]" U]
            by (metis Arr Con_Arr_self Cons_eq_appendI Resid_Ide(1) arr_append_imp_seq
                arr_char ide_char ide_implies_arr neq_Nil_conv self_append_conv2)
          moreover have "[u] @ U = u # U"
            by simp
          ultimately show ?thesis by auto
          next
          assume U: "\<not> Ide U"
          have "filter notIde (u # U) = [u] @ filter notIde U"
            using u U Arr by simp
          also have "... \<^sup>*\<sim>\<^sup>* [u] @ U"
          proof (cases "U = []")
            show "U = [] \<Longrightarrow> ?thesis"
              by (metis Arr arr_char cong_reflexive append_Nil2 filter.simps(1))
            assume 1: "U \<noteq> []"
            have "seq [u] (filter notIde U)"
              by (metis (full_types) 1 Arr Arr.simps(2-3) Con_imp_eq_Srcs Con_implies_Arr(1)
                  Ide.elims(3) Ide.simps(1) Trgs.simps(2) U ide_char ind seq_char
                  seq_implies_Trgs_eq_Srcs)
            thus ?thesis
              using u U Arr ind cong_append [of "[u]" "filter notIde U" "[u]" U]
              by (meson 1 Arr_consE cong_reflexive seqE)
          qed
          also have "[u] @ U = u # U"
            by simp
          finally show ?thesis by argo
        qed
      qed
    qed

    lemma Std_filter_map_un_App1:
    shows "\<lbrakk>Std U; set U \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App1 U))"
    proof (induct U)
      show "\<lbrakk>Std []; set [] \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App1 []))"
        by simp
      fix u U
      assume ind: "\<lbrakk>Std U; set U \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App1 U))"
      assume 1: "Std (u # U)"
      assume 2: "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
      show "Std (filter notIde (map \<Lambda>.un_App1 (u # U)))"
        using 1 2 ind
        apply (cases u)
            apply simp_all
      proof -
        fix u1 u2
        assume uU: "Std ((u1 \<^bold>\<circ> u2) # U)"
        assume set: "set U \<subseteq> Collect \<Lambda>.is_App"
        assume ind: "Std U \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App1 U))"
        assume u: "u = u1 \<^bold>\<circ> u2"
        show "(\<not> \<Lambda>.Ide u1 \<longrightarrow> Std (u1 # filter notIde (map \<Lambda>.un_App1 U))) \<and>
              (\<Lambda>.Ide u1 \<longrightarrow> Std (filter notIde (map \<Lambda>.un_App1 U)))"
        proof (intro conjI impI)
          assume u1: "\<Lambda>.Ide u1"
          show "Std (filter notIde (map \<Lambda>.un_App1 U))"
            by (metis 1 Std.simps(1) Std.simps(3) ind neq_Nil_conv)
          next
          assume u1: "\<not> \<Lambda>.Ide u1"
          show "Std (u1 # filter notIde (map \<Lambda>.un_App1 U))"
          proof (cases "Ide (map \<Lambda>.un_App1 U)")
            show "Ide (map \<Lambda>.un_App1 U) \<Longrightarrow> ?thesis"
            proof -
              assume U: "Ide (map \<Lambda>.un_App1 U)"
              have "filter notIde (map \<Lambda>.un_App1 U) = []"
                by (metis U Ide_char filter_False \<Lambda>.ide_char
                    mem_Collect_eq subsetD)
              thus ?thesis
                by (metis Std.elims(1) Std.simps(2) \<Lambda>.elementary_reduction.simps(4) list.discI
                    list.sel(1) \<Lambda>.sseq_imp_elementary_reduction1 u1 uU)
            qed
            assume U: "\<not> Ide (map \<Lambda>.un_App1 U)"
            show ?thesis
            proof (cases "U = []")
              show "U = [] \<Longrightarrow> ?thesis"
                using 1 u u1 by fastforce
              assume "U \<noteq> []"
              hence U: "U \<noteq> [] \<and> \<not> Ide (map \<Lambda>.un_App1 U)"
                using U by simp
              have "\<Lambda>.sseq u1 (hd (filter notIde (map \<Lambda>.un_App1 U)))"
              proof -
                have "\<And>u1 u2. \<lbrakk>set U \<subseteq> Collect \<Lambda>.is_App; \<not> Ide (map \<Lambda>.un_App1 U); U \<noteq> [];
                               Std ((u1 \<^bold>\<circ> u2) # U); \<not> \<Lambda>.Ide u1\<rbrakk>
                                   \<Longrightarrow> \<Lambda>.sseq u1 (hd (filter notIde (map \<Lambda>.un_App1 U)))"
                  for U
                  apply (induct U)
                   apply simp_all
                  apply (intro conjI impI)
                proof -
                  fix u U u1 u2
                  assume ind: "\<And>u1 u2. \<lbrakk>\<not> Ide (map \<Lambda>.un_App1 U); U \<noteq> [];
                                        Std ((u1 \<^bold>\<circ> u2) # U); \<not> \<Lambda>.Ide u1\<rbrakk>
                                          \<Longrightarrow> \<Lambda>.sseq u1 (hd (filter notIde (map \<Lambda>.un_App1 U)))"
                  assume 1: "\<Lambda>.is_App u \<and> set U \<subseteq> Collect \<Lambda>.is_App"
                  assume 2: "\<not> Ide (\<Lambda>.un_App1 u # map \<Lambda>.un_App1 U)"
                  assume 3: "\<Lambda>.sseq (u1 \<^bold>\<circ> u2) u \<and> Std (u # U)"
                  show "\<not> \<Lambda>.Ide (\<Lambda>.un_App1 u) \<Longrightarrow> \<Lambda>.sseq u1 (\<Lambda>.un_App1 u)"
                    by (metis 1 3 \<Lambda>.Arr.simps(4) \<Lambda>.Ide_Trg \<Lambda>.lambda.collapse(3) \<Lambda>.seq_char
                        \<Lambda>.sseq.simps(4) \<Lambda>.sseq_imp_seq)
                  assume 4: "\<not> \<Lambda>.Ide u1"
                  assume 5: "\<Lambda>.Ide (\<Lambda>.un_App1 u)"
                  have u1: "\<Lambda>.elementary_reduction u1"
                    using 3 4 \<Lambda>.elementary_reduction.simps(4) \<Lambda>.sseq_imp_elementary_reduction1
                    by blast
                  have 6: "Arr (\<Lambda>.un_App1 u # map \<Lambda>.un_App1 U)"
                    using 1 3 Std_imp_Arr Arr_map_un_App1 [of "u # U"] by auto
                  have 7: "Arr (map \<Lambda>.un_App1 U)"
                    using 1 2 3 5 6 Arr_map_un_App1 Std_imp_Arr \<Lambda>.ide_char by fastforce
                  have 8: "\<not> Ide (map \<Lambda>.un_App1 U)"
                    using 2 5 6 set_Ide_subset_ide by fastforce
                  have 9: "\<Lambda>.seq u (hd U)"
                    by (metis 3 7 Std.simps(3) Arr.simps(1) list.collapse list.simps(8)
                        \<Lambda>.sseq_imp_seq)
                  show "\<Lambda>.sseq u1 (hd (filter notIde (map \<Lambda>.un_App1 U)))"
                  proof -
                    have "\<Lambda>.sseq (u1 \<^bold>\<circ> \<Lambda>.Trg (\<Lambda>.un_App2 u)) (hd U)"
                    proof (cases "\<Lambda>.Ide (\<Lambda>.un_App1 (hd U))")
                      assume 10: "\<Lambda>.Ide (\<Lambda>.un_App1 (hd U))"
                      hence "\<Lambda>.elementary_reduction (\<Lambda>.un_App2 (hd U))"
                        by (metis (full_types) 1 3 7 Std.elims(2) Arr.simps(1)
                            \<Lambda>.elementary_reduction_App_iff \<Lambda>.elementary_reduction_not_ide
                            \<Lambda>.ide_char list.sel(2) list.sel(3) list.set_sel(1) list.simps(8)
                            mem_Collect_eq \<Lambda>.sseq_imp_elementary_reduction2 subsetD)
                      moreover have "\<Lambda>.Trg u1 = \<Lambda>.un_App1 (hd U)"
                      proof -
                        have "\<Lambda>.Trg u1 = \<Lambda>.Src (\<Lambda>.un_App1 u)"
                          by (metis 1 3 5 \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr \<Lambda>.Trg_Src
                              \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char \<Lambda>.lambda.collapse(3)
                              \<Lambda>.sseq.simps(4) \<Lambda>.sseq_imp_elementary_reduction2)
                        also have "... = \<Lambda>.Trg (\<Lambda>.un_App1 u)"
                          by (metis 5 \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self
                              \<Lambda>.Ide_implies_Arr)
                        also have "... = \<Lambda>.un_App1 (hd U)"
                          using 1 3 5 7 \<Lambda>.Ide_iff_Trg_self
                          by (metis 9 10 Arr.simps(1) lambda_calculus.Ide_iff_Src_self
                              \<Lambda>.Ide_implies_Arr \<Lambda>.Src_Src \<Lambda>.Src_eq_iff(2) \<Lambda>.Trg.simps(3)
                              \<Lambda>.lambda.collapse(3) \<Lambda>.seqE\<^sub>\<Lambda> list.set_sel(1) list.simps(8)
                              mem_Collect_eq subsetD)
                        finally show ?thesis by argo
                      qed
                      moreover have "\<Lambda>.Trg (\<Lambda>.un_App2 u) = \<Lambda>.Src (\<Lambda>.un_App2 (hd U))"
                        by (metis 1 7 9 Arr.simps(1) hd_in_set \<Lambda>.Src.simps(4) \<Lambda>.Src_Src
                            \<Lambda>.Trg.simps(3) \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.sel(4)
                            \<Lambda>.seq_char list.simps(8) mem_Collect_eq subset_code(1))
                      ultimately show ?thesis
                        using \<Lambda>.sseq.simps(4)
                        by (metis 1 7 u1 Arr.simps(1) hd_in_set \<Lambda>.lambda.collapse(3)
                            list.simps(8) mem_Collect_eq subsetD)
                      next
                      assume 10: "\<not> \<Lambda>.Ide (\<Lambda>.un_App1 (hd U))"
                      have False
                      proof -
                        have "\<Lambda>.elementary_reduction (\<Lambda>.un_App2 u)"
                          using 1 3 5 \<Lambda>.elementary_reduction_App_iff
                                \<Lambda>.elementary_reduction_not_ide \<Lambda>.sseq_imp_elementary_reduction2
                          by blast
                        moreover have "\<Lambda>.sseq u (hd U)"
                          by (metis 3 7 Std.simps(3) Arr.simps(1)
                              hd_Cons_tl list.simps(8))
                        moreover have "\<Lambda>.elementary_reduction (\<Lambda>.un_App1 (hd U))"
                          by (metis 1 7 10 Nil_is_map_conv Arr.simps(1)
                              calculation(2) \<Lambda>.elementary_reduction_App_iff hd_in_set \<Lambda>.ide_char
                              mem_Collect_eq \<Lambda>.sseq_imp_elementary_reduction2 subset_iff)
                        ultimately show ?thesis
                          using \<Lambda>.sseq.simps(4)
                          by (metis 1 5 7 Arr.simps(1) \<Lambda>.elementary_reduction_not_ide
                              hd_in_set \<Lambda>.ide_char \<Lambda>.lambda.collapse(3) list.simps(8)
                              mem_Collect_eq subset_iff)
                      qed
                      thus ?thesis by argo
                    qed
                    hence " Std ((u1 \<^bold>\<circ> \<Lambda>.Trg (\<Lambda>.un_App2 u)) # U)"
                      by (metis 3 7 Std.simps(3) Arr.simps(1) list.exhaust_sel list.simps(8))
                    thus ?thesis
                      using ind
                      by (metis 7 8 u1 Arr.simps(1) \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char
                          list.simps(8))
                  qed
                qed
                thus ?thesis
                  using U set u1 uU by blast
              qed
              thus ?thesis
                by (metis 1 Std.simps(2-3) \<open>U \<noteq> []\<close> ind list.exhaust_sel list.sel(1)
                    \<Lambda>.sseq_imp_elementary_reduction1)
            qed
          qed
        qed
      qed
    qed

    lemma Std_filter_map_un_App2:
    shows "\<lbrakk>Std U; set U \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App2 U))"
    proof (induct U)
      show "\<lbrakk>Std []; set [] \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App2 []))"
        by simp
      fix u U
      assume ind: "\<lbrakk>Std U; set U \<subseteq> Collect \<Lambda>.is_App\<rbrakk> \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App2 U))"
      assume 1: "Std (u # U)"
      assume 2: "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
      show "Std (filter notIde (map \<Lambda>.un_App2 (u # U)))"
        using 1 2 ind
        apply (cases u)
            apply simp_all
      proof -
        fix u1 u2
        assume uU: "Std ((u1 \<^bold>\<circ> u2) # U)"
        assume set: "set U \<subseteq> Collect \<Lambda>.is_App"
        assume ind: "Std U \<Longrightarrow> Std (filter notIde (map \<Lambda>.un_App2 U))"
        assume u: "u = u1 \<^bold>\<circ> u2"
        show "(\<not> \<Lambda>.Ide u2 \<longrightarrow> Std (u2 # filter notIde (map \<Lambda>.un_App2 U))) \<and>
              (\<Lambda>.Ide u2 \<longrightarrow> Std (filter notIde (map \<Lambda>.un_App2 U)))"
        proof (intro conjI impI)
          assume u2: "\<Lambda>.Ide u2"
          show "Std (filter notIde (map \<Lambda>.un_App2 U))"
            by (metis 1 Std.simps(1) Std.simps(3) ind neq_Nil_conv)
          next
          assume u2: "\<not> \<Lambda>.Ide u2"
          show "Std (u2 # filter notIde (map \<Lambda>.un_App2 U))"
          proof (cases "Ide (map \<Lambda>.un_App2 U)")
            show "Ide (map \<Lambda>.un_App2 U) \<Longrightarrow> ?thesis"
            proof -
              assume U: "Ide (map \<Lambda>.un_App2 U)"
              have "filter notIde (map \<Lambda>.un_App2 U) = []"
                by (metis U Ide_char filter_False \<Lambda>.ide_char mem_Collect_eq subsetD)
              thus ?thesis
                by (metis Std.elims(1) Std.simps(2) \<Lambda>.elementary_reduction.simps(4) list.discI
                    list.sel(1) \<Lambda>.sseq_imp_elementary_reduction1 u2 uU)
            qed
            assume U: "\<not> Ide (map \<Lambda>.un_App2 U)"
            show ?thesis
            proof (cases "U = []")
              show "U = [] \<Longrightarrow> ?thesis"
                using "1" u u2 by fastforce
              assume "U \<noteq> []"
              hence U: "U \<noteq> [] \<and> \<not> Ide (map \<Lambda>.un_App2 U)"
                using U by simp
              have "\<Lambda>.sseq u2 (hd (filter notIde (map \<Lambda>.un_App2 U)))"
              proof -
                have "\<And>u1 u2. \<lbrakk>set U \<subseteq> Collect \<Lambda>.is_App; \<not> Ide (map \<Lambda>.un_App2 U); U \<noteq> [];
                               Std ((u1 \<^bold>\<circ> u2) # U); \<not> \<Lambda>.Ide u2\<rbrakk>
                                   \<Longrightarrow> \<Lambda>.sseq u2 (hd (filter notIde (map \<Lambda>.un_App2 U)))"
                  for U
                  apply (induct U)
                  apply simp_all
                  apply (intro conjI impI)
                proof -
                  fix u U u1 u2
                  assume ind: "\<And>u1 u2. \<lbrakk>\<not> Ide (map \<Lambda>.un_App2 U); U \<noteq> [];
                                        Std ((u1 \<^bold>\<circ> u2) # U); \<not> \<Lambda>.Ide u2\<rbrakk>
                                          \<Longrightarrow> \<Lambda>.sseq u2 (hd (filter notIde (map \<Lambda>.un_App2 U)))"
                  assume 1: "\<Lambda>.is_App u \<and> set U \<subseteq> Collect \<Lambda>.is_App"
                  assume 2: "\<not> Ide (\<Lambda>.un_App2 u # map \<Lambda>.un_App2 U)"
                  assume 3: "\<Lambda>.sseq (u1 \<^bold>\<circ> u2) u \<and> Std (u # U)"
                  assume 4: "\<not> \<Lambda>.Ide u2"
                  show "\<not> \<Lambda>.Ide (\<Lambda>.un_App2 u) \<Longrightarrow> \<Lambda>.sseq u2 (\<Lambda>.un_App2 u)"
                    by (metis 1 3 4 \<Lambda>.elementary_reduction.simps(4)
                        \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char \<Lambda>.lambda.collapse(3)
                        \<Lambda>.sseq.simps(4) \<Lambda>.sseq_imp_elementary_reduction1)
                  assume 5: "\<Lambda>.Ide (\<Lambda>.un_App2 u)"
                  have False
                    by (metis 1 3 4 5 \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char
                        \<Lambda>.lambda.collapse(3) \<Lambda>.sseq.simps(4) \<Lambda>.sseq_imp_elementary_reduction2)
                  thus "\<Lambda>.sseq u2 (hd (filter notIde (map \<Lambda>.un_App2 U)))" by argo
                qed
                thus ?thesis
                  using U set u2 uU by blast
              qed
              thus ?thesis
                by (metis "1" Std.simps(2) Std.simps(3) \<open>U \<noteq> []\<close> ind list.exhaust_sel list.sel(1)
                    \<Lambda>.sseq_imp_elementary_reduction1)
            qed
          qed
        qed
      qed
    qed

    text \<open>
      If the first step in a standard reduction path contracts a redex that is
      not at the head position, then all subsequent terms have \<open>App\<close> as their
      top-level operator.
    \<close>

    lemma seq_App_Std_implies:
    shows "\<lbrakk>Std (t # U); \<Lambda>.is_App t \<and> \<not> \<Lambda>.contains_head_reduction t\<rbrakk>
              \<Longrightarrow> set U \<subseteq> Collect \<Lambda>.is_App"
    proof (induct U arbitrary: t)
      show "\<And>t. \<lbrakk>Std [t]; \<Lambda>.is_App t \<and> \<not> \<Lambda>.contains_head_reduction t\<rbrakk>
                   \<Longrightarrow> set [] \<subseteq> Collect \<Lambda>.is_App"
        by simp
      fix t u U
      assume ind: "\<And>t. \<lbrakk>Std (t # U); \<Lambda>.is_App t \<and> \<not> \<Lambda>.contains_head_reduction t\<rbrakk>
                           \<Longrightarrow> set U \<subseteq> Collect \<Lambda>.is_App"
      assume Std: "Std (t # u # U)"
      assume t: "\<Lambda>.is_App t \<and> \<not> \<Lambda>.contains_head_reduction t"
      have U: "set (u # U) \<subseteq> Collect \<Lambda>.elementary_reduction"
        using Std Std_implies_set_subset_elementary_reduction by fastforce
      have u: "\<Lambda>.elementary_reduction u"
        using U by simp
      have "set U \<subseteq> Collect \<Lambda>.elementary_reduction"
        using U by simp
      show "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
      proof (cases "U = []")
        show "U = [] \<Longrightarrow> ?thesis"
          by (metis Std empty_set empty_subsetI insert_subset
              \<Lambda>.sseq_preserves_App_and_no_head_reduction list.sel(1) list.simps(15)
              mem_Collect_eq reduction_paths.Std.simps(3) t)
        assume U: "U \<noteq> []"
        have "\<Lambda>.sseq t u"
          using Std by auto
        hence "\<Lambda>.is_App u \<and> \<not> \<Lambda>.Ide u \<and> \<not> \<Lambda>.contains_head_reduction u"
          using t u U \<Lambda>.sseq_preserves_App_and_no_head_reduction [of t u]
                \<Lambda>.elementary_reduction_not_ide
          by blast
        thus ?thesis
          using Std ind [of u] \<open>set U \<subseteq> Collect \<Lambda>.elementary_reduction\<close> by simp
      qed
    qed

    subsection "Standard Developments"

    text \<open>
      The following function takes a term \<open>t\<close> (representing a parallel reduction)
      and produces a standard reduction path that is a complete development of \<open>t\<close>
      and is thus congruent to \<open>[t]\<close>.  The proof of termination makes use of the
      Finite Development Theorem.
    \<close>

    function (sequential) standard_development
    where "standard_development \<^bold>\<sharp> = []"
        | "standard_development \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> = []"
        | "standard_development \<^bold>\<lambda>\<^bold>[t\<^bold>] = map \<Lambda>.Lam (standard_development t)"
        | "standard_development (t \<^bold>\<circ> u) =
           (if \<Lambda>.Arr t \<and> \<Lambda>.Arr u then
              map (\<lambda>v. v \<^bold>\<circ> \<Lambda>.Src u) (standard_development t) @
              map (\<lambda>v. \<Lambda>.Trg t \<^bold>\<circ> v) (standard_development u)
            else [])"
        | "standard_development (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) =
           (if \<Lambda>.Arr t \<and> \<Lambda>.Arr u then
              (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) # standard_development (\<Lambda>.subst u t)
            else [])"
      by pat_completeness auto

    abbreviation (in lambda_calculus) stddev_term_rel
    where "stddev_term_rel \<equiv> mlex_prod hgt subterm_rel"

    lemma (in lambda_calculus) subst_lt_Beta:
    assumes "Arr t" and "Arr u"
    shows "(subst u t, \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<in> stddev_term_rel"
    proof -
      have "(\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \\ (\<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u) = subst u t"
        using assms
        by (metis Arr_not_Nil Ide_Src Ide_iff_Src_self Ide_implies_Arr resid.simps(4)
            resid_Arr_Ide)
      moreover have "elementary_reduction (\<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u)"
        by (simp add: assms Ide_Src)
      moreover have "\<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u \<sqsubseteq> \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u"
        by (metis assms Arr.simps(5) head_redex.simps(9) subs_head_redex)
      ultimately show ?thesis
        using assms elementary_reduction_decreases_hgt [of "\<^bold>\<lambda>\<^bold>[Src t\<^bold>] \<^bold>\<Zspot> Src u" "\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u"]
        by (metis mlex_less)
    qed

    termination standard_development
    proof (relation \<Lambda>.stddev_term_rel)
      show "wf \<Lambda>.stddev_term_rel"
        using \<Lambda>.wf_subterm_rel wf_mlex by blast
      show "\<And>t. (t, \<^bold>\<lambda>\<^bold>[t\<^bold>]) \<in> \<Lambda>.stddev_term_rel"
        by (simp add: \<Lambda>.subterm_lemmas(1) mlex_prod_def)
      show "\<And>t u. (t, t \<^bold>\<circ> u) \<in> \<Lambda>.stddev_term_rel"
        using \<Lambda>.subterm_lemmas(3)
        by (metis antisym_conv1 \<Lambda>.hgt.simps(4) le_add1 mem_Collect_eq mlex_iff old.prod.case)
      show "\<And>t u. (u, t \<^bold>\<circ> u) \<in> \<Lambda>.stddev_term_rel"
        using \<Lambda>.subterm_lemmas(3) by (simp add: mlex_leq)
      show "\<And>t u. \<Lambda>.Arr t \<and> \<Lambda>.Arr u \<Longrightarrow> (\<Lambda>.subst u t, \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<in> \<Lambda>.stddev_term_rel"
        using \<Lambda>.subst_lt_Beta by simp
    qed

    lemma Ide_iff_standard_development_empty:
    shows "\<Lambda>.Arr t \<Longrightarrow> \<Lambda>.Ide t \<longleftrightarrow> standard_development t = []"
      by (induct t) auto

    lemma set_standard_development:
    shows "\<Lambda>.Arr t \<longrightarrow> set (standard_development t) \<subseteq> Collect \<Lambda>.elementary_reduction"
      apply (rule standard_development.induct)
      using \<Lambda>.Ide_Src \<Lambda>.Ide_Trg \<Lambda>.Arr_Subst by auto

    lemma cong_standard_development:
    shows "\<Lambda>.Arr t \<and> \<not> \<Lambda>.Ide t \<longrightarrow> standard_development t \<^sup>*\<sim>\<^sup>* [t]"
    proof (rule standard_development.induct)
     show "\<Lambda>.Arr \<^bold>\<sharp> \<and> \<not> \<Lambda>.Ide \<^bold>\<sharp> \<longrightarrow> standard_development \<^bold>\<sharp> \<^sup>*\<sim>\<^sup>* [\<^bold>\<sharp>]"
        by simp
      show "\<And>x. \<Lambda>.Arr \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<and> \<not> \<Lambda>.Ide \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>
                  \<longrightarrow> standard_development \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^sup>*\<sim>\<^sup>* [\<^bold>\<guillemotleft>x\<^bold>\<guillemotright>]"
        by simp
      show "\<And>t. \<Lambda>.Arr t \<and> \<not> \<Lambda>.Ide t \<longrightarrow> standard_development t \<^sup>*\<sim>\<^sup>* [t] \<Longrightarrow>
                \<Lambda>.Arr \<^bold>\<lambda>\<^bold>[t\<^bold>] \<and> \<not> \<Lambda>.Ide \<^bold>\<lambda>\<^bold>[t\<^bold>] \<longrightarrow> standard_development \<^bold>\<lambda>\<^bold>[t\<^bold>] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>]]"
        by (metis (mono_tags, lifting) cong_map_Lam \<Lambda>.Arr.simps(3) \<Lambda>.Ide.simps(3)
            list.simps(8,9) standard_development.simps(3))
      show "\<And>t u. \<lbrakk>\<Lambda>.Arr t \<and> \<Lambda>.Arr u
                     \<Longrightarrow> \<Lambda>.Arr t \<and> \<not> \<Lambda>.Ide t \<longrightarrow> standard_development t \<^sup>*\<sim>\<^sup>* [t];
                   \<Lambda>.Arr t \<and> \<Lambda>.Arr u
                     \<Longrightarrow> \<Lambda>.Arr u \<and> \<not> \<Lambda>.Ide u \<longrightarrow> standard_development u \<^sup>*\<sim>\<^sup>* [u]\<rbrakk>
                       \<Longrightarrow> \<Lambda>.Arr (t \<^bold>\<circ> u) \<and> \<not> \<Lambda>.Ide (t \<^bold>\<circ> u) \<longrightarrow>
                             standard_development (t \<^bold>\<circ> u) \<^sup>*\<sim>\<^sup>* [t \<^bold>\<circ> u]"
      proof
        fix t u
        assume ind1: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u
                        \<Longrightarrow> \<Lambda>.Arr t \<and> \<not> \<Lambda>.Ide t \<longrightarrow> standard_development t \<^sup>*\<sim>\<^sup>* [t]"
        assume ind2: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u
                        \<Longrightarrow> \<Lambda>.Arr u \<and> \<not> \<Lambda>.Ide u \<longrightarrow> standard_development u \<^sup>*\<sim>\<^sup>* [u]"
        assume 1: "\<Lambda>.Arr (t \<^bold>\<circ> u) \<and> \<not> \<Lambda>.Ide (t \<^bold>\<circ> u)"
        show "standard_development (t \<^bold>\<circ> u) \<^sup>*\<sim>\<^sup>* [t \<^bold>\<circ> u]"
        proof (cases "standard_development t = []")
          show "standard_development t = [] \<Longrightarrow> ?thesis"
            using 1 ind2 cong_map_App1 Ide_iff_standard_development_empty \<Lambda>.Ide_iff_Trg_self
            apply simp
            by (metis (no_types, opaque_lifting) list.simps(8,9))
          assume t: "standard_development t \<noteq> []"
          show ?thesis
          proof (cases "standard_development u = []")
            assume u: "standard_development u = []"
            have "standard_development (t \<^bold>\<circ> u) = map (\<lambda>X. X \<^bold>\<circ> u) (standard_development t)"
              using u 1 \<Lambda>.Ide_iff_Src_self ide_char ind2 by auto
            also have "... \<^sup>*\<sim>\<^sup>* map (\<lambda>a. a \<^bold>\<circ> u) [t]"
              using cong_map_App2 [of u]
              by (meson 1 \<Lambda>.Arr.simps(4) Ide_iff_standard_development_empty t u ind1)
            also have "map (\<lambda>a. a \<^bold>\<circ> u) [t] = [t \<^bold>\<circ> u]"
              by simp
            finally show ?thesis by blast
            next
            assume u: "standard_development u \<noteq> []"
            have "standard_development (t \<^bold>\<circ> u) =
                  map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t) @
                  map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u)"
              using 1 by force
            moreover have "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t) \<^sup>*\<sim>\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src u]"
            proof -
              have "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t) \<^sup>*\<sim>\<^sup>* map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) [t]"
                using t u 1 ind1 \<Lambda>.Ide_Src Ide_iff_standard_development_empty cong_map_App2
                by (metis \<Lambda>.Arr.simps(4))
              also have "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) [t] = [t \<^bold>\<circ> \<Lambda>.Src u]"
                by simp
              finally show ?thesis by blast
            qed
            moreover have "map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u) \<^sup>*\<sim>\<^sup>* [\<Lambda>.Trg t \<^bold>\<circ> u]"
              using t u 1 ind2 \<Lambda>.Ide_Trg Ide_iff_standard_development_empty cong_map_App1
              by (metis (mono_tags, opaque_lifting) \<Lambda>.Arr.simps(4) list.simps(8,9))
            moreover have "seq (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t))
                               (map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u))"
            proof
              show "Arr (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t))"
                by (metis Con_implies_Arr(1) Ide.simps(1) calculation(2) ide_char)
              show "Arr (map ((\<^bold>\<circ>) (\<Lambda>.Trg t)) (standard_development u))"
                by (metis Con_implies_Arr(1) Ide.simps(1) calculation(3) ide_char)
              show "\<Lambda>.Trg (last (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t))) =
                    \<Lambda>.Src (hd (map ((\<^bold>\<circ>) (\<Lambda>.Trg t)) (standard_development u)))"
                using 1 Src_hd_eqI Trg_last_eqI calculation(2) calculation(3) by auto
            qed
            ultimately have "standard_development (t \<^bold>\<circ> u) \<^sup>*\<sim>\<^sup>* [t \<^bold>\<circ> \<Lambda>.Src u] @ [\<Lambda>.Trg t \<^bold>\<circ> u]"
              using cong_append [of "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t)"
                                    "map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u)"
                                    "[t \<^bold>\<circ> \<Lambda>.Src u]" "[\<Lambda>.Trg t \<^bold>\<circ> u]"]
              by simp
            moreover have "[t \<^bold>\<circ> \<Lambda>.Src u] @ [\<Lambda>.Trg t \<^bold>\<circ> u] \<^sup>*\<sim>\<^sup>* [t \<^bold>\<circ> u]"
              using 1 \<Lambda>.Ide_Trg \<Lambda>.resid_Arr_Src \<Lambda>.resid_Arr_self \<Lambda>.null_char
                    ide_char \<Lambda>.Arr_not_Nil
              by simp
            ultimately show ?thesis
              using cong_transitive by blast
          qed
        qed
      qed
      show "\<And>t u. (\<Lambda>.Arr t \<and> \<Lambda>.Arr u \<Longrightarrow>
                     \<Lambda>.Arr (\<Lambda>.subst u t) \<and> \<not> \<Lambda>.Ide (\<Lambda>.subst u t)
                         \<longrightarrow> standard_development (\<Lambda>.subst u t) \<^sup>*\<sim>\<^sup>* [\<Lambda>.subst u t]) \<Longrightarrow>
                   \<Lambda>.Arr (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<and> \<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<longrightarrow>
                     standard_development (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
      proof
        fix t u
        assume 1: "\<Lambda>.Arr (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<and> \<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
        assume ind: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u \<Longrightarrow>
                       \<Lambda>.Arr (\<Lambda>.subst u t) \<and> \<not> \<Lambda>.Ide (\<Lambda>.subst u t)
                          \<longrightarrow> standard_development (\<Lambda>.subst u t) \<^sup>*\<sim>\<^sup>* [\<Lambda>.subst u t]"
        show "standard_development (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
        proof (cases "\<Lambda>.Ide (\<Lambda>.subst u t)")
          assume 2: "\<Lambda>.Ide (\<Lambda>.subst u t)"
          have "standard_development (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) = [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u]"
            using 1 2 Ide_iff_standard_development_empty [of "\<Lambda>.subst u t"] \<Lambda>.Arr_Subst
            by simp
          also have "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
            using 1 2 \<Lambda>.Ide_Src \<Lambda>.Ide_implies_Arr ide_char \<Lambda>.resid_Arr_Ide
            apply (intro conjI)
             apply simp_all
             apply (metis \<Lambda>.Ide.simps(1) \<Lambda>.Ide_Subst_iff \<Lambda>.Ide_Trg)
            by fastforce
          finally show ?thesis by blast
          next
          assume 2: "\<not> \<Lambda>.Ide (\<Lambda>.subst u t)"
          have "standard_development (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) =
                [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ standard_development (\<Lambda>.subst u t)"
            using 1 by auto
          also have "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ standard_development (\<Lambda>.subst u t) \<^sup>*\<sim>\<^sup>*
                     [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t]"
          proof (intro cong_append)
            show "seq [\<Lambda>.Beta (\<Lambda>.Src t) (\<Lambda>.Src u)] (standard_development (\<Lambda>.subst u t))"
              using 1 2 ind arr_char ide_implies_arr \<Lambda>.Arr_Subst Con_implies_Arr(1) Src_hd_eqI
              apply (intro seqI\<^sub>\<Lambda>\<^sub>P)
                apply simp_all
              by (metis Arr.simps(1))
            show "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u]"
              using 1
              by (metis \<Lambda>.Arr.simps(5) \<Lambda>.Ide_Src \<Lambda>.Ide_implies_Arr Arr.simps(2) Resid_Arr_self
                  ide_char \<Lambda>.arr_char)
            show "standard_development (\<Lambda>.subst u t) \<^sup>*\<sim>\<^sup>* [\<Lambda>.subst u t]"
              using 1 2 \<Lambda>.Arr_Subst ind by simp
          qed
          also have "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
          proof
            show "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t] \<^sup>*\<lesssim>\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"
            proof -
              have "t \\ \<Lambda>.Src t \<noteq> \<^bold>\<sharp> \<and> u \\ \<Lambda>.Src u \<noteq> \<^bold>\<sharp>"
                by (metis "1" \<Lambda>.Arr.simps(5) \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src \<Lambda>.Ide_iff_Src_self
                    \<Lambda>.Ide_implies_Arr)
              moreover have "\<Lambda>.con (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
                by (metis "1" \<Lambda>.head_redex.simps(9) \<Lambda>.prfx_implies_con \<Lambda>.subs_head_redex
                    \<Lambda>.subs_implies_prfx)
              ultimately have "([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t]) \<^sup>*\\\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] =
                               [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] \<^sup>*\\\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] @
                                 [\<Lambda>.subst u t] \<^sup>*\\\<^sup>* ([\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] \<^sup>*\\\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u])"
                using Resid_append(1)
                        [of "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u]" "[\<Lambda>.subst u t]" "[\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u]"]
                apply simp
                by (metis \<Lambda>.Arr_Subst \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src \<Lambda>.resid_Arr_Ide)
              also have "... = [\<Lambda>.subst (\<Lambda>.Trg u) (\<Lambda>.Trg t)] @ ([\<Lambda>.subst u t] \<^sup>*\\\<^sup>* [\<Lambda>.subst u t])"
              proof -
                have "t \\ \<Lambda>.Src t \<noteq> \<^bold>\<sharp> \<and> u \\ \<Lambda>.Src u \<noteq> \<^bold>\<sharp>"
                  by (metis "1" \<Lambda>.Arr.simps(5) \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src
                      \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr)
                moreover have "\<Lambda>.Src t \\ t \<noteq> \<^bold>\<sharp> \<and> \<Lambda>.Src u \\ u \<noteq> \<^bold>\<sharp>"
                  using \<Lambda>.Con_sym calculation(1) by presburger
                moreover have "\<Lambda>.con (\<Lambda>.subst u t) (\<Lambda>.subst u t)"
                  by (meson \<Lambda>.Arr_Subst \<Lambda>.Con_implies_Arr2 \<Lambda>.arr_char \<Lambda>.arr_def calculation(2))
                moreover have "\<Lambda>.con (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u)"
                  using \<open>\<Lambda>.con (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)\<close> \<Lambda>.con_sym by blast
                moreover have "\<Lambda>.con (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)"
                  using \<open>\<Lambda>.con (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u)\<close> by blast
                moreover have "\<Lambda>.con (\<Lambda>.subst u t) (\<Lambda>.subst (u \\ \<Lambda>.Src u) (t \\ \<Lambda>.Src t))"
                  by (metis \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src calculation(1-3) \<Lambda>.resid_Arr_Ide)
                ultimately show ?thesis
                  using "1" by auto
              qed
              finally have "([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t]) \<^sup>*\\\<^sup>* [\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] =
                            [\<Lambda>.subst (\<Lambda>.Trg u) (\<Lambda>.Trg t)] @ [\<Lambda>.subst u t] \<^sup>*\\\<^sup>* [\<Lambda>.subst u t]"
                by blast
              moreover have "Ide ..."
                by (metis "1" "2" \<Lambda>.Arr.simps(5) \<Lambda>.Arr_Subst \<Lambda>.Ide_Subst \<Lambda>.Ide_Trg
                    Nil_is_append_conv Arr_append_iff\<^sub>P\<^sub>W\<^sub>E Con_implies_Arr(2) Ide.simps(1-2)
                    Ide_appendI\<^sub>P\<^sub>W\<^sub>E Resid_Arr_self ide_char calculation \<Lambda>.ide_char ind
                    Con_imp_Arr_Resid)
              ultimately show ?thesis
                using ide_char by presburger
            qed
            show "[\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] \<^sup>*\<lesssim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t]"
            proof -
              have "[\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] \<^sup>*\\\<^sup>* ([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t]) =
                    ([\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] \<^sup>*\\\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u]) \<^sup>*\\\<^sup>* [\<Lambda>.subst u t]"
                by fastforce
              also have "... = [\<Lambda>.subst u t] \<^sup>*\\\<^sup>* [\<Lambda>.subst u t]"
              proof -
                have "t \\ \<Lambda>.Src t \<noteq> \<^bold>\<sharp> \<and> u \\ \<Lambda>.Src u \<noteq> \<^bold>\<sharp>"
                  by (metis "1" \<Lambda>.Arr.simps(5) \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src
                      \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr)
                moreover have "\<Lambda>.con (\<Lambda>.subst u t) (\<Lambda>.subst u t)"
                  by (metis "1" \<Lambda>.Arr.simps(5) \<Lambda>.Arr_Subst \<Lambda>.Coinitial_iff_Con
                      \<Lambda>.con_def \<Lambda>.null_char)
                moreover have "\<Lambda>.con (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u)"
                  by (metis "1" \<Lambda>.Con_sym \<Lambda>.con_def \<Lambda>.head_redex.simps(9) \<Lambda>.null_char
                      \<Lambda>.prfx_implies_con \<Lambda>.subs_head_redex \<Lambda>.subs_implies_prfx)
                moreover have "\<Lambda>.con (\<Lambda>.subst (u \\ \<Lambda>.Src u) (t \\ \<Lambda>.Src t)) (\<Lambda>.subst u t)"
                  by (metis \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src calculation(1) calculation(2)
                      \<Lambda>.resid_Arr_Ide)
                ultimately show ?thesis
                  using \<Lambda>.resid_Arr_Ide
                  apply simp
                  by (metis \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src)
              qed
              finally have "[\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u] \<^sup>*\\\<^sup>* ([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u] @ [\<Lambda>.subst u t]) =
                            [\<Lambda>.subst u t] \<^sup>*\\\<^sup>* [\<Lambda>.subst u t]"
                by blast
              moreover have "Ide ..."
                by (metis "1" "2" \<Lambda>.Arr.simps(5) \<Lambda>.Arr_Subst Con_implies_Arr(2) Resid_Arr_self
                    ind ide_char)
              ultimately show ?thesis
                using ide_char by presburger
            qed
          qed
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma Src_hd_standard_development:
    assumes "\<Lambda>.Arr t" and "\<not> \<Lambda>.Ide t"
    shows "\<Lambda>.Src (hd (standard_development t)) = \<Lambda>.Src t"
      by (metis assms Src_hd_eqI cong_standard_development list.sel(1))

    lemma Trg_last_standard_development:
    assumes "\<Lambda>.Arr t" and "\<not> \<Lambda>.Ide t"
    shows "\<Lambda>.Trg (last (standard_development t)) = \<Lambda>.Trg t"
      by (metis assms Trg_last_eqI cong_standard_development last_ConsL)

    lemma Srcs_standard_development:
    shows "\<lbrakk>\<Lambda>.Arr t; standard_development t \<noteq> []\<rbrakk>
              \<Longrightarrow> Srcs (standard_development t) = {\<Lambda>.Src t}"
      by (metis Con_implies_Arr(1) Ide.simps(1) Ide_iff_standard_development_empty
          Src_hd_standard_development Srcs_simp\<^sub>\<Lambda>\<^sub>P cong_standard_development ide_char)

    lemma Trgs_standard_development:
    shows "\<lbrakk>\<Lambda>.Arr t; standard_development t \<noteq> []\<rbrakk>
              \<Longrightarrow> Trgs (standard_development t) = {\<Lambda>.Trg t}"
      by (metis Con_implies_Arr(2) Ide.simps(1) Ide_iff_standard_development_empty
          Trg_last_standard_development Trgs_simp\<^sub>\<Lambda>\<^sub>P cong_standard_development ide_char)

    lemma development_standard_development:
    shows "\<Lambda>.Arr t \<longrightarrow> development t (standard_development t)"
      apply (rule standard_development.induct)
          apply blast
         apply simp
        apply (simp add: development_map_Lam)
    proof
      fix t1 t2
      assume ind1: "\<Lambda>.Arr t1 \<and> \<Lambda>.Arr t2
                       \<Longrightarrow> \<Lambda>.Arr t1 \<longrightarrow> development t1 (standard_development t1)"
      assume ind2: "\<Lambda>.Arr t1 \<and> \<Lambda>.Arr t2
                       \<Longrightarrow> \<Lambda>.Arr t2 \<longrightarrow> development t2 (standard_development t2)"
      assume t: "\<Lambda>.Arr (t1 \<^bold>\<circ> t2)"
      show "development (t1 \<^bold>\<circ> t2) (standard_development (t1 \<^bold>\<circ> t2))"
      proof (cases "standard_development t1 = []")
        show "standard_development t1 = []
                \<Longrightarrow> development (t1 \<^bold>\<circ> t2) (standard_development (t1 \<^bold>\<circ> t2))"
          using t ind2 \<Lambda>.Ide_Src \<Lambda>.Ide_Trg \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self
                Ide_iff_standard_development_empty
                development_map_App_2 [of "\<Lambda>.Src t1" t2 "standard_development t2"]
          by fastforce
        assume t1: "standard_development t1 \<noteq> []"
        show "development (t1 \<^bold>\<circ> t2) (standard_development (t1 \<^bold>\<circ> t2))"
        proof (cases "standard_development t2 = []")
          assume t2: "standard_development t2 = []"
          show ?thesis
            using t t2 ind1 Ide_iff_standard_development_empty development_map_App_1 by simp
          next
          assume t2: "standard_development t2 \<noteq> []"
          have "development (t1 \<^bold>\<circ> t2) (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1))"
            using \<Lambda>.Arr.simps(4) development_map_App_1 ind1 t by presburger
          moreover have "development ((t1 \<^bold>\<circ> t2) \<^sup>1\\\<^sup>*
                                        map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1))
                                     (map (\<lambda>a. \<Lambda>.Trg t1 \<^bold>\<circ> a) (standard_development t2))"
          proof -
            have "\<Lambda>.App t1 t2 \<^sup>1\\\<^sup>* map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1) =
                  \<Lambda>.Trg t1 \<^bold>\<circ> t2"
            proof -
              have "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1) \<^sup>*\<sim>\<^sup>* [t1 \<^bold>\<circ> \<Lambda>.Src t2]"
              proof -
                have "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1) =
                      standard_development (t1 \<^bold>\<circ> \<Lambda>.Src t2)"
                  by (metis \<Lambda>.Arr.simps(4) \<Lambda>.Ide_Src \<Lambda>.Ide_iff_Src_self
                      Ide_iff_standard_development_empty \<Lambda>.Ide_implies_Arr Nil_is_map_conv
                      append_Nil2 standard_development.simps(4) t)
                also have "standard_development (t1 \<^bold>\<circ> \<Lambda>.Src t2) \<^sup>*\<sim>\<^sup>* [t1 \<^bold>\<circ> \<Lambda>.Src t2]"
                  by (metis \<Lambda>.Arr.simps(4) \<Lambda>.Ide.simps(4) \<Lambda>.Ide_Src \<Lambda>.Ide_implies_Arr
                      cong_standard_development development_Ide ind1 t t1)
                finally show ?thesis by blast
              qed
              hence "[t1 \<^bold>\<circ> t2] \<^sup>*\\\<^sup>* map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1) =
                     [t1 \<^bold>\<circ> t2] \<^sup>*\\\<^sup>* [t1 \<^bold>\<circ> \<Lambda>.Src t2]"
                by (metis Resid_parallel con_imp_coinitial prfx_implies_con calculation
                    development_implies map_is_Nil_conv t1)
              also have "[t1 \<^bold>\<circ> t2] \<^sup>*\\\<^sup>* [t1 \<^bold>\<circ> \<Lambda>.Src t2] = [\<Lambda>.Trg t1 \<^bold>\<circ> t2]"
                using t \<Lambda>.arr_resid_iff_con \<Lambda>.resid_Arr_self
                by simp force
              finally have "[t1 \<^bold>\<circ> t2] \<^sup>*\\\<^sup>* map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1) =
                            [\<Lambda>.Trg t1 \<^bold>\<circ> t2]"
                by blast
              thus ?thesis
                by (simp add: Resid1x_as_Resid')
            qed
            thus ?thesis
              by (metis ind2 \<Lambda>.Arr.simps(4) \<Lambda>.Ide_Trg \<Lambda>.Ide_iff_Src_self development_map_App_2
                  \<Lambda>.reduction_strategy_def \<Lambda>.head_strategy_is_reduction_strategy t)
          qed
          ultimately show ?thesis
            using t development_append [of "t1 \<^bold>\<circ> t2"
                                           "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src t2) (standard_development t1)"
                                           "map (\<lambda>b. \<Lambda>.Trg t1 \<^bold>\<circ> b) (standard_development t2)"]
            by auto
        qed
      qed
      next
      fix t1 t2
      assume ind: "\<Lambda>.Arr t1 \<and> \<Lambda>.Arr t2 \<Longrightarrow>
                     \<Lambda>.Arr (\<Lambda>.subst t2 t1)
                        \<longrightarrow> development (\<Lambda>.subst t2 t1) (standard_development (\<Lambda>.subst t2 t1))"
      show "\<Lambda>.Arr (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) \<longrightarrow> development (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) (standard_development (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2))"
      proof
        assume 1: "\<Lambda>.Arr (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)"
        have "development (\<Lambda>.subst t2 t1) (standard_development (\<Lambda>.subst t2 t1))"
          using 1 ind by (simp add: \<Lambda>.Arr_Subst)
        thus "development (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) (standard_development (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2))"
          using 1 \<Lambda>.Ide_Src \<Lambda>.subs_Ide by auto
      qed
    qed

    lemma Std_standard_development:
    shows "Std (standard_development t)"
      apply (rule standard_development.induct)
          apply simp_all
      using Std_map_Lam
        apply blast
    proof
      fix t u
      assume t: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u \<Longrightarrow> Std (standard_development t)"
      assume u: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u \<Longrightarrow> Std (standard_development u)"
      assume 0: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u"
      show "Std (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t) @
                 map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u))"
      proof (cases "\<Lambda>.Ide t")
        show "\<Lambda>.Ide t \<Longrightarrow> ?thesis"
          using 0 \<Lambda>.Ide_iff_Trg_self Ide_iff_standard_development_empty u Std_map_App2
          by fastforce
        assume 1: "\<not> \<Lambda>.Ide t"
        show ?thesis
        proof (cases "\<Lambda>.Ide u")
          show "\<Lambda>.Ide u \<Longrightarrow> ?thesis"
            using t u 0 1 Std_map_App1 [of "\<Lambda>.Src u" "standard_development t"] \<Lambda>.Ide_Src
            by (metis Ide_iff_standard_development_empty append_Nil2 list.simps(8))
          assume 2: "\<not> \<Lambda>.Ide u"
          show ?thesis
          proof (intro Std_append)
            show 3: "Std (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t))"
              using t 0 Std_map_App1 \<Lambda>.Ide_Src by blast
            show "Std (map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u))"
              using u 0 Std_map_App2 \<Lambda>.Ide_Trg by simp
            show "map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t) = [] \<or>
                  map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u) = [] \<or>
                  \<Lambda>.sseq (last (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t)))
                       (hd (map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u)))"
            proof -
              have "\<Lambda>.sseq (last (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t)))
                           (hd (map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u)))"
              proof -
                obtain x where x: "last (map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u) (standard_development t)) =
                                   x \<^bold>\<circ> \<Lambda>.Src u"
                  using 0 1 Ide_iff_standard_development_empty last_map by auto
                obtain y where y: "hd (map (\<lambda>b. \<Lambda>.Trg t \<^bold>\<circ> b) (standard_development u)) =
                                   \<Lambda>.Trg t \<^bold>\<circ> y"
                  using 0 2 Ide_iff_standard_development_empty list.map_sel(1) by auto
                have "\<Lambda>.elementary_reduction x"
                proof -
                  have "\<Lambda>.elementary_reduction (x \<^bold>\<circ> \<Lambda>.Src u)"
                    using x
                    by (metis 0 1 3 Ide_iff_standard_development_empty Nil_is_map_conv Std.simps(2)
                        Std_imp_sseq_last_hd append_butlast_last_id append_self_conv2 list.discI
                        list.sel(1) \<Lambda>.sseq_imp_elementary_reduction2)
                  thus ?thesis
                    using 0 \<Lambda>.Ide_Src \<Lambda>.elementary_reduction_not_ide by auto
                qed
                moreover have "\<Lambda>.elementary_reduction y"
                proof -
                  have "\<Lambda>.elementary_reduction (\<Lambda>.Trg t \<^bold>\<circ> y)"
                    using y
                    by (metis 0 2 \<Lambda>.Ide_Trg Ide_iff_standard_development_empty
                        u Std.elims(2) \<Lambda>.elementary_reduction.simps(4) list.map_sel(1) list.sel(1)
                        \<Lambda>.sseq_imp_elementary_reduction1)
                  thus ?thesis
                    using 0 \<Lambda>.Ide_Trg \<Lambda>.elementary_reduction_not_ide by auto
                qed
                moreover have "\<Lambda>.Trg t = \<Lambda>.Trg x"
                  by (metis 0 1 Ide_iff_standard_development_empty Trg_last_standard_development
                      x \<Lambda>.lambda.inject(3) last_map)
                moreover have "\<Lambda>.Src u = \<Lambda>.Src y"
                  using y
                  by (metis 0 2 \<Lambda>.Arr_not_Nil \<Lambda>.Coinitial_iff_Con
                      Ide_iff_standard_development_empty development.elims(2) development_imp_Arr
                      development_standard_development \<Lambda>.lambda.inject(3) list.map_sel(1)
                      list.sel(1))
                ultimately show ?thesis
                  using x y by simp
              qed
              thus ?thesis by blast
            qed
          qed
        qed
      qed
      next
      fix t u
      assume ind: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u \<Longrightarrow> Std (standard_development (\<Lambda>.subst u t))"
      show "\<Lambda>.Arr t \<and> \<Lambda>.Arr u
              \<longrightarrow> Std ((\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) # standard_development (\<Lambda>.subst u t))"
      proof
        assume 1: "\<Lambda>.Arr t \<and> \<Lambda>.Arr u"
        show "Std ((\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) # standard_development (\<Lambda>.subst u t))"
        proof (cases "\<Lambda>.Ide (\<Lambda>.subst u t)")
          show "\<Lambda>.Ide (\<Lambda>.subst u t)
                  \<Longrightarrow> Std ((\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) # standard_development (\<Lambda>.subst u t))"
            using 1 \<Lambda>.Arr_Subst \<Lambda>.Ide_Src Ide_iff_standard_development_empty by simp
          assume 2: "\<not> \<Lambda>.Ide (\<Lambda>.subst u t)"
          show "Std ((\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) # standard_development (\<Lambda>.subst u t))"
          proof -
            have "\<Lambda>.sseq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) (hd (standard_development (\<Lambda>.subst u t)))"
            proof -
              have "\<Lambda>.elementary_reduction (hd (standard_development (\<Lambda>.subst u t)))"
                using ind
                by (metis 1 2 \<Lambda>.Arr_Subst Ide_iff_standard_development_empty
                    Std.elims(2) list.sel(1) \<Lambda>.sseq_imp_elementary_reduction1)
              moreover have "\<Lambda>.seq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u)
                                   (hd (standard_development (\<Lambda>.subst u t)))"
                using 1 2 Src_hd_standard_development calculation \<Lambda>.Arr.simps(5)
                       \<Lambda>.Arr_Src \<Lambda>.Arr_Subst \<Lambda>.Src_Subst \<Lambda>.Trg.simps(4) \<Lambda>.Trg_Src \<Lambda>.arr_char
                       \<Lambda>.elementary_reduction_is_arr \<Lambda>.seq_char
                by presburger
              ultimately show ?thesis
                using 1 \<Lambda>.Ide_Src \<Lambda>.sseq_Beta by auto
            qed
            moreover have "Std (standard_development (\<Lambda>.subst u t))"
              using 1 ind by blast
            ultimately show ?thesis
              by (metis 1 2 \<Lambda>.Arr_Subst Ide_iff_standard_development_empty Std.simps(3)
                  list.collapse)
          qed
        qed
      qed
    qed

    subsection "Standardization"

    text \<open>
      In this section, we define and prove correct a function that takes an arbitrary
      reduction path and produces a standard reduction path congruent to it.
      The method is roughly analogous to insertion sort: given a path, recursively
      standardize the tail and then ``insert'' the head into to the result.
      A complication is that in general the head may be a parallel reduction instead
      of an elementary reduction, and in any case elementary reductions are
      not preserved under residuation so we need to be able to handle the parallel
      reductions that arise from permuting elementary reductions.
      In general, this means that parallel reduction steps have to be decomposed into factors,
      and then each factor has to be inserted at its proper position.
      Another issue is that reductions don't all happen at the top level of a term,
      so we need to be able to descend recursively into terms during the insertion
      procedure.  The key idea here is: in a standard reduction, once a step has occurred
      that is not a head reduction, then all subsequent terms will have \<open>App\<close> as their
      top-level constructor.  So, once we have passed a step that is not a head reduction,
      we can recursively descend into the subsequent applications and treat the ``rator''
      and the ``rand'' parts independently.

      The following function performs the core insertion part of the standardization
      algorithm.  It assumes that it is given an arbitrary parallel reduction \<open>t\<close> and
      an already-standard reduction path \<open>U\<close>, and it inserts \<open>t\<close> into \<open>U\<close>, producing a
      standard reduction path that is congruent to \<open>t # U\<close>.  A somewhat elaborate case
      analysis is required to determine whether \<open>t\<close> needs to be factored and whether
      part of it might need to be permuted with the head of \<open>U\<close>.  The recursion is complicated
      by the need to make sure that the second argument \<open>U\<close> is always a standard reduction
      path.  This is so that it is possible to decide when the rest of the steps will be
      applications and it is therefore possible to recurse into them.  This constrains what
      recursive calls we can make, since we are not able to make a recursive call in which
      an identity has been prepended to \<open>U\<close>.  Also, if \<open>t # U\<close> consists completely of
      identities, then its standardization is the empty list \<open>[]\<close>, which is not a path
      and cannot be congruent to \<open>t # U\<close>.  So in order to be able to apply the induction
      hypotheses in the correctness proof, we need to make sure that we don't make
      recursive calls when \<open>U\<close> itself would consist entirely of identities.
      Finally, when we descend through an application, the step \<open>t\<close> and the path \<open>U\<close> are
      projected to their ``rator'' and ``rand'' components, which are treated separately
      and the results concatenated.  However, the projection operations can introduce
      identities and therefore do not preserve elementary reductions.  To handle this,
      we need to filter out identities after projection but before the recursive call.

      Ensuring termination also involves some care: we make recursive calls in which
      the length of the second argument is increased, but the ``height'' of the first
      argument is decreased.  So we use a lexicographic order that makes the height
      of the first argument more significant and the length of the second argument
      secondary.  The base cases either discard paths that consist entirely of
      identities, or else they expand a single parallel reduction \<open>t\<close> into a standard
      development.
    \<close>

    function (sequential) stdz_insert
    where "stdz_insert t [] = standard_development t"
        | "stdz_insert \<^bold>\<guillemotleft>_\<^bold>\<guillemotright> U = stdz_insert (hd U) (tl U)"
        | "stdz_insert \<^bold>\<lambda>\<^bold>[t\<^bold>] U =
           (if \<Lambda>.Ide t then
              stdz_insert (hd U) (tl U)
            else
              map \<Lambda>.Lam (stdz_insert t (map \<Lambda>.un_Lam U)))"
        | "stdz_insert (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<circ> u) ((\<^bold>\<lambda>\<^bold>[_\<^bold>] \<^bold>\<Zspot> _) # U) = stdz_insert (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) U"
        | "stdz_insert (t \<^bold>\<circ> u) U =
           (if \<Lambda>.Ide (t \<^bold>\<circ> u) then
              stdz_insert (hd U) (tl U)
            else if \<Lambda>.seq (t \<^bold>\<circ> u) (hd U) then
              if \<Lambda>.contains_head_reduction (t \<^bold>\<circ> u) then
                if \<Lambda>.Ide ((t \<^bold>\<circ> u) \\ \<Lambda>.head_redex (t \<^bold>\<circ> u)) then
                  \<Lambda>.head_redex (t \<^bold>\<circ> u) # stdz_insert (hd U) (tl U)
                else
                  \<Lambda>.head_redex (t \<^bold>\<circ> u) # stdz_insert ((t \<^bold>\<circ> u) \\ \<Lambda>.head_redex (t \<^bold>\<circ> u)) U
              else if \<Lambda>.contains_head_reduction (hd U) then
                if \<Lambda>.Ide ((t \<^bold>\<circ> u) \\ \<Lambda>.head_strategy (t \<^bold>\<circ> u)) then
                  stdz_insert (\<Lambda>.head_strategy (t \<^bold>\<circ> u)) (tl U)
                else
                  \<Lambda>.head_strategy (t \<^bold>\<circ> u) # stdz_insert ((t \<^bold>\<circ> u) \\ \<Lambda>.head_strategy (t \<^bold>\<circ> u)) (tl U)
              else
                map (\<lambda>a. a \<^bold>\<circ> \<Lambda>.Src u)
                    (stdz_insert t (filter notIde (map \<Lambda>.un_App1 U))) @
                map (\<lambda>b. \<Lambda>.Trg (\<Lambda>.un_App1 (last U)) \<^bold>\<circ> b)
                    (stdz_insert u (filter notIde (map \<Lambda>.un_App2 U)))
            else [])"
        | "stdz_insert (\<^bold>\<lambda>\<^bold>[t\<^bold>] \<^bold>\<Zspot> u) U =
           (if \<Lambda>.Arr t \<and> \<Lambda>.Arr u then
              (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src t\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src u) # stdz_insert (\<Lambda>.subst u t) U
            else [])"
        | "stdz_insert _ _ = []"
    by pat_completeness auto

    (*
     * TODO:
     * In the case "stdz_insert (M \<^bold>\<circ> N) U":
     *   The "if \<Lambda>.seq (M \<^bold>\<circ> N) (hd U)" is needed for the termination proof.
     *   The first "if \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N)))"
     *     cannot be removed because the resulting induction rule does not contain
     *     the induction hypotheses necessary to prove the correctness.
     *   The second "if \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N)))"
     *     results in a similar, but different problem.
     * In the case "stdz_insert (\<Lambda>.Beta M N) U":
     *   The "if \<Lambda>.Arr M \<and> \<Lambda>.Arr N" is needed for the termination proof.
     * It is possible that the function would still be correct if some of the tests
     *   for whether the term being inserted is an identity were omitted, but if these
     *   tests are removed, then the correctness proof fails ways that are not obviously
     *   repairable, probably due to the induction rule not having all the needed
     *   induction hypotheses.
     *)

    fun standardize
    where "standardize [] = []"
        | "standardize U = stdz_insert (hd U) (standardize (tl U))"

    abbreviation stdzins_rel
    where "stdzins_rel \<equiv> mlex_prod (length o snd) (inv_image (mlex_prod \<Lambda>.hgt \<Lambda>.subterm_rel) fst)"

    termination stdz_insert
      using \<Lambda>.subterm.intros(2-3) \<Lambda>.hgt_Subst less_Suc_eq_le \<Lambda>.elementary_reduction_decreases_hgt
            \<Lambda>.elementary_reduction_head_redex \<Lambda>.contains_head_reduction_iff
            \<Lambda>.elementary_reduction_is_arr \<Lambda>.Src_head_redex \<Lambda>.App_Var_contains_no_head_reduction
            \<Lambda>.hgt_resid_App_head_redex \<Lambda>.seq_char
      apply (relation stdzins_rel)
      apply (auto simp add: wf_mlex \<Lambda>.wf_subterm_rel mlex_iff mlex_less \<Lambda>.subterm_lemmas(1))
      by (meson dual_order.eq_iff length_filter_le not_less_eq_eq)+

    lemma stdz_insert_Ide:
    shows "Ide (t # U) \<Longrightarrow> stdz_insert t U = []"
    proof (induct U arbitrary: t)
      show "\<And>t. Ide [t] \<Longrightarrow> stdz_insert t [] = []"
        by (metis Ide_iff_standard_development_empty \<Lambda>.Ide_implies_Arr Ide.simps(2)
            \<Lambda>.ide_char stdz_insert.simps(1))
      show "\<And>U. \<lbrakk>\<And>t. Ide (t # U) \<Longrightarrow> stdz_insert t U = []; Ide (t # u # U)\<rbrakk>
                       \<Longrightarrow> stdz_insert t (u # U) = []"
        for t u
        using \<Lambda>.ide_char
        apply (cases t; cases u)
            apply simp_all
        by fastforce
    qed

    lemma stdz_insert_Ide_Std:
    shows "\<lbrakk>\<Lambda>.Ide u; seq [u] U; Std U\<rbrakk> \<Longrightarrow> stdz_insert u U = stdz_insert (hd U) (tl U)"
    proof (induct U arbitrary: u)
      show "\<And>u. \<lbrakk>\<Lambda>.Ide u; seq [u] []; Std []\<rbrakk> \<Longrightarrow> stdz_insert u [] = stdz_insert (hd []) (tl [])"
        by (simp add: seq_char)
      fix u v U
      assume u: "\<Lambda>.Ide u"
      assume seq: "seq [u] (v # U)"
      assume Std: "Std (v # U)"
      assume ind: "\<And>u. \<lbrakk>\<Lambda>.Ide u; seq [u] U; Std U\<rbrakk>
                          \<Longrightarrow> stdz_insert u U = stdz_insert (hd U) (tl U)"
      show "stdz_insert u (v # U) = stdz_insert (hd (v # U)) (tl (v # U))"
        using u ind stdz_insert_Ide Ide_implies_Arr
        apply (cases u; cases v)
                            apply simp_all
      proof -
        fix x y a b
        assume xy: "\<Lambda>.Ide x \<and> \<Lambda>.Ide y"
        assume u': "u = x \<^bold>\<circ> y"
        assume v': "v = \<^bold>\<lambda>\<^bold>[a\<^bold>] \<^bold>\<Zspot> b"
        have ab: "\<Lambda>.Ide a \<and> \<Lambda>.Ide b"
          using Std \<open>v = \<^bold>\<lambda>\<^bold>[a\<^bold>] \<^bold>\<Zspot> b\<close> Std.elims(2) \<Lambda>.sseq_Beta
          by (metis Std_consE \<Lambda>.elementary_reduction.simps(5) Std.simps(2))
        have "x = \<^bold>\<lambda>\<^bold>[a\<^bold>] \<and> y = b"
          using xy ab u u' v' seq seq_char
          by (metis \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src.simps(5)
              Srcs_simp\<^sub>\<Lambda>\<^sub>P Trgs.simps(2) \<Lambda>.lambda.inject(3) list.sel(1) singleton_insert_inj_eq
              \<Lambda>.targets_char\<^sub>\<Lambda>)
        thus "stdz_insert (x \<^bold>\<circ> y) ((\<^bold>\<lambda>\<^bold>[a\<^bold>] \<^bold>\<Zspot> b) # U) = stdz_insert (\<^bold>\<lambda>\<^bold>[a\<^bold>] \<^bold>\<Zspot> b) U"
          using u u' stdz_insert.simps(4) by presburger
      qed
    qed

    text \<open>
      Insertion of a term with \<open>Beta\<close> as its top-level constructor always
      leaves such a term at the head of the result.  Stated another way,
      \<open>Beta\<close> at the top-level must always come first in a standard reduction path.
    \<close>

    lemma stdz_insert_Beta_ind:
    shows "\<lbrakk>\<Lambda>.hgt t + length U \<le> n; \<Lambda>.is_Beta t; seq [t] U\<rbrakk>
              \<Longrightarrow> \<Lambda>.is_Beta (hd (stdz_insert t U))"
    proof (induct n arbitrary: t U)
      show "\<And>t U. \<lbrakk>\<Lambda>.hgt t + length U \<le> 0; \<Lambda>.is_Beta t; seq [t] U\<rbrakk>
                      \<Longrightarrow> \<Lambda>.is_Beta (hd (stdz_insert t U))"
        using Arr.simps(1) seq_char by blast
      fix n t U
      assume ind: "\<And>t U. \<lbrakk>\<Lambda>.hgt t + length U \<le> n; \<Lambda>.is_Beta t; seq [t] U\<rbrakk>
                             \<Longrightarrow> \<Lambda>.is_Beta (hd (stdz_insert t U))"
      assume seq: "seq [t] U"
      assume n: "\<Lambda>.hgt t + length U \<le> Suc n"
      assume t: "\<Lambda>.is_Beta t"
      show "\<Lambda>.is_Beta (hd (stdz_insert t U))"
        using t seq seq_char
        by (cases U; cases t; cases "hd U") auto
    qed

    lemma stdz_insert_Beta:
    assumes "\<Lambda>.is_Beta t" and "seq [t] U"
    shows "\<Lambda>.is_Beta (hd (stdz_insert t U))"
      using assms stdz_insert_Beta_ind by blast

    text \<open>
      This is the correctness lemma for insertion:
      Given a term \<open>t\<close> and standard reduction path \<open>U\<close> sequential with it,
      the result of insertion is a standard reduction path which is
      congruent to \<open>t # U\<close> unless \<open>t # U\<close> consists entirely of identities.

      The proof is very long.  Its structure parallels that of the definition
      of the function \<open>stdz_insert\<close>.  For really understanding the details,
      I strongly suggest viewing the proof in Isabelle/JEdit and using the
      code folding feature to unfold the proof a little bit at a time.
    \<close>

    lemma stdz_insert_correctness:
    shows "seq [t] U \<and> Std U \<longrightarrow>
              Std (stdz_insert t U) \<and> (\<not> Ide (t # U) \<longrightarrow> cong (stdz_insert t U) (t # U))"
           (is "?P t U")
    proof (rule stdz_insert.induct [of ?P])
      show "\<And>t. ?P t []"
        using seq_char by simp
      show "\<And>u U. ?P \<^bold>\<sharp> (u # U)"
        using seq_char not_arr_null null_char by auto
      show "\<And>x u U. ?P (hd (u # U)) (tl (u # U)) \<Longrightarrow> ?P \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> (u # U)"
      proof -
        fix x u U
        assume ind: "?P (hd (u # U)) (tl (u # U))"
        show "?P \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> (u # U)"
        proof (intro impI, elim conjE, intro conjI)
          assume seq: "seq [\<^bold>\<guillemotleft>x\<^bold>\<guillemotright>] (u # U)"
          assume Std: "Std (u # U)"
          have 1: "stdz_insert \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> (u # U) = stdz_insert u U"
            by simp
          have 2: "U \<noteq> [] \<Longrightarrow> seq [u] U"
            using Std Std_imp_Arr
            by (simp add: arrI\<^sub>P arr_append_imp_seq)
          show "Std (stdz_insert \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> (u # U))"
            using ind
            by (metis 1 2 Std Std_standard_development list.exhaust_sel list.sel(1) list.sel(3)
                reduction_paths.Std.simps(3) reduction_paths.stdz_insert.simps(1))
          show "\<not> Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # u # U) \<longrightarrow> stdz_insert \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> (u # U) \<^sup>*\<sim>\<^sup>* \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # u # U"
          proof (cases "U = []")
            show "U = [] \<Longrightarrow> ?thesis"
              using cong_standard_development cong_cons_ideI(1)
              apply simp
              by (metis Arr.simps(1-2) Arr_iff_Con_self Con_rec(3) \<Lambda>.in_sourcesI con_char
                  cong_transitive ideE \<Lambda>.Ide.simps(2) \<Lambda>.arr_char \<Lambda>.ide_char seq)
            assume U: "U \<noteq> []"
            show ?thesis
              using 1 2 ind seq seq_char cong_cons_ideI(1)
              apply simp
              by (metis Std Std_consE U \<Lambda>.Arr.simps(2) \<Lambda>.Ide.simps(2) \<Lambda>.targets_simps(2)
                  prfx_transitive)
          qed
        qed
      qed
      show "\<And>M u U. \<lbrakk>\<Lambda>.Ide M \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                     \<not> \<Lambda>.Ide M \<Longrightarrow> ?P M (map \<Lambda>.un_Lam (u # U))\<rbrakk>
                         \<Longrightarrow> ?P \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U)"
      proof -
        fix M u U
        assume ind1: "\<Lambda>.Ide M \<Longrightarrow> ?P (hd (u # U)) (tl (u # U))"
        assume ind2: "\<not> \<Lambda>.Ide M \<Longrightarrow> ?P M (map \<Lambda>.un_Lam (u # U))"
        show "?P \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U)"
        proof (intro impI, elim conjE)
          assume seq: "seq [\<^bold>\<lambda>\<^bold>[M\<^bold>]] (u # U)"
          assume Std: "Std (u # U)"
          have u: "\<Lambda>.is_Lam u"
            using seq
            by (metis insert_subset \<Lambda>.lambda.disc(8) list.simps(15) mem_Collect_eq
                seq_Lam_Arr_implies)
          have U: "set U \<subseteq> Collect \<Lambda>.is_Lam"
            using u seq
            by (metis insert_subset \<Lambda>.lambda.disc(8) list.simps(15) seq_Lam_Arr_implies)
          show "Std (stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U)) \<and>
                  (\<not> Ide (\<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U) \<longrightarrow> stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) \<^sup>*\<sim>\<^sup>* \<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U)"
          proof (cases "\<Lambda>.Ide M")
            assume M: "\<Lambda>.Ide M"
            have 1: "stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) = stdz_insert u U"
              using M by simp
            show ?thesis
            proof (cases "Ide (u # U)")
              show "Ide (u # U) \<Longrightarrow> ?thesis"
                using 1 Std_standard_development Ide_iff_standard_development_empty
                by (metis Ide_imp_Ide_hd Std Std_implies_set_subset_elementary_reduction
                    \<Lambda>.elementary_reduction_not_ide list.sel(1) list.set_intros(1)
                    mem_Collect_eq subset_code(1))
              assume 2: "\<not> Ide (u # U)"
              show ?thesis
              proof (cases "U = []")
                assume 3: "U = []"
                have 4: "standard_development u \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[M\<^bold>]] @ [u]"
                  using M 2 3 seq ide_char cong_standard_development [of u]
                        cong_append_ideI(1) [of "[\<^bold>\<lambda>\<^bold>[M\<^bold>]]" "[u]"]
                  by (metis Arr_imp_arr_hd Ide.simps(2) Std Std_imp_Arr cong_transitive
                      \<Lambda>.Ide.simps(3) \<Lambda>.arr_char \<Lambda>.ide_char list.sel(1) not_Cons_self2)
                show ?thesis
                  using 1 3 4 Std_standard_development by force
                next
                assume 3: "U \<noteq> []"
                have "stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) = stdz_insert u U"
                  using M 3 by simp
                have 5: "\<Lambda>.Arr u \<and> \<not> \<Lambda>.Ide u"
                  by (meson "3" Std Std_consE \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char
                      \<Lambda>.sseq_imp_elementary_reduction1)
                have 4: "standard_development u @ U \<^sup>*\<sim>\<^sup>* ([\<^bold>\<lambda>\<^bold>[M\<^bold>]] @ [u]) @ U"
                proof (intro cong_append seqI\<^sub>\<Lambda>\<^sub>P)
                  show "Arr (standard_development u)"
                    using 5 Std_standard_development Std_imp_Arr Ide_iff_standard_development_empty
                    by force
                  show "Arr U"
                    using Std 3 by auto
                  show "\<Lambda>.Trg (last (standard_development u)) = \<Lambda>.Src (hd U)"
                    by (metis "3" "5" Std Std_consE Trg_last_standard_development \<Lambda>.seq_char
                        \<Lambda>.sseq_imp_seq)
                  show "standard_development u \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[M\<^bold>]] @ [u]"
                    using M 5 Std Std_imp_Arr cong_standard_development [of u]
                          cong_append_ideI(3) [of "[\<^bold>\<lambda>\<^bold>[M\<^bold>]]" "[u]"]
                    by (metis (no_types, lifting) Arr.simps(2) Ide.simps(2) arr_char ide_char
                        \<Lambda>.Ide.simps(3) \<Lambda>.arr_char \<Lambda>.ide_char prfx_transitive seq seq_def
                        sources_cons)
                  show "U \<^sup>*\<sim>\<^sup>* U"
                    by (simp add: \<open>Arr U\<close> arr_char prfx_reflexive)
                qed
                show ?thesis
                proof (intro conjI)
                  show "Std (stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U))"
                    by (metis (no_types, lifting) 1 3 M Std Std_consE append_Cons
                        append_eq_append_conv2 append_self_conv arr_append_imp_seq ind1
                        list.sel(1) list.sel(3) not_Cons_self2 seq seq_def)
                  show "\<not> Ide (\<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U) \<longrightarrow> stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) \<^sup>*\<sim>\<^sup>* \<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U"
                  proof
                    have "seq [u] U \<and> Std U"
                      using 2 3 Std
                      by (metis Cons_eq_appendI Std_consE arr_append_imp_seq neq_Nil_conv
                          self_append_conv2 seq seqE)
                    thus "stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) \<^sup>*\<sim>\<^sup>* \<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U"
                      using M 1 2 3 4 ind1 cong_cons_ideI(1) [of "\<^bold>\<lambda>\<^bold>[M\<^bold>]" "u # U"]
                      apply simp
                      by (meson cong_transitive seq)
                  qed
                qed
              qed
            qed
            next
            assume M: "\<not> \<Lambda>.Ide M"
            have 1: "stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) =
                     map \<Lambda>.Lam (stdz_insert M (\<Lambda>.un_Lam u # map \<Lambda>.un_Lam U))"
              using M by simp
            show ?thesis
            proof (intro conjI)
              show "Std (stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U))"
                by (metis "1" M Std Std_map_Lam Std_map_un_Lam ind2 \<Lambda>.lambda.disc(8)
                    list.simps(9) seq seq_Lam_Arr_implies seq_map_un_Lam)
              show "\<not> Ide (\<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U) \<longrightarrow> stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) \<^sup>*\<sim>\<^sup>* \<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U"
              proof
                have "map \<Lambda>.Lam (stdz_insert M (\<Lambda>.un_Lam u # map \<Lambda>.un_Lam U)) \<^sup>*\<sim>\<^sup>*
                      \<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U"
                proof - 
                  have "map \<Lambda>.Lam (stdz_insert M (\<Lambda>.un_Lam u # map \<Lambda>.un_Lam U)) \<^sup>*\<sim>\<^sup>*
                        map \<Lambda>.Lam (M # \<Lambda>.un_Lam u # map \<Lambda>.un_Lam U)"
                    by (metis (mono_tags, opaque_lifting) Ide_imp_Ide_hd M Std Std_map_un_Lam
                        cong_map_Lam ind2 \<Lambda>.ide_char \<Lambda>.lambda.discI(2)
                        list.sel(1) list.simps(9) seq seq_Lam_Arr_implies seq_map_un_Lam)
                  thus ?thesis
                    using u U
                    by (simp add: map_idI subset_code(1))
                qed
                thus "stdz_insert \<^bold>\<lambda>\<^bold>[M\<^bold>] (u # U) \<^sup>*\<sim>\<^sup>* \<^bold>\<lambda>\<^bold>[M\<^bold>] # u # U"
                  using "1" by presburger
              qed
            qed
          qed
        qed
      qed
      show "\<And>M N A B U. ?P (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) U \<Longrightarrow> ?P (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)"
      proof -
        fix M N A B U
        assume ind: "?P (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) U"
        show "?P (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)"
        proof (intro impI, elim conjE)
          assume seq: "seq [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N] ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)"
          assume Std: "Std ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)"
          have MN: "\<Lambda>.Arr M \<and> \<Lambda>.Arr N"
            using seq
            by (simp add: seq_char)
          have AB: "\<Lambda>.Trg M = A \<and> \<Lambda>.Trg N = B"
          proof -
            have 1: "\<Lambda>.Ide A \<and> \<Lambda>.Ide B"
              using Std
              by (metis Std.simps(2) Std.simps(3) \<Lambda>.elementary_reduction.simps(5)
                        list.exhaust_sel \<Lambda>.sseq_Beta)
            moreover have "Trgs [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N] = Srcs [\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B]"
              using 1 seq seq_char
              by (simp add: \<Lambda>.Ide_implies_Arr Srcs_simp\<^sub>\<Lambda>\<^sub>P)
            ultimately show ?thesis
              by (metis \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src.simps(5) Srcs_simp\<^sub>\<Lambda>\<^sub>P
                  \<Lambda>.Trg.simps(2-3) Trgs_simp\<^sub>\<Lambda>\<^sub>P \<Lambda>.lambda.inject(2) \<Lambda>.lambda.sel(3-4)
                  last.simps list.sel(1) seq_char seq the_elem_eq)
          qed
          have 1: "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) = stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) U"
            by auto
          show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)) \<and>
                (\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<longrightarrow>
                   stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)"
          proof (cases "U = []")
            assume U: "U = []"
            have 1: "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) =
                     standard_development (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N)"
              using U by simp
            show ?thesis
            proof (intro conjI)
              show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U))"
                using 1 Std_standard_development by presburger
              show "\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<longrightarrow>
                      stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U"
              proof (intro impI)
                assume 2: "\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U)"
                have "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) =
                      (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) # standard_development (\<Lambda>.subst N M)"
                  using 1 MN by simp
                also have "... \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N]"
                  using MN AB cong_standard_development
                  by (metis 1 calculation \<Lambda>.Arr.simps(5) \<Lambda>.Ide.simps(5))
                also have "[\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U"
                  using AB MN U Beta_decomp(2) [of M N] by simp
                finally show "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<^sup>*\<sim>\<^sup>*
                              (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U"
                  by blast
              qed
            qed
            next
            assume U: "U \<noteq> []"
            have 1: "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) = stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) U"
              using U by simp
            have 2: "seq [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] U"
              using MN AB U Std \<Lambda>.sseq_imp_seq
              apply (intro seqI\<^sub>\<Lambda>\<^sub>P)
                apply auto
              by fastforce
            have 3: "Std U"
              using Std by fastforce
            show ?thesis
            proof (intro conjI)
              show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U))"
                using 2 3 ind by simp
              show "\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<longrightarrow>
                      stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U"
              proof
                have "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ U"
                  by (metis "1" "2" "3" \<Lambda>.Ide.simps(5) U Ide.simps(3) append.left_neutral
                      append_Cons \<Lambda>.ide_char ind list.exhaust)
                also have "[\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ U \<^sup>*\<sim>\<^sup>* ([\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N] @ [\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B]) @ U"
                  using MN AB Beta_decomp
                  by (meson "2" cong_append cong_reflexive seqE)
                also have "([\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N] @ [\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B]) @ U = (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U"
                  by simp
                finally show "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) ((\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U) \<^sup>*\<sim>\<^sup>*
                              (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<circ> N) # (\<^bold>\<lambda>\<^bold>[A\<^bold>] \<^bold>\<Zspot> B) # U"
                  by argo
              qed
            qed
          qed
        qed
      qed
      show "\<And>M N u U. (\<Lambda>.Arr M \<and> \<Lambda>.Arr N \<Longrightarrow> ?P (\<Lambda>.subst N M) (u # U))
                          \<Longrightarrow> ?P (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U)"
      proof -
        fix M N u U
        assume ind: "\<Lambda>.Arr M \<and> \<Lambda>.Arr N \<Longrightarrow> ?P (\<Lambda>.subst N M) (u # U)"
        show "?P (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U)"
        proof (intro impI, elim conjE)
          assume seq: "seq [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] (u # U)"
          assume Std: "Std (u # U)"
          have MN: "\<Lambda>.Arr M \<and> \<Lambda>.Arr N"
            using seq seq_char by simp
          show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U)) \<and>
                (\<not> Ide (\<Lambda>.Beta M N # u # U) \<longrightarrow>
                    cong (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U)) ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U))"
          proof (cases "\<Lambda>.Ide (\<Lambda>.subst N M)")
            assume 1: "\<Lambda>.Ide (\<Lambda>.subst N M)"
            have 2: "\<not> Ide (u # U)"
              using Std Std_implies_set_subset_elementary_reduction \<Lambda>.elementary_reduction_not_ide
              by force
            have 3: "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) = (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) # stdz_insert u U"
              using MN 1 seq seq_char Std stdz_insert_Ide_Std [of "\<Lambda>.subst N M" "u # U"]
                     \<Lambda>.Ide_implies_Arr
              by (cases "U = []") auto
            show ?thesis
            proof (cases "U = []")
              assume U: "U = []"
              have 3: "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) =
                       (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) # standard_development u"
                using 2 3 U by force
              have 4: "\<Lambda>.seq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) (hd (standard_development u))"
              proof
                show "\<Lambda>.Arr (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N)"
                  using MN by simp
                show "\<Lambda>.Arr (hd (standard_development u))"
                  by (metis 2 Arr_imp_arr_hd Ide.simps(2) Ide_iff_standard_development_empty
                      Std Std_consE Std_imp_Arr Std_standard_development U \<Lambda>.arr_char
                      \<Lambda>.ide_char)
                show "\<Lambda>.Trg (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) = \<Lambda>.Src (hd (standard_development u))"
                  by (metis 1 2 Ide.simps(2) MN Src_hd_standard_development Std Std_consE
                      Trg_last_Src_hd_eqI U \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src_Subst
                      \<Lambda>.Trg.simps(4) \<Lambda>.Trg_Src \<Lambda>.Trg_Subst \<Lambda>.ide_char last_ConsL list.sel(1) seq)
              qed
              show ?thesis
              proof (intro conjI)
                show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U))"
                proof -
                  have "\<Lambda>.sseq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) (hd (standard_development u))"
                    using MN 2 4 U \<Lambda>.Ide_Src
                    apply (intro \<Lambda>.sseq_BetaI)
                       apply auto
                    by (metis Ide.simps(1) Resid.simps(2) Std Std_consE
                        Std_standard_development cong_standard_development hd_Cons_tl ide_char
                        \<Lambda>.sseq_imp_elementary_reduction1 Std.simps(2))
                  thus ?thesis
                    by (metis 3 Std.simps(2-3) Std_standard_development hd_Cons_tl
                        \<Lambda>.sseq_imp_elementary_reduction1)
                qed
                show "\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U)
                          \<longrightarrow> stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                proof
                  have "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) =
                        [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ standard_development u"
                    using 3 by simp
                  also have 5: "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ standard_development u \<^sup>*\<sim>\<^sup>*
                                [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [u]"
                  proof (intro cong_append)
                    show "seq [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] (standard_development u)"
                      by (metis 2 3 Ide.simps(2) Ide_iff_standard_development_empty
                          Std Std_consE Std_imp_Arr U \<open>Std (stdz_insert (\<Lambda>.Beta M N) (u # U))\<close>
                          arr_append_imp_seq arr_char calculation \<Lambda>.ide_char neq_Nil_conv)
                    thus "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N]"
                      using cong_reflexive by blast
                    show "standard_development u \<^sup>*\<sim>\<^sup>* [u]"
                      by (metis 2 Arr.simps(2) Ide.simps(2) Std Std_imp_Arr U
                          cong_standard_development \<Lambda>.arr_char \<Lambda>.ide_char not_Cons_self2)
                  qed
                  also have "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [u] \<^sup>*\<sim>\<^sup>*
                             ([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [\<Lambda>.subst N M]) @ [u]"
                  proof (intro cong_append)
                    show "seq [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] [u]"
                      by (metis 5 Con_implies_Arr(1) Ide.simps(1) arr_append_imp_seq
                          arr_char ide_char not_Cons_self2)
                    show "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [\<Lambda>.subst N M]"
                      by (metis (full_types) 1 MN Ide_iff_standard_development_empty
                          cong_standard_development cong_transitive \<Lambda>.Arr.simps(5) \<Lambda>.Arr_Subst
                          \<Lambda>.Ide.simps(5) Beta_decomp(1) standard_development.simps(5))
                    show "[u] \<^sup>*\<sim>\<^sup>* [u]"
                      using Resid_Arr_self Std Std_imp_Arr U ide_char by blast
                  qed
                  also have "([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [\<Lambda>.subst N M]) @ [u] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ [u]"
                    by (metis Beta_decomp(1) MN U Resid_Arr_self cong_append
                        ide_char seq_char seq)
                  also have "[\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ [u] = (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                    using U by simp
                  finally show "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                    by blast
                qed
              qed
              next
              assume U: "U \<noteq> []"
              have 4: "seq [u] U"
                by (simp add: Std U arrI\<^sub>P arr_append_imp_seq)
              have 5: "Std U"
                using Std by auto
              have 6: "Std (stdz_insert u U) \<and>
                       set (stdz_insert u U) \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                       (\<not> Ide (u # U) \<longrightarrow>
                       cong (stdz_insert u U) (u # U))"
              proof -
                have "seq [\<Lambda>.subst N M] (u # U) \<and> Std (u # U)"
                  using MN Std Std_imp_Arr \<Lambda>.Arr_Subst
                  apply (intro conjI seqI\<^sub>\<Lambda>\<^sub>P)
                     apply simp_all
                  by (metis Trg_last_Src_hd_eqI \<Lambda>.Trg.simps(4) last_ConsL list.sel(1) seq)
                thus ?thesis
                  using MN 1 2 3 4 5 ind Std_implies_set_subset_elementary_reduction
                        stdz_insert_Ide_Std
                  apply simp
                  by (meson cong_cons_ideI(1) cong_transitive lambda_calculus.ide_char)
              qed
              have 7: "\<Lambda>.seq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) (hd (stdz_insert u U))"
                using MN 1 2 6 Arr_imp_arr_hd Con_implies_Arr(2) ide_char \<Lambda>.arr_char
                      Ide_iff_standard_development_empty Src_hd_eqI Trg_last_Src_hd_eqI
                      Trg_last_standard_development \<Lambda>.Ide_implies_Arr seq
                apply (intro \<Lambda>.seqI\<^sub>\<Lambda>)
                  apply simp
                 apply (metis Ide.simps(1))
                by (metis \<Lambda>.Arr.simps(5) \<Lambda>.Ide.simps(5) last.simps standard_development.simps(5))
              have 8: "seq [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] (stdz_insert u U)"
                by (metis 2 6 7 seqI\<^sub>\<Lambda>\<^sub>P Arr.simps(2) Con_implies_Arr(2)
                    Ide.simps(1) ide_char last.simps \<Lambda>.seqE \<Lambda>.seq_char)
              show ?thesis
              proof (intro conjI)
                show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U))"
                proof -
                  have "\<Lambda>.sseq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) (hd (stdz_insert u U))"
                    by (metis MN 2 6 7 \<Lambda>.Ide_Src Std.elims(2) Ide.simps(1)
                        Resid.simps(2) ide_char list.sel(1) \<Lambda>.sseq_BetaI
                        \<Lambda>.sseq_imp_elementary_reduction1)
                  thus ?thesis
                    by (metis 2 3 6 Std.simps(3) Resid.simps(1) con_char prfx_implies_con
                        list.exhaust_sel)
                qed
                show "\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U)
                          \<longrightarrow> stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                proof
                  have "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) = [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ stdz_insert u U"
                    using 3 by simp
                  also have "... \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ u # U"
                    using MN 2 3 6 8 cong_append
                    by (meson cong_reflexive seqE)
                  also have "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ u # U \<^sup>*\<sim>\<^sup>*
                             ([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [\<Lambda>.subst N M]) @ u # U"
                    using MN 1 2 6 8 Beta_decomp(1) Std Src_hd_eqI Trg_last_Src_hd_eqI
                          \<Lambda>.Arr_Subst \<Lambda>.ide_char ide_char
                    apply (intro cong_append cong_append_ideI seqI\<^sub>\<Lambda>\<^sub>P)
                           apply auto[2]
                         apply metis
                        apply auto[4]
                    by (metis cong_transitive)
                  also have "([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [\<Lambda>.subst N M]) @ u # U \<^sup>*\<sim>\<^sup>*
                             [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ u # U"
                    by (meson MN 2 6 Beta_decomp(1) cong_append prfx_transitive seq)
                  also have "[\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ u # U = (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                    by simp
                  finally show "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                    by simp
                qed
              qed
            qed
            next
            assume 1: "\<not> \<Lambda>.Ide (\<Lambda>.subst N M)"
            have 2: "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) =
                     (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) # stdz_insert (\<Lambda>.subst N M) (u # U)"
              using 1 MN by simp
            have 3: "seq [\<Lambda>.subst N M] (u # U)"
              using \<Lambda>.Arr_Subst MN seq_char seq by force
            have 4: "Std (stdz_insert (\<Lambda>.subst N M) (u # U)) \<and>
                     set (stdz_insert (\<Lambda>.subst N M) (u # U)) \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                     stdz_insert (\<Lambda>.Subst 0 N M) (u # U) \<^sup>*\<sim>\<^sup>* \<Lambda>.subst N M # u # U"
              using 1 3 Std ind MN Ide.simps(3) \<Lambda>.ide_char
                    Std_implies_set_subset_elementary_reduction
              by presburger
            have 5: "\<Lambda>.seq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) (hd (stdz_insert (\<Lambda>.subst N M) (u # U)))"
              using MN 4
              apply (intro \<Lambda>.seqI\<^sub>\<Lambda>)
                apply simp
               apply (metis Arr_imp_arr_hd Con_implies_Arr(1) Ide.simps(1) ide_char \<Lambda>.arr_char)
              using Src_hd_eqI
              by force
            show ?thesis
            proof (intro conjI)
              show "Std (stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U))"
              proof -
                have "\<Lambda>.sseq (\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N) (hd (stdz_insert (\<Lambda>.subst N M) (u # U)))"
                  using 5
                  by (metis 4 MN \<Lambda>.Ide_Src Std.elims(2) Ide.simps(1) Resid.simps(2)
                      ide_char list.sel(1) \<Lambda>.sseq_BetaI \<Lambda>.sseq_imp_elementary_reduction1)
                thus ?thesis
                  by (metis 2 4 Std.simps(3) Arr.simps(1) Con_implies_Arr(2)
                      Ide.simps(1) ide_char list.exhaust_sel)
              qed
              show "\<not> Ide ((\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U)
                        \<longrightarrow> stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
              proof
                have "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) =
                      [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ stdz_insert (\<Lambda>.subst N M) (u # U)"
                  using 2 by simp
                also have "... \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ \<Lambda>.subst N M # u # U"
                proof (intro cong_append)
                  show "seq [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] (stdz_insert (\<Lambda>.subst N M) (u # U))"
                    by (metis 4 5 Arr.simps(2) Con_implies_Arr(1) Ide.simps(1) ide_char
                        \<Lambda>.arr_char \<Lambda>.seq_char last_ConsL seqI\<^sub>\<Lambda>\<^sub>P)
                  show "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N]"
                    by (meson MN cong_transitive \<Lambda>.Arr_Src Beta_decomp(1))
                  show "stdz_insert (\<Lambda>.subst N M) (u # U) \<^sup>*\<sim>\<^sup>* \<Lambda>.subst N M # u # U"
                    using 4 by fastforce
                qed
                also have "[\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ \<Lambda>.subst N M # u # U =
                           ([\<^bold>\<lambda>\<^bold>[\<Lambda>.Src M\<^bold>] \<^bold>\<Zspot> \<Lambda>.Src N] @ [\<Lambda>.subst N M]) @ u # U"
                  by simp
                also have "... \<^sup>*\<sim>\<^sup>* [\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ u # U"
                  by (meson Beta_decomp(1) MN cong_append cong_reflexive seqE seq)
                also have "[\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N] @ u # U = (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                  by simp
                finally show "stdz_insert (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) (u # U) \<^sup>*\<sim>\<^sup>* (\<^bold>\<lambda>\<^bold>[M\<^bold>] \<^bold>\<Zspot> N) # u # U"
                  by blast
              qed
            qed
          qed
        qed
      qed
      text \<open>
        Because of the way the function package processes the pattern matching in the
        definition of \<open>stdz_insert\<close>, it produces eight separate subgoals for the remainder
        of the proof, even though these subgoals are all simple consequences of a single,
        more general fact.  We first prove this fact, then use it to discharge the eight
        subgoals.
      \<close>
      have *: "\<And>M N u U.
                 \<lbrakk>\<not> (\<Lambda>.is_Lam M \<and> \<Lambda>.is_Beta u);
                  \<Lambda>.Ide (M \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                  \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                   \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                   \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                   \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N)))\<rbrakk>
                      \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                  \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                   \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                   \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                   \<not> \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N)))\<rbrakk>
                      \<Longrightarrow> ?P (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N))) (u # U);
                  \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                   \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                   \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                   \<Lambda>.contains_head_reduction (hd (u # U));
                   \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N)))\<rbrakk>
                      \<Longrightarrow> ?P (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (u # U));
                  \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                   \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                   \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                   \<Lambda>.contains_head_reduction (hd (u # U));
                   \<not> \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N)))\<rbrakk>
                      \<Longrightarrow> ?P (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N))) (tl (u # U));
                  \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                   \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                   \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                   \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                      \<Longrightarrow> ?P M (filter notIde (map \<Lambda>.un_App1 (u # U)));
                  \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                   \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                   \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                   \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                      \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (u # U)))\<rbrakk>
                    \<Longrightarrow> ?P (M \<^bold>\<circ> N) (u # U)"
      proof -
        fix M N u U
        assume ind1: "\<Lambda>.Ide (M \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (u # U)) (tl (u # U))"
        assume ind2: "\<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                       \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                       \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                       \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N)))\<rbrakk>
                          \<Longrightarrow> ?P (hd (u # U)) (tl (u # U))"
        assume ind3: "\<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                       \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                       \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                       \<not> \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N)))\<rbrakk>
                          \<Longrightarrow> ?P (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_redex (M \<^bold>\<circ> N))) (u # U)"
        assume ind4: "\<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                       \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                       \<Lambda>.contains_head_reduction (hd (u # U));
                       \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N)))\<rbrakk>
                         \<Longrightarrow> ?P (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (u # U))"
        assume ind5: "\<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                       \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                       \<Lambda>.contains_head_reduction (hd (u # U));
                       \<not> \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N)))\<rbrakk>
                          \<Longrightarrow> ?P (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N))) (tl (u # U))"
        assume ind7: "\<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                       \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                       \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                          \<Longrightarrow> ?P M (filter notIde (map \<Lambda>.un_App1 (u # U)))"
        assume ind8: "\<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N);
                       \<Lambda>.seq (M \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                       \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                          \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (u # U)))"
        assume *: "\<not> (\<Lambda>.is_Lam M \<and> \<Lambda>.is_Beta u)"
        show "?P (M \<^bold>\<circ> N) (u # U)"
        proof (intro impI, elim conjE)
          assume seq: "seq [M \<^bold>\<circ> N] (u # U)"
          assume Std: "Std (u # U)"
          have MN: "\<Lambda>.Arr M \<and> \<Lambda>.Arr N"
            using seq_char seq by force
          have u: "\<Lambda>.Arr u"
            using Std
            by (meson Std_imp_Arr Arr.simps(2) Con_Arr_self Con_implies_Arr(1)
                Con_initial_left \<Lambda>.arr_char list.simps(3))
          have "U \<noteq> [] \<Longrightarrow> Arr U"
            using Std Std_imp_Arr Arr.simps(3)
            by (metis Arr.elims(3) list.discI)
          have "\<Lambda>.is_App u \<or> \<Lambda>.is_Beta u"
            using * seq MN u seq_char \<Lambda>.arr_char Srcs_simp\<^sub>\<Lambda>\<^sub>P \<Lambda>.targets_char\<^sub>\<Lambda>
            by (cases M; cases u) auto
          have **: "\<Lambda>.seq (M \<^bold>\<circ> N) u"
            using Srcs_simp\<^sub>\<Lambda>\<^sub>P seq_char seq \<Lambda>.seq_def u by force
          show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U)) \<and>
                (\<not> Ide ((M \<^bold>\<circ> N) # u # U)
                    \<longrightarrow> cong (stdz_insert (M \<^bold>\<circ> N) (u # U)) ((M \<^bold>\<circ> N) # u # U))"
          proof (cases "\<Lambda>.Ide (M \<^bold>\<circ> N)")
            assume 1: "\<Lambda>.Ide (M \<^bold>\<circ> N)"
            have MN: "\<Lambda>.Arr M \<and> \<Lambda>.Arr N \<and> \<Lambda>.Ide M \<and> \<Lambda>.Ide N"
              using MN 1 by simp
            have 2: "stdz_insert (M \<^bold>\<circ> N) (u # U) = stdz_insert u U"
              using MN 1
              by (simp add: Std seq stdz_insert_Ide_Std)
            show ?thesis
            proof (cases "U = []")
              assume U: "U = []"
              have 2: "stdz_insert (M \<^bold>\<circ> N) (u # U) = standard_development u"
                using 1 2 U by simp
              show ?thesis
              proof (intro conjI)
                show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                  using "2" Std_standard_development by presburger
                show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                          stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                  by (metis "1" "2" Ide.simps(2) U cong_cons_ideI(1) cong_standard_development
                      ide_backward_stable ide_char \<Lambda>.ide_char prfx_transitive seq u)
              qed
              next
              assume U: "U \<noteq> []"
              have 2: "stdz_insert (M \<^bold>\<circ> N) (u # U) = stdz_insert u U"
                using 1 2 U by simp
              have 3: "seq [u] U"
                by (simp add: Std U arrI\<^sub>P arr_append_imp_seq)
              have 4: "Std (stdz_insert u U) \<and>
                       set (stdz_insert u U) \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                       (\<not> Ide (u # U) \<longrightarrow> cong (stdz_insert u U) (u # U))"
                using MN 3 Std ind1 Std_implies_set_subset_elementary_reduction
                by (metis "1" Std.simps(3) U list.sel(1) list.sel(3) standardize.cases)
              show ?thesis
              proof (intro conjI)
                show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                  by (metis "1" "2" "3" Std Std.simps(3) U ind1 list.exhaust_sel list.sel(1,3))
                show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                          stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                proof
                  assume 5: "\<not> Ide ((M \<^bold>\<circ> N) # u # U)"
                  have "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* u # U"
                    using "1" "2" "4" "5" seq_char seq by force
                  also have "u # U \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> N] @ u # U"
                    using "1" Ide.simps(2) cong_append_ideI(1) ide_char seq by blast
                  also have "[M \<^bold>\<circ> N] @ (u # U) = (M \<^bold>\<circ> N) # u # U"
                    by simp
                  finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                    by blast
                qed
              qed
            qed
            next
            assume 1: "\<not> \<Lambda>.Ide (M \<^bold>\<circ> N)"
            show ?thesis
            proof (cases "\<Lambda>.contains_head_reduction (M \<^bold>\<circ> N)")
              assume 2: "\<Lambda>.contains_head_reduction (M \<^bold>\<circ> N)"
              show ?thesis
              proof (cases "\<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))")
                assume 3: "\<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))"
                have 4: "\<not> Ide (u # U)"
                  by (metis Std Std_implies_set_subset_elementary_reduction in_mono
                      \<Lambda>.elementary_reduction_not_ide list.set_intros(1) mem_Collect_eq
                      set_Ide_subset_ide)
                have 5: "stdz_insert (M \<^bold>\<circ> N) (u # U) = \<Lambda>.head_redex (M \<^bold>\<circ> N) # stdz_insert u U"
                  using MN 1 2 3 4 ** by auto
                show ?thesis
                proof (cases "U = []")
                  assume U: "U = []"
                  have u: "\<Lambda>.Arr u \<and> \<not> \<Lambda>.Ide u"
                      using 4 U u by force
                  have 5: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                           \<Lambda>.head_redex (M \<^bold>\<circ> N) # standard_development u"
                    using 5 U by simp
                  show ?thesis
                  proof (intro conjI)
                    show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                    proof -
                      have "\<Lambda>.sseq (\<Lambda>.head_redex (M \<^bold>\<circ> N)) (hd (standard_development u))"
                      proof -
                        have "\<Lambda>.seq (\<Lambda>.head_redex (M \<^bold>\<circ> N)) (hd (standard_development u))"
                        proof
                          show "\<Lambda>.Arr (\<Lambda>.head_redex (M \<^bold>\<circ> N))"
                            using MN \<Lambda>.Arr.simps(4) \<Lambda>.Arr_head_redex by presburger
                          show "\<Lambda>.Arr (hd (standard_development u))"
                            using Arr_imp_arr_hd Ide_iff_standard_development_empty
                                  Std_standard_development u
                            by force
                          show "\<Lambda>.Trg (\<Lambda>.head_redex (M \<^bold>\<circ> N)) = \<Lambda>.Src (hd (standard_development u))"
                          proof -
                            have "\<Lambda>.Trg (\<Lambda>.head_redex (M \<^bold>\<circ> N)) =
                                  \<Lambda>.Trg ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))"
                              by (metis 3 MN \<Lambda>.Con_Arr_head_redex \<Lambda>.Src_resid
                                  \<Lambda>.Arr.simps(4) \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self
                                  \<Lambda>.Ide_implies_Arr)
                            also have "... = \<Lambda>.Src u"
                              using MN
                              by (metis Trg_last_Src_hd_eqI Trg_last_eqI head_redex_decomp
                                  \<Lambda>.Arr.simps(4) last_ConsL last_appendR list.sel(1)
                                  not_Cons_self2 seq)
                            also have "... = \<Lambda>.Src (hd (standard_development u))"
                              using ** 2 3 u MN Src_hd_standard_development [of u] by metis
                            finally show ?thesis by blast
                          qed
                        qed
                        thus ?thesis
                          by (metis 2 u MN \<Lambda>.Arr.simps(4) Ide_iff_standard_development_empty
                              development.simps(2) development_standard_development
                              \<Lambda>.head_redex_is_head_reduction list.exhaust_sel
                              \<Lambda>.sseq_head_reductionI)
                      qed
                      thus ?thesis
                        by (metis 5 Ide_iff_standard_development_empty Std.simps(3)
                            Std_standard_development list.exhaust u)
                    qed
                    show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                              stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                    proof
                      have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                            [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ standard_development u"
                        using 5 by simp
                      also have "... \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ [u]"
                        using u cong_standard_development [of u] cong_append
                        by (metis 2 5 Ide_iff_standard_development_empty Std_imp_Arr
                            \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close>
                            arr_append_imp_seq arr_char calculation cong_standard_development
                            cong_transitive \<Lambda>.Arr_head_redex \<Lambda>.contains_head_reduction_iff
                            list.distinct(1))
                      also have "[\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ [u] \<^sup>*\<sim>\<^sup>*
                                 ([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]) @ [u]"
                      proof -
                        have "[\<Lambda>.head_redex (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>*
                              [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]"
                          by (metis (no_types, lifting) 1 3 MN Arr_iff_Con_self Ide.simps(2)
                              Resid.simps(2) arr_append_imp_seq arr_char cong_append_ideI(4)
                              cong_transitive head_redex_decomp ide_backward_stable ide_char
                              \<Lambda>.Arr.simps(4) \<Lambda>.ide_char not_Cons_self2)
                        thus ?thesis
                          using MN U u seq
                          by (meson cong_append head_redex_decomp \<Lambda>.Arr.simps(4) prfx_transitive)
                      qed
                      also have "([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                    [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]) @ [u] \<^sup>*\<sim>\<^sup>*
                                 [M \<^bold>\<circ> N] @ [u]"
                        by (metis \<Lambda>.Arr.simps(4) MN U Resid_Arr_self cong_append ide_char
                            seq_char head_redex_decomp seq)
                      also have "[M \<^bold>\<circ> N] @ [u] = (M \<^bold>\<circ> N) # u # U"
                        using U by simp
                      finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                        by blast
                    qed
                  qed
                  next
                  assume U: "U \<noteq> []"
                  have 6: "Std (stdz_insert u U) \<and>
                           set (stdz_insert u U) \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                           cong (stdz_insert u U) (u # U)"
                  proof -
                    have "seq [u] U"
                      by (simp add: Std U arrI\<^sub>P arr_append_imp_seq)
                    moreover have "Std U"
                      using Std Std.elims(2) U by blast
                    ultimately show ?thesis
                      using ind2 ** 1 2 3 4 Std_implies_set_subset_elementary_reduction
                      by force
                  qed
                  show ?thesis
                  proof (intro conjI)
                    show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                    proof -
                      have "\<Lambda>.sseq (\<Lambda>.head_redex (M \<^bold>\<circ> N)) (hd (stdz_insert u U))"
                      proof -
                        have "\<Lambda>.seq (\<Lambda>.head_redex (M \<^bold>\<circ> N)) (hd (stdz_insert u U))"
                        proof
                          show "\<Lambda>.Arr (\<Lambda>.head_redex (M \<^bold>\<circ> N))"
                            using MN \<Lambda>.Arr_head_redex by force
                          show "\<Lambda>.Arr (hd (stdz_insert u U))"
                            using 6
                            by (metis Arr_imp_arr_hd Con_implies_Arr(2) Ide.simps(1) ide_char
                                \<Lambda>.arr_char)
                          show "\<Lambda>.Trg (\<Lambda>.head_redex (M \<^bold>\<circ> N)) = \<Lambda>.Src (hd (stdz_insert u U))"
                          proof -
                            have "\<Lambda>.Trg (\<Lambda>.head_redex (M \<^bold>\<circ> N)) =
                                  \<Lambda>.Trg ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))"
                              by (metis 3 \<Lambda>.Arr_not_Nil \<Lambda>.Ide_iff_Src_self
                                  \<Lambda>.Ide_iff_Trg_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src_resid)
                            also have "... = \<Lambda>.Trg (M \<^bold>\<circ> N)"
                              by (metis 1 MN Trg_last_eqI Trg_last_standard_development
                                  cong_standard_development head_redex_decomp \<Lambda>.Arr.simps(4)
                                  last_snoc)
                            also have "... = \<Lambda>.Src (hd (stdz_insert u U))"
                              by (metis ** 6 Src_hd_eqI \<Lambda>.seqE\<^sub>\<Lambda> list.sel(1))
                            finally show ?thesis by blast
                          qed
                        qed
                        thus ?thesis
                          by (metis 2 6 MN \<Lambda>.Arr.simps(4) Std.elims(1) Ide.simps(1)
                              Resid.simps(2) ide_char \<Lambda>.head_redex_is_head_reduction
                              list.sel(1) \<Lambda>.sseq_head_reductionI \<Lambda>.sseq_imp_elementary_reduction1)
                      qed
                      thus ?thesis
                        by (metis 5 6 Std.simps(3) Arr.simps(1) Con_implies_Arr(1)
                            con_char prfx_implies_con list.exhaust_sel)
                    qed
                    show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                              stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                    proof
                      have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                            [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ stdz_insert u U"
                        using 5 by simp
                      also have 7: "[\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ stdz_insert u U \<^sup>*\<sim>\<^sup>*
                                    [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ u # U"
                        using 6 cong_append [of "[\<Lambda>.head_redex (M \<^bold>\<circ> N)]" "stdz_insert u U"
                                                "[\<Lambda>.head_redex (M \<^bold>\<circ> N)]" "u # U"]
                        by (metis 2 5 Arr.simps(1) Resid.simps(2) Std_imp_Arr
                            \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close>
                            arr_append_imp_seq arr_char calculation cong_standard_development
                            cong_transitive ide_implies_arr \<Lambda>.Arr_head_redex
                            \<Lambda>.contains_head_reduction_iff list.distinct(1))
                      also have "[\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ u # U \<^sup>*\<sim>\<^sup>*
                                 ([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                    [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]) @ u # U"
                      proof -
                        have "[\<Lambda>.head_redex (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>*
                              [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @ [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]"
                          by (metis 2 3 head_redex_decomp \<Lambda>.Arr_head_redex
                              \<Lambda>.Con_Arr_head_redex \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr
                              \<Lambda>.Src_resid \<Lambda>.contains_head_reduction_iff \<Lambda>.resid_Arr_self
                              prfx_decomp prfx_transitive)
                        moreover have "seq [\<Lambda>.head_redex (M \<^bold>\<circ> N)] (u # U)"
                          by (metis 7 arr_append_imp_seq cong_implies_coterminal coterminalE
                              list.distinct(1))
                        ultimately show ?thesis
                          using 3 ide_char cong_symmetric cong_append
                          by (meson 6 prfx_transitive)
                      qed
                      also have "([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                    [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]) @ u # U \<^sup>*\<sim>\<^sup>*
                                 [M \<^bold>\<circ> N] @ u # U"
                        by (meson 6 MN \<Lambda>.Arr.simps(4) cong_append prfx_transitive
                            head_redex_decomp seq)
                      also have "[M \<^bold>\<circ> N] @ (u # U) = (M \<^bold>\<circ> N) # u # U"
                        by simp
                      finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                        by blast
                    qed
                  qed
                qed
                next
                assume 3: "\<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))"
                have 4: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                         \<Lambda>.head_redex (M \<^bold>\<circ> N) #
                           stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U)"
                  using MN 1 2 3 ** by auto
                have 5: "Std (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U)) \<and>
                         set (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U))
                            \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                         stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U) \<^sup>*\<sim>\<^sup>*
                         (M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N) # u # U"
                proof -
                  have "seq [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)] (u # U)"
                    by (metis (full_types) MN arr_append_imp_seq cong_implies_coterminal
                        coterminalE head_redex_decomp \<Lambda>.Arr.simps(4) not_Cons_self2
                        seq seq_def targets_append)
                  thus ?thesis
                    using ind3 1 2 3 ** Std Std_implies_set_subset_elementary_reduction
                    by auto
                qed
                show ?thesis
                proof (intro conjI)
                  show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                  proof -
                    have "\<Lambda>.sseq (\<Lambda>.head_redex (M \<^bold>\<circ> N))
                                 (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U)))"
                    proof -
                      have "\<Lambda>.seq (\<Lambda>.head_redex (M \<^bold>\<circ> N))
                                  (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U)))"
                        using MN 5 \<Lambda>.Arr_head_redex
                        by (metis (no_types, lifting) Arr_imp_arr_hd Con_implies_Arr(2)
                            Ide.simps(1) Src_hd_eqI ide_char \<Lambda>.Arr.simps(4) \<Lambda>.Arr_head_redex
                            \<Lambda>.Con_Arr_head_redex \<Lambda>.Src_resid \<Lambda>.arr_char \<Lambda>.seq_char list.sel(1))
                      moreover have "\<Lambda>.elementary_reduction
                                       (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))
                                                        (u # U)))"
                        using 5
                        by (metis Arr.simps(1) Con_implies_Arr(2) Ide.simps(1) hd_in_set
                            ide_char mem_Collect_eq subset_code(1))
                      ultimately show ?thesis
                        using MN 2 \<Lambda>.head_redex_is_head_reduction \<Lambda>.sseq_head_reductionI
                        by simp
                    qed
                    thus ?thesis
                      by (metis 4 5 Std.simps(3) Arr.simps(1) Con_implies_Arr(2)
                          Ide.simps(1) ide_char list.exhaust_sel)
                  qed
                  show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                             stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                  proof
                    have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                         [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                           stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U)"
                      using 4 by simp
                    also have "... \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                         ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N) # u # U)"
                    proof (intro cong_append)
                      show "seq [\<Lambda>.head_redex (M \<^bold>\<circ> N)]
                                (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U))"
                        by (metis 4 5 Ide.simps(1) Resid.simps(1) Std_imp_Arr
                            \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close> arrI\<^sub>P arr_append_imp_seq
                            calculation ide_char list.discI)
                      show "[\<Lambda>.head_redex (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_redex (M \<^bold>\<circ> N)]"
                        using MN \<Lambda>.cong_reflexive ide_char \<Lambda>.Arr_head_redex by force
                      show "stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) \\
                            \<Lambda>.head_redex (M \<^bold>\<circ> N) # u # U"
                        using 5 by fastforce
                    qed
                    also have "([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                 ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N) # u # U)) =
                               ([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                  [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]) @ (u # U)"
                      by simp
                    also have "([\<Lambda>.head_redex (M \<^bold>\<circ> N)] @
                                 [(M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)]) @ u # U \<^sup>*\<sim>\<^sup>*
                               [M \<^bold>\<circ> N] @ u # U"
                      by (meson ** cong_append cong_reflexive seqE head_redex_decomp
                          seq \<Lambda>.seq_char)
                    also have "[M \<^bold>\<circ> N] @ (u # U) = (M \<^bold>\<circ> N) # u # U"
                      by simp
                    finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                      by blast
                  qed
                qed
              qed
              next
              assume 2: "\<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N)"
              show ?thesis
              proof (cases "\<Lambda>.contains_head_reduction u")
                assume 3: "\<Lambda>.contains_head_reduction u"
                have B: "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @ [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>*
                         [M \<^bold>\<circ> N] @ [u]"
                proof -
                  have "[M \<^bold>\<circ> N] @ [u] \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N]"
                  proof -
                    have "\<Lambda>.is_internal_reduction (M \<^bold>\<circ> N)"
                      using 2 ** \<Lambda>.is_internal_reduction_iff by blast
                    moreover have "\<Lambda>.is_head_reduction u"
                    proof -
                      have "\<Lambda>.elementary_reduction u"
                        by (metis Std lambda_calculus.sseq_imp_elementary_reduction1
                            list.discI list.sel(1) reduction_paths.Std.elims(2))
                      thus ?thesis
                        using \<Lambda>.is_head_reduction_if 3 by force
                    qed
                    moreover have "\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \\ (M \<^bold>\<circ> N) = u"
                      using \<Lambda>.resid_head_strategy_Src(1) ** calculation(1-2) by fastforce
                    moreover have "[M \<^bold>\<circ> N] \<^sup>*\<lesssim>\<^sup>* [\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N]"
                      using MN \<Lambda>.prfx_implies_con ide_char \<Lambda>.Arr_head_strategy
                            \<Lambda>.Src_head_strategy \<Lambda>.prfx_Join
                      by force
                    ultimately show ?thesis
                      using u \<Lambda>.Coinitial_iff_Con \<Lambda>.Arr_not_Nil \<Lambda>.resid_Join
                            prfx_decomp [of "M \<^bold>\<circ> N" "\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N"]
                      by simp
                  qed
                  also have "[\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>*
                             [\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))] @
                               [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))]"
                  proof -
                    have 3: "\<Lambda>.composite_of
                               (\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)))
                               ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)))
                               (\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N)"
                      using \<Lambda>.Arr_head_strategy MN \<Lambda>.Src_head_strategy \<Lambda>.join_of_Join
                            \<Lambda>.join_of_def
                      by force
                    hence "composite_of
                             [\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))]
                             [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))]
                             [\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N]"
                      using composite_of_single_single
                      by (metis (no_types, lifting) \<Lambda>.Con_sym Ide.simps(2) Resid.simps(3)
                          composite_ofI \<Lambda>.composite_ofE \<Lambda>.con_char ide_char \<Lambda>.prfx_implies_con)
                    hence "[\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))] @
                             [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))] \<^sup>*\<sim>\<^sup>*
                           [\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N)) \<squnion> M \<^bold>\<circ> N]"
                      using \<Lambda>.resid_Join
                      by (meson 3 composite_of_single_single composite_of_unq_upto_cong)
                    thus ?thesis by blast
                  qed
                  also have "[\<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))] @
                               [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<Lambda>.Src (M \<^bold>\<circ> N))] \<^sup>*\<sim>\<^sup>*
                             [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                               [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                    by (metis (full_types) \<Lambda>.Arr.simps(4) MN prfx_transitive calculation
                        \<Lambda>.head_strategy_Src)
                  finally show ?thesis by blast
                qed
                show ?thesis
                proof (cases "\<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))")
                  assume 4: "\<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                  have A: "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>*
                           [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @ [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                    by (meson 4 B Con_implies_Arr(1) Ide.simps(2) arr_append_imp_seq arr_char
                        con_char cong_append_ideI(2) ide_char \<Lambda>.ide_char not_Cons_self2
                        prfx_implies_con)
                  have 5: "\<not> Ide (u # U)"
                    by (meson 3 Ide_consE \<Lambda>.ide_backward_stable \<Lambda>.subs_head_redex
                        \<Lambda>.subs_implies_prfx \<Lambda>.contains_head_reduction_iff
                        \<Lambda>.elementary_reduction_head_redex \<Lambda>.elementary_reduction_not_ide)
                  have 6: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                           stdz_insert (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) U"
                    using 1 2 3 4 5 * ** \<open>\<Lambda>.is_App u \<or> \<Lambda>.is_Beta u\<close>
                    apply (cases u)
                        apply simp_all
                     apply blast
                    by (cases M) auto
                  show ?thesis
                  proof (cases "U = []")
                    assume U: "U = []"
                    have u: "\<not> \<Lambda>.Ide u"
                      using 5 U by simp
                    have 6: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                             standard_development (\<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                      using 6 U by simp
                    show ?thesis
                    proof (intro conjI)
                      show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                        using "6" Std_standard_development by presburger
                      show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                                stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                      proof
                        have "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                          using 4 6 cong_standard_development ** 1 2 3 \<Lambda>.Arr.simps(4)
                                \<Lambda>.Arr_head_strategy MN \<Lambda>.ide_backward_stable \<Lambda>.ide_char
                          by metis
                        also have "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> N] @ [u]"
                          by (meson A B prfx_transitive)
                        also have "[M \<^bold>\<circ> N] @ [u] = (M \<^bold>\<circ> N) # u # U"
                          using U by auto
                        finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                          by blast
                      qed
                    qed
                    next
                    assume U: "U \<noteq> []"
                    have 7: "seq [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] U"
                    proof
                      show "Arr [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                        by (meson A Con_implies_Arr(1) con_char prfx_implies_con)
                      show "Arr U"
                        using U \<open>U \<noteq> [] \<Longrightarrow> Arr U\<close> by presburger
                      show "\<Lambda>.Trg (last [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]) = \<Lambda>.Src (hd U)"
                        by (metis A B Std Std_consE Trg_last_eqI U \<Lambda>.seqE\<^sub>\<Lambda> \<Lambda>.sseq_imp_seq last_snoc)
                    qed
                    have 8: "Std (stdz_insert (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) U) \<and>
                             set (stdz_insert (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) U)
                                \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                             stdz_insert (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) U \<^sup>*\<sim>\<^sup>*
                             \<Lambda>.head_strategy (M \<^bold>\<circ> N) # U"
                    proof -
                      have "Std U"
                        by (metis Std Std.simps(3) U list.exhaust_sel)
                      moreover have "\<not> Ide (\<Lambda>.head_strategy (M \<^bold>\<circ> N) # tl (u # U))"
                        using 1 4 \<Lambda>.ide_backward_stable by blast
                      ultimately show ?thesis
                        using ind4 ** 1 2 3 4 7 Std_implies_set_subset_elementary_reduction
                        by force
                    qed
                    show ?thesis
                    proof (intro conjI)
                      show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                        using 6 8 by presburger
                      show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                                 stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                      proof
                        have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                              stdz_insert (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) U"
                          using 6 by simp
                        also have "... \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @ U"
                          using 8 by simp
                        also have "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @ U \<^sup>*\<sim>\<^sup>* ([M \<^bold>\<circ> N] @ [u]) @ U"
                          by (meson A B U 7 Resid_Arr_self cong_append ide_char
                              prfx_transitive \<open>U \<noteq> [] \<Longrightarrow> Arr U\<close>)
                        also have "([M \<^bold>\<circ> N] @ [u]) @ U = (M \<^bold>\<circ> N) # u # U"
                          by simp
                        finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                          by blast
                      qed
                    qed
                  qed
                  next
                  assume 4: "\<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                  show ?thesis
                  proof (cases "U = []")
                    assume U: "U = []"
                    have 5: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                             \<Lambda>.head_strategy (M \<^bold>\<circ> N) #
                               standard_development ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                      using 1 2 3 4 U * ** \<open>\<Lambda>.is_App u \<or> \<Lambda>.is_Beta u\<close>
                      apply (cases u)
                         apply simp_all
                       apply blast
                      apply (cases M)
                          apply simp_all
                      by blast+
                    show ?thesis
                    proof (intro conjI)
                      show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                      proof -
                        have "\<Lambda>.sseq (\<Lambda>.head_strategy (M \<^bold>\<circ> N))
                                     (hd (standard_development
                                            ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))))"
                        proof -
                          have "\<Lambda>.seq (\<Lambda>.head_strategy (M \<^bold>\<circ> N))
                                      (hd (standard_development
                                             ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))))"
                            using MN ** 4 \<Lambda>.Arr_head_strategy Arr_imp_arr_hd
                                  Ide_iff_standard_development_empty Src_hd_standard_development
                                  Std_imp_Arr Std_standard_development \<Lambda>.Arr_resid
                                  \<Lambda>.Src_head_strategy \<Lambda>.Src_resid
                            by force
                          moreover have "\<Lambda>.elementary_reduction
                                           (hd (standard_development
                                                 ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))))"
                            by (metis 4 Ide_iff_standard_development_empty MN Std_consE
                                Std_standard_development hd_Cons_tl \<Lambda>.Arr.simps(4)
                                \<Lambda>.Arr_resid \<Lambda>.Con_head_strategy
                                \<Lambda>.sseq_imp_elementary_reduction1 Std.simps(2))
                          ultimately show ?thesis
                            using \<Lambda>.sseq_head_reductionI Std_standard_development
                            by (metis ** 2 3 Std U \<Lambda>.internal_reduction_preserves_no_head_redex
                                \<Lambda>.is_internal_reduction_iff \<Lambda>.Src_head_strategy
                                \<Lambda>.elementary_reduction_not_ide \<Lambda>.head_strategy_Src
                                \<Lambda>.head_strategy_is_elementary \<Lambda>.ide_char \<Lambda>.is_head_reduction_char
                                \<Lambda>.is_head_reduction_if \<Lambda>.seqE\<^sub>\<Lambda> Std.simps(2))
                        qed
                        thus ?thesis
                          by (metis 4 5 MN Ide_iff_standard_development_empty
                              Std_standard_development \<Lambda>.Arr.simps(4) \<Lambda>.Arr_resid
                              \<Lambda>.Con_head_strategy list.exhaust_sel Std.simps(3))
                      qed
                      show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                              stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                      proof
                        have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                              [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                standard_development ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                          using 5 by simp
                        also have "... \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                             [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                        proof (intro cong_append)
                          show 6: "seq [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]
                                       (standard_development
                                         ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)))"
                            using 4 Ide_iff_standard_development_empty MN
                                  \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close>
                                  arr_append_imp_seq arr_char calculation \<Lambda>.Arr_head_strategy
                                  \<Lambda>.Arr_resid lambda_calculus.Src_head_strategy
                            by force
                          show "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                            by (meson MN 6 cong_reflexive seqE)
                          show "standard_development ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) \<^sup>*\<sim>\<^sup>*
                                [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                            using 4 MN cong_standard_development \<Lambda>.Arr.simps(4)
                                  \<Lambda>.Arr_resid \<Lambda>.Con_head_strategy
                            by presburger
                        qed
                        also have "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                     [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>*
                                   [M \<^bold>\<circ> N] @ [u]"
                          using B by blast
                        also have "[M \<^bold>\<circ> N] @ [u] = (M \<^bold>\<circ> N) # u # U"
                          using U by simp
                        finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                          by blast
                      qed
                    qed
                    next
                    assume U: "U \<noteq> []"
                    have 5: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                             \<Lambda>.head_strategy (M \<^bold>\<circ> N) #
                               stdz_insert (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N))) U"
                      using 1 2 3 4 U * ** \<open>\<Lambda>.is_App u \<or> \<Lambda>.is_Beta u\<close>
                      apply (cases u)
                         apply simp_all
                       apply blast
                      apply (cases M)
                          apply simp_all
                      by blast+
                    have 6: "Std (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U) \<and>
                             set (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U)
                               \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                             stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U \<^sup>*\<sim>\<^sup>*
                             (M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N) # U"
                    proof -
                      have "seq [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)] U"
                      proof
                        show "Arr [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                          by (simp add: MN \<Lambda>.Arr_resid \<Lambda>.Con_head_strategy)
                        show "Arr U"
                          using U \<open>U \<noteq> [] \<Longrightarrow> Arr U\<close> by blast
                        show "\<Lambda>.Trg (last [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]) = \<Lambda>.Src (hd U)"
                          by (metis (mono_tags, lifting) B U Std Std_consE Trg_last_eqI
                              \<Lambda>.seq_char \<Lambda>.sseq_imp_seq last_ConsL last_snoc)
                      qed
                      thus ?thesis
                        using ind5 Std_implies_set_subset_elementary_reduction
                        by (metis ** 1 2 3 4 Std Std.simps(3) Arr_iff_Con_self Ide.simps(3)
                            Resid.simps(1) seq_char \<Lambda>.ide_char list.exhaust_sel list.sel(1,3))
                    qed
                    show ?thesis
                    proof (intro conjI)
                      show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                      proof -
                        have "\<Lambda>.sseq (\<Lambda>.head_strategy (M \<^bold>\<circ> N))
                                   (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U))"
                        proof -
                          have "\<Lambda>.seq (\<Lambda>.head_strategy (M \<^bold>\<circ> N))
                                      (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U))"
                          proof
                            show "\<Lambda>.Arr (\<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                              using MN \<Lambda>.Arr_head_strategy by force
                            show "\<Lambda>.Arr (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U))"
                              using 6
                              by (metis Ide.simps(1) Resid.simps(2) Std_consE hd_Cons_tl ide_char)
                            show "\<Lambda>.Trg (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) =
                                  \<Lambda>.Src (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U))"
                              using 6
                              by (metis MN Src_hd_eqI \<Lambda>.Arr.simps(4) \<Lambda>.Con_head_strategy
                                  \<Lambda>.Src_resid list.sel(1))
                          qed
                          moreover have "\<Lambda>.is_head_reduction (\<Lambda>.head_strategy (M \<^bold>\<circ> N))"
                            using ** 1 2 3 \<Lambda>.Src_head_strategy \<Lambda>.head_strategy_is_elementary
                                  \<Lambda>.head_strategy_Src \<Lambda>.is_head_reduction_char \<Lambda>.seq_char
                            by (metis \<Lambda>.Src_head_redex \<Lambda>.contains_head_reduction_iff
                                \<Lambda>.head_redex_is_head_reduction
                                \<Lambda>.internal_reduction_preserves_no_head_redex
                                \<Lambda>.is_internal_reduction_iff)
                          moreover have "\<Lambda>.elementary_reduction
                                          (hd (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U))"
                            by (metis 6 Ide.simps(1) Resid.simps(2) ide_char hd_in_set
                                in_mono mem_Collect_eq)
                          ultimately show ?thesis
                            using \<Lambda>.sseq_head_reductionI by blast
                        qed
                        thus ?thesis
                          by (metis 5 6 Std.simps(3) Arr.simps(1) Con_implies_Arr(1)
                              con_char prfx_implies_con list.exhaust_sel)
                      qed
                      show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                                stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                      proof
                        have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                              [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U"
                          using 5 by simp
                        also have 10: "... \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                                 ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N) # U)"
                        proof (intro cong_append)
                          show 10: "seq [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]
                                        (stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U)"
                            by (metis 5 6 Ide.simps(1) Resid.simps(1) Std_imp_Arr
                                \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close> arr_append_imp_seq
                                arr_char calculation ide_char list.distinct(1))
                          show "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] \<^sup>*\<sim>\<^sup>* [\<Lambda>.head_strategy (M \<^bold>\<circ> N)]"
                            using MN 10 cong_reflexive by blast
                          show "stdz_insert ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) U \<^sup>*\<sim>\<^sup>*
                                (M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N) # U"
                            using 6 by auto
                        qed
                        also have 11: "[\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                         ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N) # U) =
                                       ([\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                         [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]) @ U"
                          by simp
                        also have "... \<^sup>*\<sim>\<^sup>* (([M \<^bold>\<circ> N] @ [u]) @ U)"
                        proof -
                          have "seq ([\<Lambda>.head_strategy (M \<^bold>\<circ> N)] @
                                       [(M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)]) U"
                            by (metis U 10 11 append_is_Nil_conv arr_append_imp_seq
                                cong_implies_coterminal coterminalE not_Cons_self2)
                          thus ?thesis
                            using B cong_append cong_reflexive by blast
                        qed
                        also have "([M \<^bold>\<circ> N] @ [u]) @ U = (M \<^bold>\<circ> N) # u # U"
                          by simp
                        finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                          by blast
                      qed
                    qed
                  qed
                qed
                next
                assume 3: "\<not> \<Lambda>.contains_head_reduction u"
                have u: "\<Lambda>.Arr u \<and> \<Lambda>.is_App u \<and> \<not> \<Lambda>.contains_head_reduction u"
                  using "3" \<open>\<Lambda>.is_App u \<or> \<Lambda>.is_Beta u\<close> \<Lambda>.is_Beta_def u by force
                have 5: "\<not> \<Lambda>.Ide u"
                  by (metis Std Std.simps(2) Std.simps(3) \<Lambda>.elementary_reduction_not_ide
                      \<Lambda>.ide_char neq_Nil_conv \<Lambda>.sseq_imp_elementary_reduction1)
                show ?thesis
                proof -
                  have 4: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                           map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Src N))
                               (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) @
                           map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                               (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                    using MN 1 2 3 5 * ** \<open>\<Lambda>.is_App u \<or> \<Lambda>.is_Beta u\<close>
                    apply (cases "U = []"; cases M; cases u)
                                        apply simp_all
                    by blast+
                  have ***: "set U \<subseteq> Collect \<Lambda>.is_App"
                    using u 5 Std seq_App_Std_implies by blast
                  have X: "Std (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                    by (metis *** Std Std_filter_map_un_App1 insert_subset list.simps(15)
                        mem_Collect_eq u)
                  have Y: "Std (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                    by (metis *** u Std Std_filter_map_un_App2 insert_subset list.simps(15)
                        mem_Collect_eq)
                  have A: "\<not> \<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide \<Longrightarrow>
                             Std (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) \<and>
                             set (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U))))
                                \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                             stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                             M # filter notIde (map \<Lambda>.un_App1 (u # U))"
                  proof -
                    assume *: "\<not> \<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                    have "seq [M] (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                    proof
                      show "Arr [M]"
                        using MN by simp
                      show "Arr (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                        by (metis (mono_tags, lifting) "*" Std_imp_Arr X empty_filter_conv
                            list.set_map mem_Collect_eq subset_code(1))
                      show "\<Lambda>.Trg (last [M]) = \<Lambda>.Src (hd (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                      proof -
                        have "\<Lambda>.Trg (last [M]) = \<Lambda>.Src (hd (map \<Lambda>.un_App1 (u # U)))"
                          using ** u by fastforce
                        also have "... = \<Lambda>.Src (hd (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                        proof -
                          have "Arr (map \<Lambda>.un_App1 (u # U))"
                            using u ***
                            by (metis Arr_map_un_App1 Std Std_imp_Arr insert_subset
                                list.simps(15) mem_Collect_eq neq_Nil_conv)
                          moreover have "\<not> Ide (map \<Lambda>.un_App1 (u # U))"
                            by (metis "*" Collect_cong \<Lambda>.ide_char list.set_map set_Ide_subset_ide)
                          ultimately show ?thesis
                            using Src_hd_eqI cong_filter_notIde by blast
                        qed
                        finally show ?thesis by blast
                      qed
                    qed
                    moreover have "\<not> Ide (M # filter notIde (map \<Lambda>.un_App1 (u # U)))"
                      using *
                      by (metis (no_types, lifting) *** Arr_map_un_App1 Std Std_imp_Arr
                          Arr.simps(1) Ide.elims(2) Resid_Arr_Ide_ind ide_char
                          seq_char calculation(1) cong_filter_notIde filter_notIde_Ide
                          insert_subset list.discI list.sel(3) list.simps(15) mem_Collect_eq u)
                    ultimately show ?thesis
                      by (metis X 1 2 3 ** ind7 Std_implies_set_subset_elementary_reduction
                          list.sel(1))
                  qed
                  have B: "\<not> \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide \<Longrightarrow>
                             Std (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))) \<and>
                             set (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))
                                \<subseteq> {a. \<Lambda>.elementary_reduction a} \<and>
                             stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))) \<^sup>*\<sim>\<^sup>*
                             N # filter notIde (map \<Lambda>.un_App2 (u # U))"
                  proof -
                    assume **: "\<not> \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                    have "seq [N] (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                    proof
                      show "Arr [N]"
                        using MN by simp
                      show "Arr (filter (\<lambda>u. \<not> \<Lambda>.Ide u) (map \<Lambda>.un_App2 (u # U)))"
                        by (metis (mono_tags, lifting) ** Std_imp_Arr Y empty_filter_conv
                            list.set_map mem_Collect_eq subset_code(1))
                      show "\<Lambda>.Trg (last [N]) = \<Lambda>.Src (hd (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                      proof -
                        have "\<Lambda>.Trg (last [N]) = \<Lambda>.Src (hd (map \<Lambda>.un_App2 (u # U)))"
                          by (metis u seq Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4)
                              \<Lambda>.Trg.simps(3) \<Lambda>.is_App_def \<Lambda>.lambda.sel(4) last_ConsL
                              list.discI list.map_sel(1) list.sel(1))
                        also have "... = \<Lambda>.Src (hd (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                        proof -
                          have "Arr (map \<Lambda>.un_App2 (u # U))"
                            using u ***
                            by (metis Arr_map_un_App2 Std Std_imp_Arr list.distinct(1)
                                mem_Collect_eq set_ConsD subset_code(1))
                          moreover have "\<not> Ide (map \<Lambda>.un_App2 (u # U))"
                            by (metis ** Collect_cong \<Lambda>.ide_char list.set_map set_Ide_subset_ide)
                          ultimately show ?thesis
                            using Src_hd_eqI cong_filter_notIde by blast
                        qed
                        finally show ?thesis by blast
                      qed
                    qed 
                    moreover have "\<Lambda>.seq (M \<^bold>\<circ> N) u"
                      by (metis u Srcs_simp\<^sub>\<Lambda>\<^sub>P Arr.simps(2) Trgs.simps(2) seq_char
                          list.sel(1) seq \<Lambda>.seqI(1) \<Lambda>.sources_char\<^sub>\<Lambda>)
                    moreover have "\<not> Ide (N # filter notIde (map \<Lambda>.un_App2 (u # U)))"
                      using u *
                      by (metis (no_types, lifting) *** Arr_map_un_App2 Std Std_imp_Arr
                          Arr.simps(1) Ide.elims(2) Resid_Arr_Ide_ind ide_char
                          seq_char calculation(1) cong_filter_notIde filter_notIde_Ide
                          insert_subset list.discI list.sel(3) list.simps(15) mem_Collect_eq)
                    ultimately show ?thesis
                      using * 1 2 3 Y ind8 Std_implies_set_subset_elementary_reduction
                      by simp
                  qed
                  show ?thesis
                  proof (cases "\<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide";
                         cases "\<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide")
                    show "\<lbrakk>\<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide;
                           \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide\<rbrakk>
                             \<Longrightarrow> ?thesis"
                    proof -
                      assume *: "\<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      assume **: "\<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      have False
                        using u 5 * ** Ide_iff_standard_development_empty
                        by (metis \<Lambda>.Ide.simps(4) image_subset_iff \<Lambda>.lambda.collapse(3)
                            list.set_intros(1) mem_Collect_eq)
                      thus ?thesis by blast
                    qed
                    show "\<lbrakk>\<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide;
                           \<not> \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide\<rbrakk>
                             \<Longrightarrow> ?thesis"
                    proof -
                      assume *: "\<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      assume **: "\<not> \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      have 6: "\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) = \<Lambda>.Trg M"
                      proof -
                        have "\<Lambda>.Trg M = \<Lambda>.Src (hd (map \<Lambda>.un_App1 (u # U)))"
                          by (metis u seq Trg_last_Src_hd_eqI hd_map \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                              \<Lambda>.is_App_def \<Lambda>.lambda.sel(3) last_ConsL list.discI list.sel(1))
                        also have "... = \<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U)))"
                        proof -
                          have 6: "Ide (map \<Lambda>.un_App1 (u # U))"
                            using * *** u Std Std_imp_Arr Ide_char ide_char Arr_map_un_App1
                            by (metis (mono_tags, lifting) Collect_cong insert_subset
                                \<Lambda>.ide_char list.distinct(1) list.set_map list.simps(15)
                                mem_Collect_eq)
                          hence "Src (map \<Lambda>.un_App1 (u # U)) = Trg (map \<Lambda>.un_App1 (u # U))"
                            using Ide_imp_Src_eq_Trg by blast
                          thus ?thesis
                            using 6 Ide_implies_Arr by force
                        qed
                        also have "... = \<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))"
                          by (simp add: last_map)
                        finally show ?thesis by simp
                      qed
                      have "filter notIde (map \<Lambda>.un_App1 (u # U)) = []"
                        using * by (simp add: subset_eq)
                      hence 4: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M) @
                                map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                    (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                        using u 4 5 * ** Ide_iff_standard_development_empty MN
                        by simp
                      show ?thesis
                      proof (intro conjI)
                        have "Std (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M) @
                                   map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                       (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                        proof (intro Std_append)
                          show "Std (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M))"
                            using Std_map_App1 Std_standard_development MN \<Lambda>.Ide_Src
                            by force
                          show "Std (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                         (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                            using "**" B MN 6 Std_map_App2 \<Lambda>.Ide_Trg by presburger
                          show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M) = [] \<or>
                                map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                    (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))) = [] \<or>
                                \<Lambda>.sseq (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M)))
                                       (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                (stdz_insert N (filter notIde
                                                               (map \<Lambda>.un_App2 (u # U))))))"
                          proof (cases "\<Lambda>.Ide M")
                            show "\<Lambda>.Ide M \<Longrightarrow> ?thesis"
                              using Ide_iff_standard_development_empty MN by blast
                            assume M: "\<not> \<Lambda>.Ide M"
                            have "\<Lambda>.sseq (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M)))
                                         (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                  (stdz_insert N (filter notIde
                                                                 (map \<Lambda>.un_App2 (u # U))))))"
                            proof -
                              have "last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M)) =
                                    \<Lambda>.App (last (standard_development M)) (\<Lambda>.Src N)"
                                using M
                                by (simp add: Ide_iff_standard_development_empty MN last_map)
                              moreover have "hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                     (stdz_insert N (filter notIde
                                                                    (map \<Lambda>.un_App2 (u # U))))) =
                                             \<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))
                                                   (hd (stdz_insert N (filter notIde
                                                                      (map \<Lambda>.un_App2 (u # U)))))"
                                by (metis ** B Ide.simps(1) Resid.simps(2) hd_map ide_char)
                              moreover
                              have "\<Lambda>.sseq (\<Lambda>.App (last (standard_development M)) (\<Lambda>.Src N))
                                            ..."
                              proof -
                                have "\<Lambda>.elementary_reduction (last (standard_development M))"
                                  using M MN Std_standard_development
                                        Ide_iff_standard_development_empty last_in_set
                                        mem_Collect_eq set_standard_development subsetD
                                  by metis
                                moreover have "\<Lambda>.elementary_reduction
                                                 (hd (stdz_insert N
                                                        (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                                  using ** B
                                  by (metis Arr.simps(1) Con_implies_Arr(2) Ide.simps(1)
                                      ide_char in_mono list.set_sel(1) mem_Collect_eq)
                                moreover have "\<Lambda>.Trg (last (standard_development M)) =
                                               \<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))"
                                  using M MN 6 Trg_last_standard_development by presburger
                                moreover have "\<Lambda>.Src N =
                                               \<Lambda>.Src (hd (stdz_insert N
                                                            (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                                  by (metis "**" B Src_hd_eqI list.sel(1))
                                ultimately show ?thesis
                                  by simp
                              qed
                              ultimately show ?thesis by simp
                            qed
                            thus ?thesis by blast
                          qed
                        qed
                        thus "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                          using 4 by simp
                        show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                                  stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                        proof
                          show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                          proof (cases "\<Lambda>.Ide M")
                            assume M: "\<Lambda>.Ide M"
                            have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                              using 4 M MN Ide_iff_standard_development_empty by simp
                            also have "... \<^sup>*\<sim>\<^sup>* (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                    (N # filter notIde (map \<Lambda>.un_App2 (u # U))))"
                            proof -
                              have "\<Lambda>.Ide (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))"
                                using M 6 \<Lambda>.Ide_Trg \<Lambda>.Ide_implies_Arr by fastforce
                              thus ?thesis
                                using ** *** B u cong_map_App1 by blast
                            qed
                            also have "map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (N # filter notIde (map \<Lambda>.un_App2 (u # U))) =
                                       map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (filter notIde (N # map \<Lambda>.un_App2 (u # U)))"
                              using 1 M by force
                            also have "map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (filter notIde (N # map \<Lambda>.un_App2 (u # U))) \<^sup>*\<sim>\<^sup>*
                                       map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (N # map \<Lambda>.un_App2 (u # U))"
                            proof -
                              have "Arr (N # map \<Lambda>.un_App2 (u # U))"
                              proof
                                show "\<Lambda>.arr N"
                                  using MN by blast
                                show "Arr (map \<Lambda>.un_App2 (u # U))"
                                  using *** u Std Arr_map_un_App2
                                  by (metis Std_imp_Arr insert_subset list.distinct(1)
                                      list.simps(15) mem_Collect_eq)
                                show "\<Lambda>.trg N = Src (map \<Lambda>.un_App2 (u # U))"
                                  using u \<open>\<Lambda>.seq (M \<^bold>\<circ> N) u\<close> \<Lambda>.seq_char \<Lambda>.is_App_def by auto
                              qed
                              moreover have "\<not> Ide (N # map \<Lambda>.un_App2 (u # U))"
                                using 1 M by force
                              moreover have "\<Lambda>.Ide (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))"
                                using M 6 \<Lambda>.Ide_Trg \<Lambda>.Ide_implies_Arr by presburger
                              ultimately show ?thesis
                                using cong_filter_notIde cong_map_App1 by blast
                            qed
                            also have "map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (N # map \<Lambda>.un_App2 (u # U)) =
                                       map (\<Lambda>.App M) (N # map \<Lambda>.un_App2 (u # U))"
                              using M MN \<open>\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) = \<Lambda>.Trg M\<close>
                                    \<Lambda>.Ide_iff_Trg_self
                              by force
                            also have "... = (M \<^bold>\<circ> N) # map (\<Lambda>.App M) (map \<Lambda>.un_App2 (u # U))"
                              by simp
                            also have "... = (M \<^bold>\<circ> N) # u # U"
                            proof -
                              have "Arr (u # U)"
                                using Std Std_imp_Arr by blast
                              moreover have "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
                                using *** u by simp
                              moreover have "\<Lambda>.un_App1 u = M"
                                by (metis * u M seq Trg_last_Src_hd_eqI \<Lambda>.Ide_iff_Src_self
                                    \<Lambda>.Ide_iff_Trg_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src.simps(4)
                                    \<Lambda>.Trg.simps(3) \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.sel(3)
                                    last.simps list.distinct(1) list.sel(1) list.set_intros(1)
                                    list.set_map list.simps(9) mem_Collect_eq standardize.cases
                                    subset_iff)
                              moreover have "\<Lambda>.un_App1 ` set (u # U) \<subseteq> {M}"
                              proof -
                                have "Ide (map \<Lambda>.un_App1 (u # U))"
                                  using * *** Std Std_imp_Arr Arr_map_un_App1
                                  by (metis Collect_cong Ide_char calculation(1-2) \<Lambda>.ide_char
                                      list.set_map)
                                thus ?thesis
                                  by (metis calculation(3) hd_map list.discI list.sel(1)
                                      list.set_map set_Ide_subset_single_hd)
                              qed
                              ultimately show ?thesis
                                using M map_App_map_un_App2 by blast
                            qed
                            finally show ?thesis by blast
                            next
                            assume M: "\<not> \<Lambda>.Ide M"
                            have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                  map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M) @
                                  map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                      (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                              using 4 6 by simp
                            also have "... \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                                 map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                                     (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                            proof (intro cong_append)
                              show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M) \<^sup>*\<sim>\<^sup>*
                                    [M \<^bold>\<circ> \<Lambda>.Src N]"
                                using MN M cong_standard_development \<Lambda>.Ide_Src
                                      cong_map_App2 [of "\<Lambda>.Src N" "standard_development M" "[M]"]
                                by simp
                              show "map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                        (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))) \<^sup>*\<sim>\<^sup>*
                                    [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                      map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                          (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                              proof -
                                have "map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                          (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))) \<^sup>*\<sim>\<^sup>*
                                      map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                          (N # filter notIde (map \<Lambda>.un_App2 (u # U)))"
                                  using ** B MN cong_map_App1 lambda_calculus.Ide_Trg
                                  by presburger
                                also have "map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                               (N # filter notIde (map \<Lambda>.un_App2 (u # U))) =
                                           [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                             map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                                 (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                                  by simp
                                finally show ?thesis by blast
                              qed
                              show "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (standard_development M))
                                        (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                             (stdz_insert N (filter notIde
                                                                    (map \<Lambda>.un_App2 (u # U)))))"
                                using MN M ** B cong_standard_development [of M]
                                by (metis Nil_is_append_conv Resid.simps(2) Std_imp_Arr
                                    \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close> arr_append_imp_seq
                                    arr_char calculation complete_development_Ide_iff
                                    complete_development_def list.map_disc_iff development.simps(1))
                            qed
                            also have "[M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                          map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                              (filter notIde (map \<Lambda>.un_App2 (u # U))) =
                                       ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N]) @
                                         map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                             (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                              by simp
                            also have "([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N]) @
                                          map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                              (filter notIde (map \<Lambda>.un_App2 (u # U))) \<^sup>*\<sim>\<^sup>*
                                        ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N]) @
                                           map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X) (map \<Lambda>.un_App2 (u # U))"
                            proof (intro cong_append)
                              show "seq ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])
                                        (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                             (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                              proof
                                show "Arr ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])"
                                  by (simp add: MN)
                                show 9: "Arr (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                             (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                                proof -
                                  have "Arr (map \<Lambda>.un_App2 (u # U))"
                                    using *** u Arr_map_un_App2
                                    by (metis Std Std_imp_Arr list.distinct(1) mem_Collect_eq
                                        set_ConsD subset_code(1))
                                  moreover have "\<not> Ide (map \<Lambda>.un_App2 (u # U))"
                                    using **
                                    by (metis Collect_cong \<Lambda>.ide_char list.set_map
                                        set_Ide_subset_ide)
                                  ultimately show ?thesis
                                    using cong_filter_notIde
                                    by (metis Arr_map_App2 Con_implies_Arr(2) Ide.simps(1)
                                        MN ide_char \<Lambda>.Ide_Trg)
                                qed
                                show "\<Lambda>.Trg (last ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])) =
                                      \<Lambda>.Src (hd (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                            (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                                proof -
                                  have "\<Lambda>.Trg (last ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])) =
                                        \<Lambda>.Trg M \<^bold>\<circ> \<Lambda>.Trg N"
                                    using MN by auto
                                  also have "... = \<Lambda>.Src u"
                                    using Trg_last_Src_hd_eqI seq by force
                                  also have "... = \<Lambda>.Src (\<Lambda>.Trg M \<^bold>\<circ> \<Lambda>.un_App2 u)"
                                    using MN \<open>\<Lambda>.App (\<Lambda>.Trg M) (\<Lambda>.Trg N) = \<Lambda>.Src u\<close> u by auto
                                  also have 8: "... = \<Lambda>.Trg M \<^bold>\<circ> \<Lambda>.Src (\<Lambda>.un_App2 u)"
                                    using MN by simp
                                  also have 7: "... = \<Lambda>.Trg M \<^bold>\<circ> 
                                                          \<Lambda>.Src (hd (filter notIde
                                                                       (map \<Lambda>.un_App2 (u # U))))"
                                    using u 5 list.simps(9) cong_filter_notIde
                                          \<open>filter notIde (map \<Lambda>.un_App1 (u # U)) = []\<close>
                                    by auto
                                  also have "... = \<Lambda>.Src (hd (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                                             (filter notIde
                                                                (map \<Lambda>.un_App2 (u # U)))))"
                                    (* TODO: Figure out what is going on with 7 8 9. *)
                                    by (metis 7 8 9 Arr.simps(1) hd_map \<Lambda>.Src.simps(4)
                                        \<Lambda>.lambda.sel(4) list.simps(8))
                                  finally show "\<Lambda>.Trg (last ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])) =
                                                \<Lambda>.Src (hd (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                                             (filter notIde
                                                                     (map \<Lambda>.un_App2 (u # U)))))"
                                    by blast
                                qed
                              qed
                              show "seq [M \<^bold>\<circ> \<Lambda>.Src N] [\<Lambda>.Trg M \<^bold>\<circ> N]"
                                using MN by force
                              show "[M \<^bold>\<circ> \<Lambda>.Src N] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> \<Lambda>.Src N]"
                                using MN
                                by (meson head_redex_decomp \<Lambda>.Arr.simps(4) \<Lambda>.Arr_Src
                                    prfx_transitive)
                              show "[\<Lambda>.Trg M \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>* [\<Lambda>.Trg M \<^bold>\<circ> N]"
                                using MN
                                by (meson \<open>seq [M \<^bold>\<circ> \<Lambda>.Src N] [\<Lambda>.Trg M \<^bold>\<circ> N]\<close> cong_reflexive seqE)
                              show "map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X)
                                        (filter notIde (map \<Lambda>.un_App2 (u # U))) \<^sup>*\<sim>\<^sup>*
                                    map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X) (map \<Lambda>.un_App2 (u # U))"
                              proof -
                                have "Arr (map \<Lambda>.un_App2 (u # U))"
                                  using *** u Arr_map_un_App2
                                  by (metis Std Std_imp_Arr list.distinct(1) mem_Collect_eq
                                      set_ConsD subset_code(1))
                                moreover have "\<not> Ide (map \<Lambda>.un_App2 (u # U))"
                                  using **
                                  by (metis Collect_cong \<Lambda>.ide_char list.set_map
                                      set_Ide_subset_ide)
                                ultimately show ?thesis
                                  using M MN cong_filter_notIde cong_map_App1 \<Lambda>.Ide_Trg
                                  by presburger
                              qed
                            qed
                            also have "([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N]) @
                                          map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X) (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
                                       [M \<^bold>\<circ> N] @ u # U"
                            proof (intro cong_append)
                              show "seq ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])
                                        (map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X) (map \<Lambda>.un_App2 (u # U)))"
                                by (metis Nil_is_append_conv Nil_is_map_conv arr_append_imp_seq
                                    calculation cong_implies_coterminal coterminalE
                                    list.distinct(1))
                              show "[M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> N]"
                                using MN \<Lambda>.resid_Arr_self \<Lambda>.Arr_not_Nil \<Lambda>.Ide_Trg ide_char by simp
                              show " map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X) (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>* u # U"
                              proof -
                                have "map (\<lambda>X. \<Lambda>.Trg M \<^bold>\<circ> X) (map \<Lambda>.un_App2 (u # U)) = u # U"
                                proof (intro map_App_map_un_App2)
                                  show "Arr (u # U)"
                                    using Std Std_imp_Arr by blast
                                  show "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
                                    using *** u by auto
                                  show "\<Lambda>.Ide (\<Lambda>.Trg M)"
                                    using MN \<Lambda>.Ide_Trg by blast
                                  show "\<Lambda>.un_App1 ` set (u # U) \<subseteq> {\<Lambda>.Trg M}"
                                  proof -
                                    have "\<Lambda>.un_App1 u = \<Lambda>.Trg M"
                                      using * u seq seq_char
                                      apply (cases u)
                                          apply simp_all
                                      by (metis Trg_last_Src_hd_eqI \<Lambda>.Ide_iff_Src_self
                                          \<Lambda>.Src_Src \<Lambda>.Src_Trg \<Lambda>.Src_eq_iff(2) \<Lambda>.Trg.simps(3)
                                          last_ConsL list.sel(1) seq u)
                                    moreover have "Ide (map \<Lambda>.un_App1 (u # U))"
                                      using * Std Std_imp_Arr Arr_map_un_App1
                                      by (metis Collect_cong Ide_char
                                          \<open>Arr (u # U)\<close> \<open>set (u # U) \<subseteq> Collect \<Lambda>.is_App\<close>
                                          \<Lambda>.ide_char list.set_map)
                                    ultimately show ?thesis
                                      using set_Ide_subset_single_hd by force 
                                  qed
                                qed
                                thus ?thesis
                                  by (simp add: Resid_Arr_self Std ide_char)
                              qed
                            qed
                            also have "[M \<^bold>\<circ> N] @ u # U = (M \<^bold>\<circ> N) # u # U"
                              by simp
                            finally show ?thesis by blast
                          qed
                        qed
                      qed
                    qed
                    show "\<lbrakk>\<not> \<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide;
                           \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide\<rbrakk>
                             \<Longrightarrow> ?thesis"
                    proof -
                      assume *: "\<not> \<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      assume **: "\<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      have 10: "filter notIde (map \<Lambda>.un_App2 (u # U)) = []"
                        using ** by (simp add: subset_eq)
                      hence 4: "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                    (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) @
                                map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                    (standard_development N)"
                        using u 4 5 * ** Ide_iff_standard_development_empty MN
                        by simp
                      have 6: "\<Lambda>.Ide (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))"
                        using *** u Std Std_imp_Arr
                        by (metis Arr_imp_arr_last in_mono \<Lambda>.Arr.simps(4) \<Lambda>.Ide_Trg \<Lambda>.arr_char
                            \<Lambda>.lambda.collapse(3) last.simps last_in_set list.discI mem_Collect_eq)
                      show ?thesis
                      proof (intro conjI)
                        show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                        proof -
                          have "Std (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                         (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) @
                                     map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                         (standard_development N))"
                          proof (intro Std_append)
                            show "Std (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                           (stdz_insert M (filter notIde
                                                                  (map \<Lambda>.un_App1 (u # U)))))"
                              using * A MN Std_map_App1 \<Lambda>.Ide_Src by presburger
                            show "Std (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (standard_development N))"
                              using MN 6 Std_map_App2 Std_standard_development by simp
                            show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                      (stdz_insert M
                                        (filter notIde (map \<Lambda>.un_App1 (u # U)))) = [] \<or>
                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (standard_development N) = [] \<or>
                                  \<Lambda>.sseq (last (map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Src N))
                                                    (stdz_insert M
                                                      (filter notIde (map \<Lambda>.un_App1 (u # U))))))
                                         (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                  (standard_development N)))"
                            proof (cases "\<Lambda>.Ide N")
                              show "\<Lambda>.Ide N \<Longrightarrow> ?thesis"
                                using Ide_iff_standard_development_empty MN by blast
                              assume N: "\<not> \<Lambda>.Ide N"
                              have "\<Lambda>.sseq (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                      (stdz_insert M
                                                        (filter notIde (map \<Lambda>.un_App1 (u # U))))))
                                           (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                    (standard_development N)))"
                              proof -
                                have "hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                     (standard_development N)) =
                                      \<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))
                                            (hd (standard_development N))"
                                  by (meson Ide_iff_standard_development_empty MN N list.map_sel(1))
                                moreover have "last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                      (stdz_insert M
                                                        (filter notIde (map \<Lambda>.un_App1 (u # U))))) =
                                               \<Lambda>.App (last (stdz_insert M
                                                              (filter notIde
                                                                      (map \<Lambda>.un_App1 (u # U)))))
                                                     (\<Lambda>.Src N)"
                                  by (metis * A Ide.simps(1) Resid.simps(1) ide_char last_map)
                                moreover have "\<Lambda>.sseq ... (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))
                                                                  (hd (standard_development N)))"
                                proof -
                                  have 7: "\<Lambda>.elementary_reduction
                                             (last (stdz_insert M (filter notIde
                                                                  (map \<Lambda>.un_App1 (u # U)))))"
                                    using * A
                                    by (metis Ide.simps(1) Resid.simps(2) ide_char last_in_set
                                        mem_Collect_eq subset_iff)
                                  moreover
                                  have "\<Lambda>.elementary_reduction (hd (standard_development N))"
                                    using MN N hd_in_set set_standard_development
                                          Ide_iff_standard_development_empty
                                    by blast
                                  moreover have "\<Lambda>.Src N = \<Lambda>.Src (hd (standard_development N))"
                                    using MN N Src_hd_standard_development by auto
                                  moreover have "\<Lambda>.Trg (last (stdz_insert M 
                                                                (filter notIde
                                                                        (map \<Lambda>.un_App1 (u # U))))) =
                                                 \<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))"
                                  proof -
                                    have "[\<Lambda>.Trg (last (stdz_insert M 
                                                          (filter notIde
                                                                  (map \<Lambda>.un_App1 (u # U)))))] =
                                          [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))]"
                                    proof -
                                      have "\<Lambda>.Trg (last (stdz_insert M
                                                           (filter notIde
                                                                   (map \<Lambda>.un_App1 (u # U))))) =
                                            \<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U)))"
                                      proof -
                                        have "\<Lambda>.Trg (last (stdz_insert M
                                                             (filter notIde (map \<Lambda>.un_App1 (u # U))))) =
                                              \<Lambda>.Trg (last (M # filter notIde (map \<Lambda>.un_App1 (u # U))))"
                                          using * A Trg_last_eqI by blast
                                        also have "... = \<Lambda>.Trg (last ([M] @ filter notIde
                                                                              (map \<Lambda>.un_App1 (u # U))))"
                                          by simp
                                        also have "... = \<Lambda>.Trg (last (filter notIde
                                                                        (map \<Lambda>.un_App1 (u # U))))"
                                        proof -
                                          have "seq [M] (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                          proof
                                            show "Arr [M]"
                                              using MN by simp
                                            show "Arr (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                              using * Std_imp_Arr
                                              by (metis (no_types, lifting)
                                                  X empty_filter_conv list.set_map mem_Collect_eq subsetI)
                                            show "\<Lambda>.Trg (last [M]) =
                                                  \<Lambda>.Src (hd (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                                            proof -
                                              have "\<Lambda>.Trg (last [M]) = \<Lambda>.Trg M"
                                                using MN by simp
                                              also have "... = \<Lambda>.Src (\<Lambda>.un_App1 u)"
                                                by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4)
                                                    \<Lambda>.Trg.simps(3) \<Lambda>.lambda.collapse(3)
                                                    \<Lambda>.lambda.inject(3) last_ConsL list.sel(1) seq u)
                                              also have "... = \<Lambda>.Src (hd (map \<Lambda>.un_App1 (u # U)))"
                                                by auto
                                              also have "... = \<Lambda>.Src (hd (filter notIde
                                                                         (map \<Lambda>.un_App1 (u # U))))"
                                                using u 5 10 by force
                                              finally show ?thesis by blast
                                            qed
                                          qed
                                          thus ?thesis by fastforce
                                        qed
                                        also have "... = \<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U)))"
                                        proof -
                                          have "filter (\<lambda>u. \<not> \<Lambda>.Ide u) (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>*
                                                map \<Lambda>.un_App1 (u # U)"
                                            using * *** u Std Std_imp_Arr Arr_map_un_App1 [of "u # U"]
                                                  cong_filter_notIde
                                            by (metis (mono_tags, lifting) empty_filter_conv
                                                filter_notIde_Ide list.discI list.set_map
                                                mem_Collect_eq set_ConsD subset_code(1))
                                          thus ?thesis
                                            using cong_implies_coterminal Trg_last_eqI
                                            by presburger
                                        qed
                                        finally show ?thesis by blast
                                      qed
                                      thus ?thesis
                                        by (simp add: last_map)
                                    qed
                                    moreover
                                    have "\<Lambda>.Ide (\<Lambda>.Trg (last (stdz_insert M
                                                                (filter notIde
                                                                        (map \<Lambda>.un_App1 (u # U))))))"
                                      using 7 \<Lambda>.Ide_Trg \<Lambda>.elementary_reduction_is_arr by blast
                                    moreover have "\<Lambda>.Ide (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))"
                                      using 6 by blast
                                    ultimately show ?thesis by simp
                                  qed
                                  ultimately show ?thesis
                                    using \<Lambda>.sseq.simps(4) by blast
                                qed
                                ultimately show ?thesis by argo
                              qed
                              thus ?thesis by blast
                            qed
                          qed
                          thus ?thesis
                            using 4 by simp
                        qed
                        show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                                  stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                        proof
                          show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                          proof (cases "\<Lambda>.Ide N")
                            assume N: "\<Lambda>.Ide N"
                            have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                  map (\<lambda>X. X \<^bold>\<circ> N)
                                      (stdz_insert M (filter notIde
                                                     (map \<Lambda>.un_App1 (u # U))))"
                              using 4 N MN Ide_iff_standard_development_empty \<Lambda>.Ide_iff_Src_self
                              by force
                            also have "... \<^sup>*\<sim>\<^sup>* map (\<lambda>X. X \<^bold>\<circ> N)
                                                   (M # filter notIde
                                                               (map \<Lambda>.un_App1 (u # U)))"
                              using * A MN N \<Lambda>.Ide_Src cong_map_App2 \<Lambda>.Ide_iff_Src_self
                              by blast
                            also have "map (\<lambda>X. X \<^bold>\<circ> N)
                                           (M # filter notIde
                                                       (map \<Lambda>.un_App1 (u # U))) =
                                       [M \<^bold>\<circ> N] @
                                         map (\<lambda>X. \<Lambda>.App X N)
                                             (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                              by auto
                            also have "[M \<^bold>\<circ> N] @
                                         map (\<lambda>X. X \<^bold>\<circ> N)
                                             (filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                                       [M \<^bold>\<circ> N] @ map (\<lambda>X. X \<^bold>\<circ> N) (map \<Lambda>.un_App1 (u # U))"
                            proof (intro cong_append)
                              show "seq [M \<^bold>\<circ> N]
                                        (map (\<lambda>X. X \<^bold>\<circ> N)
                                             (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                              proof
                                have 20: "Arr (map \<Lambda>.un_App1 (u # U))"
                                  using *** u Std Arr_map_un_App1
                                  by (metis Std_imp_Arr insert_subset list.discI list.simps(15)
                                      mem_Collect_eq)
                                show "Arr [M \<^bold>\<circ> N]"
                                  using MN by auto
                                show 21: "Arr (map (\<lambda>X. X \<^bold>\<circ> N)
                                                   (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                                proof -
                                  have "Arr (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                    using u 20 cong_filter_notIde
                                    by (metis (no_types, lifting) * Std_imp_Arr
                                        \<open>Std (filter notIde (map \<Lambda>.un_App1 (u # U)))\<close>
                                        empty_filter_conv list.set_map mem_Collect_eq subsetI)
                                  thus ?thesis
                                    using MN N Arr_map_App1 \<Lambda>.Ide_Src by presburger
                                qed
                                show "\<Lambda>.Trg (last [M \<^bold>\<circ> N]) =
                                      \<Lambda>.Src (hd (map (\<lambda>X. X \<^bold>\<circ> N)
                                                     (filter notIde (map \<Lambda>.un_App1 (u # U)))))"
                                proof -
                                  have "\<Lambda>.Trg (last [M \<^bold>\<circ> N]) = \<Lambda>.Trg M \<^bold>\<circ> N"
                                    using MN N \<Lambda>.Ide_iff_Trg_self by simp
                                  also have "... = \<Lambda>.Src (\<Lambda>.un_App1 u) \<^bold>\<circ> N"
                                    using MN u seq seq_char
                                    by (metis Trg_last_Src_hd_eqI calculation \<Lambda>.Src_Src \<Lambda>.Src_Trg
                                        \<Lambda>.Src_eq_iff(2) \<Lambda>.is_App_def \<Lambda>.lambda.sel(3) list.sel(1))
                                  also have "... = \<Lambda>.Src (\<Lambda>.un_App1 u \<^bold>\<circ> N)"
                                    using MN N \<Lambda>.Ide_iff_Src_self by simp
                                  also have "... = \<Lambda>.Src (hd (map (\<lambda>X. X \<^bold>\<circ> N)
                                                                  (map \<Lambda>.un_App1 (u # U))))"
                                    by simp
                                  also have "... = \<Lambda>.Src (hd (map (\<lambda>X. X \<^bold>\<circ> N)
                                                                  (filter notIde
                                                                          (map \<Lambda>.un_App1 (u # U)))))"
                                  proof -
                                    have "cong (map \<Lambda>.un_App1 (u # U))
                                               (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                      using * 20 21 cong_filter_notIde
                                      by (metis Arr.simps(1) filter_notIde_Ide map_is_Nil_conv)
                                    thus ?thesis
                                      by (metis (no_types, lifting) Ide.simps(1) Resid.simps(2)
                                          Src_hd_eqI hd_map ide_char \<Lambda>.Src.simps(4)
                                          list.distinct(1) list.simps(9))
                                  qed
                                  finally show ?thesis by blast
                                qed
                              qed
                              show "cong [M \<^bold>\<circ> N] [M \<^bold>\<circ> N]"
                                using MN
                                by (meson head_redex_decomp \<Lambda>.Arr.simps(4) \<Lambda>.Arr_Src
                                    prfx_transitive)
                              show "map (\<lambda>X. X \<^bold>\<circ> N) (filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                                    map (\<lambda>X. X \<^bold>\<circ> N) (map \<Lambda>.un_App1 (u # U))"
                              proof -
                                have "Arr (map \<Lambda>.un_App1 (u # U))"
                                  using *** u Std Arr_map_un_App1
                                  by (metis Std_imp_Arr insert_subset list.discI list.simps(15)
                                      mem_Collect_eq)
                                moreover have "\<not> Ide (map \<Lambda>.un_App1 (u # U))"
                                  using *
                                  by (metis Collect_cong \<Lambda>.ide_char list.set_map
                                      set_Ide_subset_ide)
                                ultimately show ?thesis
                                  using *** u MN N cong_filter_notIde cong_map_App2
                                  by (meson \<Lambda>.Ide_Src)
                              qed
                            qed
                            also have "[M \<^bold>\<circ> N] @ map (\<lambda>X. X \<^bold>\<circ> N) (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>*
                                       [M \<^bold>\<circ> N] @ u # U"
                            proof -
                              have "map (\<lambda>X. X \<^bold>\<circ> N) (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>* u # U"
                              proof -
                                have "map (\<lambda>X. X \<^bold>\<circ> N) (map \<Lambda>.un_App1 (u # U)) = u # U"
                                proof (intro map_App_map_un_App1)
                                  show "Arr (u # U)"
                                    using Std Std_imp_Arr by simp
                                  show "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
                                    using *** u by auto
                                  show "\<Lambda>.Ide N"
                                    using N by simp
                                  show "\<Lambda>.un_App2 ` set (u # U) \<subseteq> {N}"
                                  proof -
                                    have "\<Lambda>.Src (\<Lambda>.un_App2 u) = \<Lambda>.Trg N"
                                      using ** seq u seq_char N
                                      apply (cases u)
                                          apply simp_all
                                      by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                                          \<Lambda>.lambda.inject(3) last_ConsL list.sel(1) seq)
                                    moreover have "\<Lambda>.Ide (\<Lambda>.un_App2 u) \<and> \<Lambda>.Ide N"
                                      using ** N by simp
                                    moreover have "Ide (map \<Lambda>.un_App2 (u # U))"
                                      using ** Std Std_imp_Arr Arr_map_un_App2
                                      by (metis Collect_cong Ide_char
                                          \<open>Arr (u # U)\<close> \<open>set (u # U) \<subseteq> Collect \<Lambda>.is_App\<close>
                                          \<Lambda>.ide_char list.set_map)
                                    ultimately show ?thesis
                                      by (metis hd_map \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self
                                          \<Lambda>.Ide_implies_Arr list.discI list.sel(1)
                                          list.set_map set_Ide_subset_single_hd)
                                  qed
                                qed
                                thus ?thesis
                                  by (simp add: Resid_Arr_self Std ide_char)
                              qed
                              thus ?thesis
                                using MN cong_append
                                by (metis (no_types, lifting) 1 cong_standard_development
                                    cong_transitive \<Lambda>.Arr.simps(4) seq)
                            qed
                            also have "[M \<^bold>\<circ> N] @ (u # U) = (M \<^bold>\<circ> N) # u # U"
                              by simp
                            finally show ?thesis by blast
                            next
                            assume N: "\<not> \<Lambda>.Ide N"
                            have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                  map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                      (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) @
                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (standard_development N)"
                              using 4 by simp
                            also have "... \<^sup>*\<sim>\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                   (M # filter notIde (map \<Lambda>.un_App1 (u # U))) @
                                                     map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]"
                            proof (intro cong_append)
                              show 23: "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                            (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) \<^sup>*\<sim>\<^sup>*
                                        map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                            (M # filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                using * A MN \<Lambda>.Ide_Src cong_map_App2 by blast
                              show 22: "map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                            (standard_development N) \<^sup>*\<sim>\<^sup>*
                                        map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]"
                                using 6 *** u Std Std_imp_Arr MN N cong_standard_development
                                      cong_map_App1
                                by presburger
                              show "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                             (stdz_insert M (filter notIde
                                                            (map \<Lambda>.un_App1 (u # U)))))
                                        (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                             (standard_development N))"
                              proof -
                                have "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                               (M # filter notIde
                                                           (map \<Lambda>.un_App1 (u # U))))
                                          (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N])"
                                proof
                                  show 26: "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                 (M # filter notIde
                                                             (map \<Lambda>.un_App1 (u # U))))"
                                    by (metis 23 Con_implies_Arr(2) Ide.simps(1) ide_char)
                                  show "Arr (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N])"
                                    by (meson 22 arr_char con_implies_arr(2) prfx_implies_con)   
                                  show "\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                         (M # filter notIde
                                                                     (map \<Lambda>.un_App1 (u # U))))) =
                                        \<Lambda>.Src (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                       [N]))"
                                  proof -
                                    have "\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                           (M # map \<Lambda>.un_App1 (u # U))))
                                           \<sim>
                                          \<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                    (M # filter notIde
                                                                           (map \<Lambda>.un_App1 (u # U)))))"
                                    proof -
                                      have "targets (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                         (M # filter notIde
                                                                     (map \<Lambda>.un_App1 (u # U)))) =
                                            targets (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                         (M # map \<Lambda>.un_App1 (u # U)))"
                                      proof -
                                        have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                  (M # filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                                              map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                  (M # map \<Lambda>.un_App1 (u # U))"
                                        proof -
                                          have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                    (M # map \<Lambda>.un_App1 (u # U)) =
                                                map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                    ([M] @ map \<Lambda>.un_App1 (u # U))"
                                            by simp
                                          also have "cong ... (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                   ([M] @ filter notIde
                                                                           (map \<Lambda>.un_App1 (u # U))))"
                                          proof -
                                            have "[M] @ map \<Lambda>.un_App1 (u # U) \<^sup>*\<sim>\<^sup>*
                                                  [M] @ filter notIde
                                                               (map \<Lambda>.un_App1 (u # U))"
                                            proof (intro cong_append)
                                              show "cong [M] [M]"
                                                using MN
                                                by (meson head_redex_decomp prfx_transitive)
                                              show "seq [M] (map \<Lambda>.un_App1 (u # U))"
                                              proof
                                                show "Arr [M]"
                                                  using MN by simp
                                                show "Arr (map \<Lambda>.un_App1 (u # U))"
                                                  using *** u Std Arr_map_un_App1
                                                  by (metis Std_imp_Arr insert_subset list.discI
                                                      list.simps(15) mem_Collect_eq)
                                                show "\<Lambda>.Trg (last [M]) =
                                                      \<Lambda>.Src (hd (map \<Lambda>.un_App1 (u # U)))"
                                                  using MN u seq seq_char Srcs_simp\<^sub>\<Lambda>\<^sub>P by auto
                                              qed
                                              show "cong (map \<Lambda>.un_App1 (u # U))
                                                         (filter notIde
                                                                 (map \<Lambda>.un_App1 (u # U)))"
                                              proof -
                                                have "Arr (map \<Lambda>.un_App1 (u # U))"
                                                  by (metis *** Arr_map_un_App1 Std Std_imp_Arr
                                                      insert_subset list.discI list.simps(15)
                                                      mem_Collect_eq u)
                                                moreover have "\<not> Ide (map \<Lambda>.un_App1 (u # U))"
                                                  using * set_Ide_subset_ide by fastforce
                                                ultimately show ?thesis
                                                  using cong_filter_notIde by blast
                                              qed
                                            qed
                                            thus "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                      ([M] @ map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>*
                                                  map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                      ([M] @ filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                              using MN cong_map_App2 \<Lambda>.Ide_Src by presburger
                                          qed
                                          finally show ?thesis by simp
                                        qed
                                        thus ?thesis
                                          using cong_implies_coterminal by blast
                                      qed
                                      moreover have "[\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                       (M # map \<Lambda>.un_App1 (u # U))))] \<in>
                                                     targets (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                  (M # map \<Lambda>.un_App1 (u # U)))"
                                        by (metis (no_types, lifting) 26 calculation mem_Collect_eq
                                            single_Trg_last_in_targets targets_char\<^sub>\<Lambda>\<^sub>P)
                                      moreover have "[\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                  (M # filter notIde
                                                                         (map \<Lambda>.un_App1 (u # U)))))] \<in>
                                                     targets (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                             (M # filter notIde
                                                                         (map \<Lambda>.un_App1 (u # U))))"
                                        using 26 single_Trg_last_in_targets by blast
                                      ultimately show ?thesis
                                        by (metis (no_types, lifting) 26 Ide.simps(1-2) Resid_rec(1)
                                            in_targets_iff ide_char)
                                    qed
                                    moreover have "\<Lambda>.Ide (\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                            (M # map \<Lambda>.un_App1 (u # U)))))"
                                      by (metis 6 MN \<Lambda>.Ide.simps(4) \<Lambda>.Ide_Src \<Lambda>.Trg.simps(3)
                                          \<Lambda>.Trg_Src last_ConsR last_map list.distinct(1)
                                          list.simps(9))
                                    moreover have "\<Lambda>.Ide (\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                                            (M # filter notIde
                                                                                   (map \<Lambda>.un_App1 (u # U))))))"
                                      using \<Lambda>.ide_backward_stable calculation(1-2) by fast
                                    ultimately show ?thesis
                                      by (metis (no_types, lifting) 6 MN hd_map
                                          \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src.simps(4)
                                          \<Lambda>.Trg.simps(3) \<Lambda>.Trg_Src \<Lambda>.cong_Ide_are_eq
                                          last.simps last_map list.distinct(1) list.map_disc_iff
                                          list.sel(1))
                                  qed
                                qed
                                thus ?thesis
                                  using 22 23 cong_respects_seq\<^sub>P by presburger
                              qed
                            qed
                            also have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                           (M # filter notIde (map \<Lambda>.un_App1 (u # U))) @
                                         map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N] =
                                       [M \<^bold>\<circ> \<Lambda>.Src N] @
                                          map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                              (filter notIde (map \<Lambda>.un_App1 (u # U))) @
                                           [\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))) N]"
                              by simp
                            also have 1: "[M \<^bold>\<circ> \<Lambda>.Src N] @
                                            map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                (filter notIde (map \<Lambda>.un_App1 (u # U))) @
                                             [\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))) N] \<^sup>*\<sim>\<^sup>*
                                          [M \<^bold>\<circ> \<Lambda>.Src N] @
                                            map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                              [\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))) N]"
                            proof (intro cong_append)
                              show "[M \<^bold>\<circ> \<Lambda>.Src N] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> \<Lambda>.Src N]"
                                using MN
                                by (meson head_redex_decomp lambda_calculus.Arr.simps(4)
                                    lambda_calculus.Arr_Src prfx_transitive)
                              show 21: "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                            (filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                                        map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U))"
                              proof -
                                have "filter notIde (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>*
                                      map \<Lambda>.un_App1 (u # U)"
                                proof -
                                  have "\<not> Ide (map \<Lambda>.un_App1 (u # U))"
                                    using *
                                    by (metis Collect_cong \<Lambda>.ide_char list.set_map
                                        set_Ide_subset_ide)
                                  thus ?thesis
                                    using *** u Std Std_imp_Arr Arr_map_un_App1
                                          cong_filter_notIde
                                    by (metis \<open>\<not> Ide (map \<Lambda>.un_App1 (u # U))\<close>
                                        list.distinct(1) mem_Collect_eq set_ConsD
                                        subset_code(1))
                                qed
                                thus ?thesis
                                  using MN cong_map_App2 [of "\<Lambda>.Src N"] \<Lambda>.Ide_Src by presburger
                              qed
                              show "[\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>*
                                    [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]"
                                by (metis "6" Con_implies_Arr(1) MN \<Lambda>.Ide_implies_Arr arr_char
                                    cong_reflexive \<Lambda>.Ide_iff_Src_self neq_Nil_conv
                                    orthogonal_App_single_single(1))
                              show "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                             (filter notIde (map \<Lambda>.un_App1 (u # U))))
                                        [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]"
                              proof
                                show "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                               (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                                  by (metis 21 Con_implies_Arr(2) Ide.simps(1) ide_char)
                                show "Arr [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]"
                                  by (metis Con_implies_Arr(2) Ide.simps(1)
                                      \<open>[\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>*
                                       [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]\<close>
                                      ide_char)
                                show "\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                  (filter notIde
                                                          (map \<Lambda>.un_App1 (u # U))))) =
                                      \<Lambda>.Src (hd [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N])"
                                  by (metis (no_types, lifting) 6 21 MN Trg_last_eqI
                                      \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr \<Lambda>.Src.simps(4)
                                      \<Lambda>.Trg.simps(3) \<Lambda>.Trg_Src last_map list.distinct(1)
                                      list.map_disc_iff list.sel(1))
                              qed
                              show "seq [M \<^bold>\<circ> \<Lambda>.Src N]
                                        (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                             (filter notIde (map \<Lambda>.un_App1 (u # U))) @
                                          [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N])"
                              proof
                                show "Arr [M \<^bold>\<circ> \<Lambda>.Src N]"
                                  using MN by simp
                                show "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                               (filter notIde (map \<Lambda>.un_App1 (u # U))) @
                                             [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N])"
                                  apply (intro Arr_appendI\<^sub>P)
                                    apply (metis 21 Con_implies_Arr(2) Ide.simps(1) ide_char)
                                   apply (metis Con_implies_Arr(1) Ide.simps(1)
                                      \<open>[\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>*
                                       [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]\<close> ide_char)
                                  by (metis (no_types, lifting) "21" Arr.simps(1)
                                      Arr_append_iff\<^sub>P Con_implies_Arr(2) Ide.simps(1)
                                      append_is_Nil_conv calculation ide_char not_Cons_self2)
                                show "\<Lambda>.Trg (last [M \<^bold>\<circ> \<Lambda>.Src N]) =
                                      \<Lambda>.Src (hd (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                     (filter notIde
                                                             (map \<Lambda>.un_App1 (u # U))) @
                                                        [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]))"
                                  by (metis (no_types, lifting) Con_implies_Arr(2) Ide.simps(1)
                                      Trg_last_Src_hd_eqI append_is_Nil_conv arr_append_imp_seq
                                      arr_char calculation ide_char not_Cons_self2)
                               qed
                            qed
                            also have "[M \<^bold>\<circ> \<Lambda>.Src N] @
                                         map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)(map \<Lambda>.un_App1 (u # U)) @
                                           [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>*
                                       [M \<^bold>\<circ> \<Lambda>.Src N] @
                                         [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                           map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))"
                            proof (intro cong_append [of "[\<Lambda>.App M (\<Lambda>.Src N)]"])
                              show "seq [M \<^bold>\<circ> \<Lambda>.Src N]
                                        (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                             (map \<Lambda>.un_App1 (u # U)) @
                                                [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N])"
                              proof
                                show "Arr [M \<^bold>\<circ> \<Lambda>.Src N]"
                                  using MN by simp
                                show "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                               (map \<Lambda>.un_App1 (u # U)) @ 
                                                  [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N])"
                                  by (metis (no_types, lifting) 1 Con_append(2) Con_implies_Arr(2)
                                      Ide.simps(1) append_is_Nil_conv ide_char not_Cons_self2)
                                show "\<Lambda>.Trg (last [M \<^bold>\<circ> \<Lambda>.Src N]) =
                                      \<Lambda>.Src (hd (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                     (map \<Lambda>.un_App1 (u # U)) @
                                                   [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N]))"
                                proof -
                                  have "\<Lambda>.Trg M = \<Lambda>.Src (\<Lambda>.un_App1 u)"
                                    using u seq
                                    by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                                        \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.inject(3) last_ConsL
                                        list.sel(1))
                                  thus ?thesis
                                    using MN by auto
                                qed
                              qed
                              show "[M \<^bold>\<circ> \<Lambda>.Src N] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> \<Lambda>.Src N]"
                                using MN
                                by (metis head_redex_decomp \<Lambda>.Arr.simps(4) \<Lambda>.Arr_Src
                                    prfx_transitive)
                              show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                      [\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>*
                                    [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                      map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))"
                              proof -
                                have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src (hd [N])) (map \<Lambda>.un_App1 (u # U)) @
                                        map (\<Lambda>.App (\<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U))))) [N] \<^sup>*\<sim>\<^sup>*
                                      map (\<Lambda>.App (\<Lambda>.Src (hd (map \<Lambda>.un_App1 (u # U))))) [N] @
                                        map  (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg (last [N])) (map \<Lambda>.un_App1 (u # U))"
                                proof -
                                  have "Arr (map \<Lambda>.un_App1 (u # U))"
                                    using Std *** u Arr_map_un_App1
                                    by (metis Std_imp_Arr insert_subset list.discI list.simps(15)
                                        mem_Collect_eq)
                                  moreover have "Arr [N]"
                                    using MN by simp
                                  ultimately show ?thesis
                                    using orthogonal_App_cong by blast
                                qed
                                moreover
                                have "map (\<Lambda>.App (\<Lambda>.Src (hd (map \<Lambda>.un_App1 (u # U))))) [N] =
                                      [\<Lambda>.Trg M \<^bold>\<circ> N]"
                                  by (metis Trg_last_Src_hd_eqI lambda_calculus.Src.simps(4)
                                      \<Lambda>.Trg.simps(3) \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.sel(3)
                                      last_ConsL list.sel(1) list.simps(8) list.simps(9) seq u)
                                moreover have "[\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] =
                                               map (\<Lambda>.App (\<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U))))) [N]"
                                  by (simp add: last_map)
                                ultimately show ?thesis
                                  using last_map by auto
                              qed
                            qed
                            also have "[M \<^bold>\<circ> \<Lambda>.Src N] @
                                         [\<Lambda>.Trg M \<^bold>\<circ> N] @
                                           map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)) =
                                       ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N]) @
                                          map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))"
                              by simp
                            also have "... \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> N] @ (u # U)"
                            proof (intro cong_append)
                              show "[M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> N]"
                                using MN \<Lambda>.resid_Arr_self \<Lambda>.Arr_not_Nil \<Lambda>.Ide_Trg ide_char
                                by auto
                              show 1: "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>* u # U"
                              proof -
                                have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)) = u # U"
                                proof (intro map_App_map_un_App1)
                                  show "Arr (u # U)"
                                    using Std Std_imp_Arr by simp
                                  show "set (u # U) \<subseteq> Collect \<Lambda>.is_App"
                                    using "***" u by auto
                                  show "\<Lambda>.Ide (\<Lambda>.Trg N)"
                                    using MN \<Lambda>.Ide_Trg by simp
                                  show "\<Lambda>.un_App2 ` set (u # U) \<subseteq> {\<Lambda>.Trg N}"
                                  proof -
                                    have "\<Lambda>.Src (\<Lambda>.un_App2 u) = \<Lambda>.Trg N"
                                      using u seq seq_char
                                      apply (cases u)
                                          apply simp_all
                                      by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                                          \<Lambda>.lambda.inject(3) last_ConsL list.sel(1) seq)
                                    moreover have "\<Lambda>.Ide (\<Lambda>.un_App2 u)"
                                      using ** by simp
                                    moreover have "Ide (map \<Lambda>.un_App2 (u # U))"
                                      using ** Std Std_imp_Arr Arr_map_un_App2
                                      by (metis Collect_cong Ide_char
                                          \<open>Arr (u # U)\<close> \<open>set (u # U) \<subseteq> Collect \<Lambda>.is_App\<close>
                                          \<Lambda>.ide_char list.set_map)
                                    ultimately show ?thesis
                                      by (metis \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr list.sel(1)
                                          list.set_map list.simps(9) set_Ide_subset_single_hd
                                          singleton_insert_inj_eq)
                                  qed
                                qed
                                thus ?thesis
                                  by (simp add: Resid_Arr_self Std ide_char)
                              qed
                              show "seq ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])
                                        (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)))"
                              proof
                                show "Arr ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])"
                                  using MN by simp
                                show "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)))"
                                  using MN Std Std_imp_Arr Arr_map_un_App1 Arr_map_App1
                                  by (metis 1 Con_implies_Arr(1) Ide.simps(1) ide_char)
                                show "\<Lambda>.Trg (last ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Trg M \<^bold>\<circ> N])) =
                                      \<Lambda>.Src (hd (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))))"
                                  using MN Std Std_imp_Arr Arr_map_un_App1 Arr_map_App1
                                        seq seq_char u Srcs_simp\<^sub>\<Lambda>\<^sub>P by auto
                              qed
                            qed
                            also have "[M \<^bold>\<circ> N] @ (u # U) = (M \<^bold>\<circ> N) # u # U"
                              by simp
                            finally show ?thesis by blast
                          qed
                        qed
                      qed
                    qed
                    show "\<lbrakk>\<not> \<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide;
                           \<not> \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide\<rbrakk>
                             \<Longrightarrow> ?thesis"
                    proof -
                      assume *: "\<not> \<Lambda>.un_App1 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      assume **: "\<not> \<Lambda>.un_App2 ` set (u # U) \<subseteq> Collect \<Lambda>.Ide"
                      show ?thesis
                      proof (intro conjI)
                        show "Std (stdz_insert (M \<^bold>\<circ> N) (u # U))"
                        proof -
                          have "Std (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                         (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) @
                                     map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                         (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                          proof (intro Std_append)
                            show "Std (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                      (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))))"
                              using * A \<Lambda>.Ide_Src MN Std_map_App1 by presburger
                            show "Std (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                            proof - 
                              have "\<Lambda>.Arr (\<Lambda>.un_App1 (last (u # U)))"
                                by (metis *** \<Lambda>.Arr.simps(4) Std Std_imp_Arr Arr.simps(2)
                                    Arr_append_iff\<^sub>P append_butlast_last_id append_self_conv2
                                    \<Lambda>.arr_char \<Lambda>.lambda.collapse(3) last.simps last_in_set
                                    list.discI mem_Collect_eq subset_code(1) u)
                              thus ?thesis
                                using ** B \<Lambda>.Ide_Trg MN Std_map_App2 by presburger
                            qed
                            show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                      (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) = [] \<or>
                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))) = [] \<or>
                                  \<Lambda>.sseq (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                               (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U))))))
                                         (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                  (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))))"
                            proof -
                              have "\<Lambda>.sseq (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                 (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U))))))
                                           (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                               (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))))"
                              proof -
                                let ?M = "\<Lambda>.un_App1 (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                          (stdz_insert M
                                                            (filter notIde
                                                                    (map \<Lambda>.un_App1 (u # U))))))"
                                let ?M' = "\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))"
                                let ?N = "\<Lambda>.Src N"
                                let ?N' = "\<Lambda>.un_App2
                                             (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                      (stdz_insert N
                                                        (filter notIde
                                                                (map \<Lambda>.un_App2 (u # U))))))"
                                have M: "?M = last (stdz_insert M
                                                     (filter notIde (map \<Lambda>.un_App1 (u # U))))"
                                  by (metis * A Ide.simps(1) Resid.simps(1) ide_char
                                      \<Lambda>.lambda.sel(3) last_map)
                                have N': "?N' = hd (stdz_insert N
                                                     (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                                  by (metis ** B Ide.simps(1) Resid.simps(2) ide_char
                                      \<Lambda>.lambda.sel(4) hd_map)
                                have AppMN: "last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                  (stdz_insert M
                                                    (filter notIde (map \<Lambda>.un_App1 (u # U))))) =
                                             ?M \<^bold>\<circ> ?N"
                                  by (metis * A Ide.simps(1) M Resid.simps(2) ide_char last_map)
                                moreover
                                have 4: "hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                 (stdz_insert N
                                                   (filter notIde (map \<Lambda>.un_App2 (u # U))))) =
                                         ?M' \<^bold>\<circ> ?N'"
                                  by (metis (no_types, lifting) ** B Resid.simps(2) con_char
                                      prfx_implies_con \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.discI(3)
                                      \<Lambda>.lambda.inject(3) list.map_sel(1))
                                moreover have MM: "\<Lambda>.elementary_reduction ?M"
                                  by (metis * A Arr.simps(1) Con_implies_Arr(2) Ide.simps(1)
                                      M ide_char in_mono last_in_set mem_Collect_eq)
                                moreover have NN': "\<Lambda>.elementary_reduction ?N'"
                                  using ** B N'
                                  by (metis Arr.simps(1) Con_implies_Arr(2) Ide.simps(1)
                                      ide_char in_mono list.set_sel(1) mem_Collect_eq)
                                moreover have "\<Lambda>.Trg ?M = ?M'"
                                proof -
                                  have 1: "[\<Lambda>.Trg ?M] \<^sup>*\<sim>\<^sup>* [?M']"
                                  proof -
                                    have "[\<Lambda>.Trg ?M] \<^sup>*\<sim>\<^sup>*
                                          [\<Lambda>.Trg (last (M # filter notIde (map \<Lambda>.un_App1 (u # U))))]"
                                    proof -
                                      have "targets (stdz_insert M
                                                      (filter notIde (map \<Lambda>.un_App1 (u # U)))) =
                                            targets (M # filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                        using * A cong_implies_coterminal by blast
                                      moreover
                                      have "[\<Lambda>.Trg (last (M # filter notIde (map \<Lambda>.un_App1 (u # U))))]
                                              \<in> targets (M # filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                        by (metis (no_types, lifting) * A \<Lambda>.Arr_Trg \<Lambda>.Ide_Trg
                                            Arr.simps(2) Arr_append_iff\<^sub>P Arr_iff_Con_self
                                            Con_implies_Arr(2) Ide.simps(1) Ide.simps(2)
                                            Resid_Arr_Ide_ind ide_char append_butlast_last_id
                                            append_self_conv2 \<Lambda>.arr_char in_targets_iff \<Lambda>.ide_char
                                            list.discI)
                                      ultimately show ?thesis
                                        using * A M in_targets_iff
                                        by (metis (no_types, lifting) Con_implies_Arr(1)
                                            con_char prfx_implies_con in_targets_iff)
                                    qed
                                    also have 2: "[\<Lambda>.Trg (last (M # filter notIde
                                                                      (map \<Lambda>.un_App1 (u # U))))] \<^sup>*\<sim>\<^sup>*
                                                  [\<Lambda>.Trg (last (filter notIde
                                                                  (map \<Lambda>.un_App1 (u # U))))]"
                                      by (metis (no_types, lifting) * prfx_transitive
                                          calculation empty_filter_conv last_ConsR list.set_map
                                          mem_Collect_eq subsetI)
                                    also have "[\<Lambda>.Trg (last (filter notIde
                                                               (map \<Lambda>.un_App1 (u # U))))] \<^sup>*\<sim>\<^sup>*
                                               [\<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U)))]"
                                    proof -
                                      have "map \<Lambda>.un_App1 (u # U) \<^sup>*\<sim>\<^sup>*
                                            filter notIde (map \<Lambda>.un_App1 (u # U))"
                                        by (metis (mono_tags, lifting) * *** Arr_map_un_App1
                                            Std Std_imp_Arr cong_filter_notIde empty_filter_conv
                                            filter_notIde_Ide insert_subset list.discI list.set_map
                                            list.simps(15) mem_Collect_eq subsetI u)
                                      thus ?thesis
                                        by (metis 2 Trg_last_eqI prfx_transitive)
                                    qed
                                    also have "[\<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U)))] = [?M']"
                                      by (simp add: last_map)
                                    finally show ?thesis by blast
                                  qed
                                  have 3: "\<Lambda>.Trg ?M = \<Lambda>.Trg ?M \\ ?M'"
                                    by (metis (no_types, lifting) 1 * A M Con_implies_Arr(2)
                                        Ide.simps(1) Resid_Arr_Ide_ind Resid_rec(1)
                                        ide_char target_is_ide in_targets_iff list.inject)
                                  also have "... = ?M'"
                                    by (metis (no_types, lifting) 1 4 Arr.simps(2) Con_implies_Arr(2)
                                        Ide.simps(1) Ide.simps(2) MM NN' Resid_Arr_Ide_ind
                                        Resid_rec(1) Src_hd_eqI calculation ide_char
                                        \<Lambda>.Ide_iff_Src_self \<Lambda>.Src_Trg \<Lambda>.arr_char
                                        \<Lambda>.elementary_reduction.simps(4)
                                        \<Lambda>.elementary_reduction_App_iff \<Lambda>.elementary_reduction_is_arr
                                        \<Lambda>.elementary_reduction_not_ide \<Lambda>.lambda.discI(3)
                                        \<Lambda>.lambda.sel(3) list.sel(1))
                                  finally show ?thesis by blast
                                qed
                                moreover have "?N = \<Lambda>.Src ?N'"
                                proof -
                                  have 1: "[\<Lambda>.Src ?N'] \<^sup>*\<sim>\<^sup>* [?N]"
                                  proof -
                                    have "sources (stdz_insert N
                                                     (filter notIde (map \<Lambda>.un_App2 (u # U)))) =
                                          sources [N]"
                                      using ** B
                                      by (metis Con_implies_Arr(2) Ide.simps(1) coinitialE
                                          cong_implies_coinitial ide_char sources_cons)
                                    thus ?thesis
                                      by (metis (no_types, lifting) AppMN ** B \<Lambda>.Ide_Src
                                          MM MN N' NN' \<Lambda>.Trg_Src Arr.simps(1) Arr.simps(2)
                                          Con_implies_Arr(1) Ide.simps(2) con_char ideE ide_char
                                          sources_cons \<Lambda>.arr_char in_targets_iff
                                          \<Lambda>.elementary_reduction.simps(4) \<Lambda>.elementary_reduction_App_iff
                                          \<Lambda>.elementary_reduction_is_arr \<Lambda>.elementary_reduction_not_ide
                                          \<Lambda>.lambda.disc(14) \<Lambda>.lambda.sel(4) last_ConsL list.exhaust_sel
                                          targets_single_Src)
                                  qed
                                  have "\<Lambda>.Src ?N' = \<Lambda>.Src ?N' \\ ?N"
                                    by (metis (no_types, lifting) 1 MN \<Lambda>.Coinitial_iff_Con
                                        \<Lambda>.Ide_Src Arr.simps(2) Ide.simps(1) Ide_implies_Arr
                                        Resid_rec(1) ide_char \<Lambda>.not_arr_null \<Lambda>.null_char
                                        \<Lambda>.resid_Arr_Ide)
                                  also have "... = ?N"
                                    by (metis 1 MN NN' Src_hd_eqI calculation \<Lambda>.Src_Src \<Lambda>.arr_char
                                        \<Lambda>.elementary_reduction_is_arr list.sel(1))
                                  finally show ?thesis by simp
                                qed
                                ultimately show ?thesis
                                  using u \<Lambda>.sseq.simps(4)
                                  by (metis (mono_tags, lifting))
                              qed
                              thus ?thesis by blast
                            qed
                          qed
                          thus ?thesis
                            using 4 by presburger
                        qed
                        show "\<not> Ide ((M \<^bold>\<circ> N) # u # U) \<longrightarrow>
                                  stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                        proof
                          have "stdz_insert (M \<^bold>\<circ> N) (u # U) =
                                map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                    (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) @
                                map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                   (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))))"
                            using 4 by simp
                          also have "... \<^sup>*\<sim>\<^sup>* map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                 (M # map \<Lambda>.un_App1 (u # U)) @
                                                 map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                     (N # map \<Lambda>.un_App2 (u # U))"
                          proof (intro cong_append)
                            have X: "stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                                     M # map \<Lambda>.un_App1 (u # U)"
                            proof -
                              have "stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U))) \<^sup>*\<sim>\<^sup>*
                                    [M] @ filter notIde (map \<Lambda>.un_App1 (u # U))"
                                using * A by simp
                              also have "[M] @ filter notIde (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>*
                                         [M] @ map \<Lambda>.un_App1 (u # U)"
                              proof -
                                have "filter notIde (map \<Lambda>.un_App1 (u # U)) \<^sup>*\<sim>\<^sup>*
                                      map \<Lambda>.un_App1 (u # U)"
                                  using * cong_filter_notIde
                                  by (metis (mono_tags, lifting) *** Arr_map_un_App1 Std
                                      Std_imp_Arr empty_filter_conv filter_notIde_Ide insert_subset
                                      list.discI list.set_map list.simps(15) mem_Collect_eq subsetI u)
                                moreover have "seq [M] (filter notIde (map \<Lambda>.un_App1 (u # U)))"
                                  by (metis * A Arr.simps(1) Con_implies_Arr(1) append_Cons
                                      append_Nil arr_append_imp_seq arr_char calculation
                                      ide_implies_arr list.discI)
                                ultimately show ?thesis
                                  using cong_append cong_reflexive by blast
                              qed
                              also have "[M] @ map \<Lambda>.un_App1 (u # U) =
                                         M # map \<Lambda>.un_App1 (u # U)"
                                by simp
                              finally show ?thesis by blast
                            qed
                            have Y: "stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))) \<^sup>*\<sim>\<^sup>*
                                     N # map \<Lambda>.un_App2 (u # U)"
                            proof -
                              have 5: "stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U))) \<^sup>*\<sim>\<^sup>*
                                       [N] @ filter notIde (map \<Lambda>.un_App2 (u # U))"
                                using ** B by simp
                              also have "[N] @ filter notIde (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
                                         [N] @ map \<Lambda>.un_App2 (u # U)"
                              proof -
                                have "filter notIde (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
                                      map \<Lambda>.un_App2 (u # U)"
                                  using ** cong_filter_notIde
                                  by (metis (mono_tags, lifting) *** Arr_map_un_App2 Std
                                      Std_imp_Arr empty_filter_conv filter_notIde_Ide insert_subset
                                      list.discI list.set_map list.simps(15) mem_Collect_eq subsetI u)
                                moreover have "seq [N] (filter notIde (map \<Lambda>.un_App2 (u # U)))"
                                  by (metis 5 Arr.simps(1) Con_implies_Arr(2) Ide.simps(1)
                                      arr_append_imp_seq arr_char calculation ide_char not_Cons_self2)
                                ultimately show ?thesis
                                  using cong_append cong_reflexive by blast
                              qed
                              also have "[N] @ map \<Lambda>.un_App2 (u # U) =
                                         N # map \<Lambda>.un_App2 (u # U)"
                                by simp
                              finally show ?thesis by blast
                            qed
                            show "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                           (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))))
                                      (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))))"
                              by (metis 4 * ** A B Ide.simps(1) Nil_is_append_conv Nil_is_map_conv
                                  Resid.simps(1) Std_imp_Arr \<open>Std (stdz_insert (M \<^bold>\<circ> N) (u # U))\<close>
                                  arr_append_imp_seq arr_char ide_char)
                            show "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                      (stdz_insert M (filter notIde (map \<Lambda>.un_App1 (u # U)))) \<^sup>*\<sim>\<^sup>*
                                  map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (M # map \<Lambda>.un_App1 (u # U))"
                              using X cong_map_App2 MN lambda_calculus.Ide_Src by presburger
                            show "map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (stdz_insert N (filter notIde (map \<Lambda>.un_App2 (u # U)))) \<^sup>*\<sim>\<^sup>*
                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                      (N # map \<Lambda>.un_App2 (u # U))"
                            proof -
                              have "set U \<subseteq> Collect \<Lambda>.Arr \<inter> Collect \<Lambda>.is_App"
                                using *** Std Std_implies_set_subset_elementary_reduction
                                      \<Lambda>.elementary_reduction_is_arr
                                by blast
                              hence "\<Lambda>.Ide (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))"
                                by (metis inf.boundedE \<Lambda>.Arr.simps(4) \<Lambda>.Ide_Trg
                                    \<Lambda>.lambda.collapse(3) last.simps last_in_set mem_Collect_eq
                                    subset_eq u)
                              thus ?thesis
                                using Y cong_map_App1 by blast
                            qed
                          qed
                          also have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (M # map \<Lambda>.un_App1 (u # U)) @
                                       map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                           (N # map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>* 
                                     [M \<^bold>\<circ> N] @ [u] @ U"
                          proof -
                            have "(map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (M # map \<Lambda>.un_App1 (u # U)) @
                                   map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                       (N # map \<Lambda>.un_App2 (u # U))) =
                                  ([M \<^bold>\<circ> \<Lambda>.Src N] @
                                     map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U))) @
                                  ([\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))) \<^bold>\<circ> N] @
                                     map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                         (map \<Lambda>.un_App2 (u # U)))"
                              by simp
                            also have "... = [M \<^bold>\<circ> \<Lambda>.Src N] @
                                                (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                                 map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]) @
                                                map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                    (map \<Lambda>.un_App2 (u # U))"
                              by auto
                            also have "... \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> \<Lambda>.Src N] @
                                                 (map (\<Lambda>.App (\<Lambda>.Src (\<Lambda>.un_App1 u))) [N] @
                                                   map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))) @
                                                   map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                       (map \<Lambda>.un_App2 (u # U))"
                            proof -
                              (*
                               * TODO: (intro congI) does not work because it breaks the expression
                               * down too far, resulting in a false subgoal.
                               *)
                              have "(map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                       map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]) @
                                      map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                          (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
                                    (map (\<Lambda>.App (\<Lambda>.Src (\<Lambda>.un_App1 u))) [N] @
                                       map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))) @
                                       map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                   (map \<Lambda>.un_App2 (u # U))"
                              proof -
                                have 1: "Arr (map \<Lambda>.un_App1 (u # U))"
                                  using u ***
                                  by (metis Arr_map_un_App1 Std Std_imp_Arr list.discI
                                     mem_Collect_eq set_ConsD subset_code(1))
                                have "map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Src N)) (map \<Lambda>.un_App1 (u # U)) @
                                          map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N] \<^sup>*\<sim>\<^sup>*
                                        map (\<Lambda>.App (\<Lambda>.Src (\<Lambda>.un_App1 u))) [N] @
                                          map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Trg N)) (map \<Lambda>.un_App1 (u # U))"
                                proof -
                                  have "Arr [N]"
                                      using MN by simp
                                  moreover have "\<Lambda>.Trg (last (map \<Lambda>.un_App1 (u # U))) =
                                                 \<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))"
                                    by (simp add: last_map)
                                  ultimately show ?thesis
                                      using 1 orthogonal_App_cong [of "map \<Lambda>.un_App1 (u # U)" "[N]"]
                                      by simp
                                qed
                                moreover have "seq (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                                    map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N])
                                                    (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                         (map \<Lambda>.un_App2 (u # U)))"
                                proof
                                  show "Arr (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                 (map \<Lambda>.un_App1 (u # U)) @
                                             map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N])"
                                    by (metis Con_implies_Arr(1) Ide.simps(1) calculation ide_char)
                                  show "Arr (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                 (map \<Lambda>.un_App2 (u # U)))"
                                    using u ***
                                    by (metis 1 Arr_imp_arr_last Arr_map_App2 Arr_map_un_App2
                                        Std Std_imp_Arr \<Lambda>.Ide_Trg \<Lambda>.arr_char last_map list.discI
                                        mem_Collect_eq set_ConsD subset_code(1))
                                  show "\<Lambda>.Trg (last (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N)
                                                         (map \<Lambda>.un_App1 (u # U)) @
                                                     map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                         [N])) =
                                        \<Lambda>.Src (hd (map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                       (map \<Lambda>.un_App2 (u # U))))"
                                  proof -
                                    have 1: "\<Lambda>.Arr (\<Lambda>.un_App1 u)"
                                      using u \<Lambda>.is_App_def by force
                                    have 2: "U \<noteq> [] \<Longrightarrow> \<Lambda>.Arr (\<Lambda>.un_App1 (last U))"
                                      by (metis *** Arr_imp_arr_last Arr_map_un_App1
                                          \<open>U \<noteq> [] \<Longrightarrow> Arr U\<close> \<Lambda>.arr_char last_map)
                                    have 3: "\<Lambda>.Trg N = \<Lambda>.Src (\<Lambda>.un_App2 u)"
                                      by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                                          \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.inject(3) last_ConsL
                                          list.sel(1) seq u)
                                    show ?thesis
                                      using u *** seq 1 2 3
                                      by (cases "U = []") auto
                                  qed
                                qed
                                moreover have "map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                   (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
                                               map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                   (map \<Lambda>.un_App2 (u # U))"
                                  using calculation(2) cong_reflexive by blast
                                ultimately show ?thesis
                                  using cong_append by blast
                              qed
                              moreover have "seq [M \<^bold>\<circ> \<Lambda>.Src N]
                                                 ((map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                                   map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]) @
                                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                      (map \<Lambda>.un_App2 (u # U)))"
                              proof
                                show "Arr [M \<^bold>\<circ> \<Lambda>.Src N]"
                                    using MN by simp
                                show "Arr ((map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                              map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]) @
                                              map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                              (map \<Lambda>.un_App2 (u # U)))"
                                    using MN u seq
                                    by (metis Con_implies_Arr(1) Ide.simps(1) calculation ide_char)
                                show "\<Lambda>.Trg (last [M \<^bold>\<circ> \<Lambda>.Src N]) =
                                      \<Lambda>.Src (hd ((map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Src N) (map \<Lambda>.un_App1 (u # U)) @
                                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U))))) [N]) @
                                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                      (map \<Lambda>.un_App2 (u # U))))"
                                  using MN u seq seq_char Srcs_simp\<^sub>\<Lambda>\<^sub>P
                                  by (cases u) auto
                              qed
                              ultimately show ?thesis
                                using cong_append
                                by (meson Resid_Arr_self ide_char seq_char)
                            qed
                            also have "[M \<^bold>\<circ> \<Lambda>.Src N] @
                                         (map (\<Lambda>.App (\<Lambda>.Src (\<Lambda>.un_App1 u))) [N] @
                                           map (\<lambda>X. \<Lambda>.App X (\<Lambda>.Trg N)) (map \<Lambda>.un_App1 (u # U))) @
                                           map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                               (map \<Lambda>.un_App2 (u # U)) =
                                       ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Src (\<Lambda>.un_App1 u) \<^bold>\<circ> N]) @
                                         (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U))) @
                                            map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                (map \<Lambda>.un_App2 (u # U))"
                              by simp
                            also have "... \<^sup>*\<sim>\<^sup>* ([M \<^bold>\<circ> N] @ [u] @ U)"
                            proof -
                              have "[M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Src (\<Lambda>.un_App1 u) \<^bold>\<circ> N] \<^sup>*\<sim>\<^sup>* [M \<^bold>\<circ> N]"
                              proof -
                                have "\<Lambda>.Src (\<Lambda>.un_App1 u) = \<Lambda>.Trg M"
                                  by (metis Trg_last_Src_hd_eqI \<Lambda>.Src.simps(4) \<Lambda>.Trg.simps(3)
                                      \<Lambda>.lambda.collapse(3) \<Lambda>.lambda.inject(3) last.simps
                                      list.sel(1) seq u)
                                thus ?thesis
                                  using MN u seq seq_char \<Lambda>.Arr_not_Nil \<Lambda>.resid_Arr_self ide_char
                                        \<Lambda>.Ide_Trg
                                  by simp
                              qed
                              moreover have "map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)) @
                                               map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                   (map \<Lambda>.un_App2 (u # U)) \<^sup>*\<sim>\<^sup>*
                                             [u] @ U"
                              proof -
                                have "Arr ([u] @ U)"
                                  by (simp add: Std)
                                moreover have "set ([u] @ U) \<subseteq> Collect \<Lambda>.is_App"
                                  using *** u by auto
                                moreover have "\<Lambda>.Src (\<Lambda>.un_App2 (hd ([u] @ U))) = \<Lambda>.Trg N"
                                proof -
                                  have "\<Lambda>.Ide (\<Lambda>.Trg N)"
                                    using MN lambda_calculus.Ide_Trg by presburger
                                  moreover have "\<Lambda>.Ide (\<Lambda>.Src (\<Lambda>.un_App2 (hd ([u] @ U))))"
                                    by (metis Std Std_implies_set_subset_elementary_reduction
                                        \<Lambda>.Ide_Src \<Lambda>.arr_iff_has_source \<Lambda>.ide_implies_arr
                                        \<open>set ([u] @ U) \<subseteq> Collect \<Lambda>.is_App\<close> append_Cons
                                        \<Lambda>.elementary_reduction_App_iff \<Lambda>.elementary_reduction_is_arr
                                        \<Lambda>.sources_char\<^sub>\<Lambda> list.sel(1) list.set_intros(1)
                                        mem_Collect_eq subset_code(1))
                                  moreover have "\<Lambda>.Src (\<Lambda>.Trg N) =
                                                 \<Lambda>.Src (\<Lambda>.Src (\<Lambda>.un_App2 (hd ([u] @ U))))"
                                  proof -
                                    have "\<Lambda>.Src (\<Lambda>.Trg N) = \<Lambda>.Trg N"
                                      using MN by simp
                                    also have "... = \<Lambda>.Src (\<Lambda>.un_App2 u)"
                                      using u seq seq_char Srcs_simp\<^sub>\<Lambda>\<^sub>P
                                      by (cases u) auto
                                    also have "... = \<Lambda>.Src (\<Lambda>.Src (\<Lambda>.un_App2 (hd ([u] @ U))))"
                                      by (metis \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr
                                          \<open>\<Lambda>.Ide (\<Lambda>.Src (\<Lambda>.un_App2 (hd ([u] @ U))))\<close>
                                          append_Cons list.sel(1))
                                    finally show ?thesis by blast
                                  qed
                                  ultimately show ?thesis
                                    by (metis \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr)
                                qed           
                                ultimately show ?thesis
                                  using map_App_decomp
                                  by (metis append_Cons append_Nil)
                              qed
                              moreover have "seq ([M \<^bold>\<circ> \<Lambda>.Src N] @ [\<Lambda>.Src (\<Lambda>.un_App1 u) \<^bold>\<circ> N])
                                                 (map (\<lambda>X. X \<^bold>\<circ> \<Lambda>.Trg N) (map \<Lambda>.un_App1 (u # U)) @
                                                  map (\<Lambda>.App (\<Lambda>.Trg (\<Lambda>.un_App1 (last (u # U)))))
                                                      (map \<Lambda>.un_App2 (u # U)))"
                                using calculation(1-2) cong_respects_seq\<^sub>P seq by auto
                              ultimately show ?thesis
                                using cong_append by presburger
                            qed
                            finally show ?thesis by blast
                          qed
                          also have "[M \<^bold>\<circ> N] @ [u] @ U = (M \<^bold>\<circ> N) # u # U"
                            by simp
                          finally show "stdz_insert (M \<^bold>\<circ> N) (u # U) \<^sup>*\<sim>\<^sup>* (M \<^bold>\<circ> N) # u # U"
                            by blast
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      text \<open>
        The eight remaining subgoals are now trivial consequences of fact \<open>*\<close>.
        Unfortunately, I haven't found a way to discharge them without having to state each
        one of them explicitly.
      \<close>
      show "\<And>N u U. \<lbrakk>\<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                      \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<sharp> \<^bold>\<circ> N) (hd (u # U));
                       \<Lambda>.contains_head_reduction (\<^bold>\<sharp> \<^bold>\<circ> N);
                       \<Lambda>.Ide ((\<^bold>\<sharp> \<^bold>\<circ> N) \\ \<Lambda>.head_redex (\<^bold>\<sharp> \<^bold>\<circ> N))\<rbrakk>
                         \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                      \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<sharp> \<^bold>\<circ> N) (hd (u # U));
                       \<Lambda>.contains_head_reduction (\<^bold>\<sharp> \<^bold>\<circ> N);
                       \<not> \<Lambda>.Ide ((\<^bold>\<sharp> \<^bold>\<circ> N) \\ \<Lambda>.head_redex (\<^bold>\<sharp> \<^bold>\<circ> N))\<rbrakk>
                         \<Longrightarrow> ?P ((\<^bold>\<sharp> \<^bold>\<circ> N) \\ \<Lambda>.head_redex (\<^bold>\<sharp> \<^bold>\<circ> N)) (u # U);
                      \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<sharp> \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (\<^bold>\<sharp> \<^bold>\<circ> N);
                       \<Lambda>.contains_head_reduction (hd (u # U));
                       \<Lambda>.Ide ((\<^bold>\<sharp> \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<sharp> \<^bold>\<circ> N))\<rbrakk>
                         \<Longrightarrow> ?P (\<Lambda>.head_strategy (\<^bold>\<sharp> \<^bold>\<circ> N)) (tl (u # U));
                      \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<sharp> \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (\<^bold>\<sharp> \<^bold>\<circ> N);
                       \<Lambda>.contains_head_reduction (hd (u # U));
                       \<not> \<Lambda>.Ide ((\<^bold>\<sharp> \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<sharp> \<^bold>\<circ> N))\<rbrakk>
                         \<Longrightarrow> ?P (\<Lambda>.resid (\<^bold>\<sharp> \<^bold>\<circ> N) (\<Lambda>.head_strategy (\<^bold>\<sharp> \<^bold>\<circ> N))) (tl (u # U));
                      \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<sharp> \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (\<^bold>\<sharp> \<^bold>\<circ> N);
                       \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                         \<Longrightarrow> ?P \<^bold>\<sharp> (filter notIde (map \<Lambda>.un_App1 (u # U)));
                      \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<sharp> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<sharp> \<^bold>\<circ> N) (hd (u # U));
                       \<not> \<Lambda>.contains_head_reduction (\<^bold>\<sharp> \<^bold>\<circ> N);
                     \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                         \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (u # U)))\<rbrakk>
                    \<Longrightarrow> ?P (\<^bold>\<sharp> \<^bold>\<circ> N) (u # U)"
        using * \<Lambda>.lambda.disc(6) by presburger
      show "\<And>x N u U. \<lbrakk>\<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (hd (u # U));
                         \<Lambda>.contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N);
                         \<Lambda>.Ide ((\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \\ \<Lambda>.head_redex (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (hd (u # U));
                         \<Lambda>.contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N);
                         \<not> \<Lambda>.Ide ((\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \\ \<Lambda>.head_redex (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P ((\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \\ \<Lambda>.head_redex (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N)) (u # U);
                        \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (hd (u # U));
                         \<not> \<Lambda>.contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N);
                         \<Lambda>.contains_head_reduction (hd (u # U));
                         \<Lambda>.Ide ((\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P (\<Lambda>.head_strategy (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N)) (tl (u # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (hd (u # U));
                         \<not> \<Lambda>.contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N);
                         \<Lambda>.contains_head_reduction (hd (u # U));
                         \<not> \<Lambda>.Ide ((\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P ((\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N)) (tl (u # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (hd (u # U));
                         \<not> \<Lambda>.contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N);
                         \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                           \<Longrightarrow> ?P \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> (filter notIde (map \<Lambda>.un_App1 (u # U)));
                        \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (hd (u # U));
                         \<not> \<Lambda>.contains_head_reduction (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N);
                         \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                           \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (u # U)))\<rbrakk>
                    \<Longrightarrow> ?P (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> \<^bold>\<circ> N) (u # U)"
        using * \<Lambda>.lambda.disc(7) by presburger
      show "\<And>M1 M2 N u U. \<lbrakk>\<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N); \<Lambda>.seq (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<Lambda>.contains_head_reduction (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N);
                            \<Lambda>.Ide ((M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N); \<Lambda>.seq (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<Lambda>.contains_head_reduction (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N);
                            \<not> \<Lambda>.Ide ((M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P ((M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N)) (u # U);
                           \<lbrakk>\<not> \<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N); \<Lambda>.seq (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N);
                            \<Lambda>.contains_head_reduction (hd (u # U));
                            \<Lambda>.Ide ((M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P (\<Lambda>.head_strategy (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N); \<Lambda>.seq (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N);
                            \<Lambda>.contains_head_reduction (hd (u # U));
                            \<not> \<Lambda>.Ide ((M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P ((M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N); \<Lambda>.seq (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N);
                            \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                              \<Longrightarrow> ?P (M1 \<^bold>\<circ> M2) (filter notIde (map \<Lambda>.un_App1 (u # U)));
                           \<lbrakk>\<not> \<Lambda>.Ide (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N); \<Lambda>.seq (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N);
                            \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                              \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (u # U)))\<rbrakk>
                    \<Longrightarrow> ?P (M1 \<^bold>\<circ> M2 \<^bold>\<circ> N) (u # U)"
         using * \<Lambda>.lambda.disc(9) by presburger
      show "\<And>M1 M2 N u U. \<lbrakk>\<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<Lambda>.contains_head_reduction (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N);
                            \<Lambda>.Ide ((\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) \\ (\<Lambda>.head_redex (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N)))\<rbrakk>
                              \<Longrightarrow> ?P (hd (u # U)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<Lambda>.contains_head_reduction (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N);
                            \<not> \<Lambda>.Ide ((\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) \\ (\<Lambda>.head_redex (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N)))\<rbrakk>
                              \<Longrightarrow> ?P (\<Lambda>.resid (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (\<Lambda>.head_redex (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N)))
                                     (u # U);
                           \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N);
                            \<Lambda>.contains_head_reduction (hd (u # U));
                            \<Lambda>.Ide ((\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P (\<Lambda>.head_strategy (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N)) (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N);
                            \<Lambda>.contains_head_reduction (hd (u # U));
                            \<not> \<Lambda>.Ide ((\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P ((\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N))
                                     (tl (u # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N);
                            \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                              \<Longrightarrow> ?P (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2) (filter notIde (map \<Lambda>.un_App1 (u # U)));
                           \<lbrakk>\<not> \<Lambda>.Ide (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N); \<Lambda>.seq (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (hd (u # U));
                            \<not> \<Lambda>.contains_head_reduction (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N);
                            \<not> \<Lambda>.contains_head_reduction (hd (u # U))\<rbrakk>
                              \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (u # U)))\<rbrakk>
                    \<Longrightarrow> ?P (\<^bold>\<lambda>\<^bold>[M1\<^bold>] \<^bold>\<Zspot> M2 \<^bold>\<circ> N) (u # U)"
         using * \<Lambda>.lambda.disc(10) by presburger
      show "\<And>M N U. \<lbrakk>\<Lambda>.Ide (M \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (\<^bold>\<sharp> # U)) (tl (\<^bold>\<sharp> # U));
                     \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<sharp> # U));
                      \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                      \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                        \<Longrightarrow> ?P (hd (\<^bold>\<sharp> # U)) (tl (\<^bold>\<sharp> # U));
                     \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<sharp> # U));
                      \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                      \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                        \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (\<^bold>\<sharp> # U);
                     \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<sharp> # U));
                      \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                      \<Lambda>.contains_head_reduction (hd (\<^bold>\<sharp> # U));
                      \<Lambda>.Ide (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N)))\<rbrakk>
                        \<Longrightarrow> ?P (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (\<^bold>\<sharp> # U));
                     \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<sharp> # U));
                      \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                      \<Lambda>.contains_head_reduction (hd (\<^bold>\<sharp> # U));
                      \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                        \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (\<^bold>\<sharp> # U));
                     \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<sharp> # U));
                      \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                      \<not> \<Lambda>.contains_head_reduction (hd (\<^bold>\<sharp> # U))\<rbrakk>
                        \<Longrightarrow> ?P M (filter notIde (map \<Lambda>.un_App1 (\<^bold>\<sharp> # U)));
                     \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<sharp> # U));
                      \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                      \<not> \<Lambda>.contains_head_reduction (hd (\<^bold>\<sharp> # U))\<rbrakk>
                        \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (\<^bold>\<sharp> # U)))\<rbrakk>
                   \<Longrightarrow> ?P (M \<^bold>\<circ> N) (\<^bold>\<sharp> # U)"
        using * \<Lambda>.lambda.disc(16) by presburger
      show "\<And>M N x U. \<lbrakk>\<Lambda>.Ide (M \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U)) (tl (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U)) (tl (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U);
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<Lambda>.contains_head_reduction (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<Lambda>.contains_head_reduction (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<not> \<Lambda>.contains_head_reduction (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U))\<rbrakk>
                           \<Longrightarrow> ?P M (filter notIde (map \<Lambda>.un_App1 (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U)));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<not> \<Lambda>.contains_head_reduction (hd (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U))\<rbrakk>
                           \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U)))\<rbrakk>
                   \<Longrightarrow> ?P (M \<^bold>\<circ> N) (\<^bold>\<guillemotleft>x\<^bold>\<guillemotright> # U)"
        using * \<Lambda>.lambda.disc(17) by presburger
      show "\<And>M N P U. \<lbrakk>\<Lambda>.Ide (M \<^bold>\<circ> N) \<Longrightarrow> ?P (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U)) (tl (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U)) (tl (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                           \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U);
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<Lambda>.contains_head_reduction (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                            \<Longrightarrow> ?P (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<Lambda>.contains_head_reduction (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                            \<Longrightarrow> ?P (\<Lambda>.resid (M \<^bold>\<circ> N) (\<Lambda>.head_strategy (M \<^bold>\<circ> N))) (tl (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<not> \<Lambda>.contains_head_reduction (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U))\<rbrakk>
                            \<Longrightarrow> ?P M (filter notIde (map \<Lambda>.un_App1 (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U)));
                        \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U));
                         \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                         \<not> \<Lambda>.contains_head_reduction (hd (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U))\<rbrakk>
                            \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U)))\<rbrakk>
                  \<Longrightarrow> ?P (M \<^bold>\<circ> N) (\<^bold>\<lambda>\<^bold>[P\<^bold>] # U)"
        using * \<Lambda>.lambda.disc(18) by presburger
      show "\<And>M N P1 P2 U. \<lbrakk>\<Lambda>.Ide (M \<^bold>\<circ> N)
                             \<Longrightarrow> ?P (hd ((P1 \<^bold>\<circ> P2) # U)) (tl ((P1 \<^bold>\<circ> P2) # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                            \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P (hd ((P1 \<^bold>\<circ> P2) # U)) (tl((P1 \<^bold>\<circ> P2) # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                            \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_redex (M \<^bold>\<circ> N)) ((P1 \<^bold>\<circ> P2) # U);
                           \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                            \<Lambda>.contains_head_reduction (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P (\<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl ((P1 \<^bold>\<circ> P2) # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                            \<Lambda>.contains_head_reduction (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<not> \<Lambda>.Ide ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N))\<rbrakk>
                              \<Longrightarrow> ?P ((M \<^bold>\<circ> N) \\ \<Lambda>.head_strategy (M \<^bold>\<circ> N)) (tl ((P1 \<^bold>\<circ> P2) # U));
                           \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                            \<not> \<Lambda>.contains_head_reduction (hd ((P1 \<^bold>\<circ> P2) # U))\<rbrakk>
                              \<Longrightarrow> ?P M (filter notIde (map \<Lambda>.un_App1 ((P1 \<^bold>\<circ> P2) # U)));
                           \<lbrakk>\<not> \<Lambda>.Ide (M \<^bold>\<circ> N); \<Lambda>.seq (M \<^bold>\<circ> N) (hd ((P1 \<^bold>\<circ> P2) # U));
                            \<not> \<Lambda>.contains_head_reduction (M \<^bold>\<circ> N);
                            \<not> \<Lambda>.contains_head_reduction (hd ((P1 \<^bold>\<circ> P2) # U))\<rbrakk>
                              \<Longrightarrow> ?P N (filter notIde (map \<Lambda>.un_App2 ((P1 \<^bold>\<circ> P2) # U)))\<rbrakk>
                  \<Longrightarrow> ?P (M \<^bold>\<circ> N) ((P1 \<^bold>\<circ> P2) # U)"
        using * \<Lambda>.lambda.disc(19) by presburger
    qed

    subsubsection "The Standardization Theorem"

    text \<open>
      Using the function \<open>standardize\<close>, we can now prove the Standardization Theorem.
      There is still a little bit more work to do, because we have to deal with various
      cases in which the reduction path to be standardized is empty or consists
      entirely of identities.
    \<close>

    theorem standardization_theorem:
    shows "Arr T \<Longrightarrow> Std (standardize T) \<and> (Ide T \<longrightarrow> standardize T = []) \<and>
                     (\<not> Ide T \<longrightarrow> cong (standardize T) T)"
    proof (induct T)
      show "Arr [] \<Longrightarrow> Std (standardize []) \<and> (Ide [] \<longrightarrow> standardize [] = []) \<and>
                       (\<not> Ide [] \<longrightarrow> cong (standardize []) [])"
        by simp
      fix t T
      assume ind: "Arr T \<Longrightarrow> Std (standardize T) \<and> (Ide T \<longrightarrow> standardize T = []) \<and>
                             (\<not> Ide T \<longrightarrow> cong (standardize T) T)"
      assume tT: "Arr (t # T)"
      have t: "\<Lambda>.Arr t"
        using tT Arr_imp_arr_hd by force
      show "Std (standardize (t # T)) \<and> (Ide (t # T) \<longrightarrow> standardize (t # T) = []) \<and>
            (\<not> Ide (t # T) \<longrightarrow> cong (standardize (t # T)) (t # T))"
      proof (cases "T = []")
        show "T = [] \<Longrightarrow> ?thesis"
          using t tT Ide_iff_standard_development_empty Std_standard_development
                cong_standard_development
          by simp
        assume 0: "T \<noteq> []"
        hence T: "Arr T"
          using tT
          by (metis Arr_imp_Arr_tl list.sel(3))
        show ?thesis
        proof (intro conjI)
          show "Std (standardize (t # T))"
          proof -
            have 1: "\<not> Ide T \<Longrightarrow> seq [t] (standardize T)"
              using t T ind 0 ide_char Con_implies_Arr(1)
              apply (intro seqI\<^sub>\<Lambda>\<^sub>P)
                apply simp
               apply (metis Con_implies_Arr(1) Ide.simps(1) ide_char)
              by (metis Src_hd_eqI Trg_last_Src_hd_eqI \<open>T \<noteq> []\<close> append_Cons arrI\<^sub>P
                        arr_append_imp_seq list.distinct(1) self_append_conv2 tT)
            show ?thesis
              using T 1 ind Std_standard_development stdz_insert_correctness by auto
          qed
          show "Ide (t # T) \<longrightarrow> standardize (t # T) = []"
            using Ide_consE Ide_iff_standard_development_empty Ide_implies_Arr ind
                  \<Lambda>.Ide_implies_Arr \<Lambda>.ide_char
            by (metis list.sel(1,3) standardize.simps(1-2) stdz_insert.simps(1))
          show "\<not> Ide (t # T) \<longrightarrow> standardize (t # T) \<^sup>*\<sim>\<^sup>* t # T"
          proof
            assume 1: "\<not> Ide (t # T)"
            show "standardize (t # T) \<^sup>*\<sim>\<^sup>* t # T"
            proof (cases "\<Lambda>.Ide t")
              assume t: "\<Lambda>.Ide t"
              have 2: "\<not> Ide T"
                using 1 t tT by fastforce
              have "standardize (t # T) = stdz_insert t (standardize T)"
                by simp
              also have "... \<^sup>*\<sim>\<^sup>* t # T"
              proof -
                have 3: "Std (standardize T) \<and> standardize T \<^sup>*\<sim>\<^sup>* T"
                  using T 2 ind by blast
                have "stdz_insert t (standardize T) =
                       stdz_insert (hd (standardize T)) (tl (standardize T))"
                proof -
                  have "seq [t] (standardize T)"
                    using 0 2 tT ind
                    by (metis Arr.elims(2) Con_imp_eq_Srcs Con_implies_Arr(1) Ide.simps(1-2)
                        Ide_implies_Arr Trgs.simps(2) ide_char \<Lambda>.ide_char list.inject
                        seq_char seq_implies_Trgs_eq_Srcs t)
                  thus ?thesis
                    using t 3 stdz_insert_Ide_Std by blast
                qed
                also have "...  \<^sup>*\<sim>\<^sup>* hd (standardize T) # tl (standardize T)"
                proof -
                  have "\<not> Ide (standardize T)"
                    using 2 3 ide_backward_stable ide_char by blast
                  moreover have "tl (standardize T) \<noteq> [] \<Longrightarrow>
                                   seq [hd (standardize T)] (tl (standardize T)) \<and>
                                   Std (tl (standardize T))"
                    by (metis 3 Std_consE Std_imp_Arr append.left_neutral append_Cons
                        arr_append_imp_seq arr_char hd_Cons_tl list.discI tl_Nil)
                  ultimately show ?thesis
                    by (metis "2" Ide.simps(2) Resid.simps(1) Std_consE T cong_standard_development
                        ide_char ind \<Lambda>.ide_char list.exhaust_sel stdz_insert.simps(1)
                        stdz_insert_correctness)
                qed
                also have "hd (standardize T) # tl (standardize T) = standardize T"
                  by (metis 3 Arr.simps(1) Con_implies_Arr(2) Ide.simps(1) ide_char
                      list.exhaust_sel)
                also have "standardize T \<^sup>*\<sim>\<^sup>* T"
                  using 3 by simp
                also have "T \<^sup>*\<sim>\<^sup>* t # T"
                  using 0 t tT arr_append_imp_seq arr_char cong_cons_ideI(2) by simp
                finally show ?thesis by blast
              qed
              thus ?thesis by auto
              next
              assume t: "\<not> \<Lambda>.Ide t"
              show ?thesis
              proof (cases "Ide T")
                assume T: "Ide T"
                have "standardize (t # T) = standard_development t"
                  using t T Ide_implies_Arr ind by simp
                also have "... \<^sup>*\<sim>\<^sup>* [t]"
                  using t T tT cong_standard_development [of t] by blast
                also have "[t] \<^sup>*\<sim>\<^sup>* [t] @ T"
                  using t T tT cong_append_ideI(4) [of "[t]" T]
                  by (simp add: 0 arrI\<^sub>P arr_append_imp_seq ide_char)
                finally show ?thesis by auto
                next
                assume T: "\<not> Ide T"
                have 1: "Std (standardize T) \<and> standardize T \<^sup>*\<sim>\<^sup>* T"
                  using T \<open>Arr T\<close> ind by blast
                have 2: "seq [t] (standardize T)"
                  by (metis 0 Arr.simps(2) Arr.simps(3) Con_imp_eq_Srcs Con_implies_Arr(2)
                      Ide.elims(3) Ide.simps(1) T Trgs.simps(2) ide_char ind
                      seq_char seq_implies_Trgs_eq_Srcs tT)
                have "stdz_insert t (standardize T) \<^sup>*\<sim>\<^sup>* t # standardize T"
                  using t 1 2 stdz_insert_correctness [of t "standardize T"] by blast
                also have "t # standardize T \<^sup>*\<sim>\<^sup>* t # T"
                  using 1 2
                  by (meson Arr.simps(2) \<Lambda>.prfx_reflexive cong_cons seq_char)
                finally show ?thesis by auto
              qed
            qed
          qed
        qed
      qed
    qed

    subsubsection "The Leftmost Reduction Theorem"

    text \<open>
      In this section we prove the Leftmost Reduction Theorem, which states that
      leftmost reduction is a normalizing strategy.

      We first show that if a standard reduction path reaches a normal form,
      then the path must be the one produced by following the leftmost reduction strategy.
      This is because, in a standard reduction path, once a leftmost redex is skipped,
      all subsequent reductions occur ``to the right of it'', hence they are all non-leftmost
      reductions that do not contract the skipped redex, which remains in the leftmost position.

      The Leftmost Reduction Theorem then follows from the Standardization Theorem.
      If a term is normalizable, there is a reduction path from that term to a normal form.
      By the Standardization Theorem we may as well assume that path is standard.
      But a standard reduction path to a normal form is the path generated by following
      the leftmost reduction strategy, hence leftmost reduction reaches a normal form after
      a finite number of steps.
    \<close>

    lemma sseq_reflects_leftmost_reduction:
    assumes "\<Lambda>.sseq t u" and "\<Lambda>.is_leftmost_reduction u"
    shows "\<Lambda>.is_leftmost_reduction t"
    proof -
      have *: "\<And>u. u = \<Lambda>.leftmost_strategy (\<Lambda>.Src t) \\ t \<Longrightarrow> \<not> \<Lambda>.sseq t u" for t
      proof (induct t)
        show "\<And>u. \<not> \<Lambda>.sseq \<^bold>\<sharp> u"
          using \<Lambda>.sseq_imp_seq by blast
        show "\<And>x u. \<not> \<Lambda>.sseq \<^bold>\<guillemotleft>x\<^bold>\<guillemotright> u"
          using \<Lambda>.elementary_reduction.simps(2) \<Lambda>.sseq_imp_elementary_reduction1 by blast
        show "\<And>t u. \<lbrakk>\<And>u. u = \<Lambda>.leftmost_strategy (\<Lambda>.Src t) \\ t \<Longrightarrow> \<not> \<Lambda>.sseq t u;
                      u = \<Lambda>.leftmost_strategy (\<Lambda>.Src \<^bold>\<lambda>\<^bold>[t\<^bold>]) \\ \<^bold>\<lambda>\<^bold>[t\<^bold>]\<rbrakk>
                        \<Longrightarrow> \<not> \<Lambda>.sseq \<^bold>\<lambda>\<^bold>[t\<^bold>] u"
          by auto
        show "\<And>t1 t2 u. \<lbrakk>\<And>u. u = \<Lambda>.leftmost_strategy (\<Lambda>.Src t1) \\ t1 \<Longrightarrow> \<not> \<Lambda>.sseq t1 u;
                         \<And>u. u = \<Lambda>.leftmost_strategy (\<Lambda>.Src t2) \\ t2 \<Longrightarrow> \<not> \<Lambda>.sseq t2 u;
                         u = \<Lambda>.leftmost_strategy (\<Lambda>.Src (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) \\ (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)\<rbrakk>
                           \<Longrightarrow> \<not> \<Lambda>.sseq (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2) u"
          apply simp
          by (metis \<Lambda>.sseq_imp_elementary_reduction2 \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide_Src
              \<Lambda>.Ide_Subst \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char \<Lambda>.resid_Ide_Arr)
        show "\<And>t1 t2. \<lbrakk>\<And>u. u = \<Lambda>.leftmost_strategy (\<Lambda>.Src t1) \\ t1 \<Longrightarrow> \<not> \<Lambda>.sseq t1 u;
                       \<And>u. u = \<Lambda>.leftmost_strategy (\<Lambda>.Src t2) \\ t2 \<Longrightarrow> \<not> \<Lambda>.sseq t2 u;
                       u = \<Lambda>.leftmost_strategy (\<Lambda>.Src (\<Lambda>.App t1 t2)) \\ \<Lambda>.App t1 t2\<rbrakk>
                         \<Longrightarrow> \<not> \<Lambda>.sseq (\<Lambda>.App t1 t2) u" for u
          apply (cases u)
              apply simp_all
             apply (metis \<Lambda>.elementary_reduction.simps(2) \<Lambda>.sseq_imp_elementary_reduction2)
            apply (metis \<Lambda>.Src.simps(3) \<Lambda>.Src_resid \<Lambda>.Trg.simps(3) \<Lambda>.lambda.distinct(15)
                         \<Lambda>.lambda.distinct(3))
        proof -
          show "\<And>t1 t2 u1 u2.
                  \<lbrakk>\<not> \<Lambda>.sseq t1 (\<Lambda>.leftmost_strategy (\<Lambda>.Src t1) \\ t1);
                   \<not> \<Lambda>.sseq t2 (\<Lambda>.leftmost_strategy (\<Lambda>.Src t2) \\ t2);
                   \<^bold>\<lambda>\<^bold>[u1\<^bold>] \<^bold>\<Zspot> u2 = \<Lambda>.leftmost_strategy (\<Lambda>.App (\<Lambda>.Src t1) (\<Lambda>.Src t2)) \\ \<Lambda>.App t1 t2;
                   u = \<Lambda>.leftmost_strategy (\<Lambda>.App (\<Lambda>.Src t1) (\<Lambda>.Src t2)) \\ \<Lambda>.App t1 t2\<rbrakk>
                     \<Longrightarrow> \<not> \<Lambda>.sseq (\<Lambda>.App t1 t2)
                                  (\<Lambda>.leftmost_strategy (\<Lambda>.App (\<Lambda>.Src t1) (\<Lambda>.Src t2)) \\ \<Lambda>.App t1 t2)"
            by (metis \<Lambda>.sseq_imp_elementary_reduction1 \<Lambda>.Arr.simps(5) \<Lambda>.Arr_resid
                      \<Lambda>.Coinitial_iff_Con \<Lambda>.Ide.simps(5) \<Lambda>.Ide_iff_Src_self \<Lambda>.Src.simps(4)
                      \<Lambda>.Src_resid \<Lambda>.contains_head_reduction.simps(8) \<Lambda>.is_head_reduction_if
                      \<Lambda>.lambda.discI(3) \<Lambda>.lambda.distinct(7)
                      \<Lambda>.leftmost_strategy_selects_head_reduction \<Lambda>.resid_Arr_self
                      \<Lambda>.sseq_preserves_App_and_no_head_reduction)
          show "\<And>u1 u2.
                  \<lbrakk>\<not> \<Lambda>.sseq t1 (\<Lambda>.leftmost_strategy (\<Lambda>.Src t1) \\ t1);
                   \<not> \<Lambda>.sseq t2 (\<Lambda>.leftmost_strategy (\<Lambda>.Src t2) \\ t2);
                   \<Lambda>.App u1 u2 = \<Lambda>.leftmost_strategy (\<Lambda>.App (\<Lambda>.Src t1) (\<Lambda>.Src t2)) \\ \<Lambda>.App t1 t2;
                   u = \<Lambda>.leftmost_strategy (\<Lambda>.App (\<Lambda>.Src t1) (\<Lambda>.Src t2)) \\ \<Lambda>.App t1 t2\<rbrakk>
                     \<Longrightarrow> \<not> \<Lambda>.sseq (\<Lambda>.App t1 t2)
                                  (\<Lambda>.leftmost_strategy (\<Lambda>.App (\<Lambda>.Src t1) (\<Lambda>.Src t2)) \\ \<Lambda>.App t1 t2)"
           for t1 t2
            apply (cases "\<not> \<Lambda>.Arr t1")
             apply simp_all
             apply (meson \<Lambda>.Arr.simps(4) \<Lambda>.seq_char \<Lambda>.sseq_imp_seq)
            apply (cases "\<not> \<Lambda>.Arr t2")
             apply simp_all
             apply (meson \<Lambda>.Arr.simps(4) \<Lambda>.seq_char \<Lambda>.sseq_imp_seq)
            using \<Lambda>.Arr_not_Nil
            apply (cases t1)
                apply simp_all
            using \<Lambda>.NF_iff_has_no_redex \<Lambda>.has_redex_iff_not_Ide_leftmost_strategy
                  \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self
                  \<Lambda>.NF_def \<Lambda>.elementary_reduction_not_ide \<Lambda>.eq_Ide_are_cong
                  \<Lambda>.leftmost_strategy_is_reduction_strategy \<Lambda>.reduction_strategy_def
                  \<Lambda>.resid_Arr_Src
             apply simp
             apply (metis \<Lambda>.Arr.simps(4) \<Lambda>.Ide.simps(4) \<Lambda>.Ide_Trg \<Lambda>.Src.simps(4)
                          \<Lambda>.sseq_imp_elementary_reduction2)
            by (metis \<Lambda>.Ide_Trg \<Lambda>.elementary_reduction_not_ide \<Lambda>.ide_char)
        qed
      qed
      have "t \<noteq> \<Lambda>.leftmost_strategy (\<Lambda>.Src t) \<Longrightarrow> False"
      proof -
        assume 1: "t \<noteq> \<Lambda>.leftmost_strategy (\<Lambda>.Src t)"
        have 2: "\<not> \<Lambda>.Ide (\<Lambda>.leftmost_strategy (\<Lambda>.Src t))"
          by (meson assms(1) \<Lambda>.NF_def \<Lambda>.NF_iff_has_no_redex \<Lambda>.arr_char
              \<Lambda>.elementary_reduction_is_arr \<Lambda>.elementary_reduction_not_ide
              \<Lambda>.has_redex_iff_not_Ide_leftmost_strategy \<Lambda>.ide_char
              \<Lambda>.sseq_imp_elementary_reduction1)
        have "\<Lambda>.is_leftmost_reduction (\<Lambda>.leftmost_strategy (\<Lambda>.Src t) \\ t)"
        proof -
          have "\<Lambda>.is_leftmost_reduction (\<Lambda>.leftmost_strategy (\<Lambda>.Src t))"
            by (metis assms(1) 2 \<Lambda>.Ide_Src \<Lambda>.Ide_iff_Src_self \<Lambda>.arr_char
                \<Lambda>.elementary_reduction_is_arr \<Lambda>.elementary_reduction_leftmost_strategy
                \<Lambda>.is_leftmost_reduction_def \<Lambda>.leftmost_strategy_is_reduction_strategy
                \<Lambda>.reduction_strategy_def \<Lambda>.sseq_imp_elementary_reduction1)
          moreover have 3: "\<Lambda>.elementary_reduction t"
            using assms \<Lambda>.sseq_imp_elementary_reduction1 by simp
          moreover have "\<not> \<Lambda>.is_leftmost_reduction t"
            using 1 \<Lambda>.is_leftmost_reduction_def by auto
          moreover have "\<Lambda>.coinitial (\<Lambda>.leftmost_strategy (\<Lambda>.Src t)) t"
            using 3 \<Lambda>.leftmost_strategy_is_reduction_strategy \<Lambda>.reduction_strategy_def
                  \<Lambda>.Ide_Src \<Lambda>.elementary_reduction_is_arr
            by force
          ultimately show ?thesis
            using 1 \<Lambda>.leftmost_reduction_preservation by blast
        qed
        moreover have "\<Lambda>.coinitial (\<Lambda>.leftmost_strategy (\<Lambda>.Src t) \\ t) u"
          using assms(1) calculation \<Lambda>.Arr_not_Nil \<Lambda>.Src_resid \<Lambda>.elementary_reduction_is_arr
                \<Lambda>.is_leftmost_reduction_def \<Lambda>.seq_char \<Lambda>.sseq_imp_seq
          by force
        moreover have "\<And>v. \<lbrakk>\<Lambda>.is_leftmost_reduction v; \<Lambda>.coinitial v u\<rbrakk> \<Longrightarrow> v = u"
          by (metis \<Lambda>.arr_iff_has_source \<Lambda>.arr_resid_iff_con \<Lambda>.confluence assms(2)
              \<Lambda>.Arr_not_Nil \<Lambda>.Coinitial_iff_Con \<Lambda>.is_leftmost_reduction_def \<Lambda>.sources_char\<^sub>\<Lambda>)
        ultimately have "\<Lambda>.leftmost_strategy (\<Lambda>.Src t) \\ t = u"
          by blast
        thus ?thesis
          using assms(1) * by blast
      qed
      thus ?thesis
        using assms(1) \<Lambda>.is_leftmost_reduction_def \<Lambda>.sseq_imp_elementary_reduction1 by force
    qed

    lemma elementary_reduction_to_NF_is_leftmost:
    shows "\<lbrakk>\<Lambda>.elementary_reduction t; \<Lambda>.NF (Trg [t])\<rbrakk> \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src t) = t"
    proof (induct t)
      show "\<Lambda>.leftmost_strategy (\<Lambda>.Src \<^bold>\<sharp>) = \<^bold>\<sharp>"
        by simp
      show "\<And>x. \<lbrakk>\<Lambda>.elementary_reduction \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>; \<Lambda>.NF (Trg [\<^bold>\<guillemotleft>x\<^bold>\<guillemotright>])\<rbrakk>
                   \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>) = \<^bold>\<guillemotleft>x\<^bold>\<guillemotright>"
        by auto
      show "\<And>t. \<lbrakk>\<lbrakk>\<Lambda>.elementary_reduction t; \<Lambda>.NF (Trg [t])\<rbrakk>
                    \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src t) = t;
                  \<Lambda>.elementary_reduction \<^bold>\<lambda>\<^bold>[t\<^bold>]; \<Lambda>.NF (Trg [\<^bold>\<lambda>\<^bold>[t\<^bold>]])\<rbrakk>
                   \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src \<^bold>\<lambda>\<^bold>[t\<^bold>]) = \<^bold>\<lambda>\<^bold>[t\<^bold>]"
        using lambda_calculus.NF_Lam_iff lambda_calculus.elementary_reduction_is_arr by force
      show "\<And>t1 t2. \<lbrakk>\<lbrakk>\<Lambda>.elementary_reduction t1; \<Lambda>.NF (Trg [t1])\<rbrakk>
                        \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src t1) = t1;
                     \<lbrakk>\<Lambda>.elementary_reduction t2; \<Lambda>.NF (Trg [t2])\<rbrakk>
                        \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src t2) = t2;
                      \<Lambda>.elementary_reduction (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2); \<Lambda>.NF (Trg [\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2])\<rbrakk>
                        \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src (\<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2)) = \<^bold>\<lambda>\<^bold>[t1\<^bold>] \<^bold>\<Zspot> t2"
        apply simp
        by (metis \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_implies_Arr)
      fix t1 t2
      assume ind1: "\<lbrakk>\<Lambda>.elementary_reduction t1; \<Lambda>.NF (Trg [t1])\<rbrakk>
                        \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src t1) = t1"
      assume ind2: "\<lbrakk>\<Lambda>.elementary_reduction t2; \<Lambda>.NF (Trg [t2])\<rbrakk>
                        \<Longrightarrow> \<Lambda>.leftmost_strategy (\<Lambda>.Src t2) = t2"
      assume t: "\<Lambda>.elementary_reduction (\<Lambda>.App t1 t2)"
      have t1: "\<Lambda>.Arr t1"
        using t \<Lambda>.Arr.simps(4) \<Lambda>.elementary_reduction_is_arr by blast
      have t2: "\<Lambda>.Arr t2"
        using t \<Lambda>.Arr.simps(4) \<Lambda>.elementary_reduction_is_arr by blast
      assume NF: "\<Lambda>.NF (Trg [\<Lambda>.App t1 t2])"
      have 1: "\<not> \<Lambda>.is_Lam t1"
        using NF \<Lambda>.NF_def
        apply (cases t1)
            apply simp_all
        by (metis (mono_tags) \<Lambda>.Ide.simps(1) \<Lambda>.NF_App_iff \<Lambda>.Trg.simps(2-3) \<Lambda>.lambda.discI(2))
      have 2: "\<Lambda>.NF (\<Lambda>.Trg t1) \<and> \<Lambda>.NF (\<Lambda>.Trg t2)"
        using NF t1 t2 1 \<Lambda>.NF_App_iff by simp
      show "\<Lambda>.leftmost_strategy (\<Lambda>.Src (\<Lambda>.App t1 t2)) = \<Lambda>.App t1 t2"
        using t t1 t2 1 2 ind1 ind2
        apply (cases t1)
            apply simp_all
         apply (metis \<Lambda>.Ide.simps(4) \<Lambda>.Ide_iff_Src_self \<Lambda>.Ide_iff_Trg_self
            \<Lambda>.NF_iff_has_no_redex \<Lambda>.elementary_reduction_not_ide \<Lambda>.eq_Ide_are_cong
            \<Lambda>.has_redex_iff_not_Ide_leftmost_strategy \<Lambda>.resid_Arr_Src t1)
        using \<Lambda>.Ide_iff_Src_self by blast
    qed

    lemma Std_path_to_NF_is_leftmost:
    shows "\<lbrakk>Std T; \<Lambda>.NF (Trg T)\<rbrakk> \<Longrightarrow> set T \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
    proof -
      have 1: "\<And>t. \<lbrakk>Std (t # T); \<Lambda>.NF (Trg (t # T))\<rbrakk> \<Longrightarrow> \<Lambda>.is_leftmost_reduction t" for T
      proof (induct T)
        show "\<And>t. \<lbrakk>Std [t]; \<Lambda>.NF (Trg [t])\<rbrakk> \<Longrightarrow> \<Lambda>.is_leftmost_reduction t"
          using elementary_reduction_to_NF_is_leftmost \<Lambda>.is_leftmost_reduction_def by simp
        fix t u T
        assume ind: "\<And>t. \<lbrakk>Std (t # T); \<Lambda>.NF (Trg (t # T))\<rbrakk> \<Longrightarrow> \<Lambda>.is_leftmost_reduction t"
        assume Std: "Std (t # u # T)"
        assume "\<Lambda>.NF (Trg (t # u # T))"
        show "\<Lambda>.is_leftmost_reduction t"
          using Std \<open>\<Lambda>.NF (Trg (t # u # T))\<close> ind sseq_reflects_leftmost_reduction by auto
      qed
      show "\<lbrakk>Std T; \<Lambda>.NF (Trg T)\<rbrakk> \<Longrightarrow> set T \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
      proof (induct T)
        show 2: "set [] \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
          by simp
        fix t T
        assume ind: "\<lbrakk>Std T; \<Lambda>.NF (Trg T)\<rbrakk> \<Longrightarrow> set T \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
        assume Std: "Std (t # T)" and NF: "\<Lambda>.NF (Trg (t # T))"
        show "set (t # T) \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
          by (metis 1 2 NF Std Std_consE Trg.elims ind insert_subset list.inject list.simps(15)
                    mem_Collect_eq)
      qed
    qed

    theorem leftmost_reduction_theorem:
    shows "\<Lambda>.normalizing_strategy \<Lambda>.leftmost_strategy"
    proof (unfold \<Lambda>.normalizing_strategy_def, intro allI impI)
      fix a
      assume a: "\<Lambda>.normalizable a"
      show "\<exists>n. \<Lambda>.NF (\<Lambda>.reduce \<Lambda>.leftmost_strategy a n)"
      proof (cases "\<Lambda>.NF a")
        show "\<Lambda>.NF a \<Longrightarrow> ?thesis"
          by (metis lambda_calculus.reduce.simps(1))
        assume 1: "\<not> \<Lambda>.NF a"
        obtain T where T: "Arr T \<and> Src T = a \<and> \<Lambda>.NF (Trg T)"
          using a \<Lambda>.normalizable_def red_iff by auto
        have 2: "\<not> Ide T"
          using T 1 Ide_imp_Src_eq_Trg by fastforce
        obtain U where U: "Std U \<and> cong T U"
          using T 2 standardization_theorem by blast
        have 3: "set U \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
          using 1 U Std_path_to_NF_is_leftmost
          by (metis Con_Arr_self Resid_parallel Src_resid T cong_implies_coinitial)
        have "\<And>U. \<lbrakk>Arr U; length U = n; set U \<subseteq> Collect \<Lambda>.is_leftmost_reduction\<rbrakk> \<Longrightarrow>
                   U = apply_strategy \<Lambda>.leftmost_strategy (Src U) (length U)" for n
        proof (induct n)
          show "\<And>U. \<lbrakk>Arr U; length U = 0; set U \<subseteq> Collect \<Lambda>.is_leftmost_reduction\<rbrakk>
                       \<Longrightarrow> U = apply_strategy \<Lambda>.leftmost_strategy (Src U) (length U)"
            by simp
          fix n U
          assume ind: "\<And>U. \<lbrakk>Arr U; length U = n; set U \<subseteq> Collect \<Lambda>.is_leftmost_reduction\<rbrakk>
                              \<Longrightarrow> U = apply_strategy \<Lambda>.leftmost_strategy (Src U) (length U)"
          assume U: "Arr U"
          assume n: "length U = Suc n"
          assume set: "set U \<subseteq> Collect \<Lambda>.is_leftmost_reduction"
          show "U = apply_strategy \<Lambda>.leftmost_strategy (Src U) (length U)"
          proof (cases "n = 0")
            show "n = 0 \<Longrightarrow> ?thesis"
              using U n 1 set \<Lambda>.is_leftmost_reduction_def
              by (cases U) auto
            assume 5: "n \<noteq> 0"
            have 4: "hd U = \<Lambda>.leftmost_strategy (Src U)"
              using n U set \<Lambda>.is_leftmost_reduction_def
              by (cases U) auto
            have 6: "tl U \<noteq> []"
              using 4 5 n U
              by (metis Suc_length_conv list.sel(3) list.size(3))
            show ?thesis
              using 4 5 6 n U set ind [of "tl U"]
              apply (cases n)
               apply simp_all
              by (metis (no_types, lifting) Arr_consE Nil_tl Nitpick.size_list_simp(2)
                  ind [of "tl U"] \<Lambda>.arr_char \<Lambda>.trg_char list.collapse list.set_sel(2)
                  old.nat.inject reduction_paths.apply_strategy.simps(2) subset_code(1))
          qed
        qed
        hence "U = apply_strategy \<Lambda>.leftmost_strategy (Src U) (length U)"
          by (metis 3 Con_implies_Arr(1) Ide.simps(1) U ide_char)
        moreover have "Src U = a"
          using T U cong_implies_coinitial
          by (metis Con_imp_eq_Srcs Con_implies_Arr(2) Ide.simps(1) Srcs_simp\<^sub>P\<^sub>W\<^sub>E empty_set
              ex_un_Src ide_char list.set_intros(1) list.simps(15))
        ultimately have "Trg U = \<Lambda>.reduce \<Lambda>.leftmost_strategy a (length U)"
          using reduce_eq_Trg_apply_strategy
          by (metis Arr.simps(1) Con_implies_Arr(1) Ide.simps(1) U a ide_char
              \<Lambda>.leftmost_strategy_is_reduction_strategy \<Lambda>.normalizable_def length_greater_0_conv)
        thus ?thesis
          by (metis Ide.simps(1) Ide_imp_Src_eq_Trg Src_resid T Trg_resid_sym U ide_char)
      qed
    qed

  end

end


