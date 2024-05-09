(*<*)
theory Substitutions_Lambda_Free
  imports "Lambda_Free_RPOs.Lambda_Free_RPOs" "HOL-Library.LaTeXsugar" "Well_Quasi_Orders.Minimal_Elements"
begin

no_notation (latex)
  Cons  ("_ \<cdot>/ _" [66,65] 65)

declare [[syntax_ambiguity_warning = false, names_short = true]]
(*>*)

section \<open>Introduction\<close>

text \<open>
This theory is based on J. Blanchette's Formalization of Recursive Path Orders
for Lambda-Free Higher-Order Terms \cite{Lambda_Free_RPOs} which defines $\lambda$-free
higher-order terms.
\<close>

subsection \<open>Preliminary lemmas\<close>
text\<open>
The following lemma and definitions would be worth adding in the theory
@{theory Lambda_Free_RPOs.Lambda_Free_Term}.
\<close>

lemma sub_trans: \<open>sub x y \<Longrightarrow> sub y z \<Longrightarrow> sub x z\<close>
  by (induction z arbitrary: x y, blast, elim sub_AppE; simp add: sub_arg sub_fun)

definition subterms :: \<open>('s, 'v) tm \<Rightarrow> ('s, 'v) tm set\<close> where
  \<open>subterms t \<equiv> {u. sub u t}\<close>

definition proper_subterms :: \<open>('s, 'v) tm \<Rightarrow> ('s, 'v) tm set\<close> where
  \<open>proper_subterms t \<equiv> {u. proper_sub u t}\<close>

text\<open>
The following lemmas are also helpful in the following and could be easily lifted
higher in the hierarchy of theories.
\<close>

lemmas mult_Suc_left =
  mult_Suc_right[unfolded add.commute[of m \<open>m*n\<close> for m n]]
\<comment>\<open>Although this result is immediate, it might be worth adding it to Nat symmetrically.\<close>

lemma inject_nat_in_fset_ninj:
  \<open>finite S \<Longrightarrow> (range (f::nat\<Rightarrow>_) \<subseteq> S) \<Longrightarrow> (\<exists> x y. x \<noteq> y \<and> f x = f y)\<close>
  apply (induction S rule: finite_induct, fast)
  subgoal for x FS
    using
      finite_insert[of x FS]
      infinite_UNIV_char_0 inj_on_finite[of f UNIV \<open>{x} \<union> FS\<close>]
    unfolding inj_def by blast.

lemma wfPD: \<open>wfP P \<Longrightarrow> wfp_on P A\<close>
\<comment>\<open>This destruction rule for @{term \<open>wfP\<close>} could be added to the theory
@{theory Open_Induction.Restricted_Predicates}\<close>
  by (simp add: wfP_eq_minimal wfp_on_iff_minimal)

lemma set_decr_chain_empty:
  fixes u :: \<open>nat \<Rightarrow> 'a set\<close>
  assumes pord: \<open>\<And>n. u n \<noteq> \<emptyset> \<Longrightarrow> u (n+1) \<subset> u n\<close>
    and fin: \<open>\<And>n. finite (u n)\<close>
  shows \<open>\<exists> k. u k = \<emptyset>\<close>
\<comment>
\<open>
  This lemma could easily be generalized to any partial order and any minimal
  element and integrated to the theory @{theory Well_Quasi_Orders.Minimal_Elements}.
\<close>
proof-
  have \<open>wfp_on (in_rel finite_psubset) (range u)\<close>
    using wf_finite_psubset wfPD wf_in_rel
    by blast
  with fin have wfpon: \<open>wfp_on (\<subset>) (range u)\<close>
    unfolding finite_psubset_def in_rel_def wfp_on_def
    by (auto iff: image_iff, metis)
  then interpret minimal_element \<open>(\<subset>)\<close> \<open>range u\<close>
    by (unfold_locales; simp add: po_on_def)

  show ?thesis
    using pord wf
    unfolding wfp_on_def[simplified, unfolded Suc_eq_plus1]
    using rangeI[of u]
    by meson
qed

lemma distinct_in_fset:
  \<open>finite E \<Longrightarrow> card E = n \<Longrightarrow> distinct xs \<Longrightarrow> set xs \<subseteq> E \<Longrightarrow> length xs \<le> n\<close>
  by (induction n, simp, metis card_mono distinct_card)

section \<open>Substitutions\<close>

text \<open>
This section embeds substitutions in a proper type, lifting basic operations like
substitution application (i.e. \emph{substitution} as an operation on terms) and
composition.
\<close>

subsection \<open>Substitutions for terms\<close>

text \<open>
Substitutions in @{theory \<open>Lambda_Free_RPOs.Lambda_Free_RPOs\<close>}
\cite{Lambda_Free_RPOs} are not defined as a type, they are implicitly used
as functions from variables to terms.
However, not all functions from variables to terms are substitutions, which
motivates the introduction of a proper type \emph{subst} fitting the
specification of a substitution, namely that only finitely many variables are
not mapped to themselves.
\<close>

abbreviation \<V> where \<open>\<V> \<equiv> Hd \<circ> Var\<close>

lemma inj_\<V>: \<open>inj \<V>\<close>
  by (intro injI, simp)

lemma fin_var_restr:\<open>finite (\<V> ` E) \<Longrightarrow> finite E\<close>
  using inj_\<V> finite_imageI image_inv_f_f
  by metis

definition is_subst :: \<open>('v \<Rightarrow> ('s, 'v) tm) \<Rightarrow> bool\<close> where
  \<open>is_subst \<sigma> \<equiv> finite {t. is_Hd t \<and> is_Var (head t) \<and> subst \<sigma> t \<noteq> t}\<close>

text\<open>
If type-checking on terms was enforced in @{term is_subst}, the above
definition could be expressed as follows in a more concise way:

@{term \<open>is_subst \<sigma> \<equiv> finite {subst \<sigma> t \<noteq> t}\<close>}

Without type-checking, the definition must range over variables and not over
terms since @{term \<open>App x x\<close>} is a valid term, even though it does not type check.
If $x\sigma = x$, then $(x(x))\sigma = x(x)$. This inductively allows infinitely many
fixpoints of the substitution @{term \<sigma>}.

With type-checking, the second definition would only add finitely many terms,
namely type-correct applied terms of the form @{term \<open>(App y x)\<close>} where @{term x}
and @{term y} are substitutable variables.
\<close>

lemma subst_\<V>: \<open>is_subst \<V>\<close>
unfolding is_subst_def
proof -
  {
    fix t::\<open>('s, 'v) tm\<close>
    assume asm: \<open>is_Hd t\<close> \<open>is_Var (head t)\<close>
    define v where \<open>v = var (head t)\<close>
    hence t_eq:\<open>t = Hd (Var v)\<close>
      by (simp add: asm(1) asm(2))
      
    hence \<open>subst \<V> t = t\<close>
      by simp
  }
  thus \<open>finite {t. (is_Hd t \<and> is_Var (head t) \<and> subst (Hd \<circ> Var) t \<noteq> t)}\<close>
    using not_finite_existsD by blast
qed

typedef ('s, 'v) subst = \<open>{\<sigma>::('v \<Rightarrow> ('s, 'v) tm). is_subst \<sigma>}\<close>
  using subst_\<V> by blast

setup_lifting type_definition_subst

lift_definition \<V>' :: \<open>('s, 'v) subst\<close> is \<open>\<V>\<close>
  using subst_\<V> by blast

text \<open>
Informally, @{term \<V>} is almost the identity function since it casts variables
to themselves (as terms), but it has the type \<open>'v \<Rightarrow> ('s, 'v) tm\<close>. @{term \<V>}
is thus lifted to @{term \<V>'} that applies on substitutions. The fact that
@{term \<V>'} leaves ground terms unchanged follows from the definition of @{term subst}
and is obtained by lifting. @{term \<V>'} \emph{is} the identity substitution.
\<close>

lift_definition
  subst_app :: \<open>('s, 'v) tm \<Rightarrow> ('s, 'v) subst \<Rightarrow> ('s, 'v) tm\<close> (\<open>_\<cdot>_\<close> [56,55] 55) is (* previsouly infixl, but this prevents linebreaks *)
  \<open>\<lambda> x \<sigma>. subst \<sigma> x\<close>.

lemma sub_subst': \<open>sub x t \<Longrightarrow> sub (x\<cdot>\<sigma>) (t\<cdot>\<sigma>)\<close>
\<comment>\<open>This lemma is a lifted version of @{thm sub_subst}.\<close>
  by (simp add: subst_app.rep_eq sub_subst)

text \<open>
Application for substitutions (i.e.\ \emph{substitution}) is lifted from the
function @{term subst} and denoted as usual in the literature with a post-fix
notation: @{term \<open>subst \<sigma> x\<close>} is denoted by @{term \<open>x\<cdot>\<sigma>\<close>}.
\<close>

lemma subst_alt_def:\<open>finite {t. (\<V> t)\<cdot>\<sigma> \<noteq> \<V> t}\<close>
proof (transfer)
  fix \<sigma> :: \<open>'v \<Rightarrow> ('s, 'v) tm\<close>
  assume asm: \<open>is_subst \<sigma>\<close>
  have
  \<open>{t. is_Hd t \<and> is_Var (head t) \<and> subst \<sigma> t \<noteq> t} = \<V> ` {t. subst \<sigma> (\<V> t) \<noteq> \<V> t}\<close>
    apply (standard; clarsimp)
    subgoal for x
      apply (cases x)
      subgoal for hd by (cases hd; simp)
      subgoal by simp
    done.
  then show \<open>finite {t. subst \<sigma> (\<V> t) \<noteq> \<V> t}\<close>
    using fin_var_restr asm unfolding is_subst_def
    by simp
qed

text \<open>
The lemma above provides an alternative definition for substitution. Yet, there is
a subtlety since Isabelle does not provide support for dependent types:
one shall understand this lemma as the meta-implication "if
@{term \<open>\<sigma>::(_,_) subst\<close>} is of type @{term subst} then the aforementioned set is
finite".
A true alternative definition should state an equivalence, however the converse
implication makes no sense in Isabelle.
\<close>

lemma subst_eq_sub:\<open>sub s t \<Longrightarrow> t\<cdot>\<sigma> = t\<cdot>\<theta> \<Longrightarrow> s\<cdot>\<sigma> = s\<cdot>\<theta>\<close>
  by (transfer fixing: s t, induction t arbitrary: s; fastforce)

text \<open>
Composition for substitutions is also lifted as follows.
\<close>

lift_definition
  rcomp :: \<open>('s, 'v) subst \<Rightarrow> ('s, 'v) subst \<Rightarrow> ('s, 'v) subst\<close>
  (infixl \<open>\<circ>\<close> 55) is \<open>\<lambda> \<sigma> \<theta>. subst \<theta> \<circ> (subst \<sigma> \<circ> \<V>)\<close>
proof (transfer)
  fix \<sigma>::\<open>'v \<Rightarrow> ('s, 'v) tm\<close> and \<theta>::\<open>'v \<Rightarrow> ('s, 'v) tm\<close>

  assume asm: \<open>is_subst \<sigma>\<close> \<open>is_subst \<theta>\<close>

  define S where \<open>S \<equiv> {t. is_Hd t \<and> is_Var (head t) \<and> subst \<sigma> t \<noteq> t}\<close>
  define T where \<open>T \<equiv> {t. is_Hd t \<and> is_Var (head t) \<and> subst \<theta> t \<noteq> t}\<close>
  define TS where \<open>TS \<equiv>
    {t. is_Hd t \<and> is_Var (head t) \<and> subst (\<lambda>x. subst \<theta> (subst \<sigma> (\<V> x))) t \<noteq> t}\<close>

  note fin =
    asm(1)[unfolded is_subst_def, folded S_def]
    asm(2)[unfolded is_subst_def, folded T_def]

  have TS_simp:
  \<open>TS = {t. is_Hd t \<and> is_Var (head t) \<and> subst (subst \<theta> \<circ> (subst \<sigma> \<circ> \<V>)) t \<noteq> t}\<close> 
  proof -
    have eq:\<open>(\<lambda>x. subst \<theta> (subst \<sigma> (Hd (Var x)))) = subst \<theta> \<circ> (subst \<sigma> \<circ> \<V>)\<close>
      by (standard, simp)
    then show ?thesis
      by (simp add: TS_def[simplified eq])
  qed

  have \<open>TS \<subseteq> S \<union> T\<close>
    unfolding S_def T_def TS_def
    apply (intro subsetI, simp)
    subgoal for t
      apply (cases t; simp)
      subgoal for x by (cases x; auto)
    done
  done

  from finite_subset[OF this finite_UnI[OF fin], simplified TS_simp]
  show \<open>is_subst (subst \<theta> \<circ> (subst \<sigma> \<circ> \<V>))\<close>
  unfolding is_subst_def .
qed

lemma rcomp_subst_simp:
  \<open>(x::('s, 'v) tm)\<cdot>(\<sigma> \<circ> \<theta>) = (x\<cdot>\<sigma>)\<cdot>\<theta>\<close>
  by (transfer fixing: x, induction x; simp add: hd.case_eq_if)

lift_definition
  set_image_subst :: \<open>('s, 'v) tm set \<Rightarrow> ('s, 'v) subst \<Rightarrow> ('s, 'v) tm set\<close>
  (infixl \<open>\<cdot>\<close> 90) is \<open>\<lambda> S \<sigma>. subst \<sigma> ` S\<close> .

lemma set_image_subst_collect:
  \<open>S\<cdot>\<sigma> = {x\<cdot>\<sigma> | x. x \<in> S}\<close>
  by (transfer, blast)

subsection \<open>Substitutions as a monoid\<close>

text \<open>
First, we state two introduction lemmas for allowing extensional reasoning on
substitutions. The first one is on terms and the second one is for terms that are
variables.
\<close>

lemma subst_ext_tmI:
  fixes \<sigma>::\<open>('s, 'v) subst\<close> and \<theta>::\<open>('s, 'v) subst\<close>
  shows \<open>\<forall> (x::('s, 'v) tm). (x\<cdot>\<sigma>) = (x\<cdot>\<theta>) \<Longrightarrow> \<sigma> = \<theta>\<close>
proof (transfer, rule ccontr)
  fix \<sigma>::\<open>'v \<Rightarrow> ('s, 'v) tm\<close> and \<theta>::\<open>'v \<Rightarrow> ('s, 'v) tm\<close>
  assume asm:\<open>is_subst \<sigma>\<close> \<open>is_subst \<theta>\<close> \<open>\<forall>x. subst \<sigma> x = subst \<theta> x\<close> \<open>\<sigma> \<noteq> \<theta>\<close>
  
  from asm(4) obtain v where v_def:\<open>\<sigma> v \<noteq> \<theta> v\<close>
    by fast
  hence \<open>subst \<sigma> (Hd (Var v)) \<noteq> subst \<theta> (Hd (Var v))\<close>
    by simp

  with asm(3) show False
    by blast
qed

lemma subst_ext_tmI':
  fixes \<sigma>::\<open>('s, 'v) subst\<close> and \<theta>::\<open>('s, 'v) subst\<close>
  shows \<open>\<forall> x. (\<V> x)\<cdot>\<sigma> = (\<V> x)\<cdot>\<theta> \<Longrightarrow> \<sigma> = \<theta>\<close>
  by (transfer, simp, blast)

lemmas subst_extI = subst_ext_tmI subst_ext_tmI'

text \<open>
The three following lemmas state that @{term \<V>'} is the neutral element for composition.
Although uniqueness follows from the definition of a neutral element, the proof
of this claim is given below.
\<close>

lemma \<V>'_id_tm [simp]:
  fixes x::\<open>(_,_) tm\<close>
  shows \<open>(x\<cdot>\<V>') = x\<close>
  by (transfer fixing: x, induction x; simp add: hd.case_eq_if)

lemma \<V>'_neutral_rcomp[simp]:
  \<open>\<sigma> \<circ> \<V>' = \<sigma>\<close>
  \<open>\<V>' \<circ> \<sigma> = \<sigma>\<close>
  by (intro subst_ext_tmI allI, simp add: rcomp_subst_simp)+

lemma unique_\<V>':
  \<open>(\<And>\<sigma>. \<sigma> \<circ> \<eta> = \<sigma>) \<Longrightarrow> \<eta> = \<V>'\<close>
  \<open>(\<And>\<sigma>. \<eta> \<circ> \<sigma> = \<sigma>) \<Longrightarrow> \<eta> = \<V>'\<close>
proof -
  assume \<open>\<sigma> \<circ> \<eta> = \<sigma>\<close> for \<sigma>
  from \<V>'_neutral_rcomp(2)[of \<eta>, symmetric, simplified this]
  show \<open>\<eta> = \<V>'\<close>.
next
  assume \<open>\<eta> \<circ> \<sigma> = \<sigma>\<close> for \<sigma>
  from \<V>'_neutral_rcomp(1)[of \<eta>, symmetric, simplified this]
  show \<open>\<eta> = \<V>'\<close>.
qed

lemma \<V>'_iff:\<open>\<sigma> = \<V>' \<longleftrightarrow> (\<forall> x. (\<V> x)\<cdot>\<sigma> = (\<V> x))\<close>
  by (intro iffI; simp add: \<V>'.rep_eq subst_app.rep_eq subst_ext_tmI') 

lemma rcomp_assoc[simp]:
  fixes \<sigma>::\<open>('s, 'v) subst\<close>
    and \<theta>::\<open>('s, 'v) subst\<close>
    and \<gamma>::\<open>('s, 'v) subst\<close>
  shows \<open>(\<sigma> \<circ> \<theta>) \<circ> \<gamma> = \<sigma> \<circ> (\<theta> \<circ> \<gamma>)\<close>
  by (intro subst_extI, simp add: rcomp_subst_simp)

text \<open>
Knowing that the composition of substitutions @{term \<open>(\<circ>) :: (_,_) subst \<Rightarrow> _\<close>}
is associative and has a neutral element @{term \<V>'}, we may embed substitutions
in an algebraic structure with a monoid structure and enjoy Isabelle's lemmas on
monoids.
\<close>

global_interpretation subst_monoid: monoid rcomp \<V>'
  by (unfold_locales; simp)

section \<open>Acyclic substitutions\<close>
subsection \<open>Definitions and auxiliary lemmas\<close>

text \<open>
The iteration on substitutions is defined below and is followed by several
algebraic properties.

In order to show these properties, we give three different definitions for
iterated substitutions. In short, the first one is simply the iteration of
composition using Isabelle's @{term \<open>(^^)\<close>} operator. This can be understood as
follows:
\begin{align*}
  \sigma^n \triangleq (\underset{n\ \text{times}}{\underbrace{\sigma \circ (\sigma \circ (\dots(\sigma}} \circ \mathcal{V}')\dots))
\end{align*}

Using properties from the monoid structure, this can be written as
\begin{align*}
  \sigma^n \triangleq \underset{n\ \text{times}}{\underbrace{\sigma \circ \dots \circ \sigma}}
\end{align*}

The two other definitions are inductively defined using those two schemes:

\begin{align*}
  \sigma^{n+1} &= \sigma \circ \sigma^n\\
  \sigma^{n+1} &= \sigma^n \circ \sigma
\end{align*}

We prove that these three definitions are equivalent and use them in the proofs
of the properties that follow.
\<close>

definition iter_rcomp :: \<open>('s, 'v) subst \<Rightarrow> nat \<Rightarrow> ('s, 'v) subst\<close>
  (\<open>_\<^bsup>_\<^esup>\<close> [200, 0] 1000) where \<open>\<sigma>\<^bsup>n\<^esup> \<equiv> ((\<circ>) \<sigma> ^^ n) \<V>'\<close>

lemma iter_rcomp_Suc_right:\<open>\<sigma>\<^bsup>Suc n\<^esup> = \<sigma>\<^bsup>n\<^esup> \<circ> \<sigma>\<close>
  unfolding iter_rcomp_def funpow_Suc_right comp_def \<V>'_neutral_rcomp
  by (induction n; simp)

lemma iter_rcomp_Suc_left:\<open>\<sigma>\<^bsup>Suc n\<^esup> = \<sigma> \<circ> \<sigma>\<^bsup>n\<^esup>\<close>
  unfolding iter_rcomp_def funpow_Suc_right comp_def \<V>'_neutral_rcomp
  by (induction n; simp)

fun iter_rcomp' :: \<open>('s, 'v) subst \<Rightarrow> nat \<Rightarrow> ('s, 'v) subst\<close>
  where
  \<open>iter_rcomp' \<sigma> 0 = \<V>'\<close>
| \<open>iter_rcomp' \<sigma> (Suc n) = \<sigma> \<circ> (iter_rcomp' \<sigma> n)\<close>
lemma iter_rcomp_eq_iter_rcomp':\<open>\<sigma>\<^bsup>n\<^esup> = iter_rcomp' \<sigma> n\<close>
  by (induction n; simp add: iter_rcomp_def)

fun iter_rcomp'' :: \<open>('s, 'v) subst \<Rightarrow> nat \<Rightarrow> ('s, 'v) subst\<close>
  where
  \<open>iter_rcomp'' \<sigma> 0 = \<V>'\<close>
| \<open>iter_rcomp'' \<sigma> (Suc n) = (iter_rcomp'' \<sigma> n) \<circ> \<sigma>\<close>

lemma iter_rcomp_eq_iter_rcomp'':\<open>\<sigma>\<^bsup>n\<^esup> = iter_rcomp'' \<sigma> n\<close>
  by (induction n, simp add: iter_rcomp_def, simp add: iter_rcomp_Suc_right)

lemmas iter_rcomp'_eq_iter_rcomp'' =
  iter_rcomp_eq_iter_rcomp'[symmetric, simplified iter_rcomp_eq_iter_rcomp'']

text\<open>
The following lemmas show some algebraic properties on iterations of
substitutions, namely that for any @{term \<sigma>}, the function $n~\mapsto~\sigma^n$
i.e.\ @{term \<open>iter_rcomp \<sigma>\<close>} is a magma homomorphism between $(\mathbb{N}, +)$
and $(subst, \circ)$.
Since @{thm iter_rcomp_def[of \<sigma> 0, simplified]}, it is even a (commutative) monoid homomorphism.
\<close>

lemma iter_comp_add_morphism: \<open>(\<sigma>\<^bsup>n\<^esup>) \<circ> (\<sigma>\<^bsup>k\<^esup>) = \<sigma>\<^bsup>n+k\<^esup>\<close>
  unfolding iter_rcomp_eq_iter_rcomp' iter_rcomp'_eq_iter_rcomp''
  by(induction k; simp add:
    rcomp_assoc[of \<open>iter_rcomp'' \<sigma> n\<close> \<open>iter_rcomp'' \<sigma> k\<close> \<sigma> for k, symmetric])

lemmas iter_comp_com_add_morphism =
  iter_comp_add_morphism[
    of \<sigma> n k for \<sigma> n k,
    simplified add.commute,
    unfolded iter_comp_add_morphism[of \<sigma> k n, symmetric]]

text \<open>
There is a similar property with multiplication, stated as follows:
\begin{align*}
\forall \sigma,n,k. (\sigma^n)^k = \sigma^{n\times k}
\end{align*}
This is shown by the following lemma. The next one shows commutativity.
\<close>

lemma iter_comp_mult_morphism: \<open>(\<sigma>\<^bsup>n\<^esup>)\<^bsup>k\<^esup> = \<sigma>\<^bsup>n*k\<^esup>\<close>
  unfolding iter_rcomp_eq_iter_rcomp' iter_rcomp'_eq_iter_rcomp''
  by (induction k; simp only:
    mult_Suc_left iter_comp_add_morphism[
      symmetric, 
      unfolded iter_rcomp_eq_iter_rcomp' iter_rcomp'_eq_iter_rcomp'']
    iter_rcomp''.simps mult_0_right)

lemmas iter_comp_com_mult_morphism =
  iter_comp_mult_morphism[
    of \<sigma> n k for \<sigma> k n,
    simplified mult.commute,
    unfolded iter_comp_mult_morphism[of \<sigma> k n, symmetric]]

text\<open>
Some simplification rules are added to the rules to help automatize subsequent
proofs.
\<close>

lemma iter_rcomp_\<V>'[simp]: \<open>\<V>'\<^bsup>n\<^esup> = \<V>'\<close>
  unfolding iter_rcomp_eq_iter_rcomp'
  by (induction n; simp)

lemma iter_rcomp_0[simp]: \<open>\<sigma>\<^bsup>0\<^esup> = \<V>'\<close>
  unfolding iter_rcomp_eq_iter_rcomp' by simp

lemma iter_rcomp_1[simp]: \<open>\<sigma>\<^bsup>Suc 0\<^esup> = \<sigma>\<close>
  unfolding iter_rcomp_eq_iter_rcomp' by simp

definition dom :: \<open>('s, 'v) subst \<Rightarrow> ('s, 'v) tm set\<close> where
  \<open>dom \<sigma> \<equiv> {\<V> x | x. (\<V> x)\<cdot>\<sigma> \<noteq> \<V> x}\<close>

definition ran :: \<open>('s, 'v) subst \<Rightarrow> ('s, 'v) tm set\<close> where
  \<open>ran \<sigma> \<equiv> (\<lambda>x. x\<cdot>\<sigma>) ` dom \<sigma>\<close>

lemma no_sub_in_dom_subst_eq: \<open>(\<forall> x \<in> dom \<sigma>. \<not> sub x t) \<Longrightarrow> t = t\<cdot>\<sigma>\<close>
  unfolding dom_def
  by (induction t)
    ((simp add: subst_app.rep_eq split: hd.split, metis sub_refl),
    (simp add: subst_app.rep_eq, metis sub_arg sub_fun))

lemma subst_eq_on_domI:
  \<open>(\<forall>x. x \<in> dom \<sigma> \<or> x \<in> dom \<theta> \<longrightarrow> x\<cdot>\<sigma> = x\<cdot>\<theta>) \<Longrightarrow> \<sigma> = \<theta>\<close>
  by (intro subst_ext_tmI' allI)
    (metis comp_apply no_sub_in_dom_subst_eq sub_HdE)

lemma subst_finite_dom:\<open>finite (dom \<sigma>)\<close>
  unfolding dom_def using subst_alt_def[of \<sigma>] by simp

lemma \<V>'_emp_dom: \<open>dom \<V>' = \<emptyset>\<close>
  unfolding dom_def by simp

lemma var_not_in_dom [simp]: \<open>\<V> x \<notin> dom \<sigma> \<Longrightarrow> ((\<V> x)\<cdot>\<sigma>\<^bsup>n\<^esup>) = \<V> x\<close>
  unfolding dom_def
  by (induction n; simp add: iter_rcomp_Suc_left rcomp_subst_simp)

lemma ran_alt_def:\<open>ran \<sigma> = {(\<V> x)\<cdot>\<sigma> | x. (\<V> x)\<cdot>\<sigma> \<noteq> \<V> x}\<close>
  unfolding ran_def dom_def
  by blast

definition is_ground_subst :: \<open>('s, 'v) subst \<Rightarrow> bool\<close> where
  \<open>is_ground_subst \<sigma> \<equiv> (ground ` ran \<sigma>) = {True}\<close>

lemma is_ground_subst_alt_def:
  \<open>is_ground_subst \<sigma> \<longleftrightarrow> (ran \<sigma> \<noteq> \<emptyset>) \<and> (\<forall>x. (\<V> x)\<cdot>\<sigma> \<noteq> \<V> x \<longrightarrow> ground ((\<V> x)\<cdot>\<sigma>))\<close>
  unfolding is_ground_subst_def ran_def dom_def
  by (standard, auto)

lemma ground_subst_grounds:\<open>is_ground_subst \<sigma> \<Longrightarrow> x \<in> dom \<sigma> \<Longrightarrow> ground (x\<cdot>\<sigma>)\<close>
  unfolding dom_def
  by (induction x) (auto simp add: is_ground_subst_alt_def)

lemma iter_on_ground:\<open>ground (x\<cdot>\<sigma>) \<Longrightarrow> n > 0 \<Longrightarrow> x\<cdot>\<sigma>\<^bsup>n\<^esup> = x\<cdot>\<sigma>\<close>
  using ground_imp_subst_iden 
  unfolding iter_rcomp_eq_iter_rcomp'
  by (induction n, blast)
    (simp add: rcomp_subst_simp, simp add: subst_app.rep_eq)

lemma true_subst_nempty_vars:
  \<open>\<sigma> \<noteq> \<V> \<Longrightarrow> {t. is_Hd t \<and> is_Var (head t) \<and> subst \<sigma> t \<noteq> t} \<noteq> {}\<close>
proof -
  assume \<open>\<sigma> \<noteq> \<V>\<close>
  then obtain t where \<open>\<sigma> t \<noteq> \<V> t\<close>
    by blast
  moreover have \<open>is_Hd (\<V> t)\<close> \<open>is_Var (head (\<V> t))\<close>
    by simp+
  ultimately show ?thesis
    by fastforce
qed

lemma true_subst_nemp_im:\<open>ran \<sigma> = {} \<Longrightarrow> \<sigma> = \<V>'\<close>
  unfolding ran_def dom_def
  by (transfer, auto simp add: is_subst_def dest: true_subst_nempty_vars)

lemma ground_subst_imp_no_var_mapped_on_var:
  \<open>is_ground_subst \<sigma> \<Longrightarrow> (\<forall>x y. x \<noteq> y \<longrightarrow> (\<V> x)\<cdot>\<sigma> \<noteq> (\<V> y))\<close>
proof -
  have \<open>\<not> (\<forall> x y. x \<noteq> y \<longrightarrow> (\<V> x)\<cdot>\<sigma> \<noteq> (\<V> y)) \<Longrightarrow> \<not> is_ground_subst \<sigma>\<close>
  proof -
    assume \<open>\<not> (\<forall> x y. x \<noteq> y \<longrightarrow> (\<V> x)\<cdot>\<sigma> \<noteq> (\<V> y))\<close>
    then obtain x y where xy_def:\<open>x \<noteq> y\<close> \<open>(\<V> x)\<cdot>\<sigma> = (\<V> y)\<close>
      by blast
    hence
      \<open>(\<V> x)\<cdot>\<sigma>\<noteq>(\<V> x)\<close>
      \<open>\<V> x \<in> {x. is_Var (head x) \<and> x \<cdot> \<sigma> \<noteq> x}\<close>
      \<open>\<not> ground ((\<V> x)\<cdot>\<sigma>)\<close>
      by fastforce+

    then show \<open>\<not> is_ground_subst \<sigma>\<close>
      unfolding is_ground_subst_def ran_def dom_def
      by blast
  qed

  from contrapos_pp[
    rotated,
    of \<open>\<forall> x y. x \<noteq> y \<longrightarrow> (\<V> x)\<cdot>\<sigma> \<noteq> (\<V> y)\<close> \<open>is_ground_subst \<sigma>\<close>,
    OF this]
  show \<open>is_ground_subst \<sigma> \<Longrightarrow> (\<forall> x y. x \<noteq> y \<longrightarrow> (\<V> x)\<cdot>\<sigma> \<noteq> (\<V> y))\<close>.
qed

lemma ran_\<V>'_empty:\<open>ran \<V>' = \<emptyset>\<close>
  unfolding ran_def dom_def using \<V>'_iff
  by fast

lemma non_ground_\<V>': \<open>\<not> is_ground_subst \<V>'\<close>
  using is_ground_subst_alt_def ran_\<V>'_empty by blast

subsection \<open>Acyclicity\<close>

text \<open>
A substitution is said to be \emph{acyclic} if no variable @{term \<open>x::(_,_) tm\<close>}
in the domain of @{term \<sigma>} occurs as a subterm of @{term \<open>(x::(_,_) tm)\<cdot>\<sigma>\<^bsup>n\<^esup>\<close>}
for any @{term \<open>n > 0\<close>}.
\<close>

definition is_acyclic :: \<open>('s, 'v) subst \<Rightarrow> bool\<close> where
  \<open>is_acyclic \<sigma> \<equiv> (\<forall> x \<in> dom \<sigma>. \<forall> n > 0. x \<notin> subterms (x\<cdot>\<sigma>\<^bsup>n\<^esup>))\<close>

lemma is_acyclicE:\<open> is_acyclic \<sigma> \<Longrightarrow> x \<in> dom \<sigma> \<Longrightarrow> n > 0 \<Longrightarrow> x \<notin> subterms (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
  unfolding is_acyclic_def by blast

lemma non_acyclic_\<V>': \<open>is_acyclic \<V>'\<close>
  using \<V>'_emp_dom is_acyclic_def by fast

lemma acyclic_iter_dom_eq:\<open>is_acyclic \<sigma> \<Longrightarrow> dom \<sigma> = dom \<sigma>\<^bsup>n\<^esup>\<close> if \<open>n > 0\<close> for n
    using that unfolding dom_def is_acyclic_def subterms_def
    by (induction n, fast, simp)
    (smt (verit, ccfv_SIG)
      Collect_cong
      bot_nat_0.not_eq_extremum
      \<V>'_id_tm
      iter_rcomp_eq_iter_rcomp'
      iter_rcomp'.simps
      mem_Collect_eq
      rcomp_subst_simp
      sub_refl
      zero_less_Suc)
    (* TODO *)

lemma acyclic_iter: \<open>is_acyclic \<sigma> \<Longrightarrow> n > 0 \<Longrightarrow> is_acyclic \<sigma>\<^bsup>n\<^esup>\<close>
  unfolding is_acyclic_def subterms_def
  by (auto simp add: iter_comp_mult_morphism dom_def dest: CollectD,
    use var_not_in_dom[unfolded dom_def] in fastforce)

subsection \<open>Fixed-point substitution\<close>

text \<open>
We define the fixed-point substitution of a substitution @{term \<sigma>} as the substitution @{term \<open>\<sigma>\<^bsup>i\<^esup>\<close>} where $\displaystyle{i = \inf \{k \in \mathbb{N} \mid \sigma^k = \sigma^{k+1}\}}$.
\<close>

definition fp_subst :: \<open>('s, 'v) subst \<Rightarrow> ('s, 'v) subst\<close> (\<open>_\<^sup>\<star>\<close> 1000) where
  \<open>\<sigma>\<^sup>\<star> \<equiv> iter_rcomp \<sigma> (LEAST n . \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n+1\<^esup>)\<close>

lemma ground_subst_is_fp:\<open>is_ground_subst \<sigma> \<Longrightarrow> \<sigma>\<^sup>\<star> = \<sigma>\<close>
\<comment>\<open>Ground substitutions have no effect and are therefore fixed-points substitutions.
The converse is not true.\<close>
proof -
  assume asm:\<open>is_ground_subst \<sigma>\<close>
  have eq:\<open>\<sigma>\<^bsup>1\<^esup> = \<sigma>\<^bsup>2\<^esup>\<close>
    apply (simp only: one_add_one[symmetric],
      simp, intro subst_ext_tmI' allI, simp)
    subgoal for x
      unfolding iter_rcomp_eq_iter_rcomp'
      by (cases \<open>\<V> x \<in> dom \<sigma>\<close>,
        simp add: rcomp_subst_simp,
        metis
          ground_subst_grounds[OF asm, THEN ground_imp_subst_iden]
          subst_app.rep_eq,
        simp add: dom_def rcomp_subst_simp).

  note least_le1=Least_le[of \<open>\<lambda>n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n + 1\<^esup>\<close> 1, unfolded nat_1_add_1, OF this]
  have neq:\<open>\<sigma>\<^bsup>0\<^esup> \<noteq> \<sigma>\<^bsup>1\<^esup>\<close>
    using asm non_ground_\<V>'
    unfolding iter_rcomp_eq_iter_rcomp'
    by auto
  have \<open>(LEAST n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n + 1\<^esup>) \<noteq> 0\<close>
  proof (rule ccontr)
    assume \<open>\<not> (LEAST n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n + 1\<^esup>) \<noteq> 0\<close>
    hence \<open>(LEAST n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n + 1\<^esup>) = 0\<close> by blast
    from
      LeastI[of \<open>\<lambda>n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n + 1\<^esup>\<close> 1, simplified one_add_one, OF eq,
        simplified add_0 this]
      neq
    show False by blast
  qed
  moreover have \<open>(LEAST x. \<sigma>\<^bsup>x\<^esup> = \<sigma>\<^bsup>x + 1\<^esup>) = 0 \<or> (LEAST x. \<sigma>\<^bsup>x\<^esup> = \<sigma>\<^bsup>x + 1\<^esup>) = 1\<close>
    using least_le1 by linarith
  ultimately have \<open>(LEAST n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n + 1\<^esup>) = 1\<close>
    by sat
  then show \<open>\<sigma>\<^sup>\<star> = \<sigma>\<close>
    unfolding fp_subst_def iter_rcomp_eq_iter_rcomp'
    by simp
qed

text \<open>
In the following, we prove that fixed-point substitutions are well-defined for
acyclic substitutions. To help visualise how the proofs are carried out, for any
terms @{term x} and @{term y} and any substitution @{term \<sigma>}, we denote the fact 
that \<open>x\<close> is substituted by \<open>y\<close> after one application of \<open>\<sigma>\<close>, i.e.\ that @{term \<open>sub y (x\<cdot>\<sigma>)\<close>}, by \<open>x \<rightarrow>\<^sub>\<sigma> y\<close>.

\begin{remark}
In fact, automata could be used to model substitutions with variables in the domain as the initial states and variables outside of the domain and constants as final
states. The transitions would be given by the successive substitutions.
Acyclic substitutions would be represented by a DAG.
\end{remark}
\<close>

lemma dom_sub_subst: \<open>x \<in> dom \<sigma> \<Longrightarrow> sub x (t\<cdot>\<sigma>) \<Longrightarrow> \<exists>y \<in> dom \<sigma>. sub x (y\<cdot>\<sigma>)\<close>
\<comment>\<open>
If \<open>x \<rightarrow>\<^sub>\<sigma> t\<close> for \<open>x \<in> dom \<sigma>\<close> and a term \<open>t\<close>, then there is a variable \<open>y \<in> dom \<sigma>\<close>
such that \<open>x \<rightarrow>\<^sub>\<sigma> y\<close>.
\<close>
  apply (induction t)
  subgoal for t0
    apply (cases t0)
    unfolding dom_def apply fastforce
    by (metis (no_types, lifting) hd.set(4) tm.set(3) ground_imp_subst_iden subst_app.rep_eq sub_HdE)
  subgoal for t1 t2
    by (simp add: dom_def) (metis subst.simps(2) tm.distinct(1) subst_app.rep_eq sub_AppE)
  done

lemma dom_sub_subst_contrapos:
\<comment>\<open>For \<open>x\<close> in the domain, if there is no \<open>z\<close> in the domain such that \<open>x \<rightarrow>\<^sub>\<sigma> z\<close>,
then there is not term \<open>t\<close> such that \<open>x \<rightarrow>\<^sub>\<sigma> t\<close>.\<close>
  \<open>x \<in> dom \<sigma> \<Longrightarrow> \<forall>z \<in> dom \<sigma>. \<not> sub x (z\<cdot>\<sigma>) \<Longrightarrow> \<forall>t. \<not> sub x (t\<cdot>\<sigma>)\<close>
  using dom_sub_subst by blast

lemma dom_sub_subst_iter:
  \<open>x \<in> dom \<sigma> \<Longrightarrow> \<forall>z \<in> dom \<sigma>. \<not> sub x (z\<cdot>\<sigma>\<^bsup>n\<^esup>) \<Longrightarrow> \<not> sub x (t\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
  by (induction n arbitrary: x \<sigma>,
    simp, use sub_refl in blast,
    smt (verit, ccfv_threshold)
      One_nat_def
      \<V>'_id_tm
      \<V>'_neutral_rcomp(1)
      dom_def
      dom_sub_subst
      iter_comp_add_morphism
      iter_rcomp_Suc_right
      iter_rcomp_eq_iter_rcomp'
      iter_rcomp'.simps(1)
      mem_Collect_eq
      plus_1_eq_Suc
      rcomp_subst_simp
      sub_refl
      subst_eq_sub)
  (* TODO *)

lemma
  assumes \<open>x \<in> dom \<sigma>\<close> \<open>\<forall>y \<in> dom \<sigma>. sub y t \<longrightarrow> \<not> sub x (y\<cdot>\<sigma>)\<close>
  shows not_sub_subst_if:\<open>\<not> sub x (t\<cdot>\<sigma>)\<close>
\<comment>\<open>For \<open>x\<close> in the domain and any term \<open>t\<close>, if there is no variable \<open>y\<close> occurring
in \<open>t\<close> such that \<open>x \<rightarrow>\<^sub>\<sigma> y\<close>, then $x \not\rightarrow_\sigma t$.\<close>
  using assms
  by (induction t)
    ((smt (verit, ccfv_threshold)
      hd.case_eq_if
      subst.simps(1)
      \<V>'_id_tm
      dom_def
      \<V>'.rep_eq
      subst_app.rep_eq
      mem_Collect_eq
      sub_HdE
      sub_refl),
    (smt (verit, ccfv_threshold)
      subst.simps(2)
      comp_apply
      dom_def
      subst_app.rep_eq
      mem_Collect_eq
      sub_Hd_AppE
      sub_arg
      sub_fun))
  (* TODO *)

lemma dom_sub_subst_iter_Suc:
  \<open>x \<in> dom \<sigma> \<Longrightarrow> sub x (t\<cdot>\<sigma>\<^bsup>n+1\<^esup>) \<Longrightarrow>
    \<exists>y z. y \<in> dom \<sigma> \<and> z \<in> dom \<sigma> \<and> sub x (z\<cdot>\<sigma>) \<and> sub z (y\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
\<comment>\<open>If $x \rightarrow_{\sigma}^{n+1} t$, then there are variables \<open>y\<close> and \<open>z\<close> such
that $y \rightarrow_{\sigma}^{n} z \rightarrow_{\sigma} x$.\<close>
proof (induction n arbitrary: x t)
  case 0
  then show ?case
    unfolding add_0 One_nat_def iter_rcomp_Suc_right rcomp_subst_simp
      iter_rcomp_0 \<V>'_neutral_rcomp \<V>'_id_tm
    using dom_sub_subst sub_refl by blast
next
  case (Suc n)
  then obtain t' where t'_def: \<open>sub t' (t\<cdot>\<sigma>\<^bsup>n+1\<^esup>) \<close> \<open>sub x (t'\<cdot>\<sigma>)\<close> 
    by (metis Suc_eq_plus1 iter_rcomp_Suc_right rcomp_subst_simp sub_refl)
  have \<open>\<exists>w \<in> dom \<sigma>. sub w t' \<and> sub x (w\<cdot>\<sigma>)\<close>
    using not_sub_subst_if Suc.prems(1) t'_def(2) by blast
  then obtain w where w_def: \<open>w \<in> dom \<sigma>\<close> \<open>sub w t'\<close> \<open>sub x (w\<cdot>\<sigma>)\<close>
    by blast

  then obtain y where \<open>y \<in> dom \<sigma>\<close> \<open>sub w (y\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>
    apply (fold Suc_eq_plus1, unfold iter_rcomp_Suc_right rcomp_subst_simp)
    using sub_subst' sub_trans Suc.IH t'_def by meson

  with w_def show ?case
    by auto
qed

lemma sub_Suc_n_sub_n_sub:
  \<open>(\<exists> x \<in> dom \<sigma>. sub z (x\<cdot>\<sigma>\<^bsup>n+1\<^esup>)) \<longleftrightarrow>
  (\<exists> x y. x \<in> dom \<sigma> \<and> y \<in> dom \<sigma> \<and> sub z (y\<cdot>\<sigma>) \<and> sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>))\<close> if \<open>z \<in> dom \<sigma>\<close>
  using that
proof (intro iffI)
  show \<open>z \<in> dom \<sigma> \<Longrightarrow> \<exists>x\<in>dom \<sigma>. sub z (x\<cdot>\<sigma>\<^bsup>n + 1\<^esup>) \<Longrightarrow>
    \<exists>x y. x \<in> dom \<sigma> \<and> y \<in> dom \<sigma> \<and> sub z (y\<cdot>\<sigma>) \<and> sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
  proof-
    assume \<open>\<exists>x\<in>dom \<sigma>. sub z (x\<cdot>\<sigma>\<^bsup>n + 1\<^esup>)\<close> \<open>z \<in> dom \<sigma>\<close>
    then obtain x where \<open>x\<in>dom \<sigma>\<close> \<open>sub z (x\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>
      by blast

    then obtain y where \<open>y \<in> dom \<sigma>\<close> \<open>sub z (y\<cdot>\<sigma>)\<close> \<open>sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
      by (metis Suc_eq_plus1 \<open>z \<in> dom \<sigma>\<close> iter_rcomp_Suc_right
        not_sub_subst_if rcomp_subst_simp) (* TODO *)

    then show \<open>\<exists>x y. x \<in> dom \<sigma> \<and> y \<in> dom \<sigma> \<and> sub z (y\<cdot>\<sigma>) \<and> sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
      using \<open>x \<in> dom \<sigma>\<close> by blast
  qed
  show \<open>z \<in> dom \<sigma> \<Longrightarrow>
    \<exists>x y. x \<in> dom \<sigma> \<and> y \<in> dom \<sigma> \<and> sub z (y\<cdot>\<sigma>) \<and> sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>) \<Longrightarrow>
    \<exists>x\<in>dom \<sigma>. sub z (x\<cdot>\<sigma>\<^bsup>n + 1\<^esup>)\<close>
  proof -
    assume \<open>\<exists> x y. x \<in> dom \<sigma> \<and> y \<in> dom \<sigma> \<and> sub z (y\<cdot>\<sigma>) \<and> sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
    then obtain x y where xy_def:
      \<open>x \<in> dom \<sigma>\<close> \<open>y \<in> dom \<sigma>\<close> \<open>sub z (y\<cdot>\<sigma>)\<close> \<open>sub y (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
      by blast
    then have \<open>sub (y\<cdot>\<sigma>) (x\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>
      unfolding Suc_eq_plus1[symmetric] iter_rcomp_Suc_right rcomp_subst_simp
      using sub_subst' by blast
    with xy_def(3) have \<open>sub z (x\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>
      using sub_trans by blast
    with xy_def(1) show \<open>\<exists>x\<in>dom \<sigma>. sub z (x\<cdot>\<sigma>\<^bsup>n + 1\<^esup>)\<close>
      by fast
  qed
qed

text\<open>
The following theorem is the main result of this theory and states that for acyclic
substitutions, the fixed-point substitution exists and is well defined. The main
idea of the proof is to define a non-negative quantity and show that successively
applying the substitution makes it decrease.

For any such iteration $n$, we define the set of variables that will be
substituted by the next iteration of the substitution and denote it by $S_n$.
Formally, $S_n$ is defined as follows:

\begin{equation*}
  S_n :=  \{z \in \text{dom}\ \sigma \mid \exists x \in \text{dom}\ \sigma.\ x \rightarrow_{\sigma}^n z\}
\end{equation*}

There is a clear recurrence relation between $S_{n+1}$ and $S_n$, namely that
the variables in $S_{n+1}$ are exactly the variables in $S_n$ that are not sources
in $S_n$, i.e.\ that have a predecessor -- for the subterm relation -- in $S_n$.
This is formalized as follows: 

\begin{equation*}
  S_{n+1} = S_n - \{z \in S_n \mid \forall x \in S_n.\ x \not\rightarrow_\sigma z \}
\end{equation*}

This implies that the sequence $(S_n)_{n \in \mathbb{N}}$ is strictly monotone
for inclusion.
Since it is bounded and has its values in finite sets, it is convergent and there
is a rank $k$ from which it is constant and equal to the infimum of the range,
the empty set.
\<close>

theorem fp_subst: \<open>is_acyclic \<sigma> \<Longrightarrow> \<exists>n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n+1\<^esup>\<close>
proof -
  assume acyc:\<open>is_acyclic \<sigma>\<close>
  define S where \<open>S \<equiv> \<lambda> n. \<Union>(subterms ` ran \<sigma>\<^bsup>n\<^esup>) \<inter> dom \<sigma>\<close>
  
  have S_alt_def: \<open>S n = {z \<in> dom \<sigma>. \<exists>x \<in> dom \<sigma>. sub z (x\<cdot>\<sigma>\<^bsup>n\<^esup>)}\<close> if \<open>n > 0\<close> for n
    unfolding S_def ran_def subterms_def
      acyclic_iter_dom_eq[OF that acyc, symmetric]
    by blast
  
  have S_\<sigma>_unfold:
    \<open>S n \<cdot> \<sigma> = {x\<cdot>\<sigma> | x. x \<in> dom \<sigma> \<and> (\<exists>y\<in>dom \<sigma>. sub x (y\<cdot>\<sigma>\<^bsup>n\<^esup>))}\<close> if \<open>n > 0\<close> for n
    unfolding set_image_subst_collect[of \<open>S n\<close>, unfolded S_def]
      S_def subterms_def
    unfolding ran_def acyclic_iter_dom_eq[OF that acyc, symmetric]
    by blast
  
  have sources_charac:
    \<open>n > 0 \<Longrightarrow> S (n+1) = S n - {z \<in> S n. \<forall>x \<in> S n. \<not> sub z (x\<cdot>\<sigma>)}\<close> for n
  proof (intro subset_antisym subsetI)
    fix z assume \<open>n > 0\<close>
    show \<open>z \<in> S (n + 1) \<Longrightarrow> z \<in> S n - {z \<in> S n. \<forall>x\<in>S n. \<not> sub z (x\<cdot>\<sigma>)}\<close>
    proof-
      assume \<open>z \<in> S (n + 1)\<close>
      then obtain x where x_def: \<open>x \<in> dom \<sigma>\<close> \<open>sub z (x\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>
        unfolding S_alt_def[OF zero_less_Suc[of n, unfolded Suc_eq_plus1]]
        by blast
      then have \<open>z \<in> S n\<close>
        unfolding S_def ran_def
          acyclic_iter_dom_eq[OF \<open>n > 0\<close> acyc, symmetric]
          subterms_def
        by (simp, metis IntE S_def Suc_eq_plus1 \<open>z \<in> S (n + 1)\<close>
          dom_sub_subst_iter iter_rcomp_Suc_left rcomp_subst_simp)
      moreover have \<open>\<exists>x\<in>S n. sub z (x\<cdot>\<sigma>)\<close>
        using 
          S_alt_def[OF \<open>n > 0\<close>]
          dom_sub_subst_iter_Suc[of z \<sigma>]
          x_def(2) \<open>z \<in> S n\<close>
        by fast

      ultimately show \<open>z \<in> S n - {z \<in> S n. \<forall>x\<in>S n. \<not> sub z (x\<cdot>\<sigma>)}\<close>
        by blast
    qed
    show \<open>z \<in> S n - {z \<in> S n. \<forall>x\<in>S n. \<not> sub z (x\<cdot>\<sigma>)} \<Longrightarrow> z \<in> S (n + 1)\<close>
    proof-
      assume \<open>z \<in> S n - {z \<in> S n. \<forall>x\<in>S n. \<not> sub z (x\<cdot>\<sigma>)}\<close>
      hence \<open>z \<in> S n\<close> \<open>\<exists>y\<in>S n. sub z (y\<cdot>\<sigma>)\<close>
        by blast+
      then obtain x y w where
        \<open>x \<in> dom \<sigma>\<close> \<open>sub z (x\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
        \<open>y \<in> dom \<sigma>\<close> \<open>w \<in> dom \<sigma>\<close> \<open>sub z (y\<cdot>\<sigma>)\<close> \<open>sub y (w\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
        unfolding S_def subterms_def ran_def
          acyclic_iter_dom_eq[OF \<open>n > 0\<close> acyc, symmetric]
        by blast
      show \<open>z \<in> S (n+1)\<close>
        unfolding S_alt_def[OF zero_less_Suc[of n], unfolded Suc_eq_plus1]
        apply (simp, intro conjI, use \<open>z \<in> S n\<close>[unfolded S_def] in simp)
          using sub_trans[OF \<open>sub z (y\<cdot>\<sigma>)\<close>
            sub_subst'[OF \<open>sub y (w\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>, of \<sigma>]] \<open>w \<in> dom \<sigma>\<close>
          unfolding iter_rcomp_Suc_right rcomp_subst_simp
        by (intro bexI[of _ w])
    qed
  qed

  have fin_Sn: \<open>finite (S n)\<close> for n
    unfolding S_def using subst_finite_dom
    by blast

  have decr: \<open>S n \<noteq> \<emptyset> \<Longrightarrow> S (n+1) \<subset> S n\<close> for n
  proof
    show \<open>S n \<noteq> \<emptyset> \<Longrightarrow> S (n+1) \<subseteq> S n\<close>
    proof (cases \<open>n > 0\<close>)
      case True
      assume \<open>S n \<noteq> \<emptyset>\<close>
      show ?thesis
      proof (intro subsetI, rule ccontr)
        fix x assume \<open>x \<in> S(n+1)\<close> \<open>x \<notin> S n\<close>
        from this(1)[
          unfolded S_alt_def[OF zero_less_Suc[of n],
            unfolded Suc_eq_plus1],
          simplified,
          unfolded Suc_eq_plus1]
        obtain y where \<open>x \<in> dom \<sigma>\<close> \<open>y \<in> dom \<sigma>\<close> \<open>sub x (y\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>
          by blast
        with \<open>x \<notin> S n\<close>[unfolded S_alt_def[OF True], simplified]
        have \<open>\<forall>z\<in>dom \<sigma>. \<not> sub x (z\<cdot>\<sigma>\<^bsup>n\<^esup>)\<close>
          by blast
        from
          dom_sub_subst_iter[OF \<open>x \<in> dom \<sigma>\<close> this, of \<open>y\<cdot>\<sigma>\<close>]
        show False
          using \<open>sub x (y\<cdot>\<sigma>\<^bsup>n+1\<^esup>)\<close>[
            folded Suc_eq_plus1,
            unfolded iter_rcomp_Suc_left rcomp_subst_simp] ..
      qed
    next
      case False
      assume \<open>S n \<noteq> \<emptyset>\<close>
      moreover have \<open>S 0 = \<emptyset>\<close>
        unfolding S_def iter_rcomp_eq_iter_rcomp'
        by (simp add: ran_\<V>'_empty)
      ultimately show ?thesis
        using False by simp
    qed

    show \<open>S n \<noteq> \<emptyset> \<Longrightarrow> S (n+1) \<noteq> S n\<close>
    proof (cases n)
      case (Suc m)
      hence \<open>n > 0\<close> by simp
      assume \<open>S n  \<noteq> \<emptyset>\<close>
      have \<open>{z \<in> S n. \<forall>x \<in> S n. \<not> sub z (x\<cdot>\<sigma>)} \<noteq> \<emptyset>\<close>
      proof (rule ccontr)
        assume \<open>\<not> {z \<in> S n. \<forall>x\<in>S n. \<not> sub z (x\<cdot>\<sigma>)} \<noteq> {}\<close>
        hence ch: \<open>\<forall>x. x \<in> S n \<longrightarrow> (\<exists>y \<in> S n. sub x (y\<cdot>\<sigma>))\<close>
          by simp
        define E where \<open>E \<equiv> \<lambda>x. {y \<in> S n. sub x (y\<cdot>\<sigma>)}\<close>
        have E_nemp: \<open>x \<in> S n \<Longrightarrow> E x \<noteq> \<emptyset>\<close> for x
          unfolding E_def using ch by fast
        have \<open>x \<in> S n \<Longrightarrow> x \<notin> E x\<close> for x
        proof (rule ccontr)
          assume a: \<open>x \<in> S n\<close> \<open>\<not> x \<notin> E x\<close>
          from this(1) have \<open>x \<in> dom \<sigma>\<close>
            unfolding S_def by fast
          with conjunct2[OF a(2)[simplified, unfolded E_def, simplified]]
          acyc[
            unfolded is_acyclic_def subterms_def,
            simplified,
            rule_format,
            OF this zero_less_Suc[of 0],
            unfolded iter_rcomp_Suc_right,
            simplified]
          show False
            by satx
        qed

        with ch \<open>S n  \<noteq> \<emptyset>\<close> obtain x y where \<open>x \<in> S n\<close> \<open>y \<in> S n\<close> \<open>sub y (x\<cdot>\<sigma>)\<close>
          by blast
        with acyc have \<open>y \<noteq> x\<close>
          unfolding S_def is_acyclic_def subterms_def
          by (metis IntE One_nat_def \<V>'_id_tm iter_rcomp_0
            iter_rcomp_Suc_left mem_Collect_eq rcomp_subst_simp zero_less_one)

        let ?C = \<open>card (S n)\<close>
        have incl: \<open>E v \<subseteq> S n\<close> for v
          unfolding E_def by blast

        have \<open>k > 0 \<Longrightarrow>
          \<exists> seq. k = length seq \<and>
            seq!0 \<in> S n \<and>
            (\<forall> m < length seq - 1. seq!(m+1) \<in> E (seq!m)) \<and>
            distinct seq\<close>
          for k
        proof (induction k rule: nat_induct_non_zero)
          case (Suc k)
          then obtain seq where seq_def: \<open>k = length seq\<close> \<open>seq!0 \<in> S n\<close>
            \<open>(\<forall> m < k-1. seq!(m+1) \<in> E (seq!m))\<close> \<open>distinct seq\<close>
            by blast
          hence \<open>l < k \<Longrightarrow> seq!l \<in> S n\<close> for l
            unfolding E_def
            by (metis (no_types, lifting) CollectD Suc_eq_plus1
              less_Suc_eq less_Suc_eq_0_disj less_diff_conv)
          with seq_def obtain v where v_def: \<open>v \<in> E (seq!(k-1))\<close>
            using E_nemp Suc.hyps
            by (metis Suc_eq_plus1 Suc_pred' all_not_in_conv less_add_one)
          
          have seq_sub:
            \<open>i < length seq \<Longrightarrow> j \<le> i \<Longrightarrow> sub (seq!j) ((seq!i)\<cdot>\<sigma>\<^bsup>i-j\<^esup>)\<close> for i j
          proof (induction i arbitrary: j)
            case (Suc l)
            with seq_def have \<open>seq!(Suc l) \<in> E (seq!l)\<close>
              by simp
            hence \<open>sub (seq!l) ((seq!(Suc l))\<cdot>\<sigma>)\<close>
              unfolding E_def by blast
            with Suc show ?case
            by (smt (verit, ccfv_SIG)
              cancel_comm_monoid_add_class.diff_cancel
              bot_nat_0.not_eq_extremum
              Suc_diff_Suc
              Suc_lessD
              \<V>'_id_tm
              diff_Suc_Suc
              diff_diff_cancel
              iter_rcomp_0
              iter_rcomp_Suc_left
              le_Suc_eq
              rcomp_subst_simp
              sub_refl
              sub_subst'
              sub_trans
              zero_less_diff)
            (* TODO *)
          qed (simp add: sub_refl)

          define seq' where \<open>seq' \<equiv> seq @ [v]\<close>
          hence \<open>sub (seq!(k-1)) (v\<cdot>\<sigma>)\<close>
            using v_def unfolding E_def
            by blast

          have \<open>v \<in> dom \<sigma>\<close>
            using incl v_def
            unfolding E_def S_def
            by fast

          have \<open>v \<notin> set seq\<close>
          proof
            assume \<open>v \<in> set seq\<close>
            then obtain j where \<open>j < k\<close> \<open>v = seq!j\<close>
              unfolding in_set_conv_nth seq_def(1) by fast
            with seq_sub[of \<open>k-1\<close> j, folded seq_def(1) this(2)] Suc.hyps
            have \<open>sub v (seq!(k-1)\<cdot>\<sigma>\<^bsup>k-1-j\<^esup>)\<close>
              by simp
            from sub_trans[OF
                this
                sub_subst'[OF \<open>sub (seq!(k-1)) (v\<cdot>\<sigma>)\<close>, of \<open>\<sigma>\<^bsup>k-1-j\<^esup>\<close>,
              folded rcomp_subst_simp iter_rcomp_Suc_left]]
            show False
              using acyc \<open>v \<in> dom \<sigma>\<close>
              unfolding is_acyclic_def subterms_def
              by blast
          qed

          show ?case
            by (intro exI[of _ seq'] conjI, unfold seq'_def,
              simp add: seq_def(1),
              simp add:
                seq_def(2)
                nth_append[
                    of seq \<open>[v]\<close> 0,
                    folded seq_def(1),
                    unfolded if_split,
                    simplified]
                Suc.hyps,
              intro allI,
              metis
                butlast_snoc
                diff_add_inverse2
                length_append_singleton
                length_butlast
                less_Suc_eq
                less_diff_conv
                nth_append
                nth_append_length
                seq_def(1,3)
                v_def,
              simp add: \<open>v \<notin> set seq\<close> seq_def(4))
        qed (intro exI[of _ \<open>[x]\<close>] conjI, (simp add: \<open>x \<in> S n\<close>)+)

        then obtain seq where seq_def:
          \<open>?C + 1 = length seq\<close> \<open>seq!0 \<in> S n\<close> \<open>distinct seq\<close>
          \<open>(\<forall> m < length seq - 1. seq!(m+1) \<in> E (seq!m))\<close>
          by auto
          
        have \<open>set seq \<subseteq> S n\<close>
        proof
          fix x assume \<open>x \<in> set seq\<close>
          then obtain i where \<open>seq!i = x\<close> \<open>i < length seq\<close>
            by (metis in_set_conv_nth)
          then show \<open>x \<in> S n\<close>
            by (cases i, use seq_def(2) in simp)
              (metis seq_def(4) One_nat_def Suc_eq_plus1 in_mono incl less_diff_conv)
        qed

        from
          distinct_in_fset[OF fin_Sn, of n ?C, simplified, OF seq_def(3) this]
          seq_def(1)
        show False
          by simp
      qed
      thus ?thesis
        unfolding sources_charac[OF \<open>n > 0\<close>]
        by blast
    next
      case 0 assume \<open>S n \<noteq> \<emptyset>\<close>
      moreover have \<open>S 0 = \<emptyset>\<close>
        unfolding S_def iter_rcomp_0 ran_\<V>'_empty
        by blast
      ultimately show ?thesis
        using 0 by simp
    qed
  qed

  have subset_dom: \<open>n > 0 \<Longrightarrow> S n \<subseteq> dom \<sigma>\<close> for n
    by (induction n) (simp add: S_def)+

  have \<open>finite (S n)\<close> for n
    by (cases n)
      (simp add:
        S_def subst_finite_dom
        subset_dom[THEN finite_subset[OF _ subst_finite_dom[of \<sigma>]]])+
  
  moreover have \<open>S 0 = \<emptyset>\<close>
    unfolding S_def iter_rcomp_eq_iter_rcomp'
    by (simp add: ran_\<V>'_empty)
  
  ultimately obtain k where \<open>k > 0\<close> \<open>S k = \<emptyset>\<close>
    using set_decr_chain_empty[where u=\<open>\<lambda>n. S (Suc n)\<close>] decr
    by auto

  from this(2)[unfolded S_def subterms_def ran_def
    acyclic_iter_dom_eq[OF this(1) acyc, symmetric], simplified]
  have f: \<open>{y. y \<in> dom \<sigma> \<and> (\<exists>x\<in>dom \<sigma>. sub y (x\<cdot>\<sigma>\<^bsup>k\<^esup>))} = \<emptyset>\<close>
    by blast
  then have \<open>\<sigma>\<^bsup>k\<^esup> = \<sigma>\<^bsup>k+1\<^esup>\<close>
    by (intro subst_eq_on_domI allI impI)
    ((simp add:
        acyclic_iter_dom_eq[OF \<open>k > 0\<close> acyc, symmetric]
        acyclic_iter_dom_eq[OF zero_less_Suc[of k] acyc, symmetric]),
      unfold iter_rcomp_Suc_right rcomp_subst_simp,
      simp add: no_sub_in_dom_subst_eq)
  then show ?thesis
    by (intro exI[of _ k])
qed

lemma fp_subst_comp_stable: \<open>is_acyclic \<sigma> \<Longrightarrow> (\<sigma>\<^sup>\<star>) \<circ> (\<sigma>\<^sup>\<star>) = \<sigma>\<^sup>\<star>\<close>
proof-
  assume \<open>is_acyclic \<sigma>\<close>
  with fp_subst obtain m where m_def: \<open>\<sigma>\<^bsup>m\<^esup> = \<sigma>\<^bsup>m+1\<^esup>\<close>
    by blast
  define n where \<open>n \<equiv> LEAST n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n+1\<^esup>\<close>
  have eq: \<open>\<sigma>\<^sup>\<star> = \<sigma>\<^bsup>n\<^esup>\<close>
    unfolding fp_subst_def n_def..
  from m_def have \<open>\<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n+1\<^esup>\<close>
    unfolding n_def
    by (intro LeastI[of \<open>\<lambda>n. \<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n+1\<^esup>\<close> m])
  hence \<open>\<sigma>\<^bsup>n\<^esup> = \<sigma>\<^bsup>n+k\<^esup>\<close> for k
  proof (induction k)
    case (Suc k)
    show ?case
      unfolding add_Suc_right iter_rcomp_Suc_right
        Suc.IH[OF Suc.prems, symmetric]
      unfolding iter_rcomp_Suc_right[symmetric] Suc_eq_plus1
      using Suc.prems.
  qed simp
  then show ?thesis
    unfolding eq iter_comp_com_add_morphism
    by (induction n) presburger+
qed

lemma fp_subst_stable_iter: \<open>is_acyclic \<sigma> \<Longrightarrow> n > 0 \<Longrightarrow> (\<sigma>\<^sup>\<star>)\<^bsup>n\<^esup> = \<sigma>\<^sup>\<star>\<close>
  by (induction n, simp,
    unfold iter_rcomp_Suc_right,
    use fp_subst_comp_stable in fastforce)

lemma fp_subst_stable_fp: \<open>is_acyclic \<sigma> \<Longrightarrow> (\<sigma>\<^sup>\<star>)\<^sup>\<star> = \<sigma>\<^sup>\<star>\<close>
proof -
  assume \<open>is_acyclic \<sigma>\<close>
  define m where \<open>m \<equiv> LEAST n. (\<sigma>\<^sup>\<star>)\<^bsup>n\<^esup> = (\<sigma>\<^sup>\<star>)\<^bsup>n+1\<^esup>\<close>
  show ?thesis
    unfolding fp_subst_def[of \<open>\<sigma>\<^sup>\<star>\<close>, folded m_def]
    using fp_subst_stable_iter[OF \<open>is_acyclic \<sigma>\<close>]
    by (metis (mono_tags, lifting) LeastI_ex Suc_eq_plus1 m_def zero_less_Suc)
qed

end