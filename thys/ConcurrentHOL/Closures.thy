(*<*)
theory Closures
imports
  More_Lattices
begin

(*>*)
section\<open> Closure operators\label{sec:closures} \<close>

text\<open>

Our semantic spaces are modelled as lattices arising from the fixed
points of various closure operators.  We attempt to reduce our proof
obligations by defining a locale for Kuratowski's closure axioms,
where we do not requre strictness (i.e., it need not be the case that
the closure maps \<open>\<bottom>\<close> to
\<open>\<bottom>\<close>).  \<^citet>\<open>\<open>\S2.33\<close> in
"DaveyPriestley:2002"\<close> term these \<^emph>\<open>topped
intersection structures\<close>; see also
\<^citet>\<open>"PfaltzSlapal:2013"\<close> for additional useful
results.

\<close>

locale closure =
  ordering "(\<^bold>\<le>)" "(\<^bold><)" \<comment>\<open> We use a partial order as a preorder does not ensure that the closure is idempotent \<close>
  for less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
     and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 50)
+ fixes cl :: "'a \<Rightarrow> 'a"
  assumes cl: "x \<^bold>\<le> cl y \<longleftrightarrow> cl x \<^bold>\<le> cl y" \<comment>\<open> All-in-one non-strict Kuratowski axiom \<close>
begin

definition closed :: "'a set" where \<comment>\<open> These pre fixed points form a complete lattice ala Tarski/Knaster \<close>
  "closed = {x. cl x \<^bold>\<le> x}"

lemma closed_clI:
  assumes "cl x \<^bold>\<le> x"
  shows "x \<in> closed"
unfolding closed_def using assms by simp

lemma expansive:
  shows "x \<^bold>\<le> cl x"
by (simp add: cl refl)

lemma idempotent[simp]:
  shows "cl (cl x) = cl x"
    and "cl \<circ> cl = cl"
using cl antisym by (auto iff: expansive)

lemma monotone_cl:
  shows "monotone (\<^bold>\<le>) (\<^bold>\<le>) cl"
by (rule monotoneI) (meson cl expansive trans)

lemmas strengthen_cl[strg] = st_monotone[OF monotone_cl]
lemmas mono_cl[trans] = monotoneD[OF monotone_cl]

lemma least:
  assumes "x \<^bold>\<le> y"
  assumes "y \<in> closed"
  shows "cl x \<^bold>\<le> y"
using assms cl closed_def trans by (blast intro: expansive)

lemma least_conv:
  assumes "y \<in> closed"
  shows "cl x \<^bold>\<le> y \<longleftrightarrow> x \<^bold>\<le> y"
using assms expansive least trans by blast

lemma closed[iff]:
  shows "cl x \<in> closed"
unfolding closed_def by (simp add: refl)

lemma le_closedE:
  assumes "x \<^bold>\<le> cl y"
  assumes "y \<in> closed"
  shows "x \<^bold>\<le> y"
using assms closed_def trans by blast

lemma closed_conv: \<comment>\<open> Typically used to manifest the closure using \<open>subst\<close> \<close>
  assumes "X \<in> closed"
  shows "X = cl X"
using assms unfolding closed_def by (blast intro: antisym expansive)

end

lemma (in ordering) closure_axioms_alt_def: \<comment>\<open> Equivalence with the Kuratowski closure axioms \<close>
  shows "closure_axioms (\<^bold>\<le>) cl \<longleftrightarrow> (\<forall>x. x \<^bold>\<le> cl x) \<and> monotone (\<^bold>\<le>) (\<^bold>\<le>) cl \<and> (\<forall>x. cl (cl x) = cl x)"
unfolding closure_axioms_def monotone_def by (metis antisym trans refl)

lemma (in ordering) closureI:
  assumes "\<And>x. x \<^bold>\<le> cl x"
  assumes "monotone (\<^bold>\<le>) (\<^bold>\<le>) cl"
  assumes "\<And>x. cl (cl x) = cl x"
  shows "closure (\<^bold>\<le>) (\<^bold><) cl"
by (blast intro: assms closure.intro[OF ordering_axioms, unfolded closure_axioms_alt_def])

lemma closure_inf_closure:
  fixes cl\<^sub>1 :: "'a::semilattice_inf \<Rightarrow> 'a"
  assumes "closure_axioms (\<le>) cl\<^sub>1"
  assumes "closure_axioms (\<le>) cl\<^sub>2"
  shows "closure_axioms (\<le>) (\<lambda>X. cl\<^sub>1 X \<sqinter> cl\<^sub>2 X)"
using assms unfolding closure_axioms_def by (meson order.trans inf_mono le_inf_iff order_refl)


subsection\<open> Complete lattices and algebraic closures\label{sec:closures-lattices} \<close>

locale closure_complete_lattice =
  complete_lattice "\<^bold>\<Sqinter>" "\<^bold>\<Squnion>" "(\<^bold>\<sqinter>)" "(\<^bold>\<le>)" "(\<^bold><)" "(\<^bold>\<squnion>)" "\<^bold>\<bottom>" "\<^bold>\<top>"
+ closure "(\<^bold>\<le>)" "(\<^bold><)" cl
    for less_eqa :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
    and lessa (infix "\<^bold><" 50)
    and infa (infixl "\<^bold>\<sqinter>" 70)
    and supa (infixl "\<^bold>\<squnion>" 65)
    and bota ("\<^bold>\<bottom>")
    and topa ("\<^bold>\<top>")
    and Inf ("\<^bold>\<Sqinter>")
    and Sup ("\<^bold>\<Squnion>")
    and cl :: "'a \<Rightarrow> 'a"
begin

lemma cl_bot_least:
  shows "cl \<^bold>\<bottom> \<^bold>\<le> cl X"
using cl by auto

lemma cl_Inf_closed:
  shows "cl x = \<^bold>\<Sqinter>{y \<in> closed. x \<^bold>\<le> y}"
by (blast intro: sym[OF Inf_eqI] least expansive)

lemma cl_top:
  shows "cl \<^bold>\<top> = \<^bold>\<top>"
by (simp add: top_le expansive)

lemma closed_top[iff]:
  shows "\<^bold>\<top> \<in> closed"
unfolding closed_def by simp

lemma Sup_cl_le:
  shows "\<^bold>\<Squnion>(cl ` X) \<^bold>\<le> cl (\<^bold>\<Squnion>X)"
by (meson cl expansive SUP_least Sup_le_iff)

lemma sup_cl_le:
  shows "cl x \<^bold>\<squnion> cl y \<^bold>\<le> cl (x \<^bold>\<squnion> y)"
using Sup_cl_le[where X="{x, y}"] by simp

lemma cl_Inf_le:
  shows "cl (\<^bold>\<Sqinter>X) \<^bold>\<le> \<^bold>\<Sqinter>(cl ` X)"
by (meson cl expansive INF_greatest Inf_lower2)

lemma cl_inf_le:
  shows "cl (x \<^bold>\<sqinter> y) \<^bold>\<le> cl x \<^bold>\<sqinter> cl y"
using cl_Inf_le[where X="{x, y}"] by simp

lemma closed_Inf:
  assumes "X \<subseteq> closed"
  shows "\<^bold>\<Sqinter>X \<in> closed"
unfolding closed_def using assms by (simp add: least Inf_greatest Inf_lower subset_eq)

lemmas closed_Inf'[intro] = closed_Inf[OF subsetI]

lemma closed_inf[intro]:
  assumes "P \<in> closed"
  assumes "Q \<in> closed"
  shows "P \<^bold>\<sqinter> Q \<in> closed"
using assms closed_Inf[where X="{P, Q}"] by simp

lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF monotone_cl, simplified]

definition dense :: "'a set" where
  "dense = {x. cl x = \<^bold>\<top>}"

lemma dense_top:
  shows "\<^bold>\<top> \<in> dense"
by (simp add: dense_def cl_top)

lemma dense_Sup:
  assumes "X \<subseteq> dense"
  assumes "X \<noteq> {}"
  shows "\<^bold>\<Squnion>X \<in> dense"
using assms by (fastforce simp: dense_def order.eq_iff intro: order.trans[OF _ Sup_cl_le] elim: SUP_upper2)

lemma dense_sup:
  assumes "P \<in> dense"
  assumes "Q \<in> dense"
  shows "P \<^bold>\<squnion> Q \<in> dense"
using assms dense_def top_le sup_cl_le by auto

lemma dense_le:
  assumes "P \<in> dense"
  assumes "P \<^bold>\<le> Q"
  shows "Q \<in> dense"
using assms dense_def top_le mono_cl by auto

lemma dense_inf_closed:
  shows "dense \<inter> closed = {\<^bold>\<top>}"
using dense_def closed_conv closed_top by fastforce

end

locale closure_complete_lattice_class =
  closure_complete_lattice "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"

text\<open>

Traditionally closures for logical purposes are taken to be ``algebraic'', aka ``consequence operators''
\<^citep>\<open>\<open>Definition~7.12\<close> in "DaveyPriestley:2002"\<close>, where \<^emph>\<open>compactness\<close> does the work
of the finite/singleton sets.

\<close>

locale closure_complete_lattice_algebraic = \<comment>\<open> \<^citet>\<open>\<open>Definition~7.12\<close> in "DaveyPriestley:2002"\<close> \<close>
  closure_complete_lattice
+ assumes algebraic_le: "cl x \<^bold>\<le> \<^bold>\<Squnion>(cl ` ({y. y \<^bold>\<le> x} \<inter> compact_points))" \<comment>\<open> The converse is given by monotonicity \<close>
begin

lemma algebraic:
  shows "cl x = \<^bold>\<Squnion>(cl ` ({y. y \<^bold>\<le> x} \<inter> compact_points))"
by (clarsimp simp: order.eq_iff Sup_le_iff algebraic_le expansive simp flip: cl elim!: order.trans)

lemma cont_cl: \<comment>\<open> Equivalent to @{thm [source] algebraic_le} \<^citet>\<open>\<open>Theorem~7.14\<close> in "DaveyPriestley:2002"\<close> \<close>
  shows "cont \<^bold>\<Squnion> (\<^bold>\<le>) \<^bold>\<Squnion> (\<^bold>\<le>) cl"
proof(rule contI)
  fix X :: "'a set"
  assume X: "Complete_Partial_Order.chain (\<^bold>\<le>) X" "X \<noteq> {}"
  show "cl (\<^bold>\<Squnion>X) = \<^bold>\<Squnion>(cl ` X)" (is "?lhs = ?rhs")
  proof(rule order.antisym[OF _ Sup_cl_le])
    have "?lhs = \<^bold>\<Squnion>(cl ` ({y. y \<^bold>\<le> \<^bold>\<Squnion>X} \<inter> compact_points))" by (subst algebraic) simp
    also from X have "\<dots> \<^bold>\<le> \<^bold>\<Squnion>(cl ` ({Y |Y x. Y \<^bold>\<le> x \<and> x \<in> X} \<inter> compact_points))"
      by (auto dest: chain_directed compact_points_directedD intro: SUP_upper simp: Sup_le_iff)
    also have "\<dots> \<^bold>\<le> ?rhs"
      by (clarsimp simp: Sup_le_iff SUP_upper2 monotoneD[OF monotone_cl])
    finally show "?lhs \<^bold>\<le> ?rhs" .
  qed
qed

lemma mcont_cl:
  shows "mcont \<^bold>\<Squnion> (\<^bold>\<le>) \<^bold>\<Squnion> (\<^bold>\<le>) cl"
by (simp add: mcontI[OF _ cont_cl])

lemma mcont2mcont_cl[cont_intro]:
  assumes "mcont luba orda \<^bold>\<Squnion> (\<^bold>\<le>) P"
  shows "mcont luba orda \<^bold>\<Squnion> (\<^bold>\<le>) (\<lambda>x. cl (P x))"
using assms ccpo.mcont2mcont[OF complete_lattice_ccpo] mcont_cl by blast

end

locale closure_complete_lattice_algebraic_class =
  closure_complete_lattice_algebraic "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"

text\<open>

Our closures often satisfy the stronger condition of \<^emph>\<open>distributivity\<close> (see
\<^citet>\<open>\<open>\S2\<close> in "Scott:1980"\<close>).

\<close>

locale closure_complete_lattice_distributive =
  closure_complete_lattice
+ assumes cl_Sup_le: "cl (\<^bold>\<Squnion>X) \<^bold>\<le> \<^bold>\<Squnion>(cl ` X) \<^bold>\<squnion> cl \<^bold>\<bottom>"
begin

lemma cl_Sup:
  shows "cl (\<^bold>\<Squnion>X) = \<^bold>\<Squnion>(cl ` X) \<^bold>\<squnion> cl \<^bold>\<bottom>"
by (simp add: order.eq_iff Sup_cl_le cl_Sup_le cl_bot_least)

lemma cl_Sup_not_empty:
  assumes "X \<noteq> {}"
  shows "cl (\<^bold>\<Squnion>X) = \<^bold>\<Squnion>(cl ` X)"
by (metis assms cl_Sup cl_bot_least SUP_eq_const SUP_upper2 sup.orderE)

lemma cl_sup:
  shows "cl (X \<^bold>\<squnion> Y) = cl X \<^bold>\<squnion> cl Y"
using cl_Sup[where X="{X, Y}"] by (simp add: sup_absorb1 cl_bot_least le_supI2)

lemma closed_sup[intro]:
  assumes "P \<in> closed"
  assumes "Q \<in> closed"
  shows "P \<^bold>\<squnion> Q \<in> closed"
by (metis assms cl_sup closed_conv closed)

lemma closed_Sup: \<comment>\<open> Alexandrov: \<^url>\<open>https://en.wikipedia.org/wiki/Alexandrov_topology\<close> \<close>
  assumes "X \<subseteq> closed"
  shows "\<^bold>\<Squnion>X \<^bold>\<squnion> cl \<^bold>\<bottom> \<in> closed"
using assms by (fastforce simp: cl_Sup cl_sup Sup_le_iff simp flip: closed_conv intro: closed_clI Sup_upper le_supI1)

lemmas closed_Sup'[intro] = closed_Sup[OF subsetI]

lemma cont_cl:
  shows "cont \<^bold>\<Squnion> (\<^bold>\<le>) \<^bold>\<Squnion> (\<^bold>\<le>) cl"
by (simp add: cl_Sup_not_empty contI)

lemma mcont_cl:
  shows "mcont \<^bold>\<Squnion> (\<^bold>\<le>) \<^bold>\<Squnion> (\<^bold>\<le>) cl"
by (simp add: mcontI[OF _ cont_cl])

lemma mcont2mcont_cl[cont_intro]:
  assumes "mcont luba orda \<^bold>\<Squnion> (\<^bold>\<le>) F"
  shows "mcont luba orda \<^bold>\<Squnion> (\<^bold>\<le>) (\<lambda>x. cl (F x))"
using assms ccpo.mcont2mcont[OF complete_lattice_ccpo] mcont_cl by blast

lemma closure_sup_irreducible_on: \<comment>\<open> converse requires the closure to be T0 \<close>
  assumes "sup_irreducible_on closed (cl x)"
  shows "sup_irreducible_on closed x"
using assms sup_irreducible_on_def closed_conv closed_sup by auto

end

locale closure_complete_lattice_distributive_class =
  closure_complete_lattice_distributive "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"

locale closure_complete_distrib_lattice_distributive_class =
  closure_complete_lattice_distributive "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_distrib_lattice" "\<top>" "Inf" "Sup"
begin

text\<open>

The lattice arising from the closed elements for a distributive closure is completely distributive,
i.e., \<open>Inf\<close> and \<open>Sup\<close> distribute. See \<^citet>\<open>\<open>Section~10.23\<close> in "DaveyPriestley:2002"\<close>.

\<close>

lemma closed_complete_distrib_lattice_axiomI':
  assumes "\<forall>A\<in>A. \<forall>x\<in>A. x \<in> closed"
  shows "(\<Sqinter>X\<in>A. \<Squnion>X \<squnion> cl \<bottom>)
           \<le> \<Squnion>(Inf ` {f ` A |f. (\<forall>X\<subseteq>closed. f X \<in> closed) \<and> (\<forall>Y \<in> A. f Y \<in> Y)}) \<squnion> cl \<bottom>"
proof -
  from assms
  have "\<exists>f'. f ` A = f' ` A \<and> (\<forall>X\<subseteq>closed. f' X \<in> closed) \<and> (\<forall>Y\<in>A. f' Y \<in> Y)"
    if "\<forall>Y\<in>A. f Y \<in> Y" for f
    using that by (fastforce intro!: exI[where x="\<lambda>x. if f x \<in> closed then f x else cl \<bottom>"])
  then show ?thesis
    by (clarsimp simp: Inf_Sup Sup_le_iff simp flip: INF_sup intro!: le_supI1 Sup_upper)
qed

lemma closed_complete_distrib_lattice_axiomI[intro]:
  assumes "\<forall>A\<in>A. \<forall>x\<in>A. x \<in> closed"
  shows "(\<Sqinter>X\<in>A. \<Squnion>X \<squnion> cl \<bottom>)
           \<le> \<Squnion>(Inf ` {B. (\<exists>f. (\<forall>x. (\<forall>x\<in>x. x \<in> closed) \<longrightarrow> f x \<in> closed)
                         \<and> B = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<forall>x\<in>B. x \<in> closed)})
               \<squnion> cl \<bottom>"
by (rule order.trans[OF closed_complete_distrib_lattice_axiomI'[OF assms]])
   (use assms in \<open>clarsimp simp: Sup_le_iff ac_simps\<close>; fast intro!: exI imageI Sup_upper le_supI2)

lemma closed_strict_complete_distrib_lattice_axiomI[intro]:
  assumes "cl \<bottom> = \<bottom>"
  assumes "\<forall>A\<in>A. \<forall>x\<in>A. x \<in> closed"
  shows "(\<Sqinter>X\<in>A. \<Squnion>X)
           \<le> \<Squnion>(Inf ` {x. (\<exists>f. (\<forall>x. (\<forall>x\<in>x. x \<in> closed) \<longrightarrow> f x \<in> closed)
                         \<and> x = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<forall>x\<in>x. x \<in> closed)})"
using closed_complete_distrib_lattice_axiomI[simplified assms(1), simplified, OF assms(2)] .

end


subsection\<open> Closures over powersets\label{sec:closures-powersets} \<close>

locale closure_powerset =
  closure_complete_lattice_class cl for cl :: "'a set \<Rightarrow> 'a set"
begin

lemmas expansive' = subsetD[OF expansive]

lemma closedI[intro]:
  assumes "\<And>x. x \<in> cl X \<Longrightarrow> x \<in> X"
  shows "X \<in> closed"
unfolding closed_def using assms by blast

lemma closedE:
  assumes "x \<in> cl Y"
  assumes "Y \<in> closed"
  shows "x \<in> Y"
using assms closed_def by auto

lemma cl_mono:
  assumes "x \<in> cl X"
  assumes "X \<subseteq> Y"
  shows "x \<in> cl Y"
using assms by (rule subsetD[OF monotoneD[OF monotone_cl], rotated])

lemma cl_bind_le:
  shows "X \<bind> cl \<circ> f \<le> cl (X \<bind> f)"
by (metis bind_UNION bind_image Sup_cl_le)

lemma pointwise_distributive_iff:
  shows "(\<forall>X. cl (\<Union>X) = \<Union>(cl ` X) \<union> cl {}) \<longleftrightarrow> (\<forall>X. cl X = (\<Union>x\<in>X. cl {x}) \<union> cl {})" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs" by (metis UN_singleton image_image)
next
  assume ?rhs
  note distributive = \<open>?rhs\<close>[rule_format]
  have cl_union: "cl (X \<union> Y) = cl X \<union> cl Y" (is "?lhs1 = ?rhs1") for X Y
  proof(rule antisym[OF _ sup_cl_le])
    from cl expansive' show "?lhs1 \<subseteq> ?rhs1" by (subst distributive) auto
  qed
  have cl_insert: "cl (insert x X) = cl {x} \<union> cl X" for x X
    by (metis cl_union insert_is_Un)
  show ?lhs
  proof(intro allI antisym)
    show "cl (\<Union> X) \<subseteq> \<Union> (cl ` X) \<union> cl {}" for X
      by (subst distributive) (clarsimp; metis UnCI cl_insert insert_Diff)
  qed (simp add: cl_bot_least Sup_cl_le)
qed

lemma Sup_prime_on_singleton:
  shows "Sup_prime_on closed (cl {x})"
unfolding Sup_prime_on_def by (meson UnionE expansive' insert_subsetI least bot_least singletonI subsetD)

end

locale closure_powerset_algebraic =
  closure_powerset
+ closure_complete_lattice_algebraic_class

locale closure_powerset_distributive =
  closure_powerset
+ closure_complete_distrib_lattice_distributive_class
begin

lemmas distributive = pointwise_distributive_iff[THEN iffD1, rule_format, OF cl_Sup]

(* don't use \<open>sublocale\<close> as it yields name clashes *)
lemma algebraic_axiom: \<comment>\<open> \<^citet>\<open>\<open>Theorem~7.14\<close> in "DaveyPriestley:2002"\<close> \<close>
  shows "cl x \<subseteq> \<Union> (cl ` ({y. y \<subseteq> x} \<inter> local.compact_points))"
unfolding compact_points_def complete_lattice_class.compact_points_def[symmetric]
by (metis Int_iff algebraic cl_Sup_not_empty complete_lattice_class.compact_pointsI emptyE
          finite.intros(1) mem_Collect_eq order_bot_class.bot_least order.refl)

lemma cl_insert:
  shows "cl (insert x X) = cl {x} \<union> cl X"
by (metis cl_sup insert_is_Un)

lemma cl_UNION:
  shows "cl (\<Union>i\<in>I. f i) = (\<Union>i\<in>I. cl (f i)) \<union> cl {}"
by (auto simp add: cl_Sup SUP_upper)

lemma closed_UNION:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> closed"
  shows "(\<Union>i\<in>I. f i) \<union> cl {} \<in> closed"
using assms closed_def by (auto simp: cl_Sup cl_sup)

lemma sort_of_inverse: \<comment> \<open> \<^citet>\<open>\<open>Proposition~2.5\<close> in "PfaltzSlapal:2013"\<close> \<close>
  assumes "y \<in> cl X - cl {}"
  shows "\<exists>x\<in>X. y \<in> cl {x}"
using assms by (subst (asm) distributive) blast

lemma cl_diff_le:
  shows "cl x - cl y \<subseteq> cl (x - y)"
by (metis Diff_subset_conv Un_Diff_cancel Un_upper2 cl_sup)

lemma cl_bind:
  shows "cl (X \<bind> f) = (X \<bind> cl \<circ> f) \<union> cl {}"
by (simp add: bind_UNION cl_Sup)

lemma sup_irreducible_on_singleton:
  shows "sup_irreducible_on closed (cl {a})"
by (rule sup_irreducible_onI)
   (metis Un_iff sup_bot.right_neutral expansive insert_subset least antisym local.sup.commute sup_ge2)

end


subsection\<open> Matroids and antimatroids\label{sec:closures-matroids} \<close>

text\<open>

The \<^emph>\<open>exchange\<close> axiom characterises \<^emph>\<open>matroids\<close> (see, for instance,
\S\ref{sec:galois-concrete}), while the \<^emph>\<open>anti-exchange\<close> axiom characterises
@{emph \<open>antimatroids\<close>} (see e.g. \S\ref{sec:closures-downwards}).

References:
 \<^item> \<^citet>\<open>"PfaltzSlapal:2013"\<close> provide an overview of these concepts
 \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Antimatroid\<close>

\<close>

definition anti_exchange :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "anti_exchange cl \<longleftrightarrow> (\<forall>X x y. x \<noteq> y \<and> y \<in> cl (insert x X) - cl X \<longrightarrow> x \<notin> cl (insert y X) - cl X)"

definition exchange :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "exchange cl \<longleftrightarrow> (\<forall>X x y. y \<in> cl (insert x X) - cl X \<longrightarrow> x \<in> cl (insert y X) - cl X)"

lemmas anti_exchangeI = iffD2[OF anti_exchange_def, rule_format]
lemmas exchangeI = iffD2[OF exchange_def, rule_format]

lemma anti_exchangeD:
  assumes "y \<in> cl (insert x X) - cl X"
  assumes "x \<noteq> y"
  assumes "anti_exchange cl"
  shows "x \<notin> cl (insert y X) - cl X"
using assms unfolding anti_exchange_def by blast

lemma exchange_Image: \<comment>\<open> Some matroids arise from equivalence relations. Note \<open>sym r \<and> trans r \<longrightarrow> Refl r\<close> \<close>
  shows "exchange (Image r) \<longleftrightarrow> sym r \<and> trans r"
by (auto 6 0 simp: exchange_def sym_def intro!: transI elim: transE)

locale closure_powerset_distributive_exchange =
  closure_powerset_distributive
+ assumes exchange: "exchange cl"
begin

lemma exchange_exchange:
  assumes "x \<in> cl {y}"
  assumes "x \<notin> cl {}"
  shows "y \<in> cl {x}"
using assms exchange unfolding exchange_def by blast

lemma exchange_closed_inter:
  assumes "Q \<in> closed"
  shows "cl P \<inter> Q = cl (P \<inter> Q)" (is "?lhs = ?rhs")
    and "Q \<inter> cl P = cl (P \<inter> Q)" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym)
    have "((\<Union>x\<in>P. cl {x}) \<union> cl {}) \<inter> Q \<subseteq> (\<Union>x\<in>P \<inter> cl Q. cl {x}) \<union> cl {}"
      by clarsimp (metis IntI UnCI cl_insert exchange_exchange mk_disjoint_insert)
    then show "?lhs \<subseteq> ?rhs"
      by (simp flip: distributive closed_conv[OF assms])
    from assms show "?rhs \<subseteq> ?lhs"
      using cl_inf_le closed_conv by blast
  qed
  then show ?thesis1 by blast
qed

lemma exchange_both_closed_inter:
  assumes "P \<in> closed"
  assumes "Q \<in> closed"
  shows "cl (P \<inter> Q) = P \<inter> Q"
using assms closed_conv closed_inf by force

end

lemma anti_exchange_Image: \<comment>\<open> when \<open>r\<close> is asymmetric on distinct points \<close>
  shows "anti_exchange (Image r) \<longleftrightarrow> (\<forall>x y. x \<noteq> y \<and> (x, y) \<in> r \<longrightarrow> (y, x) \<notin> r)"
by (auto simp: anti_exchange_def)

locale closure_powerset_distributive_anti_exchange =
  closure_powerset_distributive
+ assumes anti_exchange: "anti_exchange cl"


subsection\<open> Composition \label{sec:closures-composition} \<close>

text\<open>

Conditions under which composing two closures yields a closure.
See also \<^citet>\<open>"PfaltzSlapal:2013"\<close>.

\<close>

lemma closure_comp:
  assumes "closure lesseqa lessa cl\<^sub>1"
  assumes "closure lesseqa lessa cl\<^sub>2"
  assumes "\<And>X. cl\<^sub>1 (cl\<^sub>2 X) = cl\<^sub>2 (cl\<^sub>1 X)"
  shows "closure lesseqa lessa (\<lambda>X. cl\<^sub>1 (cl\<^sub>2 X))"
using assms by (clarsimp simp: closure_def closure_axioms_def) metis

lemma closure_complete_lattice_comp:
  assumes "closure_complete_lattice Infa Supa infa lesseqa lessa supa bota topa cl\<^sub>1"
  assumes "closure_complete_lattice Infa Supa infa lesseqa lessa supa bota topa cl\<^sub>2"
  assumes "\<And>X. cl\<^sub>1 (cl\<^sub>2 X) = cl\<^sub>2 (cl\<^sub>1 X)"
  shows "closure_complete_lattice Infa Supa infa lesseqa lessa supa bota topa (\<lambda>X. cl\<^sub>1 (cl\<^sub>2 X))"
using assms(1)[unfolded closure_complete_lattice_def]
      closure_comp[OF closure_complete_lattice.axioms(2)[OF assms(1)]
      closure_complete_lattice.axioms(2)[OF assms(2)]]
      assms(3)
by (blast intro: closure_complete_lattice.intro)

lemma closure_powerset_comp:
  assumes "closure_powerset cl\<^sub>1"
  assumes "closure_powerset cl\<^sub>2"
  assumes "\<And>X. cl\<^sub>1 (cl\<^sub>2 X) = cl\<^sub>2 (cl\<^sub>1 X)"
  shows "closure_powerset (\<lambda>X. cl\<^sub>1 (cl\<^sub>2 X))"
using assms by (simp add: closure_complete_lattice_class_def closure_complete_lattice_comp closure_powerset_def)

lemma closure_powerset_distributive_comp:
  assumes "closure_powerset_distributive cl\<^sub>1"
  assumes "closure_powerset_distributive cl\<^sub>2"
  assumes "\<And>X. cl\<^sub>1 (cl\<^sub>2 X) = cl\<^sub>2 (cl\<^sub>1 X)"
  shows "closure_powerset_distributive (\<lambda>X. cl\<^sub>1 (cl\<^sub>2 X))"
proof -
  have "cl\<^sub>1 (cl\<^sub>2 (\<Union> X)) \<subseteq> (\<Union>X\<in>X. cl\<^sub>1 (cl\<^sub>2 X)) \<union> cl\<^sub>1 (cl\<^sub>2 {})" for X
    apply (subst (1 2 3) closure_powerset_distributive.distributive[OF assms(1)])
    apply (subst (1 2 3) closure_powerset_distributive.distributive[OF assms(2)])
    apply fast
    done
  moreover
  from assms have "closure_axioms (\<subseteq>) (\<lambda>X. cl\<^sub>1 (cl\<^sub>2 X))"
    by (metis closure_powerset_distributive_def closure_complete_lattice_class_def closure_def
              closure_powerset.axioms closure_powerset_comp  closure_complete_lattice.axioms(2))
  ultimately show ?thesis
    by (intro_locales; blast intro: closure_complete_lattice_distributive_axioms.intro)
qed


subsection\<open> Path independence \<close>

text\<open>

\<^citet>\<open>\<open>Prop 1.1\<close> in "PfaltzSlapal:2013"\<close>: ``an expansive operator is a closure operator iff it
is path independent.''

References:
 \<^item> \<^verbatim>\<open>$AFP/Stable_Matching/Choice_Functions.thy\<close>

\<close>

context semilattice_sup
begin

definition path_independent :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "path_independent f \<longleftrightarrow> (\<forall>x y. f (x \<squnion> y) = f (f x \<squnion> f y))"

lemma cl_path_independent:
  shows "closure (\<le>) (<) cl \<longleftrightarrow> path_independent cl \<and> (\<forall>x. x \<le> cl x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (auto 5 0 simp: closure_def closure_axioms_def path_independent_def order.eq_iff
                 elim: le_supE)
  show "?rhs \<Longrightarrow> ?lhs"
    by unfold_locales (metis path_independent_def le_sup_iff sup.absorb_iff2 sup.idem)
qed

end


subsection\<open> Some closures \<close>

interpretation id_cl: closure_powerset_distributive id
by standard auto


subsubsection\<open> Reflexive, symmetric and transitive closures \<close>

text\<open>

The reflexive closure \<^const>\<open>reflcl\<close> is very well behaved. Note the new bottom is @{const \<open>Id\<close>}.
The reflexive transitive closure @{const \<open>rtrancl\<close>} and transitive closure @{const \<open>trancl\<close>} are clearly not distributive.

\<^const>\<open>rtrancl\<close> is neither matroidal nor antimatroidal.

\<close>

interpretation reflcl_cl: closure_powerset_distributive_exchange reflcl
by standard (auto simp: exchange_def)

interpretation symcl_cl: closure_powerset_distributive_exchange "\<lambda>X. X \<union> X\<inverse>"
by standard (auto simp: exchange_def)

interpretation trancl_cl: closure_powerset trancl
by standard (metis r_into_trancl' subsetI trancl_id trancl_mono trans_trancl)

interpretation rtrancl_cl: closure_powerset rtrancl
by standard (use rtrancl_subset_rtrancl in blast)

lemma rtrancl_closed_Id:
  shows "Id \<in> rtrancl_cl.closed"
using rtrancl_cl.idempotent rtrancl_empty by fastforce

lemma rtrancl_closed_reflcl_closed:
  shows "rtrancl_cl.closed \<subseteq> reflcl_cl.closed"
using rtrancl_cl.closed_conv by fast


subsubsection\<open> Relation image \<close>

lemma idempotent_Image:
  assumes "refl_on Y r"
  assumes "trans r"
  assumes "X \<subseteq> Y"
  shows "r `` r `` X = r `` X"
using assms by (auto elim: transE intro: refl_onD refl_onD2)

lemmas distributive_Image = Image_eq_UN

lemma closure_powerset_distributive_ImageI:
  assumes "cl = Image r"
  assumes "refl r"
  assumes "trans r"
  shows "closure_powerset_distributive cl"
proof -
  from assms have "closure_axioms (\<subseteq>) cl"
    unfolding order.closure_axioms_alt_def
    by (force simp: idempotent_Image Image_mono monotoneI dest: refl_onD)
  with \<open>cl = Image r\<close> show ?thesis
    by - (intro_locales; auto simp: closure_complete_lattice_distributive_axioms_def)
qed

lemma closure_powerset_distributive_exchange_ImageI:
  assumes "cl = Image r"
  assumes "equiv UNIV r" \<comment>\<open> symmetric, transitive and universal domain \<close>
  shows "closure_powerset_distributive_exchange cl"
using closure_powerset_distributive_ImageI[OF assms(1)] exchange_Image[of r] assms
unfolding closure_powerset_distributive_exchange_def closure_powerset_distributive_exchange_axioms_def
by (metis equivE)

interpretation Image_rtrancl: closure_powerset_distributive "Image (r\<^sup>*)"
by (rule closure_powerset_distributive_ImageI) auto


subsubsection\<open> Kleene closure\label{sec:closures-kleene} \<close>

text\<open>

We define Kleene closure in the traditional way with respect to some
axioms that our various lattices satisfy. As trace models are not
going to validate \<open>x \<bullet> \<bottom> = \<bottom>\<close>
\<^citep>\<open>\<open>Axiom~13\<close> in "Kozen:1994"\<close>, we
cannot reuse existing developments of Kleene Algebra (and Concurrent
Kleene Algebra
\<^citep>\<open>"HoareMoellerStruthWehrman:2011"\<close>). In general
it is not distributive.

\<close>

locale weak_kleene =
  fixes unit :: "'a::complete_lattice" ("\<epsilon>")
  fixes comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<bullet>" 60)
  assumes comp_assoc: "(x \<bullet> y) \<bullet> z = x \<bullet> (y \<bullet> z)"
  assumes weak_comp_unitL: "\<epsilon> \<le> x \<Longrightarrow> \<epsilon> \<bullet> x = x"
  assumes comp_unitR: "x \<bullet> \<epsilon> = x"
  assumes comp_supL: "(x \<squnion> y) \<bullet> z = (x \<bullet> z) \<squnion> (y \<bullet> z)"
  assumes comp_supR: "x \<bullet> (y \<squnion> z) = (x \<bullet> y) \<squnion> (x \<bullet> z)"
  assumes mcont_compL: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>x. x \<bullet> y)"
  assumes mcont_compR: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. x \<bullet> y)"
  assumes comp_botL: "\<bottom> \<bullet> x = \<bottom>"
begin

lemma mcont2mcont_comp:
  assumes "mcont Supa orda Sup (\<le>) f"
  assumes "mcont Supa orda Sup (\<le>) g"
  shows "mcont Supa orda Sup (\<le>) (\<lambda>x. f x \<bullet> g x)"
by (simp add: ccpo.mcont2mcont'[OF complete_lattice_ccpo mcont_compL _ assms(1)]
              ccpo.mcont2mcont'[OF complete_lattice_ccpo mcont_compR _ assms(2)])

lemma mono2mono_comp:
  assumes "monotone orda (\<le>) f"
  assumes "monotone orda (\<le>) g"
  shows "monotone orda (\<le>) (\<lambda>x. f x \<bullet> g x)"
using mcont_mono[OF mcont_compL] mcont_mono[OF mcont_compR] assms
by (clarsimp simp: monotone_def) (meson order.trans)

context
  notes mcont2mcont_comp[cont_intro]
  notes mono2mono_comp[cont_intro, partial_function_mono]
  notes st_monotone[OF mcont_mono[OF mcont_compL], strg]
  notes st_monotone[OF mcont_mono[OF mcont_compR], strg]
begin

context
  notes [[function_internals]] \<comment>\<open> Exposes the induction rules we need \<close>
begin

partial_function (lfp) star :: "'a \<Rightarrow> 'a" where
  "star x = (x \<bullet> star x) \<squnion> \<epsilon>"

partial_function (lfp) rev_star :: "'a \<Rightarrow> 'a" where
  "rev_star x = (rev_star x \<bullet> x) \<squnion> \<epsilon>"

end

lemmas parallel_star_induct_1_1 =
  parallel_fixp_induct_1_1[OF
    complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions
    star.mono star.mono star_def star_def]

lemma star_bot:
  shows "star \<bottom> = \<epsilon>"
by (subst star.simps) (simp add: comp_botL)

lemma epsilon_star_le:
  shows "\<epsilon> \<le> star P"
by (subst star.simps) simp

lemma monotone_star:
  shows "mono star"
proof(rule monotoneI)
  fix x y :: "'a"
  assume "x \<le> y" show "star x \<le> star y"
  proof(induct rule: star.fixp_induct[case_names adm bot step])
    case (step R) show ?case
      apply (strengthen ord_to_strengthen(1)[OF \<open>x \<le> y\<close>])
      apply (strengthen ord_to_strengthen(1)[OF step])
      apply (rule order.refl)
      done
  qed simp_all
qed

lemma expansive_star:
  shows "x \<le> star x"
by (subst star.simps, subst star.simps)
   (simp add: comp_supL comp_supR comp_unitR le_supI1 flip: sup.assoc)

lemma star_comp_star:
  shows "star x \<bullet> star x = star x" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: star.fixp_induct[where P="\<lambda>R. R x \<bullet> star x \<le> star x", case_names adm bot step])
    case (step R) show ?case
      apply (simp add: comp_supL weak_comp_unitL[OF epsilon_star_le] comp_assoc)
      apply (strengthen ord_to_strengthen(1)[OF step])
      apply (subst (2) star.simps)
      apply simp
      done
  qed (simp_all add: comp_botL)
  show "?rhs \<le> ?lhs"
    by (strengthen ord_to_strengthen(2)[OF epsilon_star_le])
       (simp add: weak_comp_unitL[OF epsilon_star_le])
qed

lemma idempotent_star:
  shows "star (star x) = star x" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: star.fixp_induct[where P="\<lambda>R. R (star x) \<le> ?rhs", case_names adm bot step])
  next
    case (step R) then show ?case
      by (metis comp_supR epsilon_star_le le_iff_sup le_sup_iff star_comp_star)
  qed simp_all
  show "?rhs \<le> ?lhs"
    by (simp add: expansive_star)
qed

interpretation star: closure_complete_lattice_class star
by standard (metis order.trans expansive_star idempotent_star monotoneD[OF monotone_star])

lemma star_epsilon:
  shows "star \<epsilon> = \<epsilon>"
by (metis idempotent_star star_bot)

lemma epsilon_rev_star_le:
  shows "\<epsilon> \<le> rev_star P"
by (subst rev_star.simps) simp

lemma rev_star_comp_rev_star:
  shows "rev_star x \<bullet> rev_star x = rev_star x" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: rev_star.fixp_induct[where P="\<lambda>R. rev_star x \<bullet> R x \<le> rev_star x", case_names adm bot step])
    case bot show ?case
      by (subst (2) rev_star.simps) (simp add: le_supI1 mcont_monoD[OF mcont_compR])
  next
    case (step R) then show ?case
      by (simp add: comp_supR epsilon_rev_star_le comp_unitR flip: comp_assoc)
         (metis comp_supL le_iff_sup le_supI1 rev_star.simps)
  qed simp
  show "?rhs \<le> ?lhs"
    by (metis comp_supR comp_unitR epsilon_rev_star_le le_iff_sup)
qed

lemma star_rev_star:
  shows "star = rev_star" (is "?lhs = ?rhs")
proof(intro fun_eqI antisym)
  show "?lhs P \<le> ?rhs P" for P
  proof(induct rule: star.fixp_induct[case_names adm bot step])
    case (step R)
    have expansive: "x \<le> rev_star x" for x
      apply (subst rev_star.simps)
      apply (subst rev_star.simps)
      apply (simp add: comp_supL sup_assoc)
      apply (metis comp_supR comp_unitR sup_ge2 le_supI2 sup_commute weak_comp_unitL)
      done
    show ?case
      by (strengthen ord_to_strengthen(1)[OF step])
         (metis comp_supL epsilon_rev_star_le expansive rev_star_comp_rev_star le_sup_iff sup.absorb_iff2)
  qed simp_all
  show "?rhs P \<le> ?lhs P" for P
  proof(induct rule: rev_star.fixp_induct[case_names adm bot step])
    case (step R) show ?case
      by (strengthen ord_to_strengthen(1)[OF step])
         (metis epsilon_star_le expansive_star mcont_monoD[OF mcont_compR] le_supI star_comp_star)
  qed simp_all
qed

lemmas star_fixp_rev_induct = rev_star.fixp_induct[folded star_rev_star]

interpretation rev_star: closure_complete_lattice_class rev_star
by (rule star.closure_complete_lattice_class_axioms[unfolded star_rev_star])

lemma rev_star_bot:
  shows "rev_star \<bottom> = \<epsilon>"
by (simp add: star_bot flip: star_rev_star)

lemma rev_star_epsilon:
  shows "rev_star \<epsilon> = \<epsilon>"
by (simp add: star_epsilon flip: star_rev_star)

lemmas star_unfoldL = star.simps

lemma star_unfoldR:
  shows "star x = (star x \<bullet> x) \<squnion> \<epsilon>"
by (subst (1 2) star_rev_star) (simp flip: rev_star.simps)

lemmas rev_star_unfoldR = rev_star.simps

lemma rev_star_unfoldL:
  shows "rev_star x = (x \<bullet> rev_star x) \<squnion> \<epsilon>"
by (simp flip: star_rev_star star_unfoldL)

lemma fold_starL:
  shows "x \<bullet> star x \<le> star x"
by (subst (2) star.simps) simp

lemma fold_starR:
  shows "star x \<bullet> x \<le> star x"
by (metis inf_sup_ord(3) star_unfoldR)

lemma fold_rev_starL:
  shows "x \<bullet> rev_star x \<le> rev_star x"
by (simp add: fold_starL flip: star_rev_star)

lemma fold_rev_starR:
  shows "rev_star x \<bullet> x \<le> rev_star x"
by (simp add: fold_starR flip: star_rev_star)

declare star.strengthen_cl[strg] rev_star.strengthen_cl[strg]

end

end

locale kleene = weak_kleene +
  assumes comp_unitL: "\<epsilon> \<bullet> x = x" \<comment>\<open> satisfied by \<open>('a, 's, 'v) prog\<close> but not \<open>('a, 's, 'v) spec\<close> \<close>
(*<*)

end
(*>*)
