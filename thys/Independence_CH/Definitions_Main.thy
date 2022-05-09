section\<open>Main definitions of the development\label{sec:main-definitions}\<close>

theory Definitions_Main
  imports
    Absolute_Versions
begin

text\<open>This theory gathers the main definitions of the Forcing session.

It might be considered as the bare minimum reading requisite to
trust that our development indeed formalizes the theory of
forcing. This should be mathematically clear since this is the
only known method for obtaining proper extensions of ctms while
preserving the ordinals.

The main theorem of this session and all of its relevant definitions
appear in Section~\ref{sec:def-main-forcing}. The reader trusting
all the libraries in which our development is based, might jump
directly there. But in case one wants to dive deeper, the following
sections treat some basic concepts in the ZF logic
(Section~\ref{sec:def-main-ZF})  and in the
ZF-Constructible library (Section~\ref{sec:def-main-relative})
on which our definitions are built.
\<close>

declare [[show_question_marks=false]]

subsection\<open>ZF\label{sec:def-main-ZF}\<close>

text\<open>For the basic logic ZF we restrict ourselves to just a few
concepts.\<close>

thm bij_def[unfolded inj_def surj_def]
text\<open>@{thm [display] bij_def[unfolded inj_def surj_def]}\<close>
(*
  bij(A, B) \<equiv> {f \<in> A \<rightarrow> B . \<forall>w\<in>A. \<forall>x\<in>A. f ` w = f ` x \<longrightarrow> w = x}
               \<inter> {f \<in> A \<rightarrow> B . \<forall>y\<in>B. \<exists>x\<in>A. f ` x = y}
*)

thm eqpoll_def
text\<open>@{thm [display] eqpoll_def}\<close>
(*
  A \<approx> B \<equiv> \<exists>f. f \<in> bij(A, B)
*)

thm Transset_def
text\<open>@{thm [display] Transset_def}\<close>
(*
  Transset(i) \<equiv> \<forall>x\<in>i. x \<subseteq> i
*)

thm Ord_def
text\<open>@{thm [display] Ord_def}\<close>
(*
  Ord(i) \<equiv> Transset(i) \<and> (\<forall>x\<in>i. Transset(x))
*)

thm lt_def le_iff
text\<open>@{thm [display] lt_def le_iff}\<close>
(*
  i < j \<equiv> i \<in> j \<and> Ord(j)
  i \<le> j \<longleftrightarrow> i < j \<or> i = j \<and> Ord(j)
*)

text\<open>With the concepts of empty set and successor in place,\<close>
lemma empty_def': "\<forall>x. x \<notin> 0" by simp
lemma succ_def': "succ(i) = i \<union> {i}" by blast

text\<open>we can define the set of natural numbers \<^term>\<open>\<omega>\<close>. In the
sources, it is  defined as a fixpoint, but here we just write
its characterization as the first limit ordinal.\<close>
thm Limit_nat[unfolded Limit_def] nat_le_Limit[unfolded Limit_def]
text\<open>@{thm [display] Limit_nat[unfolded Limit_def]
 nat_le_Limit[unfolded Limit_def]}\<close>
(*
  Ord(\<omega>) \<and> 0 < \<omega> \<and> (\<forall>y. y < \<omega> \<longrightarrow> succ(y) < \<omega>)
  Ord(i) \<and> 0 < i \<and> (\<forall>y. y < i \<longrightarrow> succ(y) < i) \<Longrightarrow> \<omega> \<le> i
*)

text\<open>Then, addition and predecessor are inductively characterized
as follows:\<close>
thm add_0_right add_succ_right pred_0 pred_succ_eq
text\<open>@{thm [display] add_succ_right add_0_right pred_0 pred_succ_eq}\<close>
(*
  m \<in> \<omega> \<Longrightarrow> m +\<^sub>\<omega> 0 = m
  m +\<^sub>\<omega> succ(n) = succ(m +\<^sub>\<omega> n)

  pred(0) = 0
  pred(succ(y)) = y
*)

text\<open>Lists on a set \<^term>\<open>A\<close> can be characterized by being
recursively generated from the empty list \<^term>\<open>[]\<close> and the
operation \<^term>\<open>Cons\<close> that adds a new element to the left end;
the induction theorem for them shows that the characterization is
“complete”.\<close>

thm Nil Cons list.induct
text\<open>@{thm [display] Nil Cons list.induct }\<close>
(*
  [] \<in> list(A)
  a \<in> A \<Longrightarrow> l \<in> list(A) \<Longrightarrow> Cons(a, l) \<in> list(A)
  x \<in> list(A) \<Longrightarrow> P([]) \<Longrightarrow> (\<And>a l. a \<in> A \<Longrightarrow> l \<in> list(A) \<Longrightarrow> P(l) \<Longrightarrow> P(Cons(a, l))) \<Longrightarrow> P(x)
*)

text\<open>Length, concatenation, and \<^term>\<open>n\<close>th element of lists are
recursively characterized as follows.\<close>
thm length.simps app.simps nth_0 nth_Cons
text\<open>@{thm [display] length.simps app.simps nth_0 nth_Cons}\<close>
(*
  length([]) = 0
  length(Cons(a, l)) = succ(length(l))

  [] @ ys = ys
  Cons(a, l) @ ys = Cons(a, l @ ys)

  nth(0, Cons(a, l)) = a
  n \<in> \<omega> \<Longrightarrow> nth(succ(n), Cons(a, l)) = nth(n, l)
*)
txt\<open>We have the usual Haskell-like notation for iterated applications
of \<^term>\<open>Cons\<close>:\<close>
lemma Cons_app: "[a,b,c] = Cons(a,Cons(b,Cons(c,[])))" ..

txt\<open>Relative quantifiers restrict the range of the bound variable to a
class \<^term>\<open>M\<close> of type \<^typ>\<open>i\<Rightarrow>o\<close>; that is, a truth-valued function with
set arguments.\<close>
lemma "\<forall>x[M]. P(x) \<equiv> \<forall>x. M(x) \<longrightarrow> P(x)"
      "\<exists>x[M]. P(x) \<equiv> \<exists>x. M(x) \<and> P(x)"
  unfolding rall_def rex_def .

txt\<open>Finally, a set can be viewed (“cast”) as a class using the
following function of type \<^typ>\<open>i\<Rightarrow>(i\<Rightarrow>o)\<close>.\<close>
thm setclass_iff
text\<open>@{thm [display] setclass_iff}\<close>
(*
  (##A)(x) \<longleftrightarrow> x \<in> A
*)

subsection\<open>Relative concepts\label{sec:def-main-relative}\<close>
txt\<open>A list of relative concepts (mostly from the ZF-Constructible
    library) follows next.\<close>

thm big_union_def
text\<open>@{thm [display] big_union_def}\<close>
(*
  big_union(M, A, z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>y[M]. y \<in> A \<and> x \<in> y)
*)

thm upair_def
text\<open>@{thm [display] upair_def}\<close>
(*
  upair(M, a, b, z) \<equiv> a \<in> z \<and> b \<in> z \<and> (\<forall>x[M]. x \<in> z \<longrightarrow> x = a \<or> x = b)
*)

thm pair_def
text\<open>@{thm [display] pair_def}\<close>
(*
  pair(M, a, b, z) \<equiv> \<exists>x[M]. upair(M, a, a, x) \<and>
                        (\<exists>y[M]. upair(M, a, b, y) \<and> upair(M, x, y, z))
*)

thm successor_def[unfolded is_cons_def union_def]
text\<open>@{thm [display] successor_def[unfolded is_cons_def union_def]}\<close>
(*
  successor(M, a, z) \<equiv> \<exists>x[M]. upair(M, a, a, x) \<and> (\<forall>xa[M]. xa \<in> z \<longleftrightarrow> xa \<in> x \<or> xa \<in> a)
*)

thm empty_def
text\<open>@{thm [display] empty_def}\<close>
(*
  empty(M, z) \<equiv> \<forall>x[M]. x \<notin> z
*)

thm transitive_set_def[unfolded subset_def]
text\<open>@{thm [display] transitive_set_def[unfolded subset_def]}\<close>
(*
  transitive_set(M, a) \<equiv> \<forall>x[M]. x \<in> a \<longrightarrow> (\<forall>xa[M]. xa \<in> x \<longrightarrow> xa \<in> a)
*)


thm ordinal_def
text\<open>@{thm [display] ordinal_def}\<close>
(*
  ordinal(M, a) \<equiv> transitive_set(M, a) \<and> (\<forall>x[M]. x \<in> a \<longrightarrow>
                                              transitive_set(M, x))
*)

thm image_def
text\<open>@{thm [display] image_def}\<close>
(*
  image(M, r, A, z) \<equiv> \<forall>y[M]. y \<in> z \<longleftrightarrow>
                (\<exists>w[M]. w \<in> r \<and> (\<exists>x[M]. x \<in> A \<and> pair(M, x, y, w)))
*)

thm fun_apply_def
text\<open>@{thm [display] fun_apply_def}\<close>
(*
  fun_apply(M, f, x, y) \<equiv> \<exists>xs[M]. \<exists>fxs[M]. upair(M, x, x, xs) \<and>
                       image(M, f, xs, fxs) \<and> big_union(M, fxs, y)
*)

thm is_function_def
text\<open>@{thm [display] is_function_def}\<close>
(*
  is_function(M, r) \<equiv> \<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M].
       pair(M, x, y, p) \<longrightarrow> pair(M, x, y', p') \<longrightarrow> p \<in> r \<longrightarrow> p' \<in> r \<longrightarrow> y = y'
*)

thm is_relation_def
text\<open>@{thm [display] is_relation_def}\<close>
(*
  is_relation(M, r) \<equiv> \<forall>z[M]. z \<in> r \<longrightarrow> (\<exists>x[M]. \<exists>y[M]. pair(M, x, y, z))
*)

thm is_domain_def
text\<open>@{thm [display] is_domain_def}\<close>
(*
  is_domain(M, r, z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow>
                        (\<exists>w[M]. w \<in> r \<and> (\<exists>y[M]. pair(M, x, y, w)))
*)

thm typed_function_def
text\<open>@{thm [display] typed_function_def}\<close>
(*
  typed_function(M, A, B, r) \<equiv> is_function(M, r) \<and> is_relation(M, r) \<and>
                                is_domain(M, r, A) \<and>
            (\<forall>u[M]. u \<in> r \<longrightarrow> (\<forall>x[M]. \<forall>y[M]. pair(M, x, y, u) \<longrightarrow> y \<in> B))
*)

thm is_function_space_def[unfolded is_funspace_def]
  function_space_rel_def surjection_def
text\<open>@{thm [display] is_function_space_def[unfolded is_funspace_def]
  function_space_rel_def surjection_def}\<close>
(*
  is_function_space(M, A, B, fs) \<equiv>
  M(fs) \<and> (\<forall>f[M]. f \<in> fs \<longleftrightarrow> typed_function(M, A, B, f))

  A \<rightarrow>\<^bsup>M\<^esup> B \<equiv> THE d. is_function_space(M, A, B, d)

  surjection(M, A, B, f) \<equiv>
  typed_function(M, A, B, f) \<and>
  (\<forall>y[M]. y \<in> B \<longrightarrow> (\<exists>x[M]. x \<in> A \<and> is_apply(M, f, x, y)))
*)


txt\<open>Relative version of the $\ZFC$ axioms\<close>
thm extensionality_def
text\<open>@{thm [display] extensionality_def}\<close>
(*
  extensionality(M) \<equiv> \<forall>x[M]. \<forall>y[M]. (\<forall>z[M]. z \<in> x \<longleftrightarrow> z \<in> y) \<longrightarrow> x = y
*)

thm foundation_ax_def
text\<open>@{thm [display] foundation_ax_def}\<close>
(*
  foundation_ax(M) \<equiv> \<forall>x[M]. (\<exists>y[M]. y \<in> x) \<longrightarrow> (\<exists>y[M]. y \<in> x \<and> \<not> (\<exists>z[M]. z \<in> x \<and> z \<in> y))
*)

thm upair_ax_def
text\<open>@{thm [display] upair_ax_def}\<close>
(*
  upair_ax(M) \<equiv> \<forall>x[M]. \<forall>y[M]. \<exists>z[M]. upair(M, x, y, z)
*)

thm Union_ax_def
text\<open>@{thm [display] Union_ax_def}\<close>
(*
  Union_ax(M) \<equiv> \<forall>x[M]. \<exists>z[M]. \<forall>xa[M]. xa \<in> z \<longleftrightarrow> (\<exists>y[M]. y \<in> x \<and> xa \<in> y)
*)

thm power_ax_def[unfolded powerset_def subset_def]
text\<open>@{thm [display] power_ax_def[unfolded powerset_def subset_def]}\<close>
(*
  power_ax(M) \<equiv> \<forall>x[M]. \<exists>z[M]. \<forall>xa[M]. xa \<in> z \<longleftrightarrow> (\<forall>xb[M]. xb \<in> xa \<longrightarrow> xb \<in> x)
*)

thm infinity_ax_def
text\<open>@{thm [display] infinity_ax_def}\<close>
(*
  infinity_ax(M) \<equiv> \<exists>I[M]. (\<exists>z[M]. empty(M, z) \<and> z \<in> I) \<and> (\<forall>y[M]. y \<in> I \<longrightarrow>
                        (\<exists>sy[M]. successor(M, y, sy) \<and> sy \<in> I))
*)

thm choice_ax_def
text\<open>@{thm [display] choice_ax_def}\<close>
(*
  choice_ax(M) \<equiv> \<forall>x[M]. \<exists>a[M]. \<exists>f[M]. ordinal(M, a) \<and> surjection(M, a, x, f)
*)

thm separation_def
text\<open>@{thm [display] separation_def}\<close>
(*
  separation(M, P) \<equiv> \<forall>z[M]. \<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x)
*)

thm univalent_def
text\<open>@{thm [display] univalent_def}\<close>
(*
  univalent(M, A, P) \<equiv> \<forall>x[M]. x \<in> A \<longrightarrow>
                          (\<forall>y[M]. \<forall>z[M]. P(x, y) \<and> P(x, z) \<longrightarrow> y = z)
*)

thm strong_replacement_def
text\<open>@{thm [display] strong_replacement_def}\<close>
(*
  strong_replacement(M, P) \<equiv> \<forall>A[M]. univalent(M, A, P) \<longrightarrow>
       (\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x, b)))
*)

text\<open>Internalized formulas\<close>

txt\<open>“Codes” for formulas (as sets) are constructed from natural
numbers using \<^term>\<open>Member\<close>, \<^term>\<open>Equal\<close>, \<^term>\<open>Nand\<close>,
and \<^term>\<open>Forall\<close>.\<close>

thm Member Equal Nand Forall formula.induct
text\<open>@{thm [display] Member Equal Nand Forall formula.induct}\<close>
(*
  x \<in> \<omega> \<Longrightarrow> y \<in> \<omega> \<Longrightarrow> \<cdot>x \<in> y\<cdot> \<in> formula
  x \<in> \<omega> \<Longrightarrow> y \<in> \<omega> \<Longrightarrow> \<cdot>x = y\<cdot> \<in> formula
  p \<in> formula \<Longrightarrow> q \<in> formula \<Longrightarrow> \<cdot>\<not>(p \<and> q)\<cdot> \<in> formula
  p \<in> formula \<Longrightarrow> (\<forall>p) \<in> formula

  x \<in> formula \<Longrightarrow>
  (\<And>x y. x \<in> \<omega> \<Longrightarrow> y \<in> \<omega> \<Longrightarrow> P(\<cdot>x \<in> y\<cdot>)) \<Longrightarrow>
  (\<And>x y. x \<in> \<omega> \<Longrightarrow> y \<in> \<omega> \<Longrightarrow> P(\<cdot>x = y\<cdot>)) \<Longrightarrow>
  (\<And>p q. p \<in> formula \<Longrightarrow> P(p) \<Longrightarrow> q \<in> formula \<Longrightarrow> P(q) \<Longrightarrow> P(\<cdot>\<not>(p \<and> q)\<cdot>)) \<Longrightarrow>
  (\<And>p. p \<in> formula \<Longrightarrow> P(p) \<Longrightarrow> P((\<forall>p))) \<Longrightarrow> P(x)
*)

txt\<open>Definitions for the other connectives and the internal existential
quantifier are also provided. For instance, negation:\<close>
thm Neg_def
text\<open>@{thm [display] Neg_def}\<close>

thm arity.simps
text\<open>@{thm [display] arity.simps}\<close>
(*
  arity(\<cdot>x \<in> y\<cdot>) = succ(x) \<union> succ(y)
  arity(\<cdot>x = y\<cdot>) = succ(x) \<union> succ(y)
  arity(\<cdot>\<not>(p \<and> q)\<cdot>) = arity(p) \<union> arity(q)
  arity((\<forall>p)) = pred(arity(p))
*)

txt\<open>We have the satisfaction relation between $\in$-models and
    first order formulas (given a “environment” list representing
    the assignment of free variables),\<close>
thm mem_iff_sats equal_iff_sats sats_Nand_iff sats_Forall_iff
text\<open>@{thm [display] mem_iff_sats equal_iff_sats sats_Nand_iff sats_Forall_iff}\<close>
(*
  nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> env \<in> list(A) \<Longrightarrow> x \<in> y \<longleftrightarrow> A, env \<Turnstile> \<cdot>i \<in> j\<cdot>
  nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> env \<in> list(A) \<Longrightarrow> x = y \<longleftrightarrow> A, env \<Turnstile> \<cdot>i = j\<cdot>
  env \<in> list(A) \<Longrightarrow> (A, env \<Turnstile> \<cdot>\<not>(p \<and> q)\<cdot>) \<longleftrightarrow> \<not> ((A, env \<Turnstile> p) \<and> (A, env \<Turnstile> q))
  env \<in> list(A) \<Longrightarrow> (A, env \<Turnstile> (\<cdot>\<forall>p\<cdot>)) \<longleftrightarrow> (\<forall>x\<in>A. A, Cons(x, env) \<Turnstile> p)*)

txt\<open>as well as the satisfaction of an arbitrary set of sentences.\<close>
thm satT_def
text\<open>@{thm [display] satT_def}\<close>
(*
  A \<Turnstile> \<Phi>  \<equiv>  \<forall>\<phi>\<in>\<Phi>. A, [] \<Turnstile> \<phi>
*)

txt\<open>The internalized (viz. as elements of the set \<^term>\<open>formula\<close>)
    version of the axioms follow next.\<close>

thm ZF_union_iff_sats ZF_power_iff_sats ZF_pairing_iff_sats
  ZF_foundation_iff_sats ZF_extensionality_iff_sats
  ZF_infinity_iff_sats sats_ZF_separation_fm_iff
  sats_ZF_replacement_fm_iff ZF_choice_iff_sats
text\<open>@{thm [display] ZF_union_iff_sats ZF_power_iff_sats
  ZF_pairing_iff_sats
  ZF_foundation_iff_sats ZF_extensionality_iff_sats
  ZF_infinity_iff_sats sats_ZF_separation_fm_iff
  sats_ZF_replacement_fm_iff ZF_choice_iff_sats}\<close>
(*
  Union_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>Union Ax\<cdot>
  power_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>Powerset Ax\<cdot>
  upair_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>Pairing\<cdot>
  foundation_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>Foundation\<cdot>
  extensionality(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>Extensionality\<cdot>
  infinity_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>Infinity\<cdot>

  \<phi> \<in> formula \<Longrightarrow>
  (M, [] \<Turnstile> \<cdot>Separation(\<phi>)\<cdot>) \<longleftrightarrow>
  (\<forall>env\<in>list(M).
      arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env) \<longrightarrow> separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>))

  \<phi> \<in> formula \<Longrightarrow>
  (M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>) \<longleftrightarrow>
  (\<forall>env\<in>list(M).
      arity(\<phi>) \<le> 2 +\<^sub>\<omega> length(env) \<longrightarrow>
      strong_replacement(##M, \<lambda>x y. M, [x, y] @ env \<Turnstile> \<phi>))

  choice_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> \<cdot>AC\<cdot>
*)

thm ZF_fin_def ZF_schemes_def Zermelo_fms_def ZC_def ZF_def ZFC_def
text\<open>@{thm [display] ZF_fin_def ZF_schemes_def Zermelo_fms_def ZC_def ZF_def
  ZFC_def}\<close>
(*
  ZF_fin \<equiv> {\<cdot>Extensionality\<cdot>, \<cdot>Foundation\<cdot>, \<cdot>Pairing\<cdot>, \<cdot>Union Ax\<cdot>, \<cdot>Infinity\<cdot>, \<cdot>Powerset Ax\<cdot>}
  ZF_schemes \<equiv> {\<cdot>Separation(p)\<cdot> . p \<in> formula} \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> formula}
  \<cdot>Z\<cdot> \<equiv> ZF_fin \<union> {\<cdot>Separation(p)\<cdot> . p \<in> formula}
  ZC \<equiv> \<cdot>Z\<cdot> \<union> {\<cdot>AC\<cdot>}
  ZF \<equiv> ZF_schemes \<union> ZF_fin
  ZFC \<equiv> ZF \<union> {\<cdot>AC\<cdot>}
*)

subsection\<open>Relativization of infinitary arithmetic\<close>

txt\<open>In order to state the defining property of the relative
    equipotence relation, we work under the assumptions of the
    locale \<^term>\<open>M_cardinals\<close>. They comprise a finite set
    of instances of Separation and Replacement to prove
    closure properties of the transitive class \<^term>\<open>M\<close>.\<close>

lemma (in M_cardinals) eqpoll_def':
  assumes "M(A)" "M(B)" shows "A \<approx>\<^bsup>M\<^esup> B \<longleftrightarrow> (\<exists>f[M]. f \<in> bij(A,B))"
  using assms unfolding eqpoll_rel_def by auto

txt\<open>Below, $\mu$ denotes the minimum operator on the ordinals.\<close>
lemma cardinalities_defs:
  fixes M::"i\<Rightarrow>o"
  shows
    "|A|\<^bsup>M\<^esup> \<equiv> \<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"
    "Card\<^bsup>M\<^esup>(\<alpha>) \<equiv> \<alpha> = |\<alpha>|\<^bsup>M\<^esup>"
    "\<kappa>\<^bsup>\<up>\<nu>,M\<^esup> \<equiv> |\<nu> \<rightarrow>\<^bsup>M\<^esup> \<kappa>|\<^bsup>M\<^esup>"
    "(\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<equiv> \<mu> x. M(x) \<and> Card\<^bsup>M\<^esup>(x) \<and> \<kappa> < x"
  unfolding cardinal_rel_def cexp_rel_def
    csucc_rel_def Card_rel_def .

context M_aleph
begin

txt\<open>As in the previous Lemma @{thm [source] eqpoll_def'}, we are now under
    the assumptions of the locale \<^term>\<open>M_aleph\<close>. The axiom instances
    included are sufficient to state and prove the defining
    properties of the relativized \<^term>\<open>Aleph\<close> function
    (in particular, the required ability to perform transfinite recursions).\<close>

thm Aleph_rel_zero Aleph_rel_succ Aleph_rel_limit
text\<open>@{thm [display] Aleph_rel_zero Aleph_rel_succ Aleph_rel_limit}\<close>
(*
  \<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup> = \<omega>
  Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> = (\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>
  Limit(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> = (\<Union>j\<in>\<alpha>. \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>)
*)

end \<comment> \<open>\<^locale>\<open>M_aleph\<close>\<close>

lemma ContHyp_rel_def':
  fixes N::"i\<Rightarrow>o"
  shows
    "CH\<^bsup>N\<^esup> \<equiv> \<aleph>\<^bsub>1\<^esub>\<^bsup>N\<^esup> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>N\<^esup>,N\<^esup>"
  unfolding ContHyp_rel_def .

txt\<open>Under appropriate hypothesis (this time, from the locale \<^term>\<open>M_master\<close>),
   \<^term>\<open>CH\<^bsup>M\<^esup>\<close> is equivalent to its fully relational version \<^term>\<open>is_ContHyp\<close>.
    As a sanity check, we see that if the transitive class is indeed \<^term>\<open>\<V>\<close>,
    we recover the original $\CH$.\<close>

thm M_master.is_ContHyp_iff is_ContHyp_iff_CH[unfolded ContHyp_def]
text\<open>@{thm [display] M_master.is_ContHyp_iff
    is_ContHyp_iff_CH[unfolded ContHyp_def]}\<close>
(*
  M_master(M) \<Longrightarrow> is_ContHyp(M) \<longleftrightarrow> CH\<^bsup>M\<^esup>
  is_ContHyp(\<V>) \<longleftrightarrow> \<aleph>\<^bsub>1\<^esub> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^esup>
*)

txt\<open>In turn, the fully relational version evaluated on a nonempty
    transitive \<^term>\<open>A\<close> is equivalent to the satisfaction of the
    first-order formula \<^term>\<open>\<cdot>CH\<cdot>\<close>.\<close>
thm is_ContHyp_iff_sats
text\<open>@{thm [display] is_ContHyp_iff_sats}\<close>
(*
  env \<in> list(A) \<Longrightarrow> 0 \<in> A \<Longrightarrow> is_ContHyp(##A) \<longleftrightarrow> A, env \<Turnstile> \<cdot>CH\<cdot>
*)


subsection\<open>Forcing \label{sec:def-main-forcing}\<close>

txt\<open>Our first milestone was to obtain a proper extension using forcing.
It's original proof didn't required the previous developments involving
the relativization of material on cardinal arithmetic. Now it is
derived from a stronger result, namely @{thm [source] extensions_of_ctms}
below.\<close>

thm extensions_of_ctms_ZF
text\<open>@{thm [display] extensions_of_ctms_ZF}\<close>
(*
  M \<approx> \<omega> \<Longrightarrow>
  Transset(M) \<Longrightarrow>
  M \<Turnstile> ZF \<Longrightarrow>
  \<exists>N. M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZF \<and> M \<noteq> N \<and>
    (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N) \<and> ((M, [] \<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N \<Turnstile> ZFC)
*)

txt\<open>We can finally state our main results, namely, the existence of models
for $\ZFC + \CH$ and $\ZFC + \neg\CH$ under the assumption of a ctm of $\ZFC$.\<close>

thm ctm_ZFC_imp_ctm_not_CH
text\<open>@{thm [display] ctm_ZFC_imp_ctm_not_CH}\<close>
(*
  M \<approx> \<omega> \<Longrightarrow>
  Transset(M) \<Longrightarrow>
  M \<Turnstile> ZFC \<Longrightarrow>
  \<exists>N. M \<subseteq> N \<and>
    N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZFC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>} \<and>
    (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)
*)

thm ctm_ZFC_imp_ctm_CH
text\<open>@{thm [display] ctm_ZFC_imp_ctm_CH}\<close>
(*
  M \<approx> \<omega> \<Longrightarrow>
  Transset(M) \<Longrightarrow>
  M \<Turnstile> ZFC \<Longrightarrow>
  \<exists>N. M \<subseteq> N \<and>
      N \<approx> \<omega> \<and>
      Transset(N) \<and> N \<Turnstile> ZFC \<union> {\<cdot>CH\<cdot>} \<and> (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)
*)

txt\<open>These results can be strengthened by enumerating four finite sets of
replacement instances which are sufficient to develop forcing and for
the construction of the aforementioned models: \<^term>\<open>instances1_fms\<close>
through \<^term>\<open>instances4_fms\<close>, which are then collected into
\<^term>\<open>overhead\<close>. For example, we have:\<close>

thm instances1_fms_def
text\<open>@{thm [display] instances1_fms_def}\<close>
(*
instances1_fms \<equiv>
{ wfrec_Hfrc_at_fm, list_repl1_intf_fm, list_repl2_intf_fm,
 formula_repl2_intf_fm, eclose_repl2_intf_fm, powapply_repl_fm,
 phrank_repl_fm, wfrec_rank_fm, trans_repl_HVFrom_fm, wfrec_Hcheck_fm,
 repl_PHcheck_fm, check_replacement_fm, G_dot_in_M_fm, repl_opname_check_fm,
 tl_repl_intf_fm, formula_repl1_intf_fm, eclose_repl1_intf_fm }
*)

thm overhead_def
text\<open>@{thm [display] overhead_def}\<close>
(*
overhead \<equiv> instances1_fms \<union> instances2_fms \<union> instances3_fms \<union> instances4_fms
*)

thm extensions_of_ctms
text\<open>@{thm [display] extensions_of_ctms}\<close>
(*
M \<approx> \<omega> \<Longrightarrow>
Transset(M) \<Longrightarrow>
M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms} \<Longrightarrow>
\<Phi> \<subseteq> formula \<Longrightarrow>
M \<Turnstile> {\<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>} \<Longrightarrow>
\<exists>N. M \<subseteq> N \<and>
    N \<approx> \<omega> \<and>
    Transset(N) \<and>
    M \<noteq> N \<and>
    (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N) \<and>
    ((M, [] \<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N, [] \<Turnstile> \<cdot>AC\<cdot>) \<and>
    N \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>}
*)

thm ctm_of_not_CH
text\<open>@{thm [display] ctm_of_not_CH}\<close>
(*
M \<approx> \<omega> \<Longrightarrow>
Transset(M) \<Longrightarrow>
M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead} \<Longrightarrow>
\<Phi> \<subseteq> formula \<Longrightarrow>
M \<Turnstile> {\<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>} \<Longrightarrow>
\<exists>N. M \<subseteq> N \<and>
    N \<approx> \<omega> \<and>
    Transset(N) \<and>
    N \<Turnstile> ZC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>} \<union> {\<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>} \<and>
    (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)*)

thm ctm_of_CH
text\<open>@{thm [display] ctm_of_CH}\<close>
(*
M \<approx> \<omega> \<Longrightarrow>
Transset(M) \<Longrightarrow>
M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead} \<Longrightarrow>
\<Phi> \<subseteq> formula \<Longrightarrow>
M \<Turnstile> {\<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>} \<Longrightarrow>
\<exists>N. M \<subseteq> N \<and>
    N \<approx> \<omega> \<and>
    Transset(N) \<and>
    N \<Turnstile> ZC \<union> {\<cdot>CH\<cdot>} \<union> {\<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>} \<and>
    (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)
*)

txt\<open>In the above three statements, the function \<^term>\<open>ground_repl_fm\<close>
takes an element \<^term>\<open>\<phi>\<close>of \<^term>\<open>formula\<close> and returns the
replacement instance in the ground model that produces the
\<^term>\<open>\<phi>\<close>-replacement instance in the generic extension. The next
result is stated in the context \<^locale>\<open>G_generic1\<close>, which assumes
the existence of a generic filter.\<close>

context G_generic1
begin

thm sats_ground_repl_fm_imp_sats_ZF_replacement_fm
text\<open>@{thm [display] sats_ground_repl_fm_imp_sats_ZF_replacement_fm}\<close>
(*
\<phi> \<in> formula \<Longrightarrow> M, [] \<Turnstile> \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> \<Longrightarrow> M[G], [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>
*)

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end