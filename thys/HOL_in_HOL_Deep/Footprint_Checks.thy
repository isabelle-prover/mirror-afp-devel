theory Footprint_Checks
  imports Consistency
begin

section \<open>Footprint of the consistency proof\<close>

text \<open>A footprint audit for the consistency result \<open>nk_consistent\<close>; nothing new is proved
  here.  The instances \<open>consistency_bool_params\<close> and \<open>consistency_unit_params\<close> instantiate
  the parameter type \<open>'p\<close> (BKK's typed constants) --- not the individuals \<open>\<iota>\<close>, which the
  model makes a singleton --- with the finite types \<open>bool\<close> and \<open>unit\<close>; they would fail to
  type-check if the proof required \<open>'p :: infinite\<close>, so no infinite supply of parameters is
  needed.

  The result is what the introduction calls an @{emph \<open>outright\<close>} consistency proof, relative
  only to plain Isabelle/HOL: the meta-logic certifies the embedded object logic --- which
  carries no axiom of infinity --- by a standard model with finite domains at every type,
  using no set theory.  The model construction uses no Hilbert choice: its description
  operator selects by definite description (\<open>THE\<close>, locale @{locale lambda_universe} in
  theory \<open>Semantics\<close>).  The soundness proof that the argument relies on uses Isabelle's
  choice operator in one place, to name a canonical assignment (\<open>xi0\<close> in theory
  \<open>Semantics\<close>).

  The type \<^typ>\<open>ival\<close> that hosts the model is infinite, as every recursive HOL datatype is.
  For the object logic this does not matter: its quantifiers range over the domains
  \<open>cD 1 \<sigma>\<close> of the size-one instance \<open>k = 1\<close> of the model family of \<open>Consistency\<close>, and
  each of these is a finite set.  The domain of individuals has a single element:
  @{lemma \<open>en 1 \<iota> = [VI 0]\<close> by (simp add: upt_rec)}.  The model therefore refutes every
  axiom of infinity, which by definition has no finite models; concretely, a Dedekind-style
  axiom demands an injective, non-surjective self-map of the individuals, and a one-element
  domain has none.  Nor can the model keep two individual constants apart.  This is why the
  consistency proof needs neither an infinite model nor a stronger meta-theory.

  Finally, the kind of statement this is.  The meta-logic Isabelle/HOL has an axiom of
  infinity; the object logic has none.  The meta-level infinity is needed only for the
  syntax, and there only in the form of the natural numbers: the term type, the names of free
  variables and the inductively defined set of derivations are infinite, as they must be in
  any meta-theory that speaks about derivations.  The argument itself is finitary ---
  evaluation in a finite model is decidable, and soundness is an induction over derivations
  --- and would go through in primitive recursive arithmetic, which needs no infinite object
  at all (a metatheoretic remark, not formalised).  Inside HOL there seems no lighter route:
  the term type itself exists only by the axiom of infinity, and that axiom states exactly
  that some type is Dedekind-infinite, which is all the natural numbers need.  The datatype
  \<^typ>\<open>ival\<close> that hosts the model is infinite only because every HOL datatype is; its
  domains are finite.  So the consistency proof is carried out in a logic with an axiom of
  infinity, about a logic without one; it is not a logic proving its own consistency.
  G\"odel's second incompleteness theorem does not apply to the object logic: a theory with a
  one-element model interprets no arithmetic.  For many applications this is no restriction: where HOL
  serves as a representation language, as in the LogiKEy embeddings of object logics
  \<^cite>\<open>LogiKEy\<close>, arithmetic at the object level is optional; the introduction's paragraph
  on the two tiers of consistency says which core of the logic in use is the one certified
  here.\<close>

theorem consistency_bool_params: "\<not> (\<turnstile> (\<^bold>\<bottom> :: bool tm))"
  by (rule nk_consistent)

theorem consistency_unit_params: "\<not> (\<turnstile> (\<^bold>\<bottom> :: unit tm))"
  by (rule nk_consistent)

end
