theory Footprint_Checks
  imports Consistency
begin

text \<open>Finally, a footprint audit for the consistency result \<open>nk_consistent\<close> --- nothing new is proved here.
  The instances \<open>consistency_bool_params\<close> and \<open>consistency_unit_params\<close> instantiate the alphabet
  of non-logical constants \<open>'p\<close> --- not the individuals \<open>\<iota>\<close>, which the model makes a singleton ---
  with the finite types \<open>bool\<close> and \<open>unit\<close>; they would fail to type-check if the proof required
  \<open>'p :: infinite\<close>, so no infinite alphabet is needed.

  The result is what the introduction calls an @{emph \<open>outright\<close>} consistency proof ---
  relative only to plain Isabelle/HOL itself: the meta-logic certifies the embedded object
  logic --- which carries no axiom of infinity --- by a standard model with finite domains
  at every type, using no Hilbert choice in this construction --- the description operator
  selects its witness by definite description (\<open>THE\<close>), not by choice (\<open>SOME\<close>) --- and no
  set theory.

  One point deserves care.  The type \<^typ>\<open>ival\<close> that hosts the model is infinite ---
  every recursive HOL datatype is.  For the object logic this does not matter: its
  quantifiers range not over the type but over the domains \<open>cD 1 \<sigma>\<close> --- the domain at
  type \<open>\<sigma>\<close> of the size-one instance \<open>k = 1\<close> of the model family built in
  \<open>Consistency\<close> --- and each of these is a finite set.  The domain of individuals even has a single element: the list \<open>en k \<tau>\<close>, which
  enumerates the domain of type \<open>\<tau>\<close>, is here @{term \<open>en 1 \<iota> = [VI 0]\<close>} --- one
  individual, the value \<open>VI 0\<close>.  The model therefore does more than not assert infinity:
  it \<^emph>\<open>refutes\<close> every axiom of infinity.  By definition such an axiom has no finite
  models, so it is false here.  Concretely, a Dedekind-style axiom demands a self-map of
  the individuals that is injective but not surjective; a one-element domain has none,
  since its only self-map is the identity.  Nor can the model keep even two individual
  constants apart.  This is why the consistency proof needs neither an infinite model
  nor a stronger meta-theory.  Note, finally, what kind of statement this is: the
  meta-logic certifies the embedded object logic consistent.  It is not a logic proving
  its own consistency, which G\"odel's second incompleteness theorem forbids.\<close>

theorem consistency_bool_params: "\<not> (\<turnstile> (\<^bold>\<bottom> :: bool tm))"
  by (rule nk_consistent)

theorem consistency_unit_params: "\<not> (\<turnstile> (\<^bold>\<bottom> :: unit tm))"
  by (rule nk_consistent)

end
