theory MSOinHOL_experiments
  imports
    MSOinHOL_deep
    MSOinHOL_shallow
    MSOinHOL_shallow_minimal
begin

abbreviation "(x::V) \<equiv> 1"
abbreviation "(y::V) \<equiv> 2"
abbreviation "(z::V) \<equiv> 3"
abbreviation "(X::V2) \<equiv> 1"
abbreviation "(Y::V2) \<equiv> 2"

consts P :: R

subsubsection \<open>Propositional tautologies, lifted to MSO in all three embeddings\<close>

lemma "\<Turnstile>\<^sup>d (P\<^sup>d(x,x) \<supset>\<^sup>d P\<^sup>d(x,x))"
  unfolding DefD by simp

lemma "\<Turnstile>\<^sup>s (P\<^sup>s(x,x) \<supset>\<^sup>s P\<^sup>s(x,x))"
  unfolding DefS by simp

lemma "\<Turnstile>\<^sup>m (P\<^sup>m(x,x) \<supset>\<^sup>m P\<^sup>m(x,x))"
  unfolding DefM by simp

lemma "\<Turnstile>\<^sup>d (\<not>\<^sup>d\<not>\<^sup>d P\<^sup>d(x,y)) \<supset>\<^sup>d P\<^sup>d(x,y)"
  unfolding DefD by auto

lemma "\<Turnstile>\<^sup>s (\<not>\<^sup>s\<not>\<^sup>s P\<^sup>s(x,y)) \<supset>\<^sup>s P\<^sup>s(x,y)"
  unfolding DefS by auto

lemma "\<Turnstile>\<^sup>m (\<not>\<^sup>m\<not>\<^sup>m P\<^sup>m(x,y)) \<supset>\<^sup>m P\<^sup>m(x,y)"
  unfolding DefM by auto

subsubsection \<open>First-order tautologies\<close>

text \<open>The individual domain is inhabited whenever some assignment exists.\<close>

lemma "\<Turnstile>\<^sup>d (\<forall>\<^sup>dx. P\<^sup>d(x,x)) \<supset>\<^sup>d (\<exists>\<^sup>dx. P\<^sup>d(x,x))"
  unfolding DefD by auto

lemma "\<Turnstile>\<^sup>s (\<forall>\<^sup>sx. P\<^sup>s(x,x)) \<supset>\<^sup>s (\<exists>\<^sup>sx. P\<^sup>s(x,x))"
  unfolding DefS by auto

lemma "\<Turnstile>\<^sup>m (\<forall>\<^sup>mx. P\<^sup>m(x,x)) \<supset>\<^sup>m (\<exists>\<^sup>mx. P\<^sup>m(x,x))"
  unfolding DefM by auto

subsubsection \<open>Membership tautology\<close>

text \<open>Every individual that is in \<open>X\<close> is in \<open>X\<close>.\<close>

lemma "\<Turnstile>\<^sup>d (\<forall>\<^sup>dx. (X\<^sup>d(x) \<supset>\<^sup>d X\<^sup>d(x)))"
  unfolding DefD by auto

lemma "\<Turnstile>\<^sup>s (\<forall>\<^sup>sx. (X\<^sup>s(x) \<supset>\<^sup>s X\<^sup>s(x)))"
  unfolding DefS by auto

lemma "\<Turnstile>\<^sup>m (\<forall>\<^sup>mx. (X\<^sup>m(x) \<supset>\<^sup>m X\<^sup>m(x)))"
  unfolding DefM by auto

subsubsection \<open>Monadic comprehension\<close>

text \<open>Headline second-order validity: the set of \<open>P\<close>-self-related
  individuals exists.  Stated over the full second-order domain, where
  every monadic set is admissible.\<close>

lemma comprehension_d:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>dx. ((X\<^sup>d(x)) \<longleftrightarrow>\<^sup>d P\<^sup>d(x,x)))"
  unfolding DefD by (intro allI; simp) meson

lemma comprehension_s:
  "\<Turnstile>\<^sup>s' (\<exists>\<^sup>s\<^sub>2X. \<forall>\<^sup>sx. ((X\<^sup>s(x)) \<longleftrightarrow>\<^sup>s P\<^sup>s(x,x)))"
  unfolding DefS by (intro allI; simp) meson

text \<open>A universal monadic set exists over the full domain (the predicate
  that holds everywhere).\<close>

lemma "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>dx. (X\<^sup>d(x)))"
  unfolding DefD by (simp, rule exI[where x="\<lambda>d. True"]) simp

subsubsection \<open>Invalid schemata\<close>

text \<open>\<open>nitpick\<close> reports finite countermodels (using the full-domain
  relation).\<close>

text \<open>Not every monadic set is inhabited: the empty set is a countermodel
  to \<open>\<forall>X. \<exists>x. x \<in> X\<close>.\<close>

lemma "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<exists>\<^sup>dx. (X\<^sup>d(x)))"
  unfolding DefD apply simp nitpick oops

text \<open>Symmetry of \<open>P\<close> is not implied: \<open>nitpick\<close> produces a 2-element
  countermodel.\<close>

lemma "\<Turnstile>\<^sup>d' (\<forall>\<^sup>dx. \<forall>\<^sup>dy. (P\<^sup>d(x,y) \<supset>\<^sup>d P\<^sup>d(y,x)))"
  unfolding DefD apply simp nitpick oops

text \<open>No monadic set can contain and exclude every individual at once:
  \<open>\<exists>X. \<forall>x. x\<in>X \<and> \<not>x\<in>X\<close> is unsatisfiable, hence invalid.\<close>

lemma "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>dx. ((X\<^sup>d(x)) \<and>\<^sup>d \<not>\<^sup>d(X\<^sup>d(x))))"
  unfolding DefD apply simp nitpick oops

end
