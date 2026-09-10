theory Main_Results
  imports Completeness Cantor NK_Infinity
begin

section \<open>Main results\<close>

text \<open>The central results of this entry, restated in one place.  Soundness
  and completeness of \<open>NK\<close> for the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (BKK Theorem 7.3 and a
  strengthening of BKK Corollary 7.7): for well-formed (open) formulas over
  every signature with infinitely many parameters \<open>'p\<close>, derivability coincides
  with validity at @{emph \<open>every\<close>} infinite value carrier \<open>'u\<close> --- no cardinality
  link between the parameter type \<open>'p\<close> and the carrier \<open>'u\<close> is needed.  Consistency holds
  for arbitrary signatures, by the concrete standard model --- note the asymmetry:
  consistency needs @{emph \<open>no\<close>} constraint on \<open>'p\<close> at all, whereas completeness
  requires \<open>'p\<close> infinite, since the rule \<open>NK(\<Pi>I)\<close> consumes fresh
  eigen-parameters.  Cantor's theorem, surjective and injective, is derived inside \<open>NK\<close>
  at every type.\<close>

text \<open>Completeness comes without hypotheses (\<open>NK_completeness\<close>) and relative to hypotheses.
  For the latter the primary relation is \<open>\<Phi> \<tturnstile> A\<close> --- some finite part of \<open>\<Phi>\<close> derives
  \<open>A\<close> (theory \<open>Calculus\<close>) --- which is monotone and of finite character by construction
  and coincides with \<open>\<Phi> \<turnstile> A\<close> whenever the context leaves enough parameters unused.  For
  \<open>\<tturnstile>\<close>, completeness holds with @{emph \<open>no\<close>} condition on the context beyond
  well-formedness: any set of @{emph \<open>open\<close>} formulas --- context and conclusion may
  together carry infinitely many free variables --- at any signature, over any carrier at
  least as large as the signature (\<open>NK_completeness_hyps\<close>); the instance for a closed
  context and conclusion over a countable signature is BKK Corollary 7.7 proper.  At the
  level of the calculus \<open>\<turnstile>\<close> itself --- deriving from the @{emph \<open>whole\<close>} context rather
  than from a finite part --- a proviso on the context is needed, since an impure infinite
  context can exhaust the eigen-parameters of \<open>NK(\<Pi>I)\<close>; that family of theorems lives in
  theory \<open>Completeness\<close> (\<open>completeness_hyps_open_full\<close>, \<open>completeness_hyps_open_rich\<close>).
  Restated here is only its @{emph \<open>finite\<close>}-context form, which needs no side condition
  at all (\<open>NK_completeness_hyps_fin\<close>), as unrestricted as \<open>NK_completeness\<close> itself.\<close>

theorem NK_soundness:
  "\<Phi> \<turnstile> C \<Longrightarrow> \<Phi> \<Turnstile>('u) C"
  by (rule soundness_sat)

theorem NK_completeness:
  assumes "wff\<^bsub>\<o>\<^esub>(A::'p::infinite tm)" and "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
  by (rule completeness_at_any_signature[OF assms])

text \<open>Derivability from hypotheses, in final form.  The premise \<open>inj emb\<close> --- the carrier
  is at least as large as the signature --- is necessary (closing remark of theory
  \<open>Completeness\<close>); nothing else is assumed about the context.  Semantic compactness of
  the Henkin consequence falls out as a corollary: consequence at one sufficiently large
  carrier reduces to a finite sub-context, which by soundness is good at @{emph \<open>every\<close>}
  carrier \<open>'v\<close> --- no ultraproducts are involved.\<close>

theorem NK_soundness_hyps: "\<Phi> \<tturnstile> C \<Longrightarrow> \<Phi> \<Turnstile>('u) C"
  by (rule soundness_fprov)

theorem NK_completeness_hyps:
  fixes \<Phi> :: "'p::infinite tm set" and emb :: "'p \<Rightarrow> 'u"
  assumes "inj emb" and "wff\<^bsub>\<o>\<^esub>(A)" and "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and "\<Phi> \<Turnstile>('u) A"
  shows "\<Phi> \<tturnstile> A"
  by (rule completeness_fprov[OF assms])

theorem sound_and_complete_hyps:
  fixes \<Phi> :: "'p::infinite tm set" and emb :: "'p \<Rightarrow> 'u"
  assumes emb: "inj emb" and A: "wff\<^bsub>\<o>\<^esub>(A)" and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
  shows "\<Phi> \<tturnstile> A \<longleftrightarrow> \<Phi> \<Turnstile>('u) A"
  using NK_completeness_hyps[OF emb A w\<Phi>] NK_soundness_hyps by blast

corollary NK_consequence_compact:
  fixes \<Phi> :: "'p::infinite tm set" and emb :: "'p \<Rightarrow> 'u"
  assumes "inj emb" and "wff\<^bsub>\<o>\<^esub>(A)" and "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and "\<Phi> \<Turnstile>('u) A"
  shows "\<exists>\<Phi>\<^sub>0. finite \<Phi>\<^sub>0 \<and> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<and> \<Phi>\<^sub>0 \<Turnstile>('v) A"
  using NK_completeness_hyps[OF assms] soundness_sat by (auto simp: fprov_def)

text \<open>For a \<^emph>\<open>finite\<close> context nothing beyond well-formedness is required: free variables
  may occur in the hypotheses \<^emph>\<open>and\<close> in the conclusion, and neither purity nor
  countability of \<open>'p\<close> is assumed.  The hypotheses are discharged into implications.\<close>

theorem NK_completeness_hyps_fin:
  fixes \<Phi> :: "'p::infinite tm set"
  assumes "finite \<Phi>" and "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)" and "wff\<^bsub>\<o>\<^esub>(A)"
      and "\<Phi> \<Turnstile>('u::infinite) A"
  shows "\<Phi> \<turnstile> A"
  by (rule completeness_hyps_open_finite[OF assms(1) assms(2) assms(3) assms(4)])

theorem sound_and_complete_hyps_fin:
  fixes \<Phi> :: "'p::infinite tm set"
  assumes fin: "finite \<Phi>" and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)" and A: "wff\<^bsub>\<o>\<^esub>(A)"
  shows "\<Phi> \<turnstile> A \<longleftrightarrow> \<Phi> \<Turnstile>('u::infinite) A"
proof
  assume "\<Phi> \<turnstile> A" thus "\<Phi> \<Turnstile>('u) A" by (rule NK_soundness)
next
  assume h: "\<Phi> \<Turnstile>('u) A"
  show "\<Phi> \<turnstile> A" by (rule NK_completeness_hyps_fin[OF fin w\<Phi> A h])
qed

theorem sound_and_complete:
  assumes "wff\<^bsub>\<o>\<^esub>(A::'p::infinite tm)"
  shows "\<turnstile> A \<longleftrightarrow> \<Turnstile>('u::infinite) A"
  using assms completeness_at_any_signature soundness_valid by blast

text \<open>The constraint \<open>'u::infinite\<close> is essential, not an artefact of the proof.  Soundness
  needs no constraint on \<open>'u\<close>.  Completeness does: over a @{emph \<open>finite\<close>} carrier no model
  of the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> exists at all --- with negation and disjunction in the signature
  every boolean function is \<open>\<lambda>\<close>-definable, so the domains at the types \<open>\<o>\<^sup>n \<^bold>\<Rightarrow> \<o>\<close> grow
  beyond any bound --- and validity at a finite carrier would hold vacuously for every
  formula, making the direction \<open>\<Turnstile> \<Longrightarrow> \<turnstile>\<close> false.\<close>

theorem consistency: "\<not> \<turnstile> \<^bold>\<bottom>"
  by (rule nk_consistent)

corollary no_contradiction: "\<turnstile> A \<Longrightarrow> \<not> \<turnstile> \<^bold>\<not> A"
  by (rule nk_not_both)

text \<open>Cantor's theorem is derived @{emph \<open>inside\<close>} \<open>NK\<close>, in surjective and injective form
  and at every type: @{thm [source] nk_surjective_cantor} and
  @{thm [source] nk_injective_cantor} in theory \<open>Cantor\<close>.  The two facts keep the names
  under which the published version of this entry exported them:\<close>

lemmas cantor_surjective = nk_surjective_cantor
lemmas cantor_injective = nk_injective_cantor

text \<open>Consistency with an infinity scheme, for every injective family of
  individual constants, obtained by compactness from arbitrarily large finite
  models:\<close>

corollary consistency_with_infinity_scheme:
  "inj (f :: nat \<Rightarrow> 'p::infinite) \<Longrightarrow> con (Diag f)"
  by (rule con_Diag)

text \<open>The scheme does not yield the single Dedekind-style axiom of infinity \<open>DInf\<close>: no
  finite part of the scheme derives it, and a countable Henkin model of the whole scheme
  refutes it (@{thm [source] henkin_scheme_refutes_DInf} in theory \<open>NK_Infinity\<close>; the
  scheme's consistency also holds in the strong finitary form
  @{thm [source] con_Diag_fprov}, and \<open>con_Diag_not_DInf\<close> adds \<open>\<^bold>\<not> DInf\<close> to the whole
  scheme).  The converse non-derivability --- the pure axiom yields no diagram
  inequation --- is established in the companion development via its set-theoretic model;
  as sentences, axiom and scheme are incomparable.\<close>

corollary scheme_does_not_derive_axiom:
  "inj (f :: nat \<Rightarrow> 'p::infinite) \<Longrightarrow> \<not> (Diag f \<tturnstile> (DInf :: 'p tm))"
  by (rule Diag_not_derives_DInf)

text \<open>Model existence (the positive half of Henkin completeness), restated: every consistent
  sentence has a @{emph \<open>countable\<close>} \<open>\<Sigma>\<close>-Henkin model, within plain HOL.  Consistency is the
  only premise --- so where an axiom (e.g.\ of infinity) has no finite models and its
  consistency must be borrowed from a stronger meta-theory, that meta-theory is used for the
  consistency premise alone, and the witnessing model still has a countable total domain,
  carved out of the carrier \<^typ>\<open>'p tm set\<close> as the \<open>\<sim>\<close>-classes of closed wffs.\<close>

corollary countable_henkin_model:
  fixes A :: "'p::{countable,infinite} tm"
  assumes "cwff \<o> A" and "con {A}"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" and vl \<xi>
  where "bkk_model Dm Ap Ee vl" "countable {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "vl (Ee \<xi> A)"
  by (rule countable_henkin_sat[OF assms])

end
