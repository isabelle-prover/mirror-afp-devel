theory Main_Results
  imports Cantor
begin

section \<open>Main results\<close>

text \<open>The central results of this entry, restated in one place.  Soundness
  and completeness of \<open>NK\<close> for the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (BKK Theorem 7.3 and a
  strengthening of BKK Corollary 7.7): for well-formed (open) formulas over
  every signature with infinitely many parameters, derivability coincides
  with validity at @{emph \<open>every\<close>} infinite value carrier --- no cardinality
  link between the parameter type \<open>'p\<close> and the carrier \<open>'u\<close> is needed.  Consistency holds
  for arbitrary signatures, by the concrete standard model --- note the asymmetry:
  consistency needs @{emph \<open>no\<close>} constraint on \<open>'p\<close> at all, whereas completeness
  requires \<open>'p\<close> infinite, since the rule \<open>NK(\<Pi>I)\<close> consumes fresh
  eigen-parameters.  Cantor's theorem, surjective and injective, is derived
  inside \<open>NK\<close> at every type.\<close>

theorem NK_soundness:
  "\<Phi> \<turnstile> C \<Longrightarrow> \<Phi> \<Turnstile>('u) C"
  using soundness_sat.

theorem NK_completeness:
  assumes "wff\<^bsub>\<o>\<^esub>(A::'p::infinite tm)" and "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
  using completeness_at_any_signature[OF assms].

theorem sound_and_complete:
  assumes "wff\<^bsub>\<o>\<^esub>(A::'p::infinite tm)"
  shows "\<turnstile> A \<longleftrightarrow> \<Turnstile>('u::infinite) A"
  using assms completeness_at_any_signature soundness_valid by blast

theorem consistency: "\<not> \<turnstile> \<^bold>\<bottom>"
  by (rule nk_consistent)

corollary no_contradiction: "\<turnstile> A \<Longrightarrow> \<not> \<turnstile> \<^bold>\<not> A"
  by (rule nk_not_both)

theorem cantor_surjective: fixes \<sigma> :: ty shows
  "\<turnstile> (\<^bold>\<not> (\<^bold>\<exists>\<G>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<exists>\<X>\<^bsub>\<sigma>\<^esub>.
     ((\<G>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> \<X>\<^sup>f\<^bsub>\<sigma>\<^esub>) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>)) :: 'p::infinite tm)"
  by (rule nk_surjective_cantor)

theorem cantor_injective: fixes \<sigma> :: ty shows
  "\<turnstile> (\<^bold>\<not> (\<^bold>\<exists>\<I>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<H>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>.
       (((\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>=\<^bsub>\<sigma>\<^esub> (\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
        \<^bold>\<supset> (\<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))) :: 'p::infinite tm)"
  by (rule nk_injective_cantor)

end
