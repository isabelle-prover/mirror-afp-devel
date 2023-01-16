section \<open>Selected Simplified Ontological Argument \label{sec:selected}\<close>

theory SimplifiedOntologicalArgument imports 
  HOML
begin
text \<open>Positive properties:\<close>
consts posProp::"\<gamma>\<Rightarrow>\<sigma>" ("\<P>")

text \<open>An entity x is God-like if it possesses all positive properties.\<close>
definition G ("\<G>") where "\<G>(x) \<equiv> \<^bold>\<forall>\<Phi>.(\<P>(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"

text \<open>The axiom's of the simplified variant are presented next; these axioms are further motivated in \<^cite>\<open>"C85" and "J52"\<close>).\<close> 
text \<open>Self-difference is not a positive property (possible alternative: 
      the empty property is not a positive property).\<close>
axiomatization where CORO1: "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" 
text \<open>A property entailed by a positive property is positive.\<close>
axiomatization where CORO2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. \<P>(\<Phi>) \<^bold>\<and> (\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> \<P>(\<Psi>)\<rfloor>" 
text \<open>Being Godlike is a positive property.\<close>
axiomatization where AXIOM3: "\<lfloor>\<P> \<G>\<rfloor>" 

subsection\<open>Verifying the Selected Simplified Ontological Argument (version 1)\<close>

text \<open>The existence of a non-exemplified positive property implies that self-difference 
      (or, alternatively, the empty property) is a positive property.\<close>
lemma LEMMA1: "\<lfloor>(\<^bold>\<exists>\<Phi>.(\<P>(\<Phi>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>x. \<Phi>(x)))) \<^bold>\<rightarrow> \<P>(\<lambda>x.(x\<^bold>\<noteq>x))\<rfloor>" 
  using CORO2 by meson 
text \<open>A non-exemplified positive property does not exist.\<close>
lemma LEMMA2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<Phi>.(\<P>(\<Phi>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>x. \<Phi>(x))))\<rfloor>" 
  using CORO1 LEMMA1 by blast
text \<open>Positive properties are exemplified.\<close>
lemma LEMMA3: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<P>(\<Phi>) \<^bold>\<rightarrow> (\<^bold>\<exists>x. \<Phi>(x)))\<rfloor>" 
  using LEMMA2 by blast
text \<open>There exists a God-like entity.\<close>
theorem THEOREM3': "\<lfloor>\<^bold>\<exists>x. \<G>(x)\<rfloor>" 
  using AXIOM3 LEMMA3 by auto
text \<open>Necessarily, there exists a God-like entity.\<close>
theorem THEOREM3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  using THEOREM3' by simp
text \<open>However, the possible existence of Godlike entity is not implied.\<close>
theorem CORO: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  nitpick oops (*Countermodel*)

subsection\<open>Verifying the Selected Simplified Ontological Argument (version 2)\<close>

text \<open>We switch to logic T.\<close>
axiomatization where T: "\<lfloor>\<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" 
lemma T': "\<lfloor>\<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>\<rfloor>" using T by metis
text \<open>Positive properties are possibly exemplified.\<close>
theorem THEOREM1: "\<lfloor>\<^bold>\<forall>\<Phi>. \<P>(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<Phi>(x))\<rfloor>" 
  using CORO1 CORO2 T' by metis
text \<open>Possibly there exists a God-like entity.\<close>
theorem CORO: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  using AXIOM3 THEOREM1 by auto
text \<open>The possible existence of a God-like entity impplies the necessary  existence of a God-like entity.\<close>
theorem THEOREM2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. \<G>(x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  using AXIOM3 CORO1 CORO2 by metis
text \<open>Necessarily, there exists a God-like entity.\<close>
theorem THEO3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. \<G>(x))\<rfloor>" 
  using CORO THEOREM2 by blast 
text \<open>There exists a God-like entity.\<close>
theorem THEO3': "\<lfloor>\<^bold>\<exists>x. \<G>(x)\<rfloor>" 
  using T THEO3 by metis

text \<open>Modal collapse is not implied; nitpick reports a countermodel.\<close>

lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" nitpick oops

text \<open>Consistency of the theory; nitpick reports a model.\<close>
lemma True nitpick[satisfy] oops (*Model found*)
end

