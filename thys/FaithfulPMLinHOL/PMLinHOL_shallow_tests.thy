subsection\<open>Tests with the maximal shallow embedding\<close>

theory PMLinHOL_shallow_tests   (* Christoph Benzmüller, 2025 *)
   imports PMLinHOL_shallow
begin

\<comment>\<open>Hilbert calculus: proving that the schematic axioms and rules implied by the embedding\<close>
lemma H1: "\<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s (\<psi> \<supset>\<^sup>s \<phi>)" by auto
lemma H2: "\<Turnstile>\<^sup>s (\<phi> \<supset>\<^sup>s (\<psi> \<supset>\<^sup>s \<gamma>)) \<supset>\<^sup>s ((\<phi> \<supset>\<^sup>s \<psi>) \<supset>\<^sup>s (\<phi> \<supset>\<^sup>s \<gamma>)) " by auto
lemma H3: "\<Turnstile>\<^sup>s (\<not>\<^sup>s\<phi>\<supset>\<^sup>s \<not>\<^sup>s\<psi>) \<supset>\<^sup>s (\<psi> \<supset>\<^sup>s \<phi>)" by auto
lemma MP: "\<Turnstile>\<^sup>s \<phi> \<Longrightarrow> \<Turnstile>\<^sup>s (\<phi>\<supset>\<^sup>s \<psi>) \<Longrightarrow> \<Turnstile>\<^sup>s \<psi>" by auto

\<comment>\<open>Reasoning with the Hilbert calculus: interactive and fully automated\<close>
lemma HCderived1: "\<Turnstile>\<^sup>s (\<phi> \<supset>\<^sup>s \<phi>)" \<comment>\<open>sledgehammer(HC1 HC2 HC3 MP) returns: by (metis HC1 HC2 MP)\<close>
  proof -
    have 1: "\<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s ((\<psi> \<supset>\<^sup>s \<phi>) \<supset>\<^sup>s \<phi>)" using H1 by auto 
    have 2: "\<Turnstile>\<^sup>s (\<phi> \<supset>\<^sup>s ((\<psi> \<supset>\<^sup>s \<phi>) \<supset>\<^sup>s \<phi>)) \<supset>\<^sup>s ((\<phi> \<supset>\<^sup>s (\<psi> \<supset>\<^sup>s \<phi>)) \<supset>\<^sup>s (\<phi> \<supset>\<^sup>s \<phi>))" using H2 by auto 
    have 3: "\<Turnstile>\<^sup>s (\<phi> \<supset>\<^sup>s (\<psi> \<supset>\<^sup>s \<phi>)) \<supset>\<^sup>s (\<phi> \<supset>\<^sup>s \<phi>)" using 1 2 MP by meson
    have 4: "\<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s (\<psi>\<supset>\<^sup>s \<phi>)" using H1 by auto 
    thus ?thesis using 3 4 MP by meson 
  qed

lemma HCderived2: "\<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s (\<not>\<^sup>s\<phi>\<supset>\<^sup>s \<psi>) " by (metis H1 H2 H3 MP) 
lemma HCderived3: "\<Turnstile>\<^sup>s (\<not>\<^sup>s\<phi>\<supset>\<^sup>s \<phi>) \<supset>\<^sup>s \<phi>" by (metis H1 H2 H3 MP) 
lemma HCderived4: "\<Turnstile>\<^sup>s (\<phi> \<supset>\<^sup>s \<psi>) \<supset>\<^sup>s (\<not>\<^sup>s\<psi> \<supset>\<^sup>s \<not>\<^sup>s\<phi>) " by auto 

\<comment>\<open>Modal logic: the schematic necessitation rule and distribution axiom are implied\<close>
lemma Nec: "\<Turnstile>\<^sup>s \<phi> \<Longrightarrow> \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi>" by auto
lemma Dist:"\<Turnstile>\<^sup>s \<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<psi>) \<supset>\<^sup>s (\<box>\<^sup>s\<phi> \<supset>\<^sup>s \<box>\<^sup>s\<psi>) " by auto

\<comment>\<open>Correspondence theory: correct statements\<close> 
lemma cM:"reflexive R \<longleftrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi> \<supset>\<^sup>s \<phi>)" \<comment>\<open>sledgehammer: Proof found\<close> oops (**)
lemma cBa: "symmetric R \<longrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>))" by auto 
(**)lemma cBb: "symmetric R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>))" \<comment>\<open>sledgehammer: No proof\<close> oops
lemma c4a: "transitive R \<longrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>))" by (smt DefS)
(**)lemma c4b: "transitive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>))" \<comment>\<open>sledgehammer: No proof\<close> oops

\<comment>\<open>Correspondence theory: incorrect statements\<close> 
lemma "reflexive R \<longrightarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s\<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>))" nitpick[card \<w>=3] oops \<comment>\<open>nitpick: Counterexample\<close>

\<comment>\<open>Simple, incorrect validity statements\<close>
lemma "\<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s\<phi>" nitpick[card \<w>=2, card \<S>= 1] oops \<comment>\<open>nitpick: Counterexample: modal collapse not implied\<close>
(**)lemma "\<Turnstile>\<^sup>s \<box>\<^sup>s( \<box>\<^sup>s\<phi> \<supset>\<^sup>s\<box>\<^sup>s\<psi>) \<or>\<^sup>s \<box>\<^sup>s( \<box>\<^sup>s\<psi> \<supset>\<^sup>s\<box>\<^sup>s\<phi>)" oops \<comment>\<open>\<open>nitpick[card \<w>=3]\<close> returns: unknown\<close> 
lemma "\<Turnstile>\<^sup>s (\<diamond>\<^sup>s(\<box>\<^sup>s \<phi>)) \<supset>\<^sup>s\<box>\<^sup>s(\<diamond>\<^sup>s \<phi>)" nitpick[card \<w>=2] oops \<comment>\<open>nitpick: Counterexample\<close> 

\<comment>\<open>Implied axiom schemata in S5\<close>
lemma KB: "symmetric R \<longrightarrow> (\<forall>\<phi> \<psi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>))" by auto
lemma K4B: "symmetric R \<and> transitive R \<longrightarrow> (\<forall>\<phi> \<psi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s( \<box>\<^sup>s\<phi> \<supset>\<^sup>s\<box>\<^sup>s\<psi>) \<or>\<^sup>s \<box>\<^sup>s( \<box>\<^sup>s\<psi> \<supset>\<^sup>s\<box>\<^sup>s\<phi>))" by (smt DefS)
end


