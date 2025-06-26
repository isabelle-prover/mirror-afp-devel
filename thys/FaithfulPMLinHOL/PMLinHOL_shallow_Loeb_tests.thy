
theory PMLinHOL_shallow_Loeb_tests (* Christoph Benzmüller, 2025 *)
  imports PMLinHOL_shallow 
begin

\<comment>\<open>Löb axiom: with the minimal shallow embedding automated reasoning tools are still partly responsive\<close>
lemma Loeb1: "\<forall>\<phi>. \<Turnstile>\<^sup>s \<box>\<^sup>s( \<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>" nitpick[card \<w>=1,card \<S>=1] oops \<comment>\<open>nitpick: Counterexample\<close>
lemma Loeb2: "(conversewf R \<and> transitive R) \<longrightarrow>(\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: Proof found\<close> oops
lemma Loeb3: "(conversewf R \<and> transitive R) \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: No Proof\<close> oops
lemma Loeb3a: "conversewf R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: Proof found\<close> oops (**)
lemma Loeb3b: "transitive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: No Proof\<close> oops
lemma Loeb3c: "irreflexive R \<longleftarrow> (\<forall>\<phi> W V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi> \<supset>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s\<phi>)" \<comment>\<open>sledgehammer: Proof found\<close> oops
end

