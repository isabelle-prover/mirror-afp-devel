subsection\<open>Tests with the (maximal) shallow embedding: axiom schemata\<close>
theory PMLinHOL_shallow_further_tests_1 imports PMLinHOL_shallow_tests  
begin 
 \<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
 \<comment>\<open>Test with schematic axioms\<close>

consts \<phi>::\<sigma> \<psi>::\<sigma>
abbreviation(input) "F1 \<equiv> (\<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<supset>\<^sup>s \<diamond>\<^sup>s\<phi>"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2 \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3 \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s \<box>\<^sup>s\<phi>"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4 \<equiv> (\<box>\<^sup>s(\<diamond>\<^sup>s(\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)))) \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KB/K4\<close>
abbreviation(input) "F5 \<equiv> (\<diamond>\<^sup>s(\<phi> \<and>\<^sup>s (\<diamond>\<^sup>s\<psi>))) \<supset>\<^sup>s ((\<diamond>\<^sup>s\<phi>) \<and>\<^sup>s (\<diamond>\<^sup>s\<psi>))"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6 \<equiv> ((\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<psi>)) \<and>\<^sup>s (\<diamond>\<^sup>s(\<box>\<^sup>s(\<not>\<^sup>s\<psi>)))) \<supset>\<^sup>s \<not>\<^sup>s(\<diamond>\<^sup>s\<psi>)"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7 \<equiv> (\<diamond>\<^sup>s\<phi>) \<supset>\<^sup>s (\<box>\<^sup>s(\<phi> \<or>\<^sup>s \<diamond>\<^sup>s\<phi>))"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8 \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s (\<phi> \<or>\<^sup>s \<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KT/KB\<close>
abbreviation(input) "F9 \<equiv> ((\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and>\<^sup>s (\<box>\<^sup>s(\<diamond>\<^sup>s(\<not>\<^sup>s \<phi>)))) \<supset>\<^sup>s \<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<box>\<^sup>s\<psi>)) \<and>\<^sup>s (\<box>\<^sup>s(\<diamond>\<^sup>s(\<not>\<^sup>s\<psi>)))) \<supset>\<^sup>s \<not>\<^sup>s(\<box>\<^sup>s\<psi>)"  \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1"
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit) NegS_def)
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (verit, del_insts) NegS_def)
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close> \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis NegS_def) 
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close> 
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (lifting) BoxS_def NegS_def)
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (lifting) BoxS_def NegS_def) 
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<phi> \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s (\<box>\<^sup>s\<phi>) \<supset>\<^sup>s \<box>\<^sup>s(\<box>\<^sup>s\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

 \<comment>\<open>Summary of experiments: 
 Nitpick: ctex=32 (with simp 16, without simp 16), none=0, unknwn=128 (with simp 64, without simp 64)
 Sledgehammer: proof=32 (with simp 24, without simp 8), no prf=128 (with simp 56, without simp 72)\<close>

 \<comment>\<open>No conflict\<close>
end
