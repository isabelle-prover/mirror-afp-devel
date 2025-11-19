section\<open>Test Examples: Formula classification\<close>
subsection\<open>Tests with the deep embedding: axiom schemata\<close>
theory PMLinHOL_deep_further_tests_1
  imports PMLinHOL_deep_tests  
begin 
 \<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
 \<comment>\<open>Test with schematic axioms\<close>

consts \<phi>::PML \<psi>::PML
abbreviation(input) "F1 \<equiv> (\<diamond>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<supset>\<^sup>d \<diamond>\<^sup>d\<phi>"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2 \<equiv> (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)"  \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3 \<equiv> (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d \<box>\<^sup>d\<phi>"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4 \<equiv> (\<box>\<^sup>d(\<diamond>\<^sup>d(\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)))) \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)"  \<comment>\<open>holds in KB/K4\<close>
abbreviation(input) "F5 \<equiv> (\<diamond>\<^sup>d(\<phi> \<and>\<^sup>d (\<diamond>\<^sup>d\<psi>))) \<supset>\<^sup>d ((\<diamond>\<^sup>d\<phi>) \<and>\<^sup>d (\<diamond>\<^sup>d\<psi>))"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6 \<equiv> ((\<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<psi>)) \<and>\<^sup>d (\<diamond>\<^sup>d(\<box>\<^sup>d(\<not>\<^sup>d\<psi>)))) \<supset>\<^sup>d \<not>\<^sup>d(\<diamond>\<^sup>d\<psi>)"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7 \<equiv> (\<diamond>\<^sup>d\<phi>) \<supset>\<^sup>d (\<box>\<^sup>d(\<phi> \<or>\<^sup>d \<diamond>\<^sup>d\<phi>))"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8 \<equiv> (\<diamond>\<^sup>d(\<box>\<^sup>d\<phi>)) \<supset>\<^sup>d (\<phi> \<or>\<^sup>d \<diamond>\<^sup>d\<phi>)"  \<comment>\<open>holds in KT/KB\<close>
abbreviation(input) "F9 \<equiv> ((\<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and>\<^sup>d (\<box>\<^sup>d(\<diamond>\<^sup>d(\<not>\<^sup>d \<phi>)))) \<supset>\<^sup>d \<diamond>\<^sup>d(\<diamond>\<^sup>d\<phi>)"  \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>d(\<phi> \<supset>\<^sup>d \<box>\<^sup>d\<psi>)) \<and>\<^sup>d (\<box>\<^sup>d(\<diamond>\<^sup>d(\<not>\<^sup>d\<psi>)))) \<supset>\<^sup>d \<not>\<^sup>d(\<box>\<^sup>d\<psi>)"  \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  by (smt (z3) PML.simps(22))
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22)) 
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22)) 
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F1" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F2" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F3" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F4" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  by (smt (z3) PML.simps(22))
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  by (smt (z3) PML.simps(22))
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F5" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F6" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F7" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (smt (z3) PML.simps(22))
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F8" 
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close> 
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (mono_tags, lifting) PML.simps(22))  
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (mono_tags, lifting) PML.simps(22))  
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (mono_tags, lifting) PML.simps(22))  
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (mono_tags, lifting) PML.simps(22))  
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F9" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (mono_tags, lifting) PML.simps(22))  
lemma S4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by (metis (mono_tags, lifting) PML.simps(22))  
lemma KB4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<and> (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close> 
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close> 
  by (smt (verit) PML.simps(22,24))
lemma KT: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<phi>) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close> 
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close> 
  by (smt (verit) PML.simps(22,24))
lemma KB: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<box>\<^sup>d(\<diamond>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. (\<forall>\<phi>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>) \<supset>\<^sup>d \<box>\<^sup>d(\<box>\<^sup>d\<phi>)) \<longrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d F10" 
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>   \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

 \<comment>\<open>Summary of experiments: 
 Nitpick: ctex=16 (with simp 10, without simp 6), none=74 (with simp 0, without simp 74), unknwn=70 (with simp 70, without simp 0)
 Sledgehammer: proof=33 (with simp 16, without simp 17), no prf=127 (with simp 64, without simp 63)\<close>

 \<comment>\<open>No conflict\<close>
end
