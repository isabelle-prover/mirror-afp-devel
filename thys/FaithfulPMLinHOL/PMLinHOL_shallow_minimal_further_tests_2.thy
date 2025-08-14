subsection\<open>Tests with the (minimal) shallow embedding: semantic frame conditions\<close>
theory PMLinHOL_shallow_minimal_further_tests_2 
  imports PMLinHOL_shallow_minimal
begin 
 \<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
 \<comment>\<open>Test with semantic conditions\<close>
abbreviation(input) refl ("\<r>") where "\<r> \<equiv> \<lambda>R. reflexive R"
abbreviation(input) sym ("\<s>") where "\<s> \<equiv> \<lambda>R. symmetric R"
abbreviation(input) tra ("\<t>") where "\<t> \<equiv> \<lambda>R. transitive R"

consts \<phi>::\<sigma> \<psi>::\<sigma> 
abbreviation(input) "F1 \<equiv> (\<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<supset>\<^sup>m \<diamond>\<^sup>m\<phi>"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2 \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"  \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3 \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m \<box>\<^sup>m\<phi>"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4 \<equiv> (\<box>\<^sup>m(\<diamond>\<^sup>m(\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)))) \<supset>\<^sup>m \<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)"  \<comment>\<open>holds in KB\<close>
abbreviation(input) "F5 \<equiv> (\<diamond>\<^sup>m(\<phi> \<and>\<^sup>m (\<diamond>\<^sup>m\<psi>))) \<supset>\<^sup>m ((\<diamond>\<^sup>m\<phi>) \<and>\<^sup>m (\<diamond>\<^sup>m\<psi>))" \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6 \<equiv> ((\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<psi>)) \<and>\<^sup>m (\<diamond>\<^sup>m(\<box>\<^sup>m(\<not>\<^sup>m\<psi>)))) \<supset>\<^sup>m \<not>\<^sup>m(\<diamond>\<^sup>m\<psi>)"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7 \<equiv> (\<diamond>\<^sup>m\<phi>) \<supset>\<^sup>m (\<box>\<^sup>m(\<phi> \<or>\<^sup>m \<diamond>\<^sup>m\<phi>))"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8 \<equiv> (\<diamond>\<^sup>m(\<box>\<^sup>m\<phi>)) \<supset>\<^sup>m (\<phi> \<or>\<^sup>m \<diamond>\<^sup>m\<phi>)"  \<comment>\<open>holds in KT and in KB\<close>
abbreviation(input) "F9 \<equiv> ((\<box>\<^sup>m(\<diamond>\<^sup>m\<phi>)) \<and>\<^sup>m (\<box>\<^sup>m(\<diamond>\<^sup>m(\<not>\<^sup>m \<phi>)))) \<supset>\<^sup>m \<diamond>\<^sup>m(\<diamond>\<^sup>m\<phi>)"  \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>m(\<phi> \<supset>\<^sup>m \<box>\<^sup>m\<psi>)) \<and>\<^sup>m (\<box>\<^sup>m(\<diamond>\<^sup>m(\<not>\<^sup>m\<psi>)))) \<supset>\<^sup>m \<not>\<^sup>m(\<box>\<^sup>m\<psi>)"  \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma K: " (\<Turnstile>\<^sup>m F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
   oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis 
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma K: " (\<Turnstile>\<^sup>m F4)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma K: " (\<Turnstile>\<^sup>m F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F8)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<r> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: " \<s> R \<and> \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<r> R \<and> \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis 
lemma KT: "\<r> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=none]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>none\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB: " \<s> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: " \<t> R \<longrightarrow> (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: " (\<Turnstile>\<^sup>m F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

 \<comment>\<open>Summary of experiments: 
 Nitpick: ctex=84 (with simp 42, without simp 42), none=76 (with simp 38, without simp 38), unknwn=0 
 Sledgehammer: proof=76 (with simp 38, without simp 38), no prf=84 (with simp 42, without simp 42) \<close>

 \<comment>\<open>No conflicts\<close>
end