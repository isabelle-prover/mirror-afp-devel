subsection\<open>Tests with the (maximal) shallow embedding: semantic frame conditions\<close>
theory PMLinHOL_shallow_further_tests_2 
  imports PMLinHOL_shallow_tests  
begin 
 \<comment>\<open>What is the weakest modal logic in which the following test formulas F1-F10 are provable?\<close>
 \<comment>\<open>Test with semantic conditions\<close>
abbreviation(input) refl ("\<r>") where "\<r> \<equiv> \<lambda>R. reflexive R"
abbreviation(input) sym ("\<s>") where "\<s> \<equiv> \<lambda>R. symmetric R"
abbreviation(input) tra ("\<t>") where "\<t> \<equiv> \<lambda>R. transitive R"

consts \<phi>::\<sigma> \<psi>::\<sigma>
abbreviation(input) "F1 \<equiv> (\<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<supset>\<^sup>s \<diamond>\<^sup>s\<phi>"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F2 \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KB\<close>
abbreviation(input) "F3 \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s \<box>\<^sup>s\<phi>"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F4 \<equiv> (\<box>\<^sup>s(\<diamond>\<^sup>s(\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)))) \<supset>\<^sup>s \<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KB\<close>
abbreviation(input) "F5 \<equiv> (\<diamond>\<^sup>s(\<phi> \<and>\<^sup>s (\<diamond>\<^sup>s\<psi>))) \<supset>\<^sup>s ((\<diamond>\<^sup>s\<phi>) \<and>\<^sup>s (\<diamond>\<^sup>s\<psi>))"  \<comment>\<open>holds in K4\<close>
abbreviation(input) "F6 \<equiv> ((\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<psi>)) \<and>\<^sup>s (\<diamond>\<^sup>s(\<box>\<^sup>s(\<not>\<^sup>s\<psi>)))) \<supset>\<^sup>s \<not>\<^sup>s(\<diamond>\<^sup>s\<psi>)"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F7 \<equiv> (\<diamond>\<^sup>s\<phi>) \<supset>\<^sup>s (\<box>\<^sup>s(\<phi> \<or>\<^sup>s \<diamond>\<^sup>s\<phi>))"  \<comment>\<open>holds in KB4\<close>
abbreviation(input) "F8 \<equiv> (\<diamond>\<^sup>s(\<box>\<^sup>s\<phi>)) \<supset>\<^sup>s (\<phi> \<or>\<^sup>s \<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KT and in KB\<close>
abbreviation(input) "F9 \<equiv> ((\<box>\<^sup>s(\<diamond>\<^sup>s\<phi>)) \<and>\<^sup>s (\<box>\<^sup>s(\<diamond>\<^sup>s(\<not>\<^sup>s \<phi>)))) \<supset>\<^sup>s \<diamond>\<^sup>s(\<diamond>\<^sup>s\<phi>)"  \<comment>\<open>holds in KT\<close>
abbreviation(input) "F10 \<equiv> ((\<box>\<^sup>s(\<phi> \<supset>\<^sup>s \<box>\<^sup>s\<psi>)) \<and>\<^sup>s (\<box>\<^sup>s(\<diamond>\<^sup>s(\<not>\<^sup>s\<psi>)))) \<supset>\<^sup>s \<not>\<^sup>s(\<box>\<^sup>s\<psi>)"  \<comment>\<open>holds in KT\<close>

declare imp_cong[cong del]

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>  
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F1)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F2)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F3)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by metis
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by metis
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by metis
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by meson
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F4)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F5)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F6)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F7)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F8)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F9)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

experiment begin
lemma S5: "\<forall>w:W. \<r> R \<and> \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma S4: "\<forall>w:W. \<r> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB4: "\<forall>w:W. \<s> R \<and> \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma KTB: "\<forall>w:W. \<r> R \<and> \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KT: "\<forall>w:W. \<r> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=unknown]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>unkn\<close> \<comment>\<open>proof\<close>
  by blast
lemma KB: "\<forall>w:W. \<s> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K4: "\<forall>w:W. \<t> R \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
lemma K: "\<forall>w:W. (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s F10)"  
  \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  apply simp \<comment>\<open>nitpick[expect=genuine]\<close> \<comment>\<open>sledgehammer\<close>  \<comment>\<open>ctex\<close> \<comment>\<open>no prf\<close>
  oops
end

 \<comment>\<open>Summary of experiments: 
 Nitpick: ctex=84 (with simp 42, without simp 42), none=0, unknwn=76 (with simp 38, without simp 38) 
 Sledgehammer: proof=66 (with simp 38, without simp 28), no prf=94 (with simp 42, without simp 52)\<close>

 \<comment>\<open>No conflicts\<close>
end