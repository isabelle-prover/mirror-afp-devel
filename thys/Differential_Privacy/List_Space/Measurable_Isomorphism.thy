(*
 Title:Measurable_Isomorphism.thy
 Author: Tetsuya Sato
*)

theory Measurable_Isomorphism
  imports
    "HOL-Analysis.Sigma_Algebra"
begin

lemma measurable_isomorphism_iff:
  assumes "f \<in> M \<rightarrow>\<^sub>M N"
    and "g \<in> N \<rightarrow>\<^sub>M M"
    and "\<forall> x \<in> space M. g(f(x)) = x"
    and "\<forall> y \<in> space N. f(g(y)) = y"
  shows "\<And> h. (h \<in> N \<rightarrow>\<^sub>M K) \<longleftrightarrow> (h o f \<in> M \<rightarrow>\<^sub>M K)"
    "\<And> h. (h \<in> M \<rightarrow>\<^sub>M K) \<longleftrightarrow> (h o g \<in> N \<rightarrow>\<^sub>M K)"
    "\<And> h. (h \<in> K \<rightarrow>\<^sub>M M) \<longleftrightarrow> (f o h \<in> K \<rightarrow>\<^sub>M N)\<and>(h \<in> space K \<rightarrow> space M)"
    "\<And> h. (h \<in> K \<rightarrow>\<^sub>M N) \<longleftrightarrow> (g o h \<in> K \<rightarrow>\<^sub>M M)\<and>(h \<in> space K \<rightarrow> space N)"
proof-
  show "\<And> h. (h \<in> N \<rightarrow>\<^sub>M K) \<longleftrightarrow> (h o f \<in> M \<rightarrow>\<^sub>M K)"
  proof(intro iffI measurable_comp[OF assms(1)],clarify)
    fix h assume "h \<circ> f \<in> M \<rightarrow>\<^sub>M K"
    hence "h o f o g \<in> N \<rightarrow>\<^sub>M K"
      using assms(2) measurable_comp by blast
    thus"h \<in> N \<rightarrow>\<^sub>M K"
      by(subst measurable_cong, auto simp add: assms)
  qed
  show "\<And>h. (h \<in> M \<rightarrow>\<^sub>M K) = (h \<circ> g \<in> N \<rightarrow>\<^sub>M K)"
  proof(intro iffI measurable_comp[OF assms(2)],clarify)
    fix h assume "h \<circ> g \<in> N \<rightarrow>\<^sub>M K"
    hence "h o g o f \<in> M \<rightarrow>\<^sub>M K"
      using assms(1) measurable_comp by blast
    thus"h \<in> M \<rightarrow>\<^sub>M K"
      by(subst measurable_cong, auto simp add: assms)
  qed
  show "\<And>h. (h \<in> K \<rightarrow>\<^sub>M M) \<longleftrightarrow> (f o h \<in> K \<rightarrow>\<^sub>M N)\<and>(h \<in> space K \<rightarrow> space M)"
  proof(intro iffI conjI measurable_comp[OF _ assms(1)],clarify)
    fix h assume "f \<circ> h \<in> K \<rightarrow>\<^sub>M N \<and> h \<in> space K \<rightarrow> space M"
    hence "g o f o h \<in> K \<rightarrow>\<^sub>M M \<and> h \<in> space K \<rightarrow> space M"
      using assms(2) measurable_comp by(subst comp_assoc, auto)
    hence "g o f o h \<in> K \<rightarrow>\<^sub>M M \<and> (\<forall>w \<in> space K. (g o f o h) w = (h w))"
      using assms (3,4) by auto
    thus"h \<in> K \<rightarrow>\<^sub>M M"
      using assms (3,4) by(subst measurable_cong, auto)
  qed(auto simp:measurable_def)
  show "\<And>h. (h \<in> K \<rightarrow>\<^sub>M N) = (g \<circ> h \<in> K \<rightarrow>\<^sub>M M \<and> h \<in> space K \<rightarrow> space N)"
  proof(intro iffI conjI measurable_comp[OF _ assms(2)],clarify)
    fix h assume "g \<circ> h \<in> K \<rightarrow>\<^sub>M M \<and> h \<in> space K \<rightarrow> space N"
    hence "f o g \<circ> h \<in> K \<rightarrow>\<^sub>M N \<and> h \<in> space K \<rightarrow> space N"
      using assms(1) measurable_comp by(subst comp_assoc, auto)
    hence "f o g o h \<in> K \<rightarrow>\<^sub>M N \<and> (\<forall>w \<in> space K. (f o g o h) w = (h w))"
      using assms (3,4) by auto
    thus"h \<in> K \<rightarrow>\<^sub>M N"
      using assms (3,4) by(subst measurable_cong, auto)
  qed(auto simp:measurable_def)
qed

end