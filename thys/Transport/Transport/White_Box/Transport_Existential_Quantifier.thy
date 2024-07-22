\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nils Harmsen"\<close>
section \<open>White-Box Transport of (Bounded) Existential Quantifier\<close>
theory Transport_Existential_Quantifier
  imports
    Transport_Universal_Quantifier
begin

paragraph \<open>Summary\<close>
text \<open>Theorems for white-box transports of (bounded) existential quantifiers.\<close>

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_restricts_imp_bex_if_left_total_onI:
  assumes "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_relI) fast

lemma Fun_Rel_restricts_rev_imp_bex_if_rel_surjective_at:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_relI) fast

lemma Fun_Rel_restricts_iff_bex_if_left_total_on_if_rel_surjective_at:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  and "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_relI) fast

corollary Fun_Rel_restricts_iff_bex_if_bi_total_on:
  assumes "bi_total_on P Q R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_restricts_iff_bex_if_left_total_on_if_rel_surjective_at)
  fast+

lemma left_total_on_restrict_right_if_Fun_Rel_imp_bex:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  shows "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
proof
  fix x assume "P x"
  let ?P1 = "(=) x" and ?P2 = "R x"
  have "(R \<Rrightarrow> (\<longrightarrow>)) ?P1 ?P2" by auto
  with assms have "\<exists>\<^bsub>P\<^esub> ?P1 \<longrightarrow> \<exists>\<^bsub>Q\<^esub> ?P2" by blast
  with \<open>P x\<close> show "in_dom R\<upharpoonleft>\<^bsub>Q\<^esub> x" by blast
qed

corollary Fun_Rel_imp_all_on_iff_left_total_on_restrict_right:
  "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub> \<longleftrightarrow> left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (blast intro: Fun_Rel_restricts_imp_bex_if_left_total_onI
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    left_total_on_restrict_right_if_Fun_Rel_imp_bex)

lemma rel_surjective_at_restrict_left_if_Fun_Rel_rev_imp_bex:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  shows "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
proof
  fix y assume "Q y"
  let ?P1 = "R\<inverse> y" and ?P2 = "(=) y"
  have "(R \<Rrightarrow> (\<longleftarrow>)) ?P1 ?P2" by auto
  with assms have "\<exists>\<^bsub>P\<^esub> ?P1 \<longleftarrow> \<exists>\<^bsub>Q\<^esub> ?P2" by blast
  with \<open>Q y\<close> show "in_codom R\<restriction>\<^bsub>P\<^esub> y" by blast
qed

corollary Fun_Rel_rev_imp_bex_iff_rel_surjective_at_restrict_left:
  "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub> \<longleftrightarrow> rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  by (blast intro: Fun_Rel_restricts_rev_imp_bex_if_rel_surjective_at
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    rel_surjective_at_restrict_left_if_Fun_Rel_rev_imp_bex)

lemma bi_total_on_if_Fun_Rel_iff_bex:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  shows "bi_total_on P Q R"
proof (intro bi_total_onI left_total_onI rel_surjective_atI; rule ccontr)
  fix x assume "P x" and not_dom: "\<not>(in_dom R x)"
  let ?P1 = "(=) x" and ?P2 = "R x"
  from not_dom have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<exists>x : P. ?P1 x) \<longleftrightarrow> (\<exists>y : Q. ?P2 y)" by blast
  with \<open>P x\<close> not_dom show "False" by blast
next
  fix y assume "Q y" and not_codom: "\<not>(in_codom R y)"
  let ?P1 = "\<lambda>x. R x y" and ?P2 = "(=) y"
  from not_codom have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<exists>x : P. ?P1 x) \<longleftrightarrow> (\<exists>y : Q. ?P2 y)" by blast
  with \<open>Q y\<close> not_codom show "False" by blast
qed

corollary Fun_Rel_iff_bex_iff_bi_total_on_if_Fun_Rel_iff:
  assumes "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub> \<longleftrightarrow> bi_total_on P Q R"
  using assms by (blast intro: Fun_Rel_restricts_iff_bex_if_bi_total_on
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    bi_total_on_restricts_if_Fun_Rel_iff_if_bi_total_on
    bi_total_on_if_Fun_Rel_iff_bex)

end

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

corollary Fun_Rel_imp_ex_if_left_total:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_restricts_imp_bex_if_left_total_onI)

corollary Fun_Rel_rev_imp_ex_if_rel_surjective:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_restricts_rev_imp_bex_if_rel_surjective_at)

corollary Fun_Rel_iff_ex_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_restricts_iff_bex_if_bi_total_on)

corollary left_total_if_Fun_Rel_imp_ex:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex Ex"
  shows "left_total R"
  using assms by (urule left_total_on_restrict_right_if_Fun_Rel_imp_bex)

corollary Fun_Rel_imp_ex_iff_left_total:
  "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex Ex \<longleftrightarrow> left_total R"
  using left_total_if_Fun_Rel_imp_ex Fun_Rel_imp_ex_if_left_total by blast

corollary rel_surjective_if_Fun_Rel_rev_imp_ex:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex Ex"
  shows "rel_surjective R"
  using assms by (urule rel_surjective_at_restrict_left_if_Fun_Rel_rev_imp_bex)

corollary Fun_Rel_rev_imp_ex_iff_rel_surjective:
  "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex Ex \<longleftrightarrow> rel_surjective R"
  using rel_surjective_if_Fun_Rel_rev_imp_ex Fun_Rel_rev_imp_ex_if_rel_surjective by blast

corollary bi_total_if_Fun_Rel_iff_ex:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex"
  shows "bi_total R"
  using assms by (urule bi_total_on_if_Fun_Rel_iff_bex)

corollary Fun_Rel_iff_ex_iff_bi_total:
  "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex \<longleftrightarrow> bi_total R"
  using bi_total_if_Fun_Rel_iff_ex Fun_Rel_iff_ex_if_bi_total by blast

end

end