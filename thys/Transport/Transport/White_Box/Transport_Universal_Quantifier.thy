\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nils Harmsen"\<close>
section \<open>White-Box Transport of (Bounded) Universal Quantifier\<close>
theory Transport_Universal_Quantifier
  imports
    Bounded_Quantifiers
    Binary_Relations_Bi_Total
    Reverse_Implies
begin

paragraph \<open>Summary\<close>
text \<open>Theorems for white-box transports of (bounded) universal quantifiers.\<close>

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_restricts_imp_ball_if_rel_surjective_atI:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_relI) blast

lemma Fun_Rel_restricts_rev_imp_ball_if_left_total_onI:
  assumes "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_relI) blast

lemma Fun_Rel_restricts_iff_ball_if_left_total_on_if_rel_surjective_at:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  and "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_relI) blast

corollary Fun_Rel_restricts_iff_ball_if_bi_total_on:
  assumes "bi_total_on P Q R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_restricts_iff_ball_if_left_total_on_if_rel_surjective_at)
  force+

lemma rel_surjective_at_restrict_left_if_Fun_Rel_imp_ball:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
proof -
  let ?P2 = "in_codom R\<restriction>\<^bsub>P\<^esub>"
  have "(R \<Rrightarrow> (\<longrightarrow>)) P ?P2" by blast
  with assms have "(\<forall>x : P. P x) \<longrightarrow> (\<forall>y : Q. ?P2 y)" by blast
  then show "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>" by fast
qed

lemma Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel:
  assumes "(((O :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rrightarrow> S) \<Rrightarrow> T) U V"
  and "O \<le> O'"
  shows "((O' \<Rrightarrow> S) \<Rrightarrow> T) U V"
proof -
  from assms have "(O' \<Rrightarrow> S) \<le> (O \<Rrightarrow> S)" by blast
  with assms antimonoD[OF antimono_Dep_Fun_Rel_rel_left] show ?thesis
    unfolding Fun_Rel_rel_iff_Dep_Fun_Rel_rel by blast
qed

corollary Fun_Rel_imp_ball_iff_rel_surjective_at_restrict_left:
  "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub> \<longleftrightarrow> rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  by (blast intro: Fun_Rel_restricts_imp_ball_if_rel_surjective_atI
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    rel_surjective_at_restrict_left_if_Fun_Rel_imp_ball)

lemma left_total_on_restrict_right_if_Fun_Rel_rev_imp_ball:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
proof -
  let ?P1 = "in_dom R\<upharpoonleft>\<^bsub>Q\<^esub>"
  have "(R \<Rrightarrow> (\<longleftarrow>)) ?P1 Q" by blast
  with assms have "(\<forall>x : P. ?P1 x) \<longleftarrow> (\<forall>y : Q. Q y)" by blast
  then show "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>" by fast
qed

corollary Fun_Rel_rev_imp_ball_iff_left_total_on_restrict_right:
  "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub> \<longleftrightarrow> left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (blast intro: Fun_Rel_restricts_rev_imp_ball_if_left_total_onI
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    left_total_on_restrict_right_if_Fun_Rel_rev_imp_ball)

lemma bi_total_on_if_Fun_Rel_iff_ball:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "bi_total_on P Q R"
proof (rule bi_total_onI)
  let ?P1 = "in_dom R" and ?P2 = "\<lambda>_. True"
  have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<forall>x : P. ?P1 x) \<longleftrightarrow> (\<forall>y : Q. ?P2 y)" by blast
  then show "left_total_on P R" by fast
next
  let ?P1 = "\<lambda>_. True" and ?P2 = "in_codom R"
  have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<forall>x : P. ?P1 x) \<longleftrightarrow> (\<forall>y : Q. ?P2 y)" by blast
  then show "rel_surjective_at Q R" by fast
qed

corollary Fun_Rel_iff_ball_iff_bi_total_on_if_Fun_Rel_iff:
  assumes "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub> \<longleftrightarrow> bi_total_on P Q R"
  using assms by (blast intro: Fun_Rel_restricts_iff_ball_if_bi_total_on
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    bi_total_on_restricts_if_Fun_Rel_iff_if_bi_total_on
    bi_total_on_if_Fun_Rel_iff_ball)

end

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

corollary Fun_Rel_imp_all_if_rel_surjective:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All"
  using assms by (urule Fun_Rel_restricts_imp_ball_if_rel_surjective_atI)

corollary Fun_Rel_rev_imp_all_if_left_total:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All"
  using assms by (urule Fun_Rel_restricts_rev_imp_ball_if_left_total_onI)

corollary Fun_Rel_iff_all_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  using assms by (urule Fun_Rel_restricts_iff_ball_if_bi_total_on)

corollary rel_surjective_if_Fun_Rel_imp_all:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All"
  shows "rel_surjective R"
  using assms by (urule rel_surjective_at_restrict_left_if_Fun_Rel_imp_ball)

corollary Fun_Rel_imp_all_iff_rel_surjective:
  "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All \<longleftrightarrow> rel_surjective R"
  using rel_surjective_if_Fun_Rel_imp_all Fun_Rel_imp_all_if_rel_surjective by blast

corollary left_total_if_Fun_Rel_rev_imp_all:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All"
  shows "left_total R"
  using assms by (urule left_total_on_restrict_right_if_Fun_Rel_rev_imp_ball)

corollary Fun_Rel_rev_imp_all_iff_left_total:
  "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All \<longleftrightarrow> left_total R"
  using left_total_if_Fun_Rel_rev_imp_all Fun_Rel_rev_imp_all_if_left_total by blast

corollary bi_total_if_Fun_Rel_iff_all:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  shows "bi_total R"
  using assms by (urule bi_total_on_if_Fun_Rel_iff_ball)

corollary Fun_Rel_iff_all_iff_bi_total:
  "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All \<longleftrightarrow> bi_total R"
  using bi_total_if_Fun_Rel_iff_all Fun_Rel_iff_all_if_bi_total by blast

end


end