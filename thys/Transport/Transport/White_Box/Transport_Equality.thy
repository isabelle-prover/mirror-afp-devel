\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nils Harmsen"\<close>
section \<open>White-Box Transport of (Restricted) Equality\<close>
theory Transport_Equality
  imports
    Restricted_Equality
    Binary_Relations_Bi_Unique
begin

paragraph \<open>Summary\<close>
text \<open>Theorems for white-box transports of (restricted) equalities.\<close>

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_imp_eq_restrict_if_right_unique_onI:
  assumes runique: "right_unique_on P R"
  and rel: "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Fun_Rel_relI impI)
  fix x x' y y'
  assume "R x y" "R x' y'" "x =\<^bsub>P\<^esub> x'"
  moreover with rel have "R x y'" "Q y'" by auto
  ultimately show "y =\<^bsub>Q\<^esub> y'" using runique by (auto dest: right_unique_onD)
qed

lemma Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI:
  assumes rinjective: "rel_injective_at Q R"
  and rel: "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Fun_Rel_relI rev_impI)
  fix x x' y y'
  assume "R x y" "R x' y'" "y =\<^bsub>Q\<^esub> y'"
  moreover with rel have "R x y'" "P x" by auto
  ultimately show "x =\<^bsub>P\<^esub> x'" using rinjective by (auto dest: rel_injective_atD)
qed

corollary Fun_Rel_iff_eq_restrict_if_bi_unique_onI:
  assumes bi_unique: "bi_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof -
  from assms have "(R \<Rrightarrow> (\<longrightarrow>)) P Q" "(R \<Rrightarrow> (\<longleftarrow>)) P Q" "bi_unique_on Q R\<inverse>"
    using bi_unique_on_rel_inv_if_Fun_Rel_iff_if_bi_unique_on by auto
  with bi_unique Fun_Rel_imp_eq_restrict_if_right_unique_onI
    Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI
    have "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" by auto
  then show ?thesis by blast
qed

lemma right_unique_on_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=)"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) auto

lemma Fun_Rel_imp_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) ((S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  using assms by (intro Fun_Rel_relI) blast

corollary Fun_Rel_imp_eq_restrict_iff_right_unique_on_and_Fun_Rel_imp:
  "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>) \<longleftrightarrow> (right_unique_on P R \<and> (R \<Rrightarrow> (\<longrightarrow>)) P Q)"
  using Fun_Rel_imp_eq_restrict_if_right_unique_onI
    right_unique_on_if_Fun_Rel_imp_eq_restrict Fun_Rel_imp_if_Fun_Rel_imp_eq_restrict
  by blast

lemma rel_injective_at_if_Fun_Rel_rev_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=\<^bsub>Q\<^esub>)"
  shows "rel_injective_at Q R"
  using assms by (intro rel_injective_atI) auto

lemma Fun_Rel_rev_imp_if_Fun_Rel_rev_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) ((S :: 'a \<Rightarrow> 'a \<Rightarrow> bool)\<restriction>\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  using assms by (intro Fun_Rel_relI rev_impI) auto

corollary Fun_Rel_rev_imp_eq_restrict_iff_rel_injective_at_and_Fun_Rel_rev_imp:
  "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>) \<longleftrightarrow> (rel_injective_at Q R \<and> (R \<Rrightarrow> (\<longleftarrow>)) P Q)"
  using Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI
    rel_injective_at_if_Fun_Rel_rev_imp_eq_restrict Fun_Rel_rev_imp_if_Fun_Rel_rev_imp_eq_restrict
  by blast

lemma bi_unique_on_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "bi_unique_on P R"
  using assms by (intro bi_unique_onI) blast+

lemma Fun_Rel_iff_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  using assms by (intro Fun_Rel_relI) blast

corollary Fun_Rel_iff_eq_restrict_iff_bi_unique_on_and_Fun_Rel_iff:
  "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>) \<longleftrightarrow> (bi_unique_on P R \<and> (R \<Rrightarrow> (\<longleftrightarrow>)) P Q)"
  using Fun_Rel_iff_eq_restrict_if_bi_unique_onI
    bi_unique_on_if_Fun_Rel_iff_eq_restrict Fun_Rel_iff_if_Fun_Rel_iff_eq_restrict
  by blast

end

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

corollary Fun_Rel_imp_eq_if_right_unique:
  assumes "right_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_imp_eq_restrict_if_right_unique_onI) auto

corollary Fun_Rel_rev_imp_eq_if_rel_injective:
  assumes "rel_injective R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI) auto

corollary Fun_Rel_iff_eq_if_bi_unique:
  assumes "bi_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_iff_eq_restrict_if_bi_unique_onI) auto

corollary right_unique_if_Fun_Rel_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  shows "right_unique R"
  using assms by (urule right_unique_on_if_Fun_Rel_imp_eq_restrict)

corollary Fun_Rel_imp_eq_iff_right_unique: "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=) \<longleftrightarrow> right_unique R"
  using right_unique_if_Fun_Rel_imp_eq Fun_Rel_imp_eq_if_right_unique by blast

corollary rel_injective_if_Fun_Rel_rev_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  shows "rel_injective R"
  using assms by (urule rel_injective_at_if_Fun_Rel_rev_imp_eq_restrict)

corollary Fun_Rel_rev_imp_eq_iff_rel_injective: "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=) \<longleftrightarrow> rel_injective R"
  using rel_injective_if_Fun_Rel_rev_imp_eq Fun_Rel_rev_imp_eq_if_rel_injective by blast

corollary bi_unique_if_Fun_Rel_iff_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  shows "bi_unique R"
  using assms by (urule bi_unique_on_if_Fun_Rel_iff_eq_restrict)

corollary Fun_Rel_iff_eq_iff_bi_unique: "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=) \<longleftrightarrow> bi_unique R"
  using bi_unique_if_Fun_Rel_iff_eq Fun_Rel_iff_eq_if_bi_unique by blast

end

end