\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nils Harmsen"\<close>
section \<open>Properties of Galois Relator for White-Box Transport Side Conditions\<close>
theory Transport_Galois_Relator_Properties
  imports
    Binary_Relations_Bi_Total
    Binary_Relations_Bi_Unique
    Galois_Connections
    Galois_Relator
begin

paragraph \<open>Summary\<close>
text \<open>Properties of Galois relator arising as side conditions for white-box transport.\<close>

context galois
begin

paragraph \<open>Right-Uniqueness\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma right_unique_at_left_Galois_if_right_unique_at_rightI:
  assumes "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "right_unique_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (auto dest: right_unique_atD)

lemma right_unique_at_right_if_right_unique_at_left_GaloisI:
  assumes "right_unique_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (blast dest: right_unique_atD)

corollary right_unique_at_left_Galois_iff_right_unique_at_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_at Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms right_unique_at_left_Galois_if_right_unique_at_rightI
    right_unique_at_right_if_right_unique_at_left_GaloisI
  by blast

corollary right_unique_on_left_Galois_if_right_unique_at_rightI:
  assumes "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "right_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro right_unique_on_if_Fun_Rel_imp_if_right_unique_at)
  (blast intro: right_unique_at_left_Galois_if_right_unique_at_rightI)

corollary right_unique_at_right_if_right_unique_on_left_GaloisI:
  assumes "right_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) P Q"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro right_unique_at_right_if_right_unique_at_left_GaloisI
    right_unique_at_if_Fun_Rel_rev_imp_if_right_unique_on)

corollary right_unique_on_left_Galois_iff_right_unique_at_rightI:
  assumes "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms right_unique_on_left_Galois_if_right_unique_at_rightI
    right_unique_at_right_if_right_unique_on_left_GaloisI
  by blast

end

corollary right_unique_left_Galois_if_right_unique_rightI:
  assumes "right_unique (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "right_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule right_unique_at_left_Galois_if_right_unique_at_rightI)

corollary right_unique_right_if_right_unique_left_GaloisI:
  assumes "right_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule right_unique_at_right_if_right_unique_at_left_GaloisI)

corollary right_unique_left_Galois_iff_right_unique_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms right_unique_left_Galois_if_right_unique_rightI
    right_unique_right_if_right_unique_left_GaloisI
  by blast


paragraph \<open>Injectivity\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma injective_on_left_Galois_if_rel_injective_on_left:
  assumes "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  shows "rel_injective_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (auto dest: rel_injective_onD)

lemma rel_injective_on_left_if_injective_on_left_GaloisI:
  assumes "rel_injective_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro rel_injective_onI) (blast dest!: rel_injective_onD)

corollary injective_on_left_Galois_iff_rel_injective_on_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms injective_on_left_Galois_if_rel_injective_on_left
    rel_injective_on_left_if_injective_on_left_GaloisI
  by blast

corollary injective_at_left_Galois_if_rel_injective_on_leftI:
  assumes "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "rel_injective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro rel_injective_at_if_Fun_Rel_rev_imp_if_rel_injective_on)
  (blast intro: injective_on_left_Galois_if_rel_injective_on_left)

corollary rel_injective_on_left_if_injective_at_left_GaloisI:
  assumes "rel_injective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro rel_injective_on_left_if_injective_on_left_GaloisI
    rel_injective_on_if_Fun_Rel_imp_if_rel_injective_at)

corollary injective_at_left_Galois_iff_rel_injective_on_leftI:
  assumes "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_at Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms injective_at_left_Galois_if_rel_injective_on_leftI
    rel_injective_on_left_if_injective_at_left_GaloisI
  by blast

end

corollary injective_left_Galois_if_rel_injective_left:
  assumes "rel_injective (\<le>\<^bsub>L\<^esub>)"
  shows "rel_injective (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule injective_on_left_Galois_if_rel_injective_on_left)

corollary rel_injective_left_if_injective_left_GaloisI:
  assumes "rel_injective (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows  "rel_injective (\<le>\<^bsub>L\<^esub>)"
  using assms by (urule rel_injective_on_left_if_injective_on_left_GaloisI)

corollary rel_injective_left_Galois_iff_rel_injective_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective (\<le>\<^bsub>L\<^esub>)"
  using assms injective_left_Galois_if_rel_injective_left
    rel_injective_left_if_injective_left_GaloisI
  by blast


paragraph \<open>Bi-Uniqueness\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

corollary bi_unique_on_left_Galois_if_right_unique_at_right_if_rel_injective_on_leftI:
  assumes "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  and "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms
  by (intro bi_unique_onI right_unique_on_left_Galois_if_right_unique_at_rightI
    injective_on_left_Galois_if_rel_injective_on_left)

corollary rel_injective_on_left_and_right_unique_at_right_if_bi_unique_on_left_GaloisI:
  assumes "bi_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<le>\<^bsub>L\<^esub>) \<and> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro conjI rel_injective_on_left_if_injective_on_left_GaloisI
    right_unique_at_right_if_right_unique_on_left_GaloisI)
  auto

corollary bi_unique_on_left_Galois_iff_rel_injective_on_left_and_right_unique_at_rightI:
  assumes "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective_on P (\<le>\<^bsub>L\<^esub>) \<and> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms bi_unique_on_left_Galois_if_right_unique_at_right_if_rel_injective_on_leftI
    rel_injective_on_left_and_right_unique_at_right_if_bi_unique_on_left_GaloisI
  by blast

end

corollary bi_unique_left_Galois_if_right_unique_right_if_rel_injective_leftI:
  assumes "rel_injective (\<le>\<^bsub>L\<^esub>)"
  and "right_unique (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  by (urule (rr) bi_unique_on_left_Galois_if_right_unique_at_right_if_rel_injective_on_leftI assms)
  auto

corollary rel_injective_left_and_right_unique_right_if_bi_unique_left_GaloisI:
  assumes "bi_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective (\<le>\<^bsub>L\<^esub>) \<and> right_unique (\<le>\<^bsub>R\<^esub>)"
  by (urule (rr) rel_injective_on_left_and_right_unique_at_right_if_bi_unique_on_left_GaloisI assms)
  auto

corollary bi_unique_left_Galois_iff_rel_injective_left_and_right_unique_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective (\<le>\<^bsub>L\<^esub>) \<and> right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms bi_unique_left_Galois_if_right_unique_right_if_rel_injective_leftI
    rel_injective_left_and_right_unique_right_if_bi_unique_left_GaloisI
  by blast


paragraph \<open>Surjectivity\<close>

context
  fixes Q :: "'b \<Rightarrow> bool"
begin

lemma surjective_at_left_Galois_if_rel_surjective_at_rightI:
  assumes "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro rel_surjective_atI) fast

lemma rel_surjective_at_right_if_surjective_at_left_Galois:
  assumes "rel_surjective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro rel_surjective_atI) (auto)

corollary rel_surjective_at_right_iff_surjective_at_left_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective_at Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms surjective_at_left_Galois_if_rel_surjective_at_rightI
    rel_surjective_at_right_if_surjective_at_left_Galois
  by blast

end

corollary surjective_left_Galois_if_rel_surjective_rightI:
  assumes "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule surjective_at_left_Galois_if_rel_surjective_at_rightI)

corollary rel_surjective_right_if_surjective_left_Galois:
  assumes "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule rel_surjective_at_right_if_surjective_at_left_Galois)

corollary rel_surjective_right_iff_surjective_left_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms surjective_left_Galois_if_rel_surjective_rightI
    rel_surjective_right_if_surjective_left_Galois
  by blast


paragraph \<open>Left-Totality\<close>

context
  fixes P :: "'a \<Rightarrow> bool"
begin

lemma left_total_on_left_Galois_if_left_total_on_leftI:
  assumes "left_total_on P (\<le>\<^bsub>L\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro left_total_onI) force

lemma left_total_on_left_if_left_total_on_left_GaloisI:
  assumes "left_total_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "left_total_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro left_total_onI) auto

corollary left_total_on_left_Galois_iff_left_total_on_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total_on P (\<le>\<^bsub>L\<^esub>)"
  using assms left_total_on_left_Galois_if_left_total_on_leftI
    left_total_on_left_if_left_total_on_left_GaloisI
  by blast

end

corollary left_total_left_Galois_if_left_total_leftI:
  assumes "left_total (\<le>\<^bsub>L\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule left_total_on_left_Galois_if_left_total_on_leftI)

corollary left_total_left_if_left_total_left_Galois:
  assumes "left_total (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "left_total (\<le>\<^bsub>L\<^esub>)"
  using assms by (urule left_total_on_left_if_left_total_on_left_GaloisI)

corollary left_total_left_Galois_iff_left_total_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total (\<le>\<^bsub>L\<^esub>)"
  using assms left_total_left_Galois_if_left_total_leftI
    left_total_left_if_left_total_left_Galois
  by blast


paragraph \<open>Bi-Totality\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma bi_total_on_left_GaloisI:
  assumes "left_total_on P (\<le>\<^bsub>L\<^esub>)"
  and "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total_on P Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms surjective_at_left_Galois_if_rel_surjective_at_rightI
    left_total_on_left_Galois_if_left_total_on_leftI
  by blast

lemma left_total_on_left_rel_surjective_at_right_if_bi_total_on_left_GaloisE:
  assumes "bi_total_on P Q (\<^bsub>L\<^esub>\<lessapprox>)"
  obtains "left_total_on P (\<le>\<^bsub>L\<^esub>)" "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms rel_surjective_at_right_if_surjective_at_left_Galois
    left_total_on_left_if_left_total_on_left_GaloisI
  by auto

corollary bi_total_on_left_Galois_iff_left_total_on_left_and_rel_surjective_on_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total_on P Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total_on P (\<le>\<^bsub>L\<^esub>) \<and> rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms bi_total_on_left_GaloisI
    left_total_on_left_rel_surjective_at_right_if_bi_total_on_left_GaloisE
  by blast

end

corollary bi_total_left_GaloisI:
  assumes "left_total (\<le>\<^bsub>L\<^esub>)"
  and "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule bi_total_on_left_GaloisI)

corollary left_total_left_rel_surjective_right_if_bi_total_left_GaloisE:
  assumes "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  obtains "left_total (\<le>\<^bsub>L\<^esub>)" "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule (e) left_total_on_left_rel_surjective_at_right_if_bi_total_on_left_GaloisE)

corollary bi_total_left_Galois_iff_left_total_left_and_rel_surjective_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total (\<le>\<^bsub>L\<^esub>) \<and> rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms bi_total_left_GaloisI
    left_total_left_rel_surjective_right_if_bi_total_left_GaloisE
  by blast


paragraph \<open>Function Relator\<close>

lemma Fun_Rel_left_Galois_left_Galois_imp_left_rightI:
  assumes monol: "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and half_gal: "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and perR: "partial_equivalence_rel (\<le>\<^bsub>R\<^esub>)"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>)"
proof (intro Fun_Rel_relI impI)
  fix x y x' y'
  assume "x \<^bsub>L\<^esub>\<lessapprox> y" "x' \<^bsub>L\<^esub>\<lessapprox> y'" "x \<le>\<^bsub>L\<^esub> x'"
  with half_gal have "l x' \<le>\<^bsub>R\<^esub> y'" by auto
  with \<open>x \<le>\<^bsub>L\<^esub> x'\<close> monol perR have "l x \<le>\<^bsub>R\<^esub> y'" by blast
  with \<open>x \<^bsub>L\<^esub>\<lessapprox> y\<close> half_gal perR have "y \<le>\<^bsub>R\<^esub> l x" by (blast dest: symmetricD)
  with perR \<open>l x \<le>\<^bsub>R\<^esub> y'\<close> show "y \<le>\<^bsub>R\<^esub> y'" by blast
qed

lemma Fun_Rel_left_Galois_left_Galois_rev_imp_left_rightI:
  assumes monor: "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and perL: "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>)"
proof (intro Fun_Rel_relI rev_impI)
  fix x y x' y'
  assume "x \<^bsub>L\<^esub>\<lessapprox> y" and "x' \<^bsub>L\<^esub>\<lessapprox> y'" and "y \<le>\<^bsub>R\<^esub> y'"
  with monor perL have "x \<le>\<^bsub>L\<^esub> r y'" by fastforce
  with  \<open>x' \<^bsub>L\<^esub>\<lessapprox> y'\<close> have "x' \<le>\<^bsub>L\<^esub> r y'" by auto
  with perL \<open>x \<le>\<^bsub>L\<^esub> r y'\<close> show "x \<le>\<^bsub>L\<^esub> x'" by (blast dest: symmetricD)
qed

corollary Fun_Rel_left_Galois_left_Galois_iff_left_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>R\<^esub>)"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>)"
  using assms Fun_Rel_left_Galois_left_Galois_imp_left_rightI
    Fun_Rel_left_Galois_left_Galois_rev_imp_left_rightI
  by (intro Fun_Rel_relI) blast

end


end