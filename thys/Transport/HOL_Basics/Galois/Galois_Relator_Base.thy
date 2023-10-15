\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basics For Relator For Galois Connections\<close>
theory Galois_Relator_Base
  imports
    Galois_Base
begin

locale galois_rel = orders L R
  for L :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
  and r :: "'d \<Rightarrow> 'b"
begin

text \<open>Morally speaking, the Galois relator characterises when two terms
\<^term>\<open>x :: 'a\<close> and \<^term>\<open>y :: 'b\<close> are "similar".\<close>

definition "Galois x y \<equiv> in_codom (\<le>\<^bsub>R\<^esub>) y \<and> x \<le>\<^bsub>L\<^esub> r y"

abbreviation "left_Galois \<equiv> Galois"
notation left_Galois (infix "\<^bsub>L\<^esub>\<lessapprox>" 50)

abbreviation (input) "ge_Galois_left \<equiv> (\<^bsub>L\<^esub>\<lessapprox>)\<inverse>"
notation ge_Galois_left (infix "\<greaterapprox>\<^bsub>L\<^esub>" 50)

text \<open>Here we only introduced the (left) Galois relator @{term "(\<^bsub>L\<^esub>\<lessapprox>)"}.
All other variants can be introduced by considering suitable flipped and inversed
interpretations (see @{file "Half_Galois_Property.thy"}).\<close>

lemma left_GaloisI [intro]:
  assumes "in_codom (\<le>\<^bsub>R\<^esub>) y"
  and "x \<le>\<^bsub>L\<^esub> r y"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y"
  unfolding Galois_def using assms by blast

lemma left_GaloisE [elim]:
  assumes "x \<^bsub>L\<^esub>\<lessapprox> y"
  obtains "in_codom (\<le>\<^bsub>R\<^esub>) y" "x \<le>\<^bsub>L\<^esub> r y"
  using assms unfolding Galois_def by blast

corollary in_dom_left_if_left_Galois:
  assumes "x \<^bsub>L\<^esub>\<lessapprox> y"
  shows "in_dom (\<le>\<^bsub>L\<^esub>) x"
  using assms by blast

corollary left_Galois_iff_in_codom_and_left_rel_right:
  "x \<^bsub>L\<^esub>\<lessapprox> y \<longleftrightarrow> in_codom (\<le>\<^bsub>R\<^esub>) y \<and> x \<le>\<^bsub>L\<^esub> r y"
  by blast

lemma left_Galois_restrict_left_eq_left_Galois_left_restrict_left:
  "(\<^bsub>L\<^esub>\<lessapprox>)\<restriction>\<^bsub>P :: 'a \<Rightarrow> bool\<^esub> = galois_rel.Galois (\<le>\<^bsub>L\<^esub>)\<restriction>\<^bsub>P\<^esub> (\<le>\<^bsub>R\<^esub>) r"
  by (intro ext iffI galois_rel.left_GaloisI restrict_leftI)
  (auto elim: galois_rel.left_GaloisE)

lemma left_Galois_restrict_right_eq_left_Galois_right_restrict_right:
  "(\<^bsub>L\<^esub>\<lessapprox>)\<upharpoonleft>\<^bsub>P :: 'd \<Rightarrow> bool\<^esub> = galois_rel.Galois (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>)\<upharpoonleft>\<^bsub>P\<^esub> r"
  by (intro ext iffI galois_rel.left_GaloisI restrict_rightI)
  (auto elim!: galois_rel.left_GaloisE restrict_rightE)

end


end