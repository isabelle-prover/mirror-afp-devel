\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lattice\<close>
theory Binary_Relations_Lattice
  imports
    Binary_Relations_Order_Base
    HOL.Boolean_Algebras
begin

paragraph \<open>Summary\<close>
text \<open>Basic results about the lattice structure on binary relations.\<close>

lemma rel_infI [intro]:
  assumes "R x y"
  and "S x y"
  shows "(R \<sqinter> S) x y"
  using assms by (rule inf2I)

lemma rel_infE [elim]:
  assumes "(R \<sqinter> S) x y"
  obtains "R x y" "S x y"
  using assms by (rule inf2E)

lemma rel_infD:
  assumes "(R \<sqinter> S) x y"
  shows "R x y" and "S x y"
  using assms by auto

lemma in_dom_rel_infI [intro]:
  assumes "R x y"
  and "S x y"
  shows "in_dom (R \<sqinter> S) x"
  using assms by blast

lemma in_dom_rel_infE [elim]:
  assumes "in_dom (R \<sqinter> S) x"
  obtains y where "R x y" "S x y"
  using assms by blast

lemma in_codom_rel_infI [intro]:
  assumes "R x y"
  and "S x y"
  shows "in_codom (R \<sqinter> S) y"
  using assms by blast

lemma in_codom_rel_infE [elim]:
  assumes "in_codom (R \<sqinter> S) y"
  obtains x where "R x y" "S x y"
  using assms by blast

lemma in_field_eq_in_dom_sup_in_codom: "in_field L = (in_dom L \<squnion> in_codom L)"
  by (intro ext) (simp add: in_field_iff_in_dom_or_in_codom)

lemma in_dom_restrict_left_eq [simp]: "in_dom R\<restriction>\<^bsub>P\<^esub> = (in_dom R \<sqinter> P)"
  by (intro ext) auto

lemma in_codom_restrict_left_eq [simp]: "in_codom R\<upharpoonleft>\<^bsub>P\<^esub> = (in_codom R \<sqinter> P)"
  by (intro ext) auto

lemma restrict_left_restrict_left_eq [simp]:
  fixes R :: "'a \<Rightarrow> _" and P Q :: "'a \<Rightarrow> bool"
  shows "R\<restriction>\<^bsub>P\<^esub>\<restriction>\<^bsub>Q\<^esub> = R\<restriction>\<^bsub>P\<^esub> \<sqinter> R\<restriction>\<^bsub>Q\<^esub>"
  by (intro ext iffI restrict_leftI) auto

lemma restrict_left_restrict_right_eq [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
  shows "R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> = R\<restriction>\<^bsub>P\<^esub> \<sqinter> R\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (intro ext iffI restrict_leftI restrict_rightI) auto

lemma restrict_right_restrict_left_eq [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'b \<Rightarrow> bool" and Q :: "'a \<Rightarrow> bool"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub>\<restriction>\<^bsub>Q\<^esub> = R\<upharpoonleft>\<^bsub>P\<^esub> \<sqinter> R\<restriction>\<^bsub>Q\<^esub>"
  by (intro ext iffI restrict_leftI restrict_rightI) auto

lemma restrict_right_restrict_right_eq [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P Q :: "'b \<Rightarrow> bool"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> = R\<upharpoonleft>\<^bsub>P\<^esub> \<sqinter> R\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (intro ext iffI) auto

lemma restrict_left_sup_eq [simp]: "(R :: 'a \<Rightarrow> _)\<restriction>\<^bsub>((P :: 'a \<Rightarrow> bool) \<squnion> Q)\<^esub> = R\<restriction>\<^bsub>P\<^esub> \<squnion> R\<restriction>\<^bsub>Q\<^esub> "
  by (intro antisym le_relI) (auto elim!: restrict_leftE)

lemma restrict_left_inf_eq [simp]: "(R :: 'a \<Rightarrow> _)\<restriction>\<^bsub>((P :: 'a \<Rightarrow> bool) \<sqinter> Q)\<^esub> = R\<restriction>\<^bsub>P\<^esub> \<sqinter> R\<restriction>\<^bsub>Q\<^esub> "
  by (intro antisym le_relI) (auto elim!: restrict_leftE)

lemma inf_rel_bimap_and_eq_restrict_left_restrict_right:
  "R \<sqinter> (rel_bimap P Q (\<and>)) = R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (intro ext) auto


end
