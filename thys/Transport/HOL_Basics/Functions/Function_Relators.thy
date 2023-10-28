\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Relators\<close>
theory Function_Relators
  imports
    Binary_Relation_Functions
    Functions_Base
    Predicates_Lattice
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of function relators. The slogan of function
relators is "related functions map related inputs to related outputs".\<close>

definition "Dep_Fun_Rel_rel R S f g \<equiv> \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y)"

abbreviation "Fun_Rel_rel R S \<equiv> Dep_Fun_Rel_rel R (\<lambda>_ _. S)"

definition "Dep_Fun_Rel_pred P R f g \<equiv> \<forall>x. P x \<longrightarrow> R x (f x) (g x)"

abbreviation "Fun_Rel_pred P R \<equiv> Dep_Fun_Rel_pred P (\<lambda>_. R)"

bundle Dep_Fun_Rel_syntax begin
syntax
  "_Fun_Rel_rel" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("(_) \<Rrightarrow> (_)" [41, 40] 40)
  "_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [41, 41, 41, 40] 40)
  "_Dep_Fun_Rel_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _/ |/ _] \<Rrightarrow> (_)" [41, 41, 41, 41, 40] 40)
  "_Fun_Rel_pred" :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> bool" ("[_] \<Rrightarrow> (_)" [41, 40] 40)
  "_Dep_Fun_Rel_pred" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" ("[_/ \<Colon>/ _] \<Rrightarrow> (_)" [41, 41, 40] 40)
  "_Dep_Fun_Rel_pred_if" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" ("[_/ \<Colon>/ _/ |/ _] \<Rrightarrow> (_)" [41, 41, 41, 40] 40)
end
bundle no_Dep_Fun_Rel_syntax begin
no_syntax
  "_Fun_Rel_rel" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("(_) \<Rrightarrow> (_)" [41, 40] 40)
  "_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [41, 41, 41, 40] 40)
  "_Dep_Fun_Rel_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _/ |/ _] \<Rrightarrow> (_)" [41, 41, 41, 41, 40] 40)
  "_Fun_Rel_pred" :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> bool" ("[_] \<Rrightarrow> (_)" [41, 40] 40)
  "_Dep_Fun_Rel_pred" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" ("[_/ \<Colon>/ _] \<Rrightarrow> (_)" [41, 41, 40] 40)
  "_Dep_Fun_Rel_pred_if" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" ("[_/ \<Colon>/ _/ |/ _] \<Rrightarrow> (_)" [41, 41, 41, 40] 40)
end
unbundle Dep_Fun_Rel_syntax
translations
  "R \<Rrightarrow> S" \<rightleftharpoons> "CONST Fun_Rel_rel R S"
  "[x y \<Colon> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel_rel R (\<lambda>x y. S)"
  "[x y \<Colon> R | B] \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel_rel R (\<lambda>x y. CONST rel_if B S)"
  "[P] \<Rrightarrow> R" \<rightleftharpoons> "CONST Fun_Rel_pred P R"
  "[x \<Colon> P] \<Rrightarrow> R" \<rightleftharpoons> "CONST Dep_Fun_Rel_pred P (\<lambda>x. R)"
  "[x \<Colon> P | B] \<Rrightarrow> R" \<rightleftharpoons> "CONST Dep_Fun_Rel_pred P (\<lambda>x. CONST rel_if B R)"

lemma Dep_Fun_Rel_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  unfolding Dep_Fun_Rel_rel_def using assms by blast

lemma Dep_Fun_Rel_relD:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "R x y"
  shows "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_rel_def by blast

lemma Dep_Fun_Rel_relE [elim]:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "R x y"
  obtains "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_rel_def by blast

lemma Dep_Fun_Rel_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R x (f x) (g x)"
  shows "([x \<Colon> P] \<Rrightarrow> R x) f g"
  unfolding Dep_Fun_Rel_pred_def using assms by blast

lemma Dep_Fun_Rel_predD:
  assumes "([x \<Colon> P] \<Rrightarrow> R x) f g"
  and "P x"
  shows "R x (f x) (g x)"
  using assms unfolding Dep_Fun_Rel_pred_def by blast

lemma Dep_Fun_Rel_predE [elim]:
  assumes "([x \<Colon> P] \<Rrightarrow> R x) f g"
  and "P x"
  obtains "R x (f x) (g x)"
  using assms unfolding Dep_Fun_Rel_pred_def by blast

lemma rel_inv_Dep_Fun_Rel_rel_eq [simp]:
  "([x y \<Colon> R] \<Rrightarrow> S x y)\<inverse> = ([y x \<Colon> R\<inverse>] \<Rrightarrow> (S x y)\<inverse>)"
  by (intro ext) auto

lemma rel_inv_Dep_Fun_Rel_pred_eq [simp]:
  "([x \<Colon> P] \<Rrightarrow> R x)\<inverse> = ([x \<Colon> P] \<Rrightarrow> (R x)\<inverse>)"
  by (intro ext) auto

lemma Dep_Fun_Rel_pred_eq_Dep_Fun_Rel_rel:
  "([x \<Colon> P] \<Rrightarrow> R x) = ([x _ \<Colon> (((\<sqinter>) P) \<circ> (=))] \<Rrightarrow> R x)"
  by (intro ext) (auto intro!: Dep_Fun_Rel_predI Dep_Fun_Rel_relI)

lemma Fun_Rel_eq_eq_eq [simp]: "((=) \<Rrightarrow> (=)) = (=)"
  by (intro ext) auto


paragraph \<open>Composition\<close>

lemma Dep_Fun_Rel_rel_compI:
  assumes Dep_Fun_Rel1: "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and Dep_Fun_Rel2: "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> T x y] \<Rrightarrow> U x y x' y') f' g'"
  and le: "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y) \<Longrightarrow> T x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> U x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_relI) (auto 6 0)

corollary Dep_Fun_Rel_rel_compI':
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> S x y] \<Rrightarrow> T x y x' y') f' g'"
  shows "([x y \<Colon> R] \<Rrightarrow> T x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_rel_compI)

lemma Dep_Fun_Rel_pred_comp_Dep_Fun_Rel_rel_compI:
  assumes Dep_Fun_Rel1: "([x \<Colon> P] \<Rrightarrow> R x) f g"
  and Dep_Fun_Rel2: "\<And>x. P x \<Longrightarrow> ([x' y' \<Colon> S x] \<Rrightarrow> T x x' y') f' g'"
  and le: "\<And>x. P x \<Longrightarrow> R x (f x) (g x) \<Longrightarrow> S x (f x) (g x)"
  shows "([x \<Colon> P] \<Rrightarrow> T x (f x) (g x)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_predI) (auto 6 0)

corollary Dep_Fun_Rel_pred_comp_Dep_Fun_Rel_rel_compI':
  assumes "([x \<Colon> P] \<Rrightarrow> R x) f g"
  and "\<And>x. P x \<Longrightarrow> ([x' y' \<Colon> R x] \<Rrightarrow> S x x' y') f' g'"
  shows "([x \<Colon> P] \<Rrightarrow> S x (f x) (g x)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_pred_comp_Dep_Fun_Rel_rel_compI)


paragraph \<open>Restrictions\<close>

lemma restrict_left_Dep_Fun_Rel_rel_restrict_left_eq:
  fixes R :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and S :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and P :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b1 \<Rightarrow> bool"
  assumes "\<And>f x y. Q f \<Longrightarrow> R x y \<Longrightarrow> P x y (f x)"
  shows "([x y \<Colon> R] \<Rrightarrow> (S x y)\<restriction>\<^bsub>P x y\<^esub>)\<restriction>\<^bsub>Q\<^esub> = ([x y \<Colon> R] \<Rrightarrow> S x y)\<restriction>\<^bsub>Q\<^esub>"
  using assms by (intro ext iffI restrict_leftI Dep_Fun_Rel_relI)
  (auto dest!: Dep_Fun_Rel_relD)

lemma restrict_right_Dep_Fun_Rel_rel_restrict_right_eq:
  fixes R :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and S :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and P :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  assumes "\<And>f x y. Q f \<Longrightarrow> R x y \<Longrightarrow> P x y (f y)"
  shows "(([x y \<Colon> R] \<Rrightarrow> (S x y)\<upharpoonleft>\<^bsub>P x y\<^esub>)\<upharpoonleft>\<^bsub>Q\<^esub>) = (([x y \<Colon> R] \<Rrightarrow> S x y)\<upharpoonleft>\<^bsub>Q\<^esub>)"
  unfolding restrict_right_eq
  using assms restrict_left_Dep_Fun_Rel_rel_restrict_left_eq[where ?R="R\<inverse>"
    and ?S="\<lambda>y x. (S x y)\<inverse>"]
  by simp


end