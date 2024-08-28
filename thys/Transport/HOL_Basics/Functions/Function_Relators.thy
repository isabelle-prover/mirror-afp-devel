\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Relators\<close>
theory Function_Relators
  imports
    Binary_Relation_Functions
    Functions_Base
    Predicates_Lattice
    ML_Unification.ML_Unification_HOL_Setup
    ML_Unification.Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of function relators. The slogan of function
relators is "related functions map related inputs to related outputs".\<close>

consts Dep_Fun_Rel :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
consts Fun_Rel :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"

bundle Dep_Fun_Rel_syntax begin
syntax
  "_Fun_Rel" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool" (infixr "\<Rrightarrow>" 50)
  "_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _') \<Rrightarrow> (_)" [51, 51, 50, 50] 50)
  "_Dep_Fun_Rel_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _/ |/ _') \<Rrightarrow> (_)" [51, 51, 50, 50, 50] 50)
  "_Dep_Fun_Rel_pred" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ :/ _') \<Rrightarrow> (_)" [51, 50, 50] 50)
  "_Dep_Fun_Rel_pred_if" :: "idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ :/ _/ |/ _') \<Rrightarrow> (_)" [51, 50, 50, 50] 50)
end
bundle no_Dep_Fun_Rel_syntax begin
no_syntax
  "_Fun_Rel" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool" (infixr "\<Rrightarrow>" 50)
  "_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _') \<Rrightarrow> (_)" [51, 51, 50, 50] 50)
  "_Dep_Fun_Rel_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _/ |/ _') \<Rrightarrow> (_)" [51, 51, 50, 50, 50] 50)
  "_Dep_Fun_Rel_pred" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ :/ _') \<Rrightarrow> (_)" [51, 50, 50] 50)
  "_Dep_Fun_Rel_pred_if" :: "idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    ("'(_/ :/ _/ |/ _') \<Rrightarrow> (_)" [51, 50, 50, 50] 50)
end
unbundle Dep_Fun_Rel_syntax
syntax_consts
  "_Fun_Rel" \<rightleftharpoons> Fun_Rel and
  "_Dep_Fun_Rel_rel" "_Dep_Fun_Rel_rel_if" "_Dep_Fun_Rel_pred" "_Dep_Fun_Rel_pred_if" \<rightleftharpoons> Dep_Fun_Rel
translations
  "R \<Rrightarrow> S" \<rightleftharpoons> "CONST Fun_Rel R S"
  "(x y \<Colon> R) \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel R (\<lambda>x y. S)"
  "(x y \<Colon> R | B) \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel R (\<lambda>x y. CONST rel_if B S)"
  "(x : P) \<Rrightarrow> R" \<rightleftharpoons> "CONST Dep_Fun_Rel P (\<lambda>x. R)"
  "(x : P | B) \<Rrightarrow> R" \<rightleftharpoons> "CONST Dep_Fun_Rel P (\<lambda>x. CONST rel_if B R)"

definition "Dep_Fun_Rel_rel R S f g \<equiv> \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y)"
adhoc_overloading Dep_Fun_Rel Dep_Fun_Rel_rel

definition "Fun_Rel_rel (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (S :: 'c \<Rightarrow> 'd \<Rightarrow> bool) \<equiv>
  ((_ _ \<Colon> R) \<Rrightarrow> S) :: ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool"
adhoc_overloading Fun_Rel Fun_Rel_rel

definition "Dep_Fun_Rel_pred P R f g \<equiv> \<forall>x. P x \<longrightarrow> R x (f x) (g x)"
adhoc_overloading Dep_Fun_Rel Dep_Fun_Rel_pred

definition "Fun_Rel_pred (P :: 'a \<Rightarrow> bool) (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool) \<equiv>
  ((_ : P) \<Rrightarrow> R) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool"
adhoc_overloading Fun_Rel Fun_Rel_pred

lemma Fun_Rel_rel_eq_Dep_Fun_Rel_rel:
  "((R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rrightarrow> (S :: 'c \<Rightarrow> 'd \<Rightarrow> bool)) = ((_ _ \<Colon> R) \<Rrightarrow> S)"
  unfolding Fun_Rel_rel_def by simp

lemma Fun_Rel_rel_eq_Dep_Fun_Rel_rel_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "S' \<equiv> (\<lambda>(_ :: 'a) (_ :: 'b). S)"
  shows "((R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rrightarrow> (S :: 'c \<Rightarrow> 'd \<Rightarrow> bool)) = ((x y \<Colon> R') \<Rrightarrow> S' x y)"
  using assms by (simp add: Fun_Rel_rel_eq_Dep_Fun_Rel_rel)

lemma Fun_Rel_rel_iff_Dep_Fun_Rel_rel:
  "((R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rrightarrow> (S :: 'c \<Rightarrow> 'd \<Rightarrow> bool)) f g \<longleftrightarrow> ((_ _ \<Colon> R) \<Rrightarrow> S) f g"
  by (simp add: Fun_Rel_rel_eq_Dep_Fun_Rel_rel)

lemma Fun_Rel_pred_eq_Dep_Fun_Rel_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rrightarrow> (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool)) = ((_ : P) \<Rrightarrow> R)"
  unfolding Fun_Rel_pred_def by simp

lemma Fun_Rel_pred_eq_Dep_Fun_Rel_pred_uhint [uhint]:
  assumes "P \<equiv> P'"
  and "R' \<equiv> (\<lambda>(_ :: 'a). R)"
  shows "((P :: 'a \<Rightarrow> bool) \<Rrightarrow> (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool)) = ((x : P') \<Rrightarrow> R' x)"
  using assms by (simp add: Fun_Rel_pred_eq_Dep_Fun_Rel_pred)

lemma Fun_Rel_pred_iff_Dep_Fun_Rel_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rrightarrow> (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool)) f g \<longleftrightarrow> ((_ : P) \<Rrightarrow> R) (f :: 'a \<Rightarrow> 'b) (g :: 'a \<Rightarrow> 'c)"
  by (simp add: Fun_Rel_pred_eq_Dep_Fun_Rel_pred)

lemma Dep_Fun_Rel_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  unfolding Dep_Fun_Rel_rel_def using assms by blast

lemma Dep_Fun_Rel_relD [dest]:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  and "R x y"
  shows "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_rel_def by blast

lemma Dep_Fun_Rel_relE:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  obtains "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_rel_def by blast

lemma Dep_Fun_Rel_rel_cong [cong]:
  assumes "R = R'"
  and "\<And>x y. R' x y \<Longrightarrow> S x y = S' x y"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y) = ((x y \<Colon> R') \<Rrightarrow> S' x y)"
  using assms by force

lemma Fun_Rel_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  shows "(R \<Rrightarrow> S) f g"
  using assms by (urule Dep_Fun_Rel_relI)

lemma Fun_Rel_relD [dest]:
  assumes "(R \<Rrightarrow> S) f g"
  and "R x y"
  shows "S (f x) (g y)"
  using assms by (urule Dep_Fun_Rel_relD)

lemma Fun_Rel_relE:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  obtains "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  using assms by (urule (e) Dep_Fun_Rel_relE)

lemma Dep_Fun_Rel_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R x (f x) (g x)"
  shows "((x : P) \<Rrightarrow> R x) f g"
  unfolding Dep_Fun_Rel_pred_def using assms by blast

lemma Dep_Fun_Rel_predD [dest]:
  assumes "((x : P) \<Rrightarrow> R x) f g"
  and "P x"
  shows "R x (f x) (g x)"
  using assms unfolding Dep_Fun_Rel_pred_def by blast

lemma Dep_Fun_Rel_predE:
  assumes "((x : P) \<Rrightarrow> R x) f g"
  obtains "\<And>x. P x \<Longrightarrow> R x (f x) (g x)"
  using assms unfolding Dep_Fun_Rel_pred_def by blast

lemma Dep_Fun_Rel_pred_cong [cong]:
  assumes "P = P'"
  and "\<And>x. P' x \<Longrightarrow> R x = R' x"
  shows "((x : P) \<Rrightarrow> R x) = ((x : P') \<Rrightarrow> R' x)"
  using assms by force

lemma Fun_Rel_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R (f x) (g x)"
  shows "(P \<Rrightarrow> R) f g"
  using assms by (urule Dep_Fun_Rel_predI)

lemma Fun_Rel_predD [dest]:
  assumes "(P \<Rrightarrow> R) f g"
  and "P x"
  shows "R (f x) (g x)"
  using assms by (urule Dep_Fun_Rel_predD)

lemma Fun_Rel_predE:
  assumes "(P \<Rrightarrow> R) f g"
  obtains "\<And>x. P x \<Longrightarrow> R (f x) (g x)"
  using assms by (urule (e) Dep_Fun_Rel_predE)

lemma rel_inv_Dep_Fun_Rel_rel_eq [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y)\<inverse> = ((y x \<Colon> R\<inverse>) \<Rrightarrow> (S x y)\<inverse>)"
  by (intro ext) auto

lemma rel_inv_rel_inv_Dep_Fun_Rel_rel_iff_Dep_Fun_Rel_rel [iff]:
  "((x y \<Colon> R\<inverse>) \<Rrightarrow> (S x y)\<inverse>) f g \<longleftrightarrow> ((x y \<Colon> R) \<Rrightarrow> (S y x)) g f"
  by (simp flip: rel_inv_Dep_Fun_Rel_rel_eq)

lemma rel_inv_Dep_Fun_Rel_pred_eq [simp]:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
  shows "((x : P) \<Rrightarrow> R x)\<inverse> = ((x : P) \<Rrightarrow> (R x)\<inverse>)"
  by (intro ext) auto

lemma rel_inv_Dep_Fun_Rel_pred_iff_Dep_Fun_Rel_pred [iff]:
  "((x : P) \<Rrightarrow> (R x)\<inverse>) f g \<longleftrightarrow> ((x : P) \<Rrightarrow> (R x)) g f"
  by (simp flip: rel_inv_Dep_Fun_Rel_pred_eq)

lemma Dep_Fun_Rel_pred_eq_Dep_Fun_Rel_rel:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
  shows "((x : P) \<Rrightarrow> R x) = ((x (_ :: 'a) \<Colon> (((\<sqinter>) P) \<circ> (=))) \<Rrightarrow> R x)"
  by (intro ext) (auto intro!: Dep_Fun_Rel_predI Dep_Fun_Rel_relI)

lemma Fun_Rel_eq_eq_eq [simp]: "((=) \<Rrightarrow> (=)) = (=)"
  by (intro ext) auto


paragraph \<open>Composition\<close>

lemma Dep_Fun_Rel_rel_compI:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> ((x' y' \<Colon> T x y) \<Rrightarrow> U x y x' y') f' g'"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y) \<Longrightarrow> T x y (f x) (g y)"
  shows "((x y \<Colon> R) \<Rrightarrow> U x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_relI) (auto 6 0)

corollary Dep_Fun_Rel_rel_compI':
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> ((x' y' \<Colon> S x y) \<Rrightarrow> T x y x' y') f' g'"
  shows "((x y \<Colon> R) \<Rrightarrow> T x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_rel_compI)

lemma Dep_Fun_Rel_pred_comp_Dep_Fun_Rel_rel_compI:
  assumes "((x : P) \<Rrightarrow> R x) f g"
  and "\<And>x. P x \<Longrightarrow> ((x' y' \<Colon> S x) \<Rrightarrow> T x x' y') f' g'"
  and "\<And>x. P x \<Longrightarrow> R x (f x) (g x) \<Longrightarrow> S x (f x) (g x)"
  shows "((x : P) \<Rrightarrow> T x (f x) (g x)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_predI) (auto 6 0)

corollary Dep_Fun_Rel_pred_comp_Dep_Fun_Rel_rel_compI':
  assumes "((x : P) \<Rrightarrow> R x) f g"
  and "\<And>x. P x \<Longrightarrow> ((x' y' \<Colon> R x) \<Rrightarrow> S x x' y') f' g'"
  shows "((x : P) \<Rrightarrow> S x (f x) (g x)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (intro Dep_Fun_Rel_pred_comp_Dep_Fun_Rel_rel_compI)


paragraph \<open>Restrictions\<close>

lemma Dep_Fun_Rel_restrict_left_restrict_left_eq:
  assumes "\<And>f x y. Q f \<Longrightarrow> R x y \<Longrightarrow> P x y (f x)"
  shows "((x y \<Colon> R) \<Rrightarrow> (S x y)\<restriction>\<^bsub>P x y\<^esub>)\<restriction>\<^bsub>Q\<^esub> = ((x y \<Colon> R) \<Rrightarrow> S x y)\<restriction>\<^bsub>Q\<^esub>"
  using assms by (intro ext iffI rel_restrict_leftI Dep_Fun_Rel_relI)
  (auto dest!: Dep_Fun_Rel_relD)

lemma Dep_Fun_Rel_restrict_right_restrict_right_eq:
  assumes "\<And>f x y. Q f \<Longrightarrow> R x y \<Longrightarrow> P x y (f y)"
  shows "((x y \<Colon> R) \<Rrightarrow> (S x y)\<upharpoonleft>\<^bsub>P x y\<^esub>)\<upharpoonleft>\<^bsub>Q\<^esub> = (((x y \<Colon> R) \<Rrightarrow> S x y)\<upharpoonleft>\<^bsub>Q\<^esub>)"
  unfolding rel_restrict_right_eq
  using assms
    Dep_Fun_Rel_restrict_left_restrict_left_eq[where ?R="R\<inverse>" and ?S="\<lambda>y x. (S x y)\<inverse>"]
  by simp


end