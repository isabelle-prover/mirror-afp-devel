\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Relators\<close>
theory Function_Relators
  imports
    Predicate_Functions
    Functions_Base
    Predicates_Lattice
    ML_Unification.ML_Unification_HOL_Setup
    ML_Unification.Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of function relators. The slogan of function
relators is "related functions map related inputs to related outputs".\<close>

consts Dep_Fun_Rel_rel :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
consts Dep_Fun_Rel_pred :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
consts Fun_Rel :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"

nonterminal dep_rel_restrict and Dep_Fun_Rel_rel_pttrn and Dep_Fun_Rel_pred_pttrn
open_bundle Dep_Fun_Rel_syntax
begin
notation "Fun_Rel" (infixr \<open>\<Rrightarrow>\<close> 50)
syntax
  "_dep_rel_restrict_if" :: "'a \<Rightarrow> dep_rel_restrict" (\<open>(|/ _)\<close>)
  "_Dep_Fun_Rel_rel" :: "Dep_Fun_Rel_rel_pttrn \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_ \<Rrightarrow>/ _)\<close> [0, 10] 50)
  "_Dep_Fun_Rel_rel_standard" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> Dep_Fun_Rel_rel_pttrn" (\<open>('(_ _ \<Colon> _'))\<close>)
  "_Dep_Fun_Rel_rel_restrict" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> dep_rel_restrict  \<Rightarrow> Dep_Fun_Rel_rel_pttrn" (\<open>('(_ _ \<Colon> _ _'))\<close>)
  "_Dep_Fun_Rel_pred" :: "Dep_Fun_Rel_pred_pttrn \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_ \<Rrightarrow>/ _)\<close> [0, 10] 50)
  "_Dep_Fun_Rel_pred_standard" :: "idt \<Rightarrow> 'a \<Rightarrow> Dep_Fun_Rel_pred_pttrn" (\<open>('(_ : _'))\<close>)
  "_Dep_Fun_Rel_pred_restrict" :: "idt \<Rightarrow> 'a \<Rightarrow> dep_rel_restrict  \<Rightarrow> Dep_Fun_Rel_pred_pttrn" (\<open>('(_ : _ _'))\<close>)
syntax_consts
  "_dep_rel_restrict_if" \<rightleftharpoons> rel_if
  and "_Dep_Fun_Rel_rel" "_Dep_Fun_Rel_rel_standard" "_Dep_Fun_Rel_rel_restrict" \<rightleftharpoons> Dep_Fun_Rel_rel
  and "_Dep_Fun_Rel_pred" "_Dep_Fun_Rel_pred_standard" "_Dep_Fun_Rel_pred_restrict" \<rightleftharpoons> Dep_Fun_Rel_pred
translations
  "(x y \<Colon> R | P) \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel_rel R (\<lambda>x y. CONST rel_if P S)"
  "(x y \<Colon> R) \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel_rel R (\<lambda>x y. S)"
  "(x : P | Q) \<Rrightarrow> R" \<rightleftharpoons> "CONST Dep_Fun_Rel_pred P (\<lambda>x. CONST rel_if Q R)"
  "(x : P) \<Rrightarrow> R" \<rightleftharpoons> "CONST Dep_Fun_Rel_pred P (\<lambda>x. R)"
end

definition "Dep_Fun_Rel_rel_rel R S f g \<equiv> \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y)"
adhoc_overloading Dep_Fun_Rel_rel \<rightleftharpoons> Dep_Fun_Rel_rel_rel

definition "Fun_Rel_rel (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (S :: 'c \<Rightarrow> 'd \<Rightarrow> bool) \<equiv>
  ((_ _ \<Colon> R) \<Rrightarrow> S) :: ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool"
adhoc_overloading Fun_Rel \<rightleftharpoons> Fun_Rel_rel

definition "Dep_Fun_Rel_pred_pred P R f g \<equiv> \<forall>x. P x \<longrightarrow> R x (f x) (g x)"
adhoc_overloading Dep_Fun_Rel_pred \<rightleftharpoons> Dep_Fun_Rel_pred_pred

definition "Fun_Rel_pred (P :: 'a \<Rightarrow> bool) (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool) \<equiv>
  ((_ : P) \<Rrightarrow> R) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool"
adhoc_overloading Fun_Rel \<rightleftharpoons> Fun_Rel_pred

lemma Fun_Rel_rel_eq_Dep_Fun_Rel_rel:
  "((R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rrightarrow> (S :: 'c \<Rightarrow> 'd \<Rightarrow> bool)) = ((_ _ \<Colon> R) \<Rrightarrow> S)"
  unfolding Fun_Rel_rel_def by simp

lemma Fun_Rel_rel_eq_Dep_Fun_Rel_rel_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "\<And>x y. S' x y \<equiv> S"
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
  and "\<And>x. R' x \<equiv> R"
  shows "((P :: 'a \<Rightarrow> bool) \<Rrightarrow> (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool)) = ((x : P') \<Rrightarrow> R' x)"
  using assms by (simp add: Fun_Rel_pred_eq_Dep_Fun_Rel_pred)

lemma Fun_Rel_pred_iff_Dep_Fun_Rel_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rrightarrow> (R :: 'b \<Rightarrow> 'c \<Rightarrow> bool)) f g \<longleftrightarrow> ((_ : P) \<Rrightarrow> R) (f :: 'a \<Rightarrow> 'b) (g :: 'a \<Rightarrow> 'c)"
  by (simp add: Fun_Rel_pred_eq_Dep_Fun_Rel_pred)

lemma Dep_Fun_Rel_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  unfolding Dep_Fun_Rel_rel_rel_def using assms by blast

lemma Dep_Fun_Rel_relD [dest]:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  and "R x y"
  shows "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_rel_rel_def by blast

lemma Dep_Fun_Rel_relE:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  obtains "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_rel_rel_def by blast

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

lemma Dep_Fun_Rel_rel_collect_eq_Dep_Fun_Rel_rel_if [simp]:
  "((x y \<Colon> \<lparr>x y \<Colon> R | P x y\<rparr>) \<Rrightarrow> S x y) = ((x y \<Colon> R | P x y) \<Rrightarrow> S x y)"
  by fastforce

lemma Fun_Rel_rel_collect_eq_Dep_Fun_Rel_rel_if [simp]:
  "(\<lparr>x y \<Colon> R | P x y\<rparr> \<Rrightarrow> S) = ((x y \<Colon> R | P x y) \<Rrightarrow> S)"
  by fastforce

lemma Dep_Fun_Rel_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R x (f x) (g x)"
  shows "((x : P) \<Rrightarrow> R x) f g"
  unfolding Dep_Fun_Rel_pred_pred_def using assms by blast

lemma Dep_Fun_Rel_predD [dest]:
  assumes "((x : P) \<Rrightarrow> R x) f g"
  and "P x"
  shows "R x (f x) (g x)"
  using assms unfolding Dep_Fun_Rel_pred_pred_def by blast

lemma Dep_Fun_Rel_predE:
  assumes "((x : P) \<Rrightarrow> R x) f g"
  obtains "\<And>x. P x \<Longrightarrow> R x (f x) (g x)"
  using assms unfolding Dep_Fun_Rel_pred_pred_def by blast

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

lemma Dep_Fun_Rel_pred_collect_eq_Dep_Fun_Rel_rel_if [simp]:
  "((x : \<lparr>x : P | Q x\<rparr>) \<Rrightarrow> R x) = ((x : P | Q x) \<Rrightarrow> R x)"
  by fastforce

lemma Fun_Rel_pred_collect_eq_Dep_Fun_Rel_rel_if [simp]:
  "(\<lparr>x : P | Q x\<rparr> \<Rrightarrow> R) = ((x : P | Q x) \<Rrightarrow> R)"
  by fastforce

lemma Dep_Fun_Rel_rel_inv_rel_inv_eq [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
  shows "((y x \<Colon> R\<inverse>) \<Rrightarrow> (S x y)\<inverse>) = ((x y \<Colon> R) \<Rrightarrow> S x y)\<inverse>"
  by (intro ext) auto

lemma Dep_Fun_Rel_pred_rel_inv_eq [simp]:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
  shows "((x : P) \<Rrightarrow> (R x)\<inverse>) = ((x : P) \<Rrightarrow> R x)\<inverse>"
  by (intro ext) auto

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
  using assms Dep_Fun_Rel_restrict_left_restrict_left_eq[where ?R="R\<inverse>" and ?S="\<lambda>y x. (S x y)\<inverse>"]
  by simp

end
