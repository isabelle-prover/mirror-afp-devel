\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Monotonicity\<close>
theory Functions_Monotone
  imports
    Binary_Relations_Order_Base
    Function_Relators
    Predicates_Order
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of monotone functions. A function is monotone
if it is related to itself - see \<^term>\<open>Dep_Fun_Rel_rel\<close>.\<close>

declare le_funI[intro]
declare le_funE[elim]

consts dep_mono_wrt_rel :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
consts dep_mono_wrt_pred :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
consts mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

nonterminal dep_pred_restrict and dep_mono_wrt_rel_pttrn and dep_mono_wrt_pred_pttrn
open_bundle dep_mono_wrt_syntax
begin
no_notation disj (infixr \<open>|\<close> 30)
notation "mono_wrt" (infixr \<open>\<Rightarrow>\<close> 50)
syntax
  "_dep_pred_restrict_if" :: "'a \<Rightarrow> dep_pred_restrict" (\<open>(|/ _)\<close>)
  "_dep_mono_wrt_rel" :: "dep_mono_wrt_rel_pttrn \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_ \<Rightarrow>/ _)\<close> [0, 10] 50)
  "_dep_mono_wrt_rel_standard" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> dep_mono_wrt_rel_pttrn" (\<open>('(_ _ \<Colon> _'))\<close>)
  "_dep_mono_wrt_rel_restrict" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> dep_rel_restrict  \<Rightarrow> dep_mono_wrt_rel_pttrn" (\<open>('(_ _ \<Colon> _ _'))\<close>)
  "_dep_mono_wrt_pred" :: "dep_mono_wrt_pred_pttrn \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_ \<Rightarrow>/ _)\<close> [0, 10] 50)
  "_dep_mono_wrt_pred_standard" :: "idt \<Rightarrow> 'a \<Rightarrow> dep_mono_wrt_pred_pttrn" (\<open>('(_ : _'))\<close>)
  "_dep_mono_wrt_pred_restrict" :: "idt \<Rightarrow> 'a \<Rightarrow> dep_pred_restrict  \<Rightarrow> dep_mono_wrt_pred_pttrn" (\<open>('(_ : _ _'))\<close>)
syntax_consts
  "_dep_pred_restrict_if" \<rightleftharpoons> pred_if
  and "_dep_mono_wrt_rel" "_dep_mono_wrt_rel_standard" "_dep_mono_wrt_rel_restrict" \<rightleftharpoons> dep_mono_wrt_rel
  and "_dep_mono_wrt_pred" "_dep_mono_wrt_pred_standard" "_dep_mono_wrt_pred_restrict" \<rightleftharpoons> dep_mono_wrt_pred
translations
  "(x y \<Colon> R | P) \<Rightarrow> S" \<rightleftharpoons> "CONST dep_mono_wrt_rel R (\<lambda>x y. CONST rel_if P S)"
  "(x y \<Colon> R) \<Rightarrow> S" \<rightleftharpoons> "CONST dep_mono_wrt_rel R (\<lambda>x y. S)"
  "(x : P | Q) \<Rightarrow> U" \<rightleftharpoons> "CONST dep_mono_wrt_pred P (\<lambda>x. CONST pred_if Q U)"
  "(x : P) \<Rightarrow> Q" \<rightleftharpoons> "CONST dep_mono_wrt_pred P (\<lambda>x. Q)"
end

definition "dep_mono_wrt_rel_rel (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
  (S :: 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<equiv> ((x y \<Colon> R) \<Rrightarrow> S x y) f f"
adhoc_overloading dep_mono_wrt_rel \<rightleftharpoons> dep_mono_wrt_rel_rel

definition "mono_wrt_rel (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool) \<equiv>
  ((_ _ \<Colon> R) \<Rightarrow> S) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool"
adhoc_overloading mono_wrt \<rightleftharpoons> mono_wrt_rel

definition "dep_mono_wrt_pred_pred (P :: 'a \<Rightarrow> bool) (Q :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<equiv>
  ((x : P) \<Rrightarrow> (\<lambda>(_ :: 'b). Q x)) f f"
adhoc_overloading dep_mono_wrt_pred \<rightleftharpoons> dep_mono_wrt_pred_pred

definition "mono_wrt_pred (P :: 'a \<Rightarrow> bool) (Q :: 'b \<Rightarrow> bool) \<equiv>
  (((_ :: 'a) : P) \<Rightarrow> Q) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool"
adhoc_overloading mono_wrt \<rightleftharpoons> mono_wrt_pred

lemma mono_wrt_rel_eq_dep_mono_wrt_rel:
  "((R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) = ((_ _ \<Colon> R) \<Rightarrow> S)"
  unfolding mono_wrt_rel_def by simp

lemma mono_wrt_rel_eq_dep_mono_wrt_rel_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "\<And>x y. S' x y \<equiv> S"
  shows "((R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) = ((x y \<Colon> R') \<Rightarrow> S' x y)"
  using assms by (simp add: mono_wrt_rel_eq_dep_mono_wrt_rel)

lemma mono_wrt_rel_iff_dep_mono_wrt_rel:
  "((R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) f \<longleftrightarrow>
    dep_mono_wrt_rel R (\<lambda>(_ :: 'a) (_ :: 'a). S) (f :: 'a \<Rightarrow> 'b)"
  by (simp add: mono_wrt_rel_eq_dep_mono_wrt_rel)

lemma mono_wrt_pred_eq_dep_mono_wrt_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rightarrow> (Q :: 'b \<Rightarrow> bool)) = (((_ :: 'a) : P) \<Rightarrow> Q)"
  unfolding mono_wrt_pred_def by simp

lemma mono_wrt_pred_eq_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> P'"
  and "\<And>x. Q \<equiv> Q' x"
  shows "((P :: 'a \<Rightarrow> bool) \<Rightarrow> (Q :: 'b \<Rightarrow> bool)) = (((x : P') \<Rightarrow> Q' x) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool)"
  using assms by (simp add: mono_wrt_pred_eq_dep_mono_wrt_pred)

lemma mono_wrt_pred_iff_dep_mono_wrt_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rightarrow> (Q :: 'b \<Rightarrow> bool)) f \<longleftrightarrow> (((_ :: 'a) : P) \<Rightarrow> Q) (f :: 'a \<Rightarrow> 'b)"
  by (simp add: mono_wrt_pred_eq_dep_mono_wrt_pred)

lemma dep_mono_wrt_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y)"
  shows "((x y \<Colon> R) \<Rightarrow> S x y) f"
  using assms unfolding dep_mono_wrt_rel_rel_def by blast

lemma dep_mono_wrt_relE:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  obtains "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y)"
  using assms unfolding dep_mono_wrt_rel_rel_def by blast

lemma dep_mono_wrt_relD [dest]:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "R x y"
  shows "S x y (f x) (f y)"
  using assms unfolding dep_mono_wrt_rel_rel_def by blast

lemma dep_mono_wrt_rel_cong [cong]:
  assumes "R = R'"
  and "\<And>x y. R' x y \<Longrightarrow> S x y = S' x y"
  shows "((x y \<Colon> R) \<Rightarrow> S x y) = ((x y \<Colon> R') \<Rightarrow> S' x y)"
  using assms by force

lemma mono_wrt_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  shows "(R \<Rightarrow> S) f"
  using assms by (urule dep_mono_wrt_relI)

lemma mono_wrt_relE:
  assumes "(R \<Rightarrow> S) f"
  obtains "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  using assms by (urule (e) dep_mono_wrt_relE)

lemma mono_wrt_relD [dest]:
  assumes "(R \<Rightarrow> S) f"
  and "R x y"
  shows "S (f x) (f y)"
  using assms by (urule dep_mono_wrt_relD)

lemma dep_mono_wrt_rel_collect_eq_dep_mono_wrt_rel_if [simp]:
  "((x y \<Colon> \<lparr>x y \<Colon> R | P x y\<rparr>) \<Rightarrow> S x y) = ((x y \<Colon> R | P x y) \<Rightarrow> S x y)"
  by fastforce

lemma mono_wrt_rel_collect_eq_dep_mono_wrt_rel_if [simp]:
  "(\<lparr>x y \<Colon> R | P x y\<rparr> \<Rightarrow> S) = ((x y \<Colon> R | P x y) \<Rightarrow> S)"
  by fastforce

lemma dep_mono_wrt_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> Q x (f x)"
  shows "((x : P) \<Rightarrow> Q x) f"
  using assms unfolding dep_mono_wrt_pred_pred_def by blast

lemma dep_mono_wrt_predE:
  assumes "((x : P) \<Rightarrow> Q x) f"
  obtains "\<And>x. P x \<Longrightarrow> Q x (f x)"
  using assms unfolding dep_mono_wrt_pred_pred_def by blast

lemma dep_mono_wrt_predD [dest]:
  assumes "((x : P) \<Rightarrow> Q x) f"
  and "P x"
  shows "Q x (f x)"
  using assms unfolding dep_mono_wrt_pred_pred_def by blast

lemma dep_mono_wrt_pred_cong [cong]:
  assumes "P = P'"
  and "\<And>x. P' x \<Longrightarrow> Q x = Q' x"
  shows "((x : P) \<Rightarrow> Q x) = ((x : P') \<Rightarrow> Q' x)"
  using assms by force

lemma dep_mono_wrt_pred_codom_iff_cong:
  assumes "P = P'"
  and "\<And>x. P' x \<Longrightarrow> Q x (f x) \<longleftrightarrow> Q' x (f' x)"
  shows "((x : P) \<Rightarrow> Q x) f \<longleftrightarrow> ((x : P') \<Rightarrow> Q' x) f'"
  using assms by force

lemma mono_wrt_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> Q (f x)"
  shows "(P \<Rightarrow> Q) f"
  using assms by (urule dep_mono_wrt_predI)

lemma mono_wrt_predE:
  assumes "(P \<Rightarrow> Q) f"
  obtains "\<And>x. P x \<Longrightarrow> Q (f x)"
  using assms by (urule (e) dep_mono_wrt_predE)

lemma mono_wrt_predD [dest]:
  assumes "(P \<Rightarrow> Q) f"
  and "P x"
  shows "Q (f x)"
  using assms by (urule dep_mono_wrt_predD)

lemma Dep_Fun_Rel_pred_collect_eq_Dep_Fun_Rel_pred_if [simp]:
  "((x : \<lparr>x : P | Q x\<rparr>) \<Rightarrow> R x) = ((x : P | Q x) \<Rightarrow> R x)"
  by fastforce

lemma Fun_Rel_pred_collect_eq_Dep_Fun_Rel_pred_if [simp]:
  "(\<lparr>x : P | Q x\<rparr> \<Rightarrow> R) = ((x : P | Q x) \<Rightarrow> R)"
  by fastforce

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  and P :: "'a \<Rightarrow> bool" and Q :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

lemma dep_mono_wrt_rel_if_Dep_Fun_Rel_rel_self:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f f"
  shows "((x y \<Colon> R) \<Rightarrow> S x y) f"
  using assms by blast

lemma dep_mono_wrt_pred_if_Dep_Fun_Rel_pred_self:
  assumes "((x : P) \<Rrightarrow> (\<lambda>_. Q x)) f f"
  shows "((x : P) \<Rightarrow> Q x) f"
  using assms by blast

lemma Dep_Fun_Rel_rel_self_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y) f f"
  using assms by blast

lemma Dep_Fun_Rel_pred_self_if_dep_mono_wrt_pred:
  assumes "((x : P) \<Rightarrow> Q x) f"
  shows "((x : P) \<Rrightarrow> (\<lambda>_. Q x)) f f"
  using assms by blast

corollary Dep_Fun_Rel_rel_self_iff_dep_mono_wrt_rel:
  "((x y \<Colon> R) \<Rrightarrow> S x y) f f \<longleftrightarrow> ((x y \<Colon> R) \<Rightarrow> S x y) f"
  using dep_mono_wrt_rel_if_Dep_Fun_Rel_rel_self
    Dep_Fun_Rel_rel_self_if_dep_mono_wrt_rel by blast

corollary Dep_Fun_Rel_pred_self_iff_dep_mono_wrt_pred:
  "((x : P) \<Rrightarrow> (\<lambda>(_ :: 'b). Q x)) f f \<longleftrightarrow> ((x : P) \<Rightarrow> Q x) f"
  using dep_mono_wrt_pred_if_Dep_Fun_Rel_pred_self
    Dep_Fun_Rel_pred_self_if_dep_mono_wrt_pred by blast

lemma dep_mono_wrt_rel_eq_Dep_Fun_Rel_rel [uhint]:
  assumes "R \<equiv> R'"
  and "\<And>x y. S x y \<equiv> S' x y"
  and "f \<equiv> f'"
  shows "((x y \<Colon> R) \<Rightarrow> S x y) f \<equiv> ((x y \<Colon> R') \<Rrightarrow> S' x y) f' f'"
  using assms unfolding Dep_Fun_Rel_rel_self_iff_dep_mono_wrt_rel atomize_eq by auto

lemma dep_mono_wrt_pred_eq_Dep_Fun_Rel_pred [uhint]:
  assumes "P \<equiv> P'"
  and "\<And>x y. Q x y \<equiv> Q' x y y"
  and "f \<equiv> f'"
  shows "((x : P) \<Rightarrow> Q x) f \<equiv> ((x : P') \<Rrightarrow> Q' x) f' f'"
  using assms unfolding Dep_Fun_Rel_pred_self_iff_dep_mono_wrt_pred atomize_eq by auto

lemma dep_mono_wrt_rel_inv_inv_eq [simp]:
  "((y x \<Colon> R\<inverse>) \<Rightarrow> (S x y)\<inverse>) = ((x y \<Colon> R) \<Rightarrow> S x y)"
  by (intro ext) force

lemma in_dom_if_rel_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "R x y"
  shows "in_dom (S x y) (f x)"
  using assms by (intro in_domI) blast

end

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
begin

lemma mono_wrt_rel_eq_Fun_Rel_rel [uhint]:
  assumes "R \<equiv> R'"
  and "S \<equiv> S'"
  and "f \<equiv> f'"
  shows "(R \<Rightarrow> S) f \<equiv> (R' \<Rrightarrow> S') f' f'"
  using assms by (urule dep_mono_wrt_rel_eq_Dep_Fun_Rel_rel)

lemma mono_wrt_pred_eq_Fun_Rel_pred [uhint]:
  assumes "P :: _ \<Rightarrow> bool \<equiv> P'"
  and "\<And>y. Q y \<equiv> Q' y y"
  and "f \<equiv> f'"
  shows "(P \<Rightarrow> Q) f \<equiv> (P' \<Rrightarrow> Q') f' f'"
  using assms by (urule dep_mono_wrt_pred_eq_Dep_Fun_Rel_pred)

corollary in_dom_if_in_dom_if_mono_wrt_rel:
  assumes "(R \<Rightarrow> S) f"
  shows "(in_dom R \<Rightarrow> in_dom S) f"
  using assms in_dom_if_rel_if_dep_mono_wrt_rel by fast

lemma in_codom_if_rel_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "R x y"
  shows "in_codom (S x y) (f y)"
  using assms by (intro in_codomI) blast

corollary in_codom_if_in_codom_if_mono_wrt_rel:
  assumes "(R \<Rightarrow> S) f"
  shows "(in_codom R \<Rightarrow> in_codom S) f"
  using assms in_dom_if_rel_if_dep_mono_wrt_rel
  by fast

corollary in_field_if_in_field_if_mono_wrt_rel:
  assumes "(R \<Rightarrow> S) f"
  shows "(in_field R \<Rightarrow> in_field S) f"
  using assms by fast

lemma le_rel_map_if_mono_wrt_rel:
  assumes "(R \<Rightarrow> S) f"
  shows "R \<le> rel_map f S"
  using assms by (intro le_relI) auto

lemma le_pred_map_if_mono_wrt_pred:
  assumes "(P \<Rightarrow> Q) f"
  shows "P \<le> pred_map f Q"
  using assms by (intro le_predI) auto

lemma mono_wrt_rel_if_le_rel_map:
  assumes "R \<le> rel_map f S"
  shows "(R \<Rightarrow> S) f"
  using assms by (intro mono_wrt_relI) auto

lemma mono_wrt_pred_if_le_pred_map:
  assumes "P \<le> pred_map f Q"
  shows "(P \<Rightarrow> Q) f"
  using assms by (intro mono_wrt_predI) auto

corollary mono_wrt_rel_iff_le_rel_map: "(R \<Rightarrow> S) f \<longleftrightarrow> R \<le> rel_map f S"
  using mono_wrt_rel_if_le_rel_map le_rel_map_if_mono_wrt_rel by auto

corollary mono_wrt_pred_iff_le_pred_map: "(P \<Rightarrow> Q) f \<longleftrightarrow> P \<le> pred_map f Q"
  using mono_wrt_pred_if_le_pred_map le_pred_map_if_mono_wrt_pred by auto

end

lemma dep_mono_comp_iff_dep_mono_if_all_app_eq:
  assumes "\<And>x. A x \<Longrightarrow> f (m x) = g x"
  shows "((x : (A :: _ \<Rightarrow> bool)) \<Rightarrow> B x) (f \<circ> m) \<longleftrightarrow> ((x : A) \<Rightarrow> B x) g"
  using assms by fastforce

lemma dep_mono_pred_map_comp_iff_dep_mono_if_all_app_eq:
  assumes "\<And>x y. A x \<Longrightarrow> B x y \<Longrightarrow> f x (m y) = g x y"
  shows "((x : A) \<Rightarrow> pred_map (\<lambda>f. f \<circ> m) ((y : B x) \<Rightarrow> C x y)) f
    \<longleftrightarrow> ((x : A) \<Rightarrow> (y : (B x :: _ \<Rightarrow> bool)) \<Rightarrow> C x y) g"
  using assms by (simp cong: dep_mono_wrt_pred_codom_iff_cong)

definition "mono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool
  \<equiv> (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ((\<le>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"

lemma mono_eq_mono_wrt_le [simp]: "(mono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool) =
  (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ((\<le>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"
  unfolding mono_def by simp

lemma mono_eq_mono_wrt_le_uhint [uhint]:
  assumes "R \<equiv> (\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  and "S \<equiv> (\<le>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool"
  shows "mono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool \<equiv> (R \<Rightarrow> S)"
  using assms by simp

lemma mono_iff_mono_wrt_le [iff]: "mono f \<longleftrightarrow> ((\<le>) \<Rightarrow> (\<le>)) f" by simp

lemma monoI [intro]:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "mono f"
  using assms by (urule mono_wrt_relI)

lemma monoE [elim]:
  assumes "mono f"
  obtains "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  using assms by (urule (e) mono_wrt_relE)

lemma monoD:
  assumes "mono f"
  and "x \<le> y"
  shows "f x \<le> f y"
  using assms by (urule mono_wrt_relD)

definition "antimono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool
  \<equiv> (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ((\<ge>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"

lemma antimono_eq_mono_wrt_le_ge [simp]: "(antimono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool) =
  (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ((\<ge>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"
  unfolding antimono_def by simp

lemma antimono_eq_mono_wrt_le_ge_uhint [uhint]:
  assumes "R \<equiv> (\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  and "S \<equiv> (\<ge>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool"
  shows "antimono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool \<equiv> (R \<Rightarrow> S)"
  using assms by simp

lemma antimono_iff_mono_wrt_le_ge [iff]: "antimono f \<longleftrightarrow> ((\<le>) \<Rightarrow> (\<ge>)) f" by simp

lemma antimonoI [intro]:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<ge> f y"
  shows "antimono f"
  by (urule mono_wrt_relI) (urule assms)

lemma antimonoE [elim]:
  assumes "antimono f"
  obtains "\<And>x y. x \<le> y \<Longrightarrow> f x \<ge> f y"
  using assms by (urule (e) mono_wrt_relE)

lemma antimonoD:
  assumes "antimono f"
  and "x \<le> y"
  shows "f x \<ge> f y"
  using assms by (urule mono_wrt_relD)

lemma antimono_Dep_Fun_Rel_rel_left: "antimono (\<lambda>(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool). ((x y \<Colon> R) \<Rrightarrow> S x y))"
  by (intro antimonoI) auto

lemma antimono_Dep_Fun_Rel_pred_left: "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). ((x : P) \<Rrightarrow> Q x))"
  by (intro antimonoI) auto

lemma antimono_dep_mono_wrt_rel_left: "antimono (\<lambda>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool). ((x y \<Colon> R) \<Rightarrow> S x y))"
  by (intro antimonoI) blast

lemma antimono_dep_mono_wrt_pred_left: "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). ((x : P) \<Rightarrow> Q x))"
  by (intro antimonoI) blast

lemma Dep_Fun_Rel_rel_if_le_left_if_Dep_Fun_Rel_rel:
  fixes R R' :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  and "R' \<le> R"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  using assms by blast

lemma Dep_Fun_Rel_pred_if_le_left_if_Dep_Fun_Rel_pred:
  fixes P P' :: "'a \<Rightarrow> bool"
  assumes "((x : P) \<Rrightarrow> Q x) f g"
  and "P' \<le> P"
  shows "((x : P') \<Rrightarrow> Q x) f g"
  using assms by blast

lemma dep_mono_wrt_rel_if_le_left_if_dep_mono_wrt_rel:
  fixes R R' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "R' \<le> R"
  shows "((x y \<Colon> R') \<Rightarrow> S x y) f"
  using assms by blast

lemma dep_mono_wrt_pred_if_le_left_if_dep_mono_wrt_pred:
  fixes P P' :: "'a \<Rightarrow> bool"
  assumes "((x : P) \<Rightarrow> Q x) f"
  and "P' \<le> P"
  shows "((x : P') \<Rightarrow> Q x) f"
  using assms by blast

lemma mono_Dep_Fun_Rel_rel_right: "mono (\<lambda>(S :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool). ((x y \<Colon> R) \<Rrightarrow> S x y))"
  by (intro monoI) blast

lemma mono_Dep_Fun_Rel_pred_right: "mono (\<lambda>(Q :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool). ((x : P) \<Rrightarrow> Q x))"
  by (intro monoI) blast

lemma mono_dep_mono_wrt_rel_right: "mono (\<lambda>(S :: 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool). ((x y \<Colon> R) \<Rightarrow> S x y))"
  by (intro monoI) blast

lemma mono_dep_mono_wrt_pred_right: "mono (\<lambda>(Q :: 'a \<Rightarrow> 'b \<Rightarrow> bool). ((x : P) \<Rightarrow> Q x))"
  by (intro monoI) blast

lemma Dep_Fun_Rel_rel_if_le_right_if_Dep_Fun_Rel_rel:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y) \<Longrightarrow> T x y (f x) (g y)"
  shows "((x y \<Colon> R) \<Rrightarrow> T x y) f g"
  using assms by (intro Dep_Fun_Rel_relI) blast

lemma Dep_Fun_Rel_pred_if_le_right_if_Dep_Fun_Rel_pred:
  assumes "((x : P) \<Rrightarrow> Q x) f g"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) (g x) \<Longrightarrow> T x (f x) (g x)"
  shows "((x : P) \<Rrightarrow> T x) f g"
  using assms by blast

lemma dep_mono_wrt_rel_if_le_right_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y) \<Longrightarrow> T x y (f x) (f y)"
  shows "((x y \<Colon> R) \<Rightarrow> T x y) f"
  using assms by (intro dep_mono_wrt_relI) blast

lemma dep_mono_wrt_pred_if_le_right_if_dep_mono_wrt_pred:
  assumes "((x : P) \<Rightarrow> Q x) f"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> T x (f x)"
  shows "((x : P) \<Rightarrow> T x) f"
  using assms by blast


paragraph \<open>Composition\<close>

lemma dep_mono_wrt_rel_compI:
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> ((x' y' \<Colon> T x y) \<Rightarrow> U x y x' y') f'"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y) \<Longrightarrow> T x y (f x) (f y)"
  shows "((x y \<Colon> R) \<Rightarrow> U x y (f x) (f y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_relI) force

corollary dep_mono_wrt_rel_compI':
  assumes "((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> ((x' y' \<Colon> S x y) \<Rightarrow> T x y x' y') f'"
  shows "((x y \<Colon> R) \<Rightarrow> T x y (f x) (f y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_rel_compI)

lemma dep_mono_wrt_pred_comp_dep_mono_wrt_rel_compI:
  assumes "((x : P) \<Rightarrow> Q x) f"
  and "\<And>x. P x \<Longrightarrow> ((x' y' \<Colon> R x) \<Rightarrow> S x x' y') f'"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> R x (f x) (f x)"
  shows "((x : P) \<Rightarrow> (\<lambda>y. S x (f x) (f x) y y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_predI) force

lemma dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI:
  assumes "((x : P) \<Rightarrow> Q x) f"
  and "\<And>x. P x \<Longrightarrow> ((x' : R x) \<Rightarrow> S x x') f'"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> R x (f x)"
  shows "((x : P) \<Rightarrow> S x (f x)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_predI) force

corollary dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI':
  assumes "((x : P) \<Rightarrow> Q x) f"
  and "\<And>x. P x \<Longrightarrow> ((x' : Q x) \<Rightarrow> S x x') f'"
  shows "((x : P) \<Rightarrow> S x (f x)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI)

lemma mono_wrt_rel_top [iff]:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  shows "(R \<Rightarrow> (\<top> :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) f"
  by auto

lemma mono_wrt_pred_top [iff]:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  shows "(P \<Rightarrow> (\<top> :: 'b \<Rightarrow> bool)) f"
  by auto

paragraph \<open>Instantiations\<close>

lemma mono_wrt_rel_self_id:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  shows "(R \<Rightarrow> R) (id :: 'a \<Rightarrow> 'a)"
  by auto

lemma mono_wrt_pred_self_id:
  fixes P :: "'a \<Rightarrow> bool"
  shows "(P \<Rightarrow> P) (id :: 'a \<Rightarrow> 'a)"
  by auto

lemma mono_dep_mono_wrt_dep_mono_wrt_comp:
  "(((x : (B :: 'b \<Rightarrow> bool)) \<Rightarrow> C x) \<Rightarrow> (f : A \<Rightarrow> B) \<Rightarrow> (x : A) \<Rightarrow> C (f x)) (\<circ>)"
  by force

lemma mono_wrt_dep_mono_wrt_dep_fun_map:
  fixes A :: "'a \<Rightarrow> bool"
  shows "((f : A \<Rightarrow> B) \<Rightarrow> ((x : A) \<Rightarrow> (y : B) \<Rightarrow> (z : C (f x)) \<Rightarrow> D x y z) \<Rightarrow>
    (h : (x : B) \<Rightarrow> C x) \<Rightarrow> (x : A) \<Rightarrow> D x (f x) (h (f x))) dep_fun_map"
  by fastforce

lemma mono_wrt_dep_mono_wrt_fun_map:
  fixes A :: "'a \<Rightarrow> bool"
  shows "((f : A \<Rightarrow> B) \<Rightarrow> ((x : C) \<Rightarrow> D x) \<Rightarrow> (h : B \<Rightarrow> C) \<Rightarrow> (x : A) \<Rightarrow> D (h (f x))) fun_map"
  by fastforce

lemma mono_in_dom: "mono in_dom" by (intro monoI) fast
lemma mono_in_codom: "mono in_codom" by (intro monoI) fast
lemma mono_in_field: "mono in_field" by (intro monoI) fast
lemma mono_rel_comp: "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (\<circ>\<circ>)" by (intro mono_wrt_relI Fun_Rel_relI le_relI) fast
lemma mono_rel_inv: "mono rel_inv" by (intro monoI) fast

lemma mono_rel_restrict_left:
  "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (rel_restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI le_relI) fastforce

lemma mono_rel_restrict_right:
  "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (rel_restrict_right :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI le_relI) fastforce

lemma mono_ball: "((\<ge>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) ball" by fast
lemma mono_bex: "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) bex" by fast

end
