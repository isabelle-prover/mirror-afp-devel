\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Monotonicity\<close>
theory Functions_Monotone
  imports
    Binary_Relations_Order_Base
    Function_Relators
    Predicate_Functions
    Predicates_Order
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of monotone functions. A function is monotone
if it is related to itself - see \<^term>\<open>Dep_Fun_Rel_rel\<close>.\<close>

declare le_funI[intro]
declare le_funE[elim]

consts dep_mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
consts mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

bundle dep_mono_wrt_syntax begin
syntax
  "_mono_wrt" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("(_) \<Rrightarrow>\<^sub>m (_)" [41, 40] 40)
  "_dep_mono_wrt_rel" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40] 40)
  "_dep_mono_wrt_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _/ |/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40, 40] 40)
  "_dep_mono_wrt_pred" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("'(_/ :/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 40] 40)
  "_dep_mono_wrt_pred_if" :: "idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
    ("'(_/ :/ _/ |/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 40, 40] 40)
end
bundle no_dep_mono_wrt_syntax begin
no_syntax
  "_mono_wrt" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("(_) \<Rrightarrow>\<^sub>m (_)" [41, 40] 40)
  "_dep_mono_wrt_rel" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40] 40)
  "_dep_mono_wrt_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
    ("'(_/ _/ \<Colon>/ _/ |/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40, 40] 40)
  "_dep_mono_wrt_pred" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("'(_/ :/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 40] 40)
  "_dep_mono_wrt_pred_if" :: "idt \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
    ("'(_/ :/ _/ |/ _') \<Rrightarrow>\<^sub>m (_)" [41, 41, 40, 40] 40)
end
unbundle dep_mono_wrt_syntax
translations
  "R \<Rrightarrow>\<^sub>m S" \<rightleftharpoons> "CONST mono_wrt R S"
  "(x y \<Colon> R) \<Rrightarrow>\<^sub>m S" \<rightleftharpoons> "CONST dep_mono_wrt R (\<lambda>x y. S)"
  "(x y \<Colon> R | B) \<Rrightarrow>\<^sub>m S" \<rightleftharpoons> "CONST dep_mono_wrt R (\<lambda>x y. CONST rel_if B S)"
  "(x : P) \<Rrightarrow>\<^sub>m Q" \<rightleftharpoons> "CONST dep_mono_wrt P (\<lambda>x. Q)"
  "(x : P | B) \<Rrightarrow>\<^sub>m Q" \<rightleftharpoons> "CONST dep_mono_wrt P (\<lambda>x. CONST pred_if B Q)"


definition "dep_mono_wrt_rel (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
  (S :: 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<equiv> ((x y \<Colon> R) \<Rrightarrow> S x y) f f"
adhoc_overloading dep_mono_wrt dep_mono_wrt_rel

definition "mono_wrt_rel (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool) \<equiv>
  ((_ _ \<Colon> R) \<Rrightarrow>\<^sub>m S) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool"
adhoc_overloading mono_wrt mono_wrt_rel

definition "dep_mono_wrt_pred (P :: 'a \<Rightarrow> bool) (Q :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<equiv>
  ((x : P) \<Rrightarrow> (\<lambda>(_ :: 'b). Q x)) f f"
adhoc_overloading dep_mono_wrt dep_mono_wrt_pred

definition "mono_wrt_pred (P :: 'a \<Rightarrow> bool) (Q :: 'b \<Rightarrow> bool) \<equiv>
  (((_ :: 'a) : P) \<Rrightarrow>\<^sub>m Q) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool"
adhoc_overloading mono_wrt mono_wrt_pred

lemma mono_wrt_rel_eq_dep_mono_wrt_rel:
  "((R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) = ((_ _ \<Colon> R) \<Rrightarrow>\<^sub>m S)"
  unfolding mono_wrt_rel_def by simp

lemma mono_wrt_rel_eq_dep_mono_wrt_rel_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "S' \<equiv> (\<lambda>(_ :: 'a) (_ :: 'a). S)"
  shows "((R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) = ((x y \<Colon> R') \<Rrightarrow>\<^sub>m S' x y)"
  using assms by (simp add: mono_wrt_rel_eq_dep_mono_wrt_rel)

lemma mono_wrt_rel_iff_dep_mono_wrt_rel:
  "((R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) f \<longleftrightarrow>
    dep_mono_wrt R (\<lambda>(_ :: 'a) (_ :: 'a). S) (f :: 'a \<Rightarrow> 'b)"
  by (simp add: mono_wrt_rel_eq_dep_mono_wrt_rel)

lemma mono_wrt_pred_eq_dep_mono_wrt_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m (Q :: 'b \<Rightarrow> bool)) = (((_ :: 'a) : P) \<Rrightarrow>\<^sub>m Q)"
  unfolding mono_wrt_pred_def by simp

lemma mono_wrt_pred_eq_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> P'"
  and "Q' \<equiv> (\<lambda>(_ :: 'a). Q)"
  shows "((P :: 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m (Q :: 'b \<Rightarrow> bool)) = (((x : P') \<Rrightarrow>\<^sub>m Q' x) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool)"
  using assms by (simp add: mono_wrt_pred_eq_dep_mono_wrt_pred)

lemma mono_wrt_pred_iff_dep_mono_wrt_pred:
  "((P :: 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m (Q :: 'b \<Rightarrow> bool)) f \<longleftrightarrow> (((_ :: 'a) : P) \<Rrightarrow>\<^sub>m Q) (f :: 'a \<Rightarrow> 'b)"
  by (simp add: mono_wrt_pred_eq_dep_mono_wrt_pred)

lemma dep_mono_wrt_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y)"
  shows "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  using assms unfolding dep_mono_wrt_rel_def by blast

lemma dep_mono_wrt_relE:
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  obtains "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y)"
  using assms unfolding dep_mono_wrt_rel_def by blast

lemma dep_mono_wrt_relD [dest]:
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  shows "S x y (f x) (f y)"
  using assms unfolding dep_mono_wrt_rel_def by blast

lemma mono_wrt_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  shows "(R \<Rrightarrow>\<^sub>m S) f"
  using assms by (urule dep_mono_wrt_relI)

lemma mono_wrt_relE:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  obtains "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  using assms by (urule (e) dep_mono_wrt_relE)

lemma mono_wrt_relD [dest]:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  and "R x y"
  shows "S (f x) (f y)"
  using assms by (urule dep_mono_wrt_relD)

lemma dep_mono_wrt_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> Q x (f x)"
  shows "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  using assms unfolding dep_mono_wrt_pred_def by blast

lemma dep_mono_wrt_predE:
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  obtains "\<And>x. P x \<Longrightarrow> Q x (f x)"
  using assms unfolding dep_mono_wrt_pred_def by blast

lemma dep_mono_wrt_predD [dest]:
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  and "P x"
  shows "Q x (f x)"
  using assms unfolding dep_mono_wrt_pred_def by blast

lemma mono_wrt_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> Q (f x)"
  shows "(P \<Rrightarrow>\<^sub>m Q) f"
  using assms by (urule dep_mono_wrt_predI)

lemma mono_wrt_predE:
  assumes "(P \<Rrightarrow>\<^sub>m Q) f"
  obtains "\<And>x. P x \<Longrightarrow> Q (f x)"
  using assms by (urule (e) dep_mono_wrt_predE)

lemma mono_wrt_predD [dest]:
  assumes "(P \<Rrightarrow>\<^sub>m Q) f"
  and "P x"
  shows "Q (f x)"
  using assms by (urule dep_mono_wrt_predD)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  and P :: "'a \<Rightarrow> bool" and Q :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

lemma dep_mono_wrt_rel_if_Dep_Fun_Rel_rel_self:
  assumes "((x y \<Colon> R) \<Rrightarrow> S x y) f f"
  shows "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  using assms by blast

lemma dep_mono_wrt_pred_if_Dep_Fun_Rel_pred_self:
  assumes "((x : P) \<Rrightarrow> (\<lambda>_. Q x)) f f"
  shows "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  using assms by blast

lemma Dep_Fun_Rel_rel_self_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  shows "((x y \<Colon> R) \<Rrightarrow> S x y) f f"
  using assms by blast

lemma Dep_Fun_Rel_pred_self_if_dep_mono_wrt_pred:
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  shows "((x : P) \<Rrightarrow> (\<lambda>_. Q x)) f f"
  using assms by blast

corollary Dep_Fun_Rel_rel_self_iff_dep_mono_wrt_rel:
  "((x y \<Colon> R) \<Rrightarrow> S x y) f f \<longleftrightarrow> ((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  using dep_mono_wrt_rel_if_Dep_Fun_Rel_rel_self
    Dep_Fun_Rel_rel_self_if_dep_mono_wrt_rel by blast

corollary Dep_Fun_Rel_pred_self_iff_dep_mono_wrt_pred:
  "((x : P) \<Rrightarrow> (\<lambda>(_ :: 'b). Q x)) f f \<longleftrightarrow> ((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  using dep_mono_wrt_pred_if_Dep_Fun_Rel_pred_self
    Dep_Fun_Rel_pred_self_if_dep_mono_wrt_pred by blast

lemma dep_mono_wrt_rel_inv_eq [simp]:
  "((y x \<Colon> R\<inverse>) \<Rrightarrow>\<^sub>m (S x y)\<inverse>) = ((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y)"
  by (intro ext) force

lemma in_dom_if_rel_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  shows "in_dom (S x y) (f x)"
  using assms by (intro in_domI) blast

end

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
begin

corollary in_dom_if_in_dom_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "(in_dom R \<Rrightarrow>\<^sub>m in_dom S) f"
  using assms in_dom_if_rel_if_dep_mono_wrt_rel by fast

lemma in_codom_if_rel_if_dep_mono_wrt_rel:
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  shows "in_codom (S x y) (f y)"
  using assms by (intro in_codomI) blast

corollary in_codom_if_in_codom_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "(in_codom R \<Rrightarrow>\<^sub>m in_codom S) f"
  using assms in_dom_if_rel_if_dep_mono_wrt_rel
  by fast

corollary in_field_if_in_field_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "(in_field R \<Rrightarrow>\<^sub>m in_field S) f"
  using assms by fast

lemma le_rel_map_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "R \<le> rel_map f S"
  using assms by (intro le_relI) auto

lemma le_pred_map_if_mono_wrt_pred:
  assumes "(P \<Rrightarrow>\<^sub>m Q) f"
  shows "P \<le> pred_map f Q"
  using assms by (intro le_predI) auto

lemma mono_wrt_rel_if_le_rel_map:
  assumes "R \<le> rel_map f S"
  shows "(R \<Rrightarrow>\<^sub>m S) f"
  using assms by (intro mono_wrt_relI) auto

lemma mono_wrt_pred_if_le_pred_map:
  assumes "P \<le> pred_map f Q"
  shows "(P \<Rrightarrow>\<^sub>m Q) f"
  using assms by (intro mono_wrt_predI) auto

corollary mono_wrt_rel_iff_le_rel_map: "(R \<Rrightarrow>\<^sub>m S) f \<longleftrightarrow> R \<le> rel_map f S"
  using mono_wrt_rel_if_le_rel_map le_rel_map_if_mono_wrt_rel by auto

corollary mono_wrt_pred_iff_le_pred_map: "(P \<Rrightarrow>\<^sub>m Q) f \<longleftrightarrow> P \<le> pred_map f Q"
  using mono_wrt_pred_if_le_pred_map le_pred_map_if_mono_wrt_pred by auto

end

definition "mono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool
  \<equiv> (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m ((\<le>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"

lemma mono_eq_mono_wrt_le [simp]: "(mono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool) =
  (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m ((\<le>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"
  unfolding mono_def by simp

lemma mono_eq_mono_wrt_le_uhint [uhint]:
  assumes "R \<equiv> (\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  and "S \<equiv> (\<le>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool"
  shows "mono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  using assms by simp

lemma mono_iff_mono_wrt_le [iff]: "mono f \<longleftrightarrow> ((\<le>) \<Rrightarrow>\<^sub>m (\<le>)) f" by simp

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
  \<equiv> (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m ((\<ge>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"

lemma antimono_eq_mono_wrt_le_ge [simp]: "(antimono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool) =
  (((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rrightarrow>\<^sub>m ((\<ge>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool))"
  unfolding antimono_def by simp

lemma antimono_eq_mono_wrt_le_ge_uhint [uhint]:
  assumes "R \<equiv> (\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  and "S \<equiv> (\<ge>) :: 'b \<Rightarrow> 'b \<Rightarrow> bool"
  shows "antimono :: (('a :: ord) \<Rightarrow> ('b :: ord)) \<Rightarrow> bool \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  using assms by simp

lemma antimono_iff_mono_wrt_le_ge [iff]: "antimono f \<longleftrightarrow> ((\<le>) \<Rrightarrow>\<^sub>m (\<ge>)) f" by simp

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

lemma antimono_dep_mono_wrt_rel_left: "antimono (\<lambda>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool). ((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y))"
  by (intro antimonoI) blast

lemma antimono_dep_mono_wrt_pred_left: "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). ((x : P) \<Rrightarrow>\<^sub>m Q x))"
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
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "R' \<le> R"
  shows "((x y \<Colon> R') \<Rrightarrow>\<^sub>m S x y) f"
  using assms by blast

lemma dep_mono_wrt_pred_if_le_left_if_dep_mono_wrt_pred:
  fixes P P' :: "'a \<Rightarrow> bool"
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  and "P' \<le> P"
  shows "((x : P') \<Rrightarrow>\<^sub>m Q x) f"
  using assms by blast

lemma mono_Dep_Fun_Rel_rel_right: "mono (\<lambda>(S :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool).  ((x y \<Colon> R) \<Rrightarrow> S x y))"
  by (intro monoI) blast

lemma mono_Dep_Fun_Rel_pred_right: "mono (\<lambda>(Q :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool). ((x : P) \<Rrightarrow> Q x))"
  by (intro monoI) blast

lemma mono_dep_mono_wrt_rel_right: "mono (\<lambda>(S :: 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool). ((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y))"
  by (intro monoI) blast

lemma mono_dep_mono_wrt_pred_right: "mono (\<lambda>(Q :: 'a \<Rightarrow> 'b \<Rightarrow> bool). ((x : P) \<Rrightarrow>\<^sub>m Q x))"
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
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y) \<Longrightarrow> T x y (f x) (f y)"
  shows "((x y \<Colon> R) \<Rrightarrow>\<^sub>m T x y) f"
  using assms by (intro dep_mono_wrt_relI) blast

lemma dep_mono_wrt_pred_if_le_right_if_dep_mono_wrt_pred:
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> T x (f x)"
  shows "((x : P) \<Rrightarrow>\<^sub>m T x) f"
  using assms by blast


paragraph \<open>Composition\<close>

lemma dep_mono_wrt_rel_compI:
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> ((x' y' \<Colon> T x y) \<Rrightarrow>\<^sub>m U x y x' y') f'"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y) \<Longrightarrow> T x y (f x) (f y)"
  shows "((x y \<Colon> R) \<Rrightarrow>\<^sub>m U x y (f x) (f y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_relI) force

corollary dep_mono_wrt_rel_compI':
  assumes "((x y \<Colon> R) \<Rrightarrow>\<^sub>m S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> ((x' y' \<Colon> S x y) \<Rrightarrow>\<^sub>m T x y x' y') f'"
  shows "((x y \<Colon> R) \<Rrightarrow>\<^sub>m T x y (f x) (f y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_rel_compI)

lemma dep_mono_wrt_pred_comp_dep_mono_wrt_rel_compI:
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> ((x' y' \<Colon> R x) \<Rrightarrow>\<^sub>m S x x' y') f'"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> R x (f x) (f x)"
  shows "((x : P) \<Rrightarrow>\<^sub>m (\<lambda>y. S x (f x) (f x) y y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_predI) force

lemma dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI:
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> ((x' : R x) \<Rrightarrow>\<^sub>m S x x') f'"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> R x (f x)"
  shows "((x : P) \<Rrightarrow>\<^sub>m S x (f x)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_predI) force

corollary dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI':
  assumes "((x : P) \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> ((x' : Q x) \<Rrightarrow>\<^sub>m S x x') f'"
  shows "((x : P) \<Rrightarrow>\<^sub>m S x (f x)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI)

lemma mono_wrt_rel_top [iff]:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  shows "(R \<Rrightarrow>\<^sub>m (\<top> :: 'b \<Rightarrow> 'b \<Rightarrow> bool)) f"
  by auto

lemma mono_wrt_pred_top [iff]:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  shows "(P \<Rrightarrow>\<^sub>m (\<top> :: 'b \<Rightarrow> bool)) f"
  by auto

paragraph \<open>Instantiations\<close>

lemma mono_wrt_rel_self_id:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  shows "(R \<Rrightarrow>\<^sub>m R) (id :: 'a \<Rightarrow> 'a)"
  by auto

lemma mono_wrt_pred_self_id:
  fixes P :: "'a \<Rightarrow> bool"
  shows "(P \<Rrightarrow>\<^sub>m P) (id :: 'a \<Rightarrow> 'a)"
  by auto

lemma mono_in_dom: "mono in_dom" by (intro monoI) fast
lemma mono_in_codom: "mono in_codom" by (intro monoI) fast
lemma mono_in_field: "mono in_field" by (intro monoI) fast
lemma mono_rel_comp: "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) (\<circ>\<circ>)" by (intro mono_wrt_relI Fun_Rel_relI le_relI) fast
lemma mono_rel_inv: "mono rel_inv" by (intro monoI) fast

lemma mono_rel_restrict_left:
  "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) (rel_restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI le_relI) fastforce

lemma mono_rel_restrict_right:
  "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) (rel_restrict_right :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI le_relI) fastforce

lemma mono_ball: "((\<ge>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) ball" by fast
lemma mono_bex: "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) bex" by fast

end
