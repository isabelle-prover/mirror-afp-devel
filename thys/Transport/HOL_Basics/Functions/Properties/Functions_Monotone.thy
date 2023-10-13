\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Monotonicity\<close>
theory Functions_Monotone
  imports
    Binary_Relations_Order_Base
    Function_Relators
    Predicates
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of monotone functions. A function is monotone
if it is related to itself - see \<^term>\<open>Dep_Fun_Rel_rel\<close>.\<close>

declare le_funI[intro]
declare le_funE[elim]

definition "dep_mono_wrt_rel R S f \<equiv> ([x y \<Colon> R] \<Rrightarrow> S x y) f f"

abbreviation "mono_wrt_rel R S \<equiv> dep_mono_wrt_rel R (\<lambda>_ _. S)"

definition "dep_mono_wrt_pred P Q f \<equiv> ([x \<Colon> P] \<Rrightarrow> (\<lambda>_. Q x)) f f"

abbreviation "mono_wrt_pred P Q \<equiv> dep_mono_wrt_pred P (\<lambda>_. Q)"

bundle dep_mono_wrt_syntax begin
syntax
  "_mono_wrt_rel" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    bool" ("(_) \<Rrightarrow>\<^sub>m (_)" [41, 40] 40)
  "_dep_mono_wrt_rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40] 40)
  "_dep_mono_wrt_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _/ |/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 41, 40] 40)
  "_mono_wrt_pred" :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    bool" ("[_] \<Rrightarrow>\<^sub>m (_)" [41, 40] 40)
  "_dep_mono_wrt_pred" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ \<Colon>/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 40] 40)
  (*TODO: this only works if we introduce a pred_if constant first*)
  (* "_dep_mono_wrt_pred_if" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> *)
    (* ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ \<Colon>/ _/ |/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40] 40) *)
end
bundle no_dep_mono_wrt_syntax begin
no_syntax
  "_mono_wrt_rel" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    bool" ("(_) \<Rrightarrow>\<^sub>m (_)" [41, 40] 40)
  "_dep_mono_wrt_rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40] 40)
  "_dep_mono_wrt_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _/ |/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 41, 40] 40)
  "_mono_wrt_pred" :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    bool" ("[_] \<Rrightarrow>\<^sub>m (_)" [41, 40] 40)
  "_dep_mono_wrt_pred" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ \<Colon>/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 40] 40)
  (* "_dep_mono_wrt_pred_if" :: "idt \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> *)
    (* ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("[_/ \<Colon>/ _/ |/ _] \<Rrightarrow>\<^sub>m (_)" [41, 41, 41, 40] 40) *)
end
unbundle dep_mono_wrt_syntax
translations
  "R \<Rrightarrow>\<^sub>m S" \<rightleftharpoons> "CONST mono_wrt_rel R S"
  "[x y \<Colon> R] \<Rrightarrow>\<^sub>m S" \<rightleftharpoons> "CONST dep_mono_wrt_rel R (\<lambda>x y. S)"
  "[x y \<Colon> R | B] \<Rrightarrow>\<^sub>m S" \<rightleftharpoons> "CONST dep_mono_wrt_rel R (\<lambda>x y. CONST rel_if B S)"
  "[P] \<Rrightarrow>\<^sub>m Q" \<rightleftharpoons> "CONST mono_wrt_pred P Q"
  "[x \<Colon> P] \<Rrightarrow>\<^sub>m Q" \<rightleftharpoons> "CONST dep_mono_wrt_pred P (\<lambda>x. Q)"
  (* "[x \<Colon> P | B] \<Rrightarrow>\<^sub>m Q" \<rightleftharpoons> "CONST dep_mono_wrt_pred P (\<lambda>x. CONST rel_if B Q)" *)

lemma dep_mono_wrt_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y)"
  shows "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  using assms unfolding dep_mono_wrt_rel_def by blast

lemma dep_mono_wrt_relE [elim]:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  obtains "S x y (f x) (f y)"
  using assms unfolding dep_mono_wrt_rel_def by blast

lemma dep_mono_wrt_relD:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  shows "S x y (f x) (f y)"
  using assms by blast

lemma dep_mono_wrt_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> Q x (f x)"
  shows "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  using assms unfolding dep_mono_wrt_pred_def by blast

lemma dep_mono_wrt_predE [elim]:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "P x"
  obtains "Q x (f x)"
  using assms unfolding dep_mono_wrt_pred_def by blast

lemma dep_mono_wrt_predD:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "P x"
  shows "Q x (f x)"
  using assms by blast

lemma dep_mono_wrt_rel_if_Dep_Fun_Rel_rel_self:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f f"
  shows "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  using assms by blast

lemma dep_mono_wrt_pred_if_Dep_Fun_Rel_pred_self:
  assumes "([x \<Colon> P] \<Rrightarrow> (\<lambda>_. Q x)) f f"
  shows "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  using assms by blast

lemma Dep_Fun_Rel_rel_self_if_dep_mono_wrt_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  shows "([x y \<Colon> R] \<Rrightarrow> S x y) f f"
  using assms by blast

lemma Dep_Fun_Rel_pred_self_if_dep_mono_wrt_pred:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  shows "([x \<Colon> P] \<Rrightarrow> (\<lambda>_. Q x)) f f"
  using assms by blast

corollary Dep_Fun_Rel_rel_self_iff_dep_mono_wrt_rel:
  "([x y \<Colon> R] \<Rrightarrow> S x y) f f \<longleftrightarrow> ([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  using dep_mono_wrt_rel_if_Dep_Fun_Rel_rel_self
    Dep_Fun_Rel_rel_self_if_dep_mono_wrt_rel by blast

corollary Dep_Fun_Rel_pred_self_iff_dep_mono_wrt_pred:
  "([x \<Colon> P] \<Rrightarrow> (\<lambda>_. Q x)) f f \<longleftrightarrow> ([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  using dep_mono_wrt_pred_if_Dep_Fun_Rel_pred_self
    Dep_Fun_Rel_pred_self_if_dep_mono_wrt_pred by blast

lemma dep_mono_wrt_rel_inv_eq [simp]:
  "([y x \<Colon> R\<inverse>] \<Rrightarrow>\<^sub>m (S x y)\<inverse>) = ([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y)"
  by (intro ext) auto

lemma in_dom_if_rel_if_dep_mono_wrt_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  shows "in_dom (S x y) (f x)"
  using assms by (intro in_domI) blast

corollary in_dom_if_in_dom_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "([in_dom R] \<Rrightarrow>\<^sub>m in_dom S) f"
  using assms in_dom_if_rel_if_dep_mono_wrt_rel by fast

lemma in_codom_if_rel_if_dep_mono_wrt_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "R x y"
  shows "in_codom (S x y) (f y)"
  using assms by (intro in_codomI) blast

corollary in_codom_if_in_codom_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "([in_codom R] \<Rrightarrow>\<^sub>m in_codom S) f"
  using assms in_dom_if_rel_if_dep_mono_wrt_rel by fast

corollary in_field_if_in_field_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "([in_field R] \<Rrightarrow>\<^sub>m in_field S) f"
  using assms by (intro dep_mono_wrt_predI) blast

lemma le_rel_map_if_mono_wrt_rel:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "R \<le> rel_map f S"
  using assms by (intro le_relI) auto

lemma le_pred_map_if_mono_wrt_pred:
  assumes "([P] \<Rrightarrow>\<^sub>m Q) f"
  shows "P \<le> pred_map f Q"
  using assms by (intro le_predI) auto

lemma mono_wrt_rel_if_le_rel_map:
  assumes "R \<le> rel_map f S"
  shows "(R \<Rrightarrow>\<^sub>m S) f"
  using assms by (intro dep_mono_wrt_relI) auto

lemma mono_wrt_pred_if_le_pred_map:
  assumes "P \<le> pred_map f Q"
  shows "([P] \<Rrightarrow>\<^sub>m Q) f"
  using assms by (intro dep_mono_wrt_predI) auto

corollary mono_wrt_rel_iff_le_rel_map: "(R \<Rrightarrow>\<^sub>m S) f \<longleftrightarrow> R \<le> rel_map f S"
  using mono_wrt_rel_if_le_rel_map le_rel_map_if_mono_wrt_rel by auto

corollary mono_wrt_pred_iff_le_pred_map: "([P] \<Rrightarrow>\<^sub>m Q) f \<longleftrightarrow> P \<le> pred_map f Q"
  using mono_wrt_pred_if_le_pred_map le_pred_map_if_mono_wrt_pred by auto

definition "mono \<equiv> ((\<le>) \<Rrightarrow>\<^sub>m (\<le>))"

definition "antimono \<equiv> ((\<le>) \<Rrightarrow>\<^sub>m (\<ge>))"

lemma monoI [intro]:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "mono f"
  unfolding mono_def using assms by blast

lemma monoE [elim]:
  assumes "mono f"
  and "x \<le> y"
  obtains "f x \<le> f y"
  using assms unfolding mono_def by blast

lemma monoD:
  assumes "mono f"
  and "x \<le> y"
  shows "f x \<le> f y"
  using assms by blast

lemma antimonoI [intro]:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> f y \<le> f x"
  shows "antimono f"
  unfolding antimono_def using assms by blast

lemma antimonoE [elim]:
  assumes "antimono f"
  and "x \<le> y"
  obtains "f y \<le> f x"
  using assms unfolding antimono_def by blast

lemma antimonoD:
  assumes "antimono f"
  and "x \<le> y"
  shows "f y \<le> f x"
  using assms by blast

lemma antimono_Dep_Fun_Rel_rel_left: "antimono (\<lambda>R. [x y \<Colon> R] \<Rrightarrow> S x y)"
  by (intro antimonoI) auto

lemma antimono_Dep_Fun_Rel_pred_left: "antimono (\<lambda>P. [x \<Colon> P] \<Rrightarrow> Q x)"
  by (intro antimonoI) auto

lemma antimono_dep_mono_wrt_rel_left: "antimono (\<lambda>R. [x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y)"
  by (intro antimonoI) auto

lemma antimono_dep_mono_wrt_pred_left: "antimono (\<lambda>P. [x \<Colon> P] \<Rrightarrow>\<^sub>m Q x)"
  by (intro antimonoI) auto

lemma Dep_Fun_Rel_rel_if_le_left_if_Dep_Fun_Rel_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "T \<le> R"
  shows "([x y \<Colon> T] \<Rrightarrow> S x y) f g"
  using assms by blast

lemma Dep_Fun_Rel_pred_if_le_left_if_Dep_Fun_Rel_pred:
  assumes "([x \<Colon> P] \<Rrightarrow> Q x) f g"
  and "T \<le> P"
  shows "([x \<Colon> T] \<Rrightarrow> Q x) f g"
  using assms by blast

lemma dep_mono_wrt_rel_if_le_left_if_dep_mono_wrt_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "T \<le> R"
  shows "([x y \<Colon> T] \<Rrightarrow>\<^sub>m S x y) f"
  using assms by blast

lemma dep_mono_wrt_pred_if_le_left_if_dep_mono_wrt_pred:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "T \<le> P"
  shows "([x \<Colon> T] \<Rrightarrow>\<^sub>m Q x) f"
  using assms by blast

lemma mono_Dep_Fun_Rel_rel_right: "mono (\<lambda>S. [x y \<Colon> R] \<Rrightarrow> S x y)"
  by (intro monoI) blast

lemma mono_Dep_Fun_Rel_pred_right: "mono (\<lambda>Q. [x \<Colon> P] \<Rrightarrow> Q x)"
  by (intro monoI) blast

lemma mono_dep_mono_wrt_rel_right: "mono (\<lambda>S. [x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y)"
  by (intro monoI) blast

lemma mono_dep_mono_wrt_pred_right: "mono (\<lambda>Q. [x \<Colon> P] \<Rrightarrow>\<^sub>m Q x)"
  by (intro monoI) blast

lemma Dep_Fun_Rel_rel_if_le_right_if_Dep_Fun_Rel_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y) \<Longrightarrow> T x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> T x y) f g"
  using assms by (intro Dep_Fun_Rel_relI) blast

lemma Dep_Fun_Rel_pred_if_le_right_if_Dep_Fun_Rel_pred:
  assumes "([x \<Colon> P] \<Rrightarrow> Q x) f g"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) (g x) \<Longrightarrow> T x (f x) (g x)"
  shows "([x \<Colon> P] \<Rrightarrow> T x) f g"
  using assms by blast

lemma dep_mono_wrt_rel_if_le_right_if_dep_mono_wrt_rel:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y) \<Longrightarrow> T x y (f x) (f y)"
  shows "([x y \<Colon> R] \<Rrightarrow>\<^sub>m T x y) f"
  using assms by (intro dep_mono_wrt_relI) blast

lemma dep_mono_wrt_pred_if_le_right_if_dep_mono_wrt_pred:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> T x (f x)"
  shows "([x \<Colon> P] \<Rrightarrow>\<^sub>m T x) f"
  using assms by blast


paragraph \<open>Composition\<close>

lemma dep_mono_wrt_rel_compI:
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> T x y] \<Rrightarrow>\<^sub>m U x y x' y') f'"
  and "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y) \<Longrightarrow> T x y (f x) (f y)"
  shows "([x y \<Colon> R] \<Rrightarrow>\<^sub>m U x y (f x) (f y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_relI) (auto 6 0)

corollary dep_mono_wrt_rel_compI':
  assumes "([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> S x y] \<Rrightarrow>\<^sub>m T x y x' y') f'"
  shows "([x y \<Colon> R] \<Rrightarrow>\<^sub>m T x y (f x) (f y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_rel_compI)

lemma dep_mono_wrt_pred_comp_dep_mono_wrt_rel_compI:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> ([x' y' \<Colon> R x] \<Rrightarrow>\<^sub>m S x x' y') f'"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> R x (f x) (f x)"
  shows "([x \<Colon> P] \<Rrightarrow>\<^sub>m (\<lambda>y. S x (f x) (f x) y y)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_predI) (auto 6 0)

lemma dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI:
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> ([x' \<Colon> R x] \<Rrightarrow>\<^sub>m S x x') f'"
  and "\<And>x. P x \<Longrightarrow> Q x (f x) \<Longrightarrow> R x (f x)"
  shows "([x \<Colon> P] \<Rrightarrow>\<^sub>m S x (f x)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_predI) (auto 6 0)

corollary dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI':
  assumes "([x \<Colon> P] \<Rrightarrow>\<^sub>m Q x) f"
  and "\<And>x. P x \<Longrightarrow> ([x' \<Colon> Q x] \<Rrightarrow>\<^sub>m S x x') f'"
  shows "([x \<Colon> P] \<Rrightarrow>\<^sub>m S x (f x)) (f' \<circ> f)"
  using assms by (intro dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI)


paragraph \<open>Instantiations\<close>

lemma mono_wrt_rel_self_id: "(R \<Rrightarrow>\<^sub>m R) id" by auto
lemma mono_wrt_pred_self_id: "([P] \<Rrightarrow>\<^sub>m P) id" by auto

lemma mono_in_dom: "mono in_dom" by (intro monoI) fast
lemma mono_in_codom: "mono in_codom" by (intro monoI) fast
lemma mono_in_field: "mono in_field" by (intro monoI) fast
lemma mono_rel_comp1: "mono (\<circ>\<circ>)" by (intro monoI) fast
lemma mono_rel_comp2: "mono ((\<circ>\<circ>) x)" by (intro monoI) fast


end
