\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Functions\<close>
subsection \<open>Basic Functions\<close>
theory Functions_Base
  imports
    Binary_Relation_Functions
begin

definition "id x \<equiv> x"

lemma id_eq_self [simp]: "id x = x"
  unfolding id_def ..

consts comp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

bundle comp_syntax begin notation comp (infixl "\<circ>" 55) end
bundle no_comp_syntax begin no_notation comp (infixl "\<circ>" 55) end
unbundle comp_syntax

definition "comp_fun f g x \<equiv> f (g x)"
adhoc_overloading comp comp_fun

lemma comp_eq [simp]: "(f \<circ> g) x = f (g x)"
  unfolding comp_fun_def ..

lemma id_comp_eq [simp]: "id \<circ> f = f"
  by (rule ext) simp

lemma comp_id_eq [simp]: "f \<circ> id = f"
  by (rule ext) simp

lemma bottom_comp_eq [simp]: "\<bottom> \<circ> f = \<bottom>" by auto
lemma top_comp_eq [simp]: "\<top> \<circ> f = \<top>" by auto


definition "dep_fun_map f g h x \<equiv> g x (f x) (h (f x))"

definition "fun_map f g h \<equiv> dep_fun_map f (\<lambda>_ _. g) h"

bundle dep_fun_map_syntax begin
syntax
  "_fun_map" :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("(_) \<leadsto> (_)" [41, 40] 40)
  "_dep_fun_map" :: "idt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("'(_/ : / _') \<leadsto> (_)" [41, 41, 40] 40)
end
bundle no_dep_fun_map_syntax begin
no_syntax
  "_fun_map" :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("(_) \<leadsto> (_)" [41, 40] 40)
  "_dep_fun_map" :: "idt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("'(_/ : / _') \<leadsto> (_)" [41, 41, 40] 40)
end
unbundle dep_fun_map_syntax
translations
  "f \<leadsto> g" \<rightleftharpoons> "CONST fun_map f g"
  "(x : f) \<leadsto> g" \<rightleftharpoons> "CONST dep_fun_map f (\<lambda>x. g)"

lemma fun_map_eq_dep_fun_map: "(f \<leadsto> g) = ((_ :  f) \<leadsto> (\<lambda>_. g))"
  unfolding fun_map_def by simp

lemma fun_map_eq_dep_fun_map_uhint [uhint]:
  assumes "f \<equiv> f'"
  and "g' \<equiv> (\<lambda>_ _. g)"
  shows "(f \<leadsto> g) = ((x :  f') \<leadsto> g' x)"
  using assms by (simp add: fun_map_eq_dep_fun_map)

lemma dep_fun_map_eq [simp]: "((x : f) \<leadsto> g x) h x = g x (f x) (h (f x))"
  unfolding dep_fun_map_def ..

lemma fun_map_eq_comp [simp]: "(f \<leadsto> g) h = g \<circ> h \<circ> f"
  by (intro ext) (urule dep_fun_map_eq)

lemma fun_map_eq [simp]: "(f \<leadsto> g) h x = g (h (f x))"
  unfolding fun_map_eq_comp by simp

lemma fun_map_id_eq_comp [simp]: "fun_map id = (\<circ>)"
  by (intro ext) simp

lemma fun_map_id_eq_comp' [simp]: "(f \<leadsto> id) h = h \<circ> f"
  by (intro ext) simp


consts has_inverse_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

definition "has_inverse_on_pred (P :: 'a \<Rightarrow> bool) f \<equiv> in_codom_on P ((=) \<circ> f)"
adhoc_overloading has_inverse_on has_inverse_on_pred

lemma has_inverse_on_pred_eq_in_codom_on: "has_inverse_on P = in_codom_on P \<circ> ((\<circ>) (=))"
  unfolding has_inverse_on_pred_def by auto

lemma has_inverse_onI [intro]:
  assumes "P x"
  shows "has_inverse_on P f (f x)"
  using assms unfolding has_inverse_on_pred_def by auto

lemma has_inverse_on_if_pred_if_eq:
  assumes "y = f x"
  and "P x"
  shows "has_inverse_on P f y"
  using assms by auto

lemma has_inverse_onE [elim]:
  assumes "has_inverse_on P f y"
  obtains x where "P x" "y = f x"
  using assms unfolding has_inverse_on_pred_def by auto

context
  notes has_inverse_on_pred_eq_in_codom_on[simp]
begin

lemma has_inverse_on_bottom_eq [simp]: "has_inverse_on \<bottom> = \<bottom>"
  by (urule in_codom_bottom_pred_eq_bottom)

lemma has_inverse_on_eq_pred_eq_eq_app [simp]: "has_inverse_on ((=) P) f = (=) (f P)"
  by (urule in_codom_on_eq_pred_eq)

lemma has_inverse_on_sup_eq_has_inverse_on_sup_has_inverse_on [simp]:
  "has_inverse_on (P \<squnion> Q) = has_inverse_on P \<squnion> has_inverse_on Q"
  supply ext[simp] by (urule in_codom_on_sup_pred_eq_in_codom_on_sup_in_codom_on)

end

definition "has_inverse \<equiv> has_inverse_on \<top>"

lemma has_inverse_eq_has_inverse_on_top: "has_inverse = has_inverse_on \<top>"
  unfolding has_inverse_def by simp

lemma has_inverse_eq_has_inverse_on_top_uhint [uhint]:
  assumes "P \<equiv> \<top>"
  shows "has_inverse \<equiv> has_inverse_on P"
  using assms by (simp add: has_inverse_eq_has_inverse_on_top)

lemma has_inverse_iff_has_inverse_on_top: "has_inverse f y \<longleftrightarrow> has_inverse_on \<top> f y"
  by (simp add: has_inverse_eq_has_inverse_on_top)

lemma has_inverseI [intro]:
  assumes "y = f x"
  shows "has_inverse f y"
  using assms by (urule has_inverse_on_if_pred_if_eq) simp

lemma has_inverseE [elim]:
  assumes "has_inverse f y"
  obtains x where "y = f x"
  using assms by (urule (e) has_inverse_onE)

end