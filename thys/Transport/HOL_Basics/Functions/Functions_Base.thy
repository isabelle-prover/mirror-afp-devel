\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Functions\<close>
subsection \<open>Basic Functions\<close>
theory Functions_Base
  imports HOL_Basics_Base
begin

definition "id x \<equiv> x"

lemma id_eq_self [simp]: "id x = x"
  unfolding id_def ..

definition "comp f g x \<equiv> f (g x)"

bundle comp_syntax begin notation comp (infixl "\<circ>" 55) end
bundle no_comp_syntax begin no_notation comp (infixl "\<circ>" 55) end
unbundle comp_syntax

lemma comp_eq [simp]: "(f \<circ> g) x = f (g x)"
  unfolding comp_def ..

lemma id_comp_eq [simp]: "id \<circ> f = f"
  by (rule ext) simp

lemma comp_id_eq [simp]: "f \<circ> id = f"
  by (rule ext) simp

definition "dep_fun_map f g h x \<equiv> g x (f x) (h (f x))"

abbreviation "fun_map f g h \<equiv> dep_fun_map f (\<lambda>_ _. g) h"

bundle dep_fun_map_syntax begin
syntax
  "_fun_map" :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("(_) \<rightarrow> (_)" [41, 40] 40)
  "_dep_fun_map" :: "idt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("[_/ : / _] \<rightarrow> (_)" [41, 41, 40] 40)
end
bundle no_dep_fun_map_syntax begin
no_syntax
  "_fun_map" :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("(_) \<rightarrow> (_)" [41, 40] 40)
  "_dep_fun_map" :: "idt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("[_/ : / _] \<rightarrow> (_)" [41, 41, 40] 40)
end
unbundle dep_fun_map_syntax
translations
  "f \<rightarrow> g" \<rightleftharpoons> "CONST fun_map f g"
  "[x : f] \<rightarrow> g" \<rightleftharpoons> "CONST dep_fun_map f (\<lambda>x. g)"

lemma dep_fun_map_eq [simp]: "([x : f] \<rightarrow> g x) h x = g x (f x) (h (f x))"
  unfolding dep_fun_map_def ..

lemma fun_map_eq_comp [simp]: "(f \<rightarrow> g) h = g \<circ> h \<circ> f"
  by fastforce

lemma fun_map_eq [simp]: "(f \<rightarrow> g) h x = g (h (f x))"
  unfolding fun_map_eq_comp by simp

lemma fun_map_id_eq_comp [simp]: "fun_map id = (\<circ>)"
  by (intro ext) simp

lemma fun_map_id_eq_comp' [simp]: "(f \<rightarrow> id) h = h \<circ> f"
  by (intro ext) simp



end