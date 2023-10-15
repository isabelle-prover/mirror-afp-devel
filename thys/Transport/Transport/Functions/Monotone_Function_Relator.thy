\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Monotone Function Relator\<close>
theory Monotone_Function_Relator
  imports
    Reflexive_Relator
begin

abbreviation "Mono_Dep_Fun_Rel R S \<equiv> ([x y \<Colon> R] \<Rrightarrow> S x y)\<^sup>\<oplus>"
abbreviation "Mono_Fun_Rel R S \<equiv> Mono_Dep_Fun_Rel R (\<lambda>_ _. S)"

bundle Mono_Dep_Fun_Rel_syntax begin
syntax
  "_Mono_Fun_Rel_rel" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("(_) \<Rrightarrow>\<oplus> (_)" [41, 40] 40)
  "_Mono_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _] \<Rrightarrow>\<oplus> (_)" [41, 41, 41, 40] 40)
  "_Mono_Dep_Fun_Rel_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _/ |/ _] \<Rrightarrow>\<oplus> (_)" [41, 41, 41, 41, 40] 40)
end
bundle no_Mono_Dep_Fun_Rel_syntax begin
no_syntax
  "_Mono_Fun_Rel_rel" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("(_) \<Rrightarrow>\<oplus> (_)" [41, 40] 40)
  "_Mono_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _] \<Rrightarrow>\<oplus> (_)" [41, 41, 41, 40] 40)
  "_Mono_Dep_Fun_Rel_rel_if" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool" ("[_/ _/ \<Colon>/ _/ |/ _] \<Rrightarrow>\<oplus> (_)" [41, 41, 41, 41, 40] 40)
end
unbundle Mono_Dep_Fun_Rel_syntax

translations
  "R \<Rrightarrow>\<oplus> S" \<rightleftharpoons> "CONST Mono_Fun_Rel R S"
  "[x y \<Colon> R] \<Rrightarrow>\<oplus> S" \<rightleftharpoons> "CONST Mono_Dep_Fun_Rel R (\<lambda>x y. S)"
  "[x y \<Colon> R | B] \<Rrightarrow>\<oplus> S" \<rightleftharpoons> "CONST Mono_Dep_Fun_Rel R (\<lambda>x y. CONST rel_if B S)"

locale Dep_Fun_Rel_orders =
  fixes L :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
begin

sublocale o : orders L "R a b" for a b .

notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation o.ge_left (infix "\<ge>\<^bsub>L\<^esub>" 50)

notation R ("(\<le>\<^bsub>R (_) (_)\<^esub>)" 50)
abbreviation "right_infix c a b d \<equiv> (\<le>\<^bsub>R a b\<^esub>) c d"
notation right_infix ("(_) \<le>\<^bsub>R (_) (_)\<^esub> (_)" [51,51,51,51] 50)

notation o.ge_right ("(\<ge>\<^bsub>R (_) (_)\<^esub>)" 50)

abbreviation (input) "ge_right_infix d a b c \<equiv> (\<ge>\<^bsub>R a b\<^esub>) d c"
notation ge_right_infix ("(_) \<ge>\<^bsub>R (_) (_)\<^esub> (_)" [51,51,51,51] 50)

abbreviation (input) "DFR \<equiv> ([a b \<Colon> L] \<Rrightarrow> R a b)"

end

locale hom_Dep_Fun_Rel_orders = Dep_Fun_Rel_orders L R
  for L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

sublocale ho : hom_orders L "R a b" for a b .

lemma Mono_Dep_Fun_Refl_Rel_right_eq_Mono_Dep_Fun_if_le_if_reflexive_onI:
  assumes refl_L: "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x2 x2\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x1\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "([x y \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>)\<^sup>\<oplus>) = ([x y \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>))"
proof -
  {
    fix f g x1 x2
    assume "([x y \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R x y\<^esub>)) f g" "x1 \<le>\<^bsub>L\<^esub> x1" "x1 \<le>\<^bsub>L\<^esub> x2"
    with assms have "f x1 \<le>\<^bsub>R x1 x2\<^esub> g x1" "f x2 \<le>\<^bsub>R x1 x2\<^esub> g x2" by blast+
  }
  with refl_L show ?thesis
    by (intro ext iffI Refl_RelI Dep_Fun_Rel_relI) (auto elim!: Refl_RelE)
qed

lemma Mono_Dep_Fun_Refl_Rel_right_eq_Mono_Dep_Fun_if_mono_if_reflexive_onI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L\<^esub>) | x1 \<le>\<^bsub>L\<^esub> x3] \<Rrightarrow> (\<le>)) R"
  shows "([x y \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>)\<^sup>\<oplus>) = ([x y \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>))"
  using assms
  by (intro Mono_Dep_Fun_Refl_Rel_right_eq_Mono_Dep_Fun_if_le_if_reflexive_onI)
  auto

end

context hom_orders
begin

sublocale fro : hom_Dep_Fun_Rel_orders L "\<lambda>_ _. R" .

corollary Mono_Fun_Rel_Refl_Rel_right_eq_Mono_Fun_RelI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) = ((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R\<^esub>))"
  using assms by (intro fro.Mono_Dep_Fun_Refl_Rel_right_eq_Mono_Dep_Fun_if_le_if_reflexive_onI)
  simp_all

end


end