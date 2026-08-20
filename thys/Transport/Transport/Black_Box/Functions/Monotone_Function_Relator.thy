\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Monotone Function Relator\<close>
theory Monotone_Function_Relator
  imports
    Reflexive_Relator
begin

abbreviation "Mono_Dep_Fun_Rel (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (S :: 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<equiv>
  ((x y \<Colon> R) \<Rrightarrow> S x y)\<^sup>\<oplus>"
abbreviation "Mono_Fun_Rel R S \<equiv> Mono_Dep_Fun_Rel R (\<lambda>_ _. S)"

open_bundle Mono_Dep_Fun_Rel_syntax
begin
notation "Mono_Fun_Rel" (infixr \<open>\<Rrightarrow>\<oplus>\<close> 50)
syntax
  "_Mono_Dep_Fun_Rel_rel" :: "idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" (\<open>('(_ _ \<Colon> _') \<Rrightarrow>\<oplus>/ _)\<close> [0,0, 0, 10] 50)
syntax_consts
  "_Mono_Dep_Fun_Rel_rel" \<rightleftharpoons> Mono_Dep_Fun_Rel
translations
  "(x y \<Colon> R) \<Rrightarrow>\<oplus> S" \<rightleftharpoons> "CONST Mono_Dep_Fun_Rel R (\<lambda>x y. S)"
end

text \<open>The monotone function relator is the function relator restricted to monotone functions:\<close>

lemma Mono_Dep_Fun_Rel_eq_Dep_Fun_Rel_restrict_dep_monos:
  fixes R S defines "dep_mono \<equiv> ((x y \<Colon> R) \<Rightarrow> S x y)"
  shows "((x y \<Colon> R) \<Rrightarrow>\<oplus> S x y) = ((x y \<Colon> R) \<Rrightarrow> S x y)\<restriction>\<^bsub>dep_mono\<^esub>\<upharpoonleft>\<^bsub>dep_mono\<^esub>"
  unfolding dep_mono_def by force

locale Dep_Fun_Rel_orders =
  fixes L :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
begin

sublocale o : orders L "R a b" for a b .

notation o.ge_left (infix \<open>\<ge>\<^bsub>L\<^esub>\<close> 50)

notation (input) R (\<open>('(\<le>(\<^bsub>R (_) (_)\<^esub>)'))\<close>)
notation (output) R (\<open>('(\<le>(\<^bsub>R ('(_')) ('(_'))\<^esub>)'))\<close>)
abbreviation "right_infix c a b d \<equiv> (\<le>\<^bsub>R a b\<^esub>) c d"
notation (input) right_infix (\<open>(_ \<le>(\<^bsub>R (_) (_)\<^esub>) _)\<close> [51,0,0,51] 50)
notation (output) right_infix (\<open>(_ \<le>(\<^bsub>R ('(_')) ('(_'))\<^esub>) _)\<close> [51,0,0,51] 50)

notation (input) o.ge_right (\<open>('(\<ge>(\<^bsub>R (_) (_)\<^esub>)'))\<close>)
notation (output) o.ge_right (\<open>('(\<ge>(\<^bsub>R ('(_')) ('(_'))\<^esub>)'))\<close>)
abbreviation (input) "ge_right_infix d a b c \<equiv> (\<le>\<^bsub>R a b\<^esub>) d c"
notation (input) ge_right_infix (\<open>(_ \<ge>(\<^bsub>R (_) (_)\<^esub>) _)\<close> [51,0,0,51] 50)
notation (output) ge_right_infix (\<open>(_ \<ge>(\<^bsub>R ('(_')) ('(_'))\<^esub>) _)\<close> [51,0,0,51] 50)

abbreviation (input) "DFR \<equiv> ((a b \<Colon> (\<le>\<^bsub>L\<^esub>)) \<Rrightarrow> (\<le>\<^bsub>R a b\<^esub>))"

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
  shows "((x y \<Colon> (\<le>\<^bsub>L\<^esub>)) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>)\<^sup>\<oplus>) = ((x y \<Colon> (\<le>\<^bsub>L\<^esub>)) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>))"
proof -
  have "f x1 \<le>\<^bsub>R x1 x2\<^esub> g x1" "f x2 \<le>\<^bsub>R x1 x2\<^esub> g x2"
    if "((x y \<Colon> (\<le>\<^bsub>L\<^esub>)) \<Rrightarrow> (\<le>\<^bsub>R x y\<^esub>)) f g" "x1 \<le>\<^bsub>L\<^esub> x1" "x1 \<le>\<^bsub>L\<^esub> x2" for f g x1 x2
    using that assms by blast+
  with refl_L show ?thesis
    by (intro ext iffI Refl_RelI Dep_Fun_Rel_relI) (auto elim!: Refl_RelE)
qed

lemma Mono_Dep_Fun_Refl_Rel_right_eq_Mono_Dep_Fun_if_mono_if_reflexive_onI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "((x1 x2 \<Colon> (\<ge>\<^bsub>L\<^esub>)) \<Rightarrow> \<lparr>x3 x4 \<Colon> (\<le>\<^bsub>L\<^esub>) | x1 \<le>\<^bsub>L\<^esub> x3\<rparr> \<Rrightarrow> (\<le>)) R"
  shows "((x y \<Colon> (\<le>\<^bsub>L\<^esub>)) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>)\<^sup>\<oplus>) = ((x y \<Colon> (\<le>\<^bsub>L\<^esub>)) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R x y\<^esub>))"
  using assms
  by (intro Mono_Dep_Fun_Refl_Rel_right_eq_Mono_Dep_Fun_if_le_if_reflexive_onI)
  blast+

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