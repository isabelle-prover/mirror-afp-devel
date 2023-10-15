\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order Functors\<close>
subsubsection \<open>Basic Setup and Results\<close>
theory Order_Functors_Base
  imports
    Functions_Inverse
    Order_Functions_Base
begin

text \<open>In the following, we do not add any assumptions to our locales but rather
add them as needed to the theorem statements. This allows consumers to
state preciser results; particularly, the development of Transport depends
on this setup.\<close>

locale orders =
  fixes L :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
begin

notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

text\<open>We call @{term "(\<le>\<^bsub>L\<^esub>)"} the \<^emph>\<open>left relation\<close> and @{term "(\<le>\<^bsub>R\<^esub>)"} the
\<^emph>\<open>right relation\<close>.\<close>

abbreviation (input) "ge_left \<equiv> (\<le>\<^bsub>L\<^esub>)\<inverse>"
notation ge_left (infix "\<ge>\<^bsub>L\<^esub>" 50)

abbreviation (input) "ge_right \<equiv> (\<le>\<^bsub>R\<^esub>)\<inverse>"
notation ge_right (infix "\<ge>\<^bsub>R\<^esub>" 50)

end

text \<open>Homogeneous orders\<close>
locale hom_orders = orders L R
  for L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"

locale order_functor = hom_orders L R
  for L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
begin

lemma left_right_rel_left_self_if_reflexive_on_left_if_mono_left:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "P x"
  shows "l x \<le>\<^bsub>R\<^esub> l x"
  using assms by blast

lemma left_right_rel_left_self_if_reflexive_on_in_dom_right_if_mono_left:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "reflexive_on (in_dom (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) x"
  shows "l x \<le>\<^bsub>R\<^esub> l x"
  using assms by blast

lemma left_right_rel_left_self_if_reflexive_on_in_codom_right_if_mono_left:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "reflexive_on (in_codom (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  and "in_codom (\<le>\<^bsub>L\<^esub>) x"
  shows "l x \<le>\<^bsub>R\<^esub> l x"
  using assms by blast

lemma left_right_rel_left_self_if_reflexive_on_in_field_right_if_mono_left:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "reflexive_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) x"
  shows "l x \<le>\<^bsub>R\<^esub> l x"
  using assms by blast

lemma mono_wrt_rel_left_if_reflexive_on_if_le_eq_if_mono_wrt_in_field:
  assumes "([in_field (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m P) l"
  and "(\<le>\<^bsub>L\<^esub>) \<le> (=)"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  using assms by (intro dep_mono_wrt_relI) auto

end


locale order_functors = order_functor L R l + flip_of : order_functor R L r
  for L R l r
begin

text \<open>We call the composition \<^term>\<open>r \<circ> l\<close> the \<^emph>\<open>unit\<close>
and the term \<^term>\<open>l \<circ> r\<close> the \<^emph>\<open>counit\<close> of the order functors pair.
This is terminology is borrowed from category theory - the functors
are an \<^emph>\<open>adjoint\<close>.\<close>

definition "unit \<equiv> r \<circ> l"

notation unit ("\<eta>")

lemma unit_eq_comp: "\<eta> = r \<circ> l" unfolding unit_def by simp

lemma unit_eq [simp]: "\<eta> x = r (l x)" by (simp add: unit_eq_comp)

context
begin

text \<open>Note that by flipping the roles of the left and rights functors,
we obtain a flipped interpretation of @{locale order_functors}.
In many cases, this allows us to obtain symmetric definitions and theorems for free.
As such, in many cases, we do we do not explicitly state those free results but
users can obtain them as needed by creating said flipped interpretation.\<close>

interpretation flip : order_functors R L r l .

definition "counit \<equiv> flip.unit"

notation counit ("\<epsilon>")

lemma counit_eq_comp: "\<epsilon> = l \<circ> r" unfolding counit_def flip.unit_def by simp

lemma counit_eq [simp]: "\<epsilon> x = l (r x)" by (simp add: counit_eq_comp)

end

context
begin

interpretation flip : order_functors R L r l .

lemma flip_counit_eq_unit: "flip.counit = \<eta>"
  by (intro ext) simp

lemma flip_unit_eq_counit: "flip.unit = \<epsilon>"
  by (intro ext) simp

lemma inflationary_on_unit_if_left_rel_right_if_left_right_relI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "\<And>x y. P x \<Longrightarrow> l x \<le>\<^bsub>R\<^esub> y \<Longrightarrow> x \<le>\<^bsub>L\<^esub> r y"
  shows "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro inflationary_onI) auto

lemma deflationary_on_unit_if_right_left_rel_if_right_rel_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "\<And>x y. P x \<Longrightarrow> y \<le>\<^bsub>R\<^esub> l x \<Longrightarrow> r y \<le>\<^bsub>L\<^esub> x"
  shows "deflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro deflationary_onI) auto

context
  fixes P :: "'a \<Rightarrow> bool"
begin

lemma rel_equivalence_on_unit_iff_inflationary_on_if_inverse_on:
  assumes "inverse_on P l r"
  shows "rel_equivalence_on P (\<le>\<^bsub>L\<^esub>) \<eta> \<longleftrightarrow> inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro iffI rel_equivalence_onI inflationary_onI deflationary_onI)
  (auto dest!: inverse_onD)

lemma reflexive_on_left_if_inflationary_on_unit_if_inverse_on:
  assumes "inverse_on P l r"
  and "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro reflexive_onI) (auto dest!: inverse_onD)

lemma rel_equivalence_on_unit_if_reflexive_on_if_inverse_on:
  assumes "inverse_on P l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  shows "rel_equivalence_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro rel_equivalence_onI inflationary_onI deflationary_onI)
  (auto dest!: inverse_onD)

end

corollary rel_equivalence_on_unit_iff_reflexive_on_if_inverse_on:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "inverse_on P l r"
  shows "rel_equivalence_on P (\<le>\<^bsub>L\<^esub>) \<eta> \<longleftrightarrow> reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  using assms reflexive_on_left_if_inflationary_on_unit_if_inverse_on
    rel_equivalence_on_unit_if_reflexive_on_if_inverse_on
  by (intro iffI) auto

end


text \<open>Here is an example of a free theorem.\<close>

notepad
begin
  interpret flip : order_functors R L r l
    rewrites "flip.unit \<equiv> \<epsilon>" by (simp only: flip_unit_eq_counit)
  have "\<lbrakk>((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r; reflexive_on P (\<le>\<^bsub>R\<^esub>); \<And>x y. \<lbrakk>P x; r x \<le>\<^bsub>L\<^esub> y\<rbrakk> \<Longrightarrow> x \<le>\<^bsub>R\<^esub> l y\<rbrakk>
      \<Longrightarrow> inflationary_on P (\<le>\<^bsub>R\<^esub>) \<epsilon>" for P
    by (fact flip.inflationary_on_unit_if_left_rel_right_if_left_right_relI)
end

end


end
