\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Half Galois Property\<close>
theory Half_Galois_Property
  imports
    Galois_Relator_Base
    Order_Equivalences
begin

text \<open>As the definition of the Galois property also works on heterogeneous relations,
we define the concepts in a locale that generalises @{locale galois}.\<close>

locale galois_prop = orders L R
  for L :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'c"
  and r :: "'d \<Rightarrow> 'b"
begin

sublocale galois_rel L R r .

interpretation gr_flip_inv : galois_rel "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" l .

abbreviation "right_ge_Galois \<equiv> gr_flip_inv.Galois"
notation right_ge_Galois (infix "\<^bsub>R\<^esub>\<greaterapprox>" 50)

abbreviation (input) "Galois_right \<equiv> gr_flip_inv.ge_Galois_left"
notation Galois_right (infix "\<lessapprox>\<^bsub>R\<^esub>" 50)

lemma Galois_rightI [intro]:
  assumes "in_dom (\<le>\<^bsub>L\<^esub>) x"
  and "l x \<le>\<^bsub>R\<^esub> y"
  shows "x \<lessapprox>\<^bsub>R\<^esub> y"
  using assms by blast

lemma Galois_rightE [elim]:
  assumes "x \<lessapprox>\<^bsub>R\<^esub> y"
  obtains "in_dom (\<le>\<^bsub>L\<^esub>) x" "l x \<le>\<^bsub>R\<^esub> y"
  using assms by blast

corollary Galois_right_iff_in_dom_and_left_right_rel:
  "x \<lessapprox>\<^bsub>R\<^esub> y \<longleftrightarrow> in_dom (\<le>\<^bsub>L\<^esub>) x \<and> l x \<le>\<^bsub>R\<^esub> y"
  by blast

text \<open>Unlike common literature, we split the definition of the Galois property
into two halves. This has its merits in modularity of proofs and preciser
statement of required assumptions.\<close>

definition "half_galois_prop_left \<equiv> \<forall>x y. x \<^bsub>L\<^esub>\<lessapprox> y \<longrightarrow> l x \<le>\<^bsub>R\<^esub> y"

notation galois_prop.half_galois_prop_left (infix "\<^sub>h\<unlhd>" 50)

lemma half_galois_prop_leftI [intro]:
  assumes "\<And>x y. x \<^bsub>L\<^esub>\<lessapprox> y \<Longrightarrow> l x \<le>\<^bsub>R\<^esub> y"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding half_galois_prop_left_def using assms by blast

lemma half_galois_prop_leftD [dest]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and " x \<^bsub>L\<^esub>\<lessapprox> y"
  shows "l x \<le>\<^bsub>R\<^esub> y"
  using assms unfolding half_galois_prop_left_def by blast

text\<open>Observe that the second half can be obtained by creating an appropriately
flipped and inverted interpretation of @{locale galois_prop}. Indeed, many
concepts in our formalisation are "closed" under inversion,
i.e. taking their inversion yields a statement for a related concept.
Many theorems can thus be derived for free by inverting (and flipping) the
concepts at hand. In such cases, we only state those theorems that require some
non-trivial setup. All other theorems can simply be obtained by creating a
suitable locale interpretation.\<close>

interpretation flip_inv : galois_prop "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l .

definition "half_galois_prop_right \<equiv> flip_inv.half_galois_prop_left"

notation galois_prop.half_galois_prop_right (infix "\<unlhd>\<^sub>h" 50)

lemma half_galois_prop_rightI [intro]:
  assumes "\<And>x y. x \<lessapprox>\<^bsub>R\<^esub> y \<Longrightarrow> x \<le>\<^bsub>L\<^esub> r y"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding half_galois_prop_right_def using assms by blast

lemma half_galois_prop_rightD [dest]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<lessapprox>\<^bsub>R\<^esub> y"
  shows "x \<le>\<^bsub>L\<^esub> r y"
  using assms unfolding half_galois_prop_right_def by blast

interpretation g : galois_prop S T f g for S T f g .

lemma rel_inv_half_galois_prop_right_eq_half_galois_prop_left_rel_inv [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<ge>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) blast

corollary half_galois_prop_left_rel_inv_iff_half_galois_prop_right [iff]:
  "((\<ge>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<ge>\<^bsub>R\<^esub>)) f g \<longleftrightarrow> ((\<le>\<^bsub>R\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L\<^esub>)) g f"
  by (simp flip: rel_inv_half_galois_prop_right_eq_half_galois_prop_left_rel_inv)

lemma rel_inv_half_galois_prop_left_eq_half_galois_prop_right_rel_inv [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<ge>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) blast

corollary half_galois_prop_right_rel_inv_iff_half_galois_prop_left [iff]:
  "((\<ge>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<ge>\<^bsub>R\<^esub>)) f g \<longleftrightarrow> ((\<le>\<^bsub>R\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L\<^esub>)) g f"
  by (simp flip: rel_inv_half_galois_prop_left_eq_half_galois_prop_right_rel_inv)

end

context galois
begin

sublocale galois_prop L R l r .

interpretation flip : galois R L r l .

abbreviation "right_Galois \<equiv> flip.Galois"
notation right_Galois (infix "\<^bsub>R\<^esub>\<lessapprox>" 50)

abbreviation (input) "ge_Galois_right \<equiv> flip.ge_Galois_left"
notation ge_Galois_right (infix "\<greaterapprox>\<^bsub>R\<^esub>" 50)

abbreviation "left_ge_Galois \<equiv> flip.right_ge_Galois"
notation left_ge_Galois (infix "\<^bsub>L\<^esub>\<greaterapprox>" 50)

abbreviation (input) "Galois_left \<equiv> flip.Galois_right"
notation Galois_left (infix "\<lessapprox>\<^bsub>L\<^esub>" 50)

context
begin

interpretation flip_inv : galois "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l .

lemma rel_unit_if_left_rel_if_mono_wrt_relI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "x \<lessapprox>\<^bsub>R\<^esub> l x' \<Longrightarrow> x \<le>\<^bsub>L\<^esub> \<eta> x'"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<le>\<^bsub>L\<^esub> \<eta> x'"
  using assms by auto

corollary rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<le>\<^bsub>L\<^esub> \<eta> x'"
  using assms by (auto intro: rel_unit_if_left_rel_if_mono_wrt_relI)

corollary rel_unit_if_reflexive_on_if_half_galois_prop_right_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "P x"
  shows "x \<le>\<^bsub>L\<^esub> \<eta> x"
  using assms by (blast intro: rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel)

corollary inflationary_on_unit_if_reflexive_on_if_half_galois_prop_rightI:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  shows "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro inflationary_onI)
  (fastforce intro: rel_unit_if_reflexive_on_if_half_galois_prop_right_if_mono_wrt_rel)

interpretation flip : galois_prop R L r l .

lemma right_rel_if_Galois_left_right_if_deflationary_onI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>R\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L\<^esub>)) r l"
  and "deflationary_on P (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  and "transitive (\<le>\<^bsub>R\<^esub>)"
  and "y \<lessapprox>\<^bsub>L\<^esub> r y'"
  and "P y'"
  shows "y \<le>\<^bsub>R\<^esub> y'"
  using assms by force

lemma half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "deflationary_on (in_codom (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  and "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro half_galois_prop_leftI) fastforce

end

interpretation flip_inv : galois "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l
  rewrites "flip_inv.unit \<equiv> \<epsilon>" and "flip_inv.counit \<equiv> \<eta>"
  and "\<And>R S. (R\<inverse> \<Rrightarrow>\<^sub>m S\<inverse>) \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  and "\<And>R S f g. (R\<inverse> \<unlhd>\<^sub>h S\<inverse>) f g \<equiv> (S \<^sub>h\<unlhd> R) g f"
  and "((\<ge>\<^bsub>R\<^esub>) \<^sub>h\<unlhd> (\<ge>\<^bsub>L\<^esub>)) r l \<equiv> ((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "\<And>R. R\<inverse>\<inverse> \<equiv> R"
  and "\<And>P R. inflationary_on P R\<inverse> \<equiv> deflationary_on P R"
  and "\<And>P R. deflationary_on P R\<inverse>  \<equiv> inflationary_on P R"
  and "\<And>(P :: 'b \<Rightarrow> bool). reflexive_on P (\<ge>\<^bsub>R\<^esub>) \<equiv> reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  and "\<And>R. transitive R\<inverse> \<equiv> transitive R"
  and "\<And>R. in_codom R\<inverse> \<equiv> in_dom R"
  by (simp_all add: flip_unit_eq_counit flip_counit_eq_unit
    galois_prop.half_galois_prop_left_rel_inv_iff_half_galois_prop_right
    galois_prop.half_galois_prop_right_rel_inv_iff_half_galois_prop_left)

corollary counit_rel_if_right_rel_if_mono_wrt_relI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "r y \<^bsub>L\<^esub>\<lessapprox> y' \<Longrightarrow> \<epsilon> y \<le>\<^bsub>R\<^esub> y'"
  and "y \<le>\<^bsub>R\<^esub> y'"
  shows "\<epsilon> y \<le>\<^bsub>R\<^esub> y'"
  using assms
  by (fact flip_inv.rel_unit_if_left_rel_if_mono_wrt_relI
    [simplified rel_inv_iff_rel])

corollary counit_rel_if_right_rel_if_half_galois_prop_left_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "y \<le>\<^bsub>R\<^esub> y'"
  shows "\<epsilon> y \<le>\<^bsub>R\<^esub> y'"
  using assms
  by (fact flip_inv.rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel
    [simplified rel_inv_iff_rel])

corollary counit_rel_if_reflexive_on_if_half_galois_prop_left_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  and "P y"
  shows "\<epsilon> y \<le>\<^bsub>R\<^esub> y"
  using assms
  by (fact flip_inv.rel_unit_if_reflexive_on_if_half_galois_prop_right_if_mono_wrt_rel
    [simplified rel_inv_iff_rel])

corollary deflationary_on_counit_if_reflexive_on_if_half_galois_prop_leftI:
  fixes P :: "'b \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  shows "deflationary_on P (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  using assms
  by (fact flip_inv.inflationary_on_unit_if_reflexive_on_if_half_galois_prop_rightI)

corollary left_rel_if_left_right_Galois_if_inflationary_onI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L\<^esub>)) r l"
  and "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "l x \<^bsub>R\<^esub>\<lessapprox> x'"
  and "P x"
  shows "x \<le>\<^bsub>L\<^esub> x'"
  using assms by (intro flip_inv.right_rel_if_Galois_left_right_if_deflationary_onI
    [simplified rel_inv_iff_rel])

corollary half_galois_prop_right_left_right_if_transitive_if_inflationary_on_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "inflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (fact flip_inv.half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel)

end

context order_functors
begin

interpretation g : galois L R l r .
interpretation flip_g : galois R L r l
  rewrites "flip_g.unit \<equiv> \<epsilon>" and "flip_g.counit \<equiv> \<eta>"
  by (simp_all only: flip_unit_eq_counit flip_counit_eq_unit)

lemma left_rel_if_left_right_rel_left_if_order_equivalenceI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "l x \<le>\<^bsub>R\<^esub> l x'"
  and "in_dom (\<le>\<^bsub>L\<^esub>) x"
  and "in_codom (\<le>\<^bsub>L\<^esub>) x'"
  shows "x \<le>\<^bsub>L\<^esub> x'"
  using assms by (auto intro!:
      flip_g.right_rel_if_Galois_left_right_if_deflationary_onI
      g.half_galois_prop_right_left_right_if_transitive_if_inflationary_on_if_mono_wrt_rel
    elim!: rel_equivalence_onE
    intro: inflationary_on_if_le_pred_if_inflationary_on
      in_field_if_in_dom in_field_if_in_codom)

end


end