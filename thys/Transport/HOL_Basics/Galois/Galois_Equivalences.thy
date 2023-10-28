\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Equivalences\<close>
theory Galois_Equivalences
  imports
    Galois_Connections
    Order_Equivalences
    Partial_Equivalence_Relations
begin

context galois
begin

text\<open>In the literature, an adjoint equivalence is an adjunction for which
the unit and counit are natural isomorphisms.
Translated to the category of orders,
this means that a \<^emph>\<open>Galois equivalence\<close> between two relations
@{term "(\<le>\<^bsub>L\<^esub>)"} and @{term "(\<le>\<^bsub>R\<^esub>)"} is a Galois connection for which the unit
@{term "\<eta>"} is @{term "deflationary"} and the counit @{term "\<epsilon>"} is
@{term "inflationary"}.

For reasons of symmetry, we give a different definition which next to
@{term "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"} requires @{term "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"}.
In other words, a Galois equivalence is a Galois connection for which the left
and right adjoints are also right and left adjoints, respectively.
As shown below, in the case of preorders, the definitions coincide.\<close>

definition "galois_equivalence \<equiv> ((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r \<and> ((\<le>\<^bsub>R\<^esub>) \<unlhd> (\<le>\<^bsub>L\<^esub>)) r l"

notation galois.galois_equivalence (infix "\<equiv>\<^sub>G" 50)

lemma galois_equivalenceI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<unlhd> (\<le>\<^bsub>L\<^esub>)) r l"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding galois_equivalence_def using assms by blast

lemma galois_equivalenceE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r" "((\<le>\<^bsub>R\<^esub>) \<stileturn> (\<le>\<^bsub>L\<^esub>)) r l"
  using assms unfolding galois_equivalence_def
  by (blast intro: galois.galois_connectionI)

context
begin

interpretation g : galois S T f g for S T f g.

lemma galois_equivalence_eq_galois_connection_rel_inf_galois_prop:
  "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) \<sqinter> ((\<ge>\<^bsub>L\<^esub>) \<unlhd> (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) auto

lemma rel_inv_galois_equivalence_eq_galois_equivalence [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>))"
  by (intro ext) auto

corollary galois_equivalence_right_left_iff_galois_equivalence_left_right:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>L\<^esub>)) r l \<longleftrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  by auto

lemma galois_equivalence_rel_inv_eq_galois_equivalence [simp]:
  "((\<ge>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<ge>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>))"
  by (intro ext) auto

lemma inflationary_on_unit_if_reflexive_on_if_galois_equivalence:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  shows "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro inflationary_on_unit_if_reflexive_on_if_galois_connection)
  (elim galois_equivalenceE)

end

lemma deflationary_on_unit_if_reflexive_on_if_galois_equivalence:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  shows "deflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
proof -
  interpret flip : galois R L r l .
  show ?thesis using assms
  by (auto intro: flip.deflationary_on_counit_if_reflexive_on_if_galois_connection
    simp only: flip.flip_unit_eq_counit)
qed

text \<open>Every @{term "galois_equivalence"} on reflexive orders is a Galois
equivalence in the sense of the common literature.\<close>
lemma rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  shows "rel_equivalence_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro rel_equivalence_onI
    inflationary_on_unit_if_reflexive_on_if_galois_equivalence
    deflationary_on_unit_if_reflexive_on_if_galois_equivalence)

lemma galois_equivalence_partial_equivalence_rel_not_reflexive_not_transitive:
  assumes "\<exists>(y :: 'b) y'. y \<noteq> y'"
  shows "\<exists>(L :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (R :: 'b \<Rightarrow> 'b \<Rightarrow> bool) l r.
    (L \<equiv>\<^sub>G R) l r \<and> partial_equivalence_rel L \<and>
    \<not>(reflexive_on (in_field R) R) \<and> \<not>(transitive_on (in_field R) R)"
proof -
  from assms obtain cy cy' where "(cy :: 'b) \<noteq> cy'" by blast
  let ?cx = "undefined :: 'a"
  let ?L = "\<lambda>x x'. ?cx = x \<and> x = x'"
  and ?R = "\<lambda>y y'. (y = cy \<or> y = cy') \<and> (y' = cy \<or> y' = cy') \<and> (y \<noteq> cy' \<or> y' \<noteq> cy')"
  and ?l = "\<lambda>(a :: 'a). cy"
  and ?r = "\<lambda>(b :: 'b). ?cx"
  interpret g : galois ?L ?R ?l ?r .
  interpret flip_g : galois ?R ?L ?r ?l .
  have "(?L \<equiv>\<^sub>G ?R) ?l ?r" using \<open>cy \<noteq> cy'\<close> by blast
  moreover have "partial_equivalence_rel ?L" by blast
  moreover have
    "\<not>(transitive_on (in_field ?R) ?R)" and "\<not>(reflexive_on (in_field ?R) ?R)"
    using \<open>cy \<noteq> cy'\<close> by auto
  ultimately show "?thesis" by blast
qed


subsection \<open>Equivalence of Order Equivalences and Galois Equivalences\<close>

text \<open>In general categories, every adjoint equivalence is an equivalence
but not vice versa.
In the category of preorders, however, they are morally the same: the
adjoint zigzag equations are satisfied up to unique isomorphism rather than
equality.
In the category of partial orders, the concepts coincide.\<close>

lemma half_galois_prop_left_left_right_if_transitive_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)" "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel)
  (auto elim!: order_equivalenceE
    intro: deflationary_on_if_le_pred_if_deflationary_on in_field_if_in_codom
    intro!: le_predI)

lemma half_galois_prop_right_left_right_if_transitive_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)" "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro half_galois_prop_right_left_right_if_transitive_if_inflationary_on_if_mono_wrt_rel)
  (auto elim!: order_equivalenceE
    intro: inflationary_on_if_le_pred_if_inflationary_on in_field_if_in_dom
    intro!: le_predI
    simp only: flip_counit_eq_unit)

lemma galois_prop_left_right_if_transitive_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)" "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
    half_galois_prop_left_left_right_if_transitive_if_order_equivalence
    half_galois_prop_right_left_right_if_transitive_if_order_equivalence
  by blast

corollary galois_connection_left_right_if_transitive_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)" "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms galois_prop_left_right_if_transitive_if_order_equivalence
  by (intro galois_connectionI) auto

interpretation flip : galois R L r l
  rewrites "flip.unit \<equiv> \<epsilon>"
  by (simp only: flip_unit_eq_counit)

corollary galois_equivalence_left_right_if_transitive_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)" "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms galois_connection_left_right_if_transitive_if_order_equivalence
    flip.galois_prop_left_right_if_transitive_if_order_equivalence
  by (intro galois_equivalenceI)
  (auto simp only: order_equivalence_right_left_iff_order_equivalence_left_right)

lemma order_equivalence_if_reflexive_on_in_field_if_galois_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" "reflexive_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence
    flip.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence
  by (intro order_equivalenceI)
  (auto simp only: galois_equivalence_right_left_iff_galois_equivalence_left_right)

corollary galois_equivalence_eq_order_equivalence_if_preorder_on_in_field:
  assumes "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>))"
  using assms
    galois.order_equivalence_if_reflexive_on_in_field_if_galois_equivalence
    galois.galois_equivalence_left_right_if_transitive_if_order_equivalence
  by (elim preorder_on_in_fieldE, intro ext) blast

end


end