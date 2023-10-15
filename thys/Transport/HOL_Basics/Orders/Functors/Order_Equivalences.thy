\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Equivalences\<close>
theory Order_Equivalences
  imports
    Order_Functors_Base
    Partial_Equivalence_Relations
    Preorders
begin

context order_functors
begin

definition "order_equivalence \<equiv>
  ((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l \<and>
  ((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r \<and>
  rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta> \<and>
  rel_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"

notation order_functors.order_equivalence (infix "\<equiv>\<^sub>o" 50)

lemma order_equivalenceI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding order_equivalence_def using assms by blast

lemma order_equivalenceE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l" "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
    "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
    "rel_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  using assms unfolding order_equivalence_def by blast

interpretation of : order_functors S T f g for S T f g .

lemma rel_inv_order_equivalence_eq_order_equivalence [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>))"
  by (intro ext)
  (auto intro!: of.order_equivalenceI simp: of.flip_unit_eq_counit)

corollary order_equivalence_right_left_iff_order_equivalence_left_right:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>L\<^esub>)) r l \<longleftrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  by (simp flip: rel_inv_order_equivalence_eq_order_equivalence)

text \<open>Due to the symmetry given by
@{thm "order_equivalence_right_left_iff_order_equivalence_left_right"},
for any theorem on @{term "(\<le>\<^bsub>L\<^esub>)"}, we obtain a corresponding theorem on
@{term "(\<le>\<^bsub>R\<^esub>)"} by flipping the roles of the two functors.
As such, in what follows, we do not explicitly state these free theorems but
users can obtain them as needed by creating a flipped interpretation
of @{locale order_functors}.\<close>

lemma order_equivalence_rel_inv_eq_order_equivalence [simp]:
  "((\<ge>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<ge>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>))"
  by (intro ext) (auto intro!: of.order_equivalenceI)

lemma in_codom_left_eq_in_dom_left_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  shows "in_codom (\<le>\<^bsub>L\<^esub>) = in_dom (\<le>\<^bsub>L\<^esub>)"
  using assms by (elim order_equivalenceE)
  (rule in_codom_eq_in_dom_if_rel_equivalence_on_in_field)

corollary preorder_on_in_field_left_if_transitive_if_order_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  shows "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  using assms by (elim order_equivalenceE)
  (rule preorder_on_in_field_if_transitive_if_rel_equivalence_on)

lemma order_equivalence_partial_equivalence_rel_not_reflexive_not_transitive:
  assumes "\<exists>(y :: 'b) y'. y \<noteq> y'"
  shows "\<exists>(L :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (R :: 'b \<Rightarrow> 'b \<Rightarrow> bool) l r.
    (L \<equiv>\<^sub>o R) l r \<and> partial_equivalence_rel L \<and>
    \<not>(reflexive_on (in_field R) R) \<and> \<not>(transitive_on (in_field R) R)"
proof -
  from assms obtain cy cy' where "(cy :: 'b) \<noteq> cy'" by blast
  let ?cx = "undefined :: 'a"
  let ?L = "\<lambda>x x'. ?cx = x \<and> x = x'"
  and ?R = "\<lambda>y y'. (y = cy \<or> y = cy') \<and> (y' = cy \<or> y' = cy') \<and> (y \<noteq> cy' \<or> y' \<noteq> cy')"
  and ?l = "\<lambda>(a :: 'a). cy"
  and ?r = "\<lambda>(b :: 'b). ?cx"
  have "(?L \<equiv>\<^sub>o ?R)?l ?r" using \<open>cy \<noteq> cy'\<close>
    by (intro of.order_equivalenceI) (auto 0 4)
  moreover have "partial_equivalence_rel ?L" by blast
  moreover have
    "\<not>(transitive_on (in_field ?R) ?R)" and "\<not>(reflexive_on (in_field ?R) ?R)"
    using \<open>cy \<noteq> cy'\<close> by auto
  ultimately show "?thesis" by blast
qed

end


end