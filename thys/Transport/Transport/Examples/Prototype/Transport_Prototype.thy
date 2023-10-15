\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport via Equivalences on PERs (Prototype)\<close>
theory Transport_Prototype
  imports
    Transport_Rel_If
    ML_Unification.ML_Unification_HOL_Setup
    ML_Unification.Unify_Resolve_Tactics
  keywords "trp_term" :: thy_goal_defn
begin

paragraph \<open>Summary\<close>
text \<open>We implement a simple Transport prototype. The prototype is restricted
to work with equivalences on partial equivalence relations.
It is also not forming the compositions of equivalences so far.
The support for dependent function relators is restricted to the form
described in
@{thm transport_Dep_Fun_Rel_no_dep_fun.partial_equivalence_rel_equivalenceI}:
The relations can be dependent, but the functions must be simple.
This is not production ready, but a proof of concept.

The package provides a command @{command trp_term}, which sets up the
required goals to prove a given term. See the examples in this directory for
some use cases and refer to \<^cite>\<open>"transport"\<close> for more details.\<close>

paragraph \<open>Theorem Setups\<close>

context transport
begin

lemma left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro left_Galois_left_if_left_rel_if_inflationary_on_in_fieldI)
  (blast elim: preorder_equivalence_order_equivalenceE)+

definition "transport_per x y \<equiv> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r \<and> x \<^bsub>L\<^esub>\<lessapprox> y"

text \<open>The choice of @{term "x'"} is arbitrary. All we need is @{term "in_dom (\<le>\<^bsub>L\<^esub>) x"}.\<close>
lemma transport_per_start:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "transport_per x (l x)"
  using assms unfolding transport_per_def
  by (blast intro: left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence)

lemma left_Galois_if_transport_per:
  assumes "transport_per x y"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms unfolding transport_per_def by blast

end

context transport_Fun_Rel
begin

text \<open>Simplification of Galois relator for simple function relator.\<close>

corollary left_Galois_eq_Fun_Rel_left_Galois:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
proof (intro ext)
  fix f g
  show "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  proof
    assume "f \<^bsub>L\<^esub>\<lessapprox> g"
    moreover have "g \<le>\<^bsub>R\<^esub> g"
    proof -
      from assms have per: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
        by (intro partial_equivalence_rel_equivalenceI) auto
      with \<open>f \<^bsub>L\<^esub>\<lessapprox> g\<close> show ?thesis by blast
    qed
    ultimately show "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g" using assms
      by (intro Fun_Rel_left_Galois_if_left_GaloisI)
      (auto elim!: tdfrs.t1.partial_equivalence_rel_equivalenceE
        tdfrs.t1.preorder_equivalence_galois_equivalenceE
        tdfrs.t1.galois_equivalenceE
        intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
  next
    assume "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
    with assms have "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> f g"
      by (subst Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI) blast+
    with assms show "f \<^bsub>L\<^esub>\<lessapprox> g"
      by (intro left_Galois_if_Fun_Rel_left_GaloisI) blast+
  qed
qed

end

lemmas related_Fun_Rel_combI = Dep_Fun_Rel_relD[where ?S="\<lambda>_ _. S" for S, rotated]
lemma related_Fun_Rel_lambdaI:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  and "T = (R \<Rrightarrow> S)"
  shows "T f g"
  using assms by blast


paragraph \<open>General ML setups\<close>
ML_file\<open>transport_util.ML\<close>

paragraph \<open>Unification Setup\<close>

ML\<open>
  @{functor_instance struct_name = Transport_Unification_Combine
    and functor_name = Unification_Combine
    and id = Transport_Util.transport_id}
\<close>
local_setup \<open>Transport_Unification_Combine.setup_attribute NONE\<close>
ML\<open>
  @{functor_instance struct_name = Transport_Mixed_Unification
    and functor_name = Mixed_Unification
    and id = Transport_Util.transport_id
    and more_args = \<open>structure UC = Transport_Unification_Combine\<close>}
\<close>

ML\<open>
  @{functor_instance struct_name = Transport_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = Transport_Util.transport_id
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        concl_unifier = SOME Higher_Order_Pattern_Unification.unify,
        normalisers = SOME Transport_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
        prems_unifier = SOME (Transport_Mixed_Unification.first_higherp_first_comb_higher_unify
          |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.unifiables),
        hint_preprocessor = SOME (K I)
      }\<close>}
\<close>
local_setup \<open>Transport_Unification_Hints.setup_attribute NONE\<close>
declare [[trp_uhint where hint_preprocessor = \<open>Unification_Hints_Base.obj_logic_hint_preprocessor
  @{thm atomize_eq[symmetric]} (Conv.rewr_conv @{thm eq_eq_True})\<close>]]
declare [[trp_ucombine add = \<open>Transport_Unification_Combine.eunif_data
  (Transport_Unification_Hints.try_hints
  |> Unification_Combinator.norm_unifier
    (#norm_term Transport_Mixed_Unification.norms_first_higherp_first_comb_higher_unify)
  |> K)
  (Transport_Unification_Combine.default_metadata Transport_Unification_Hints.binding)\<close>]]

paragraph \<open>Prototype\<close>
ML_file\<open>transport.ML\<close>

declare
  transport_Dep_Fun_Rel.transport_defs[trp_def]
  transport_Fun_Rel.transport_defs[trp_def]

declare
  (*dependent case currently disabled by default since they easily make the
    unifier enumerate many undesired instantiations*)
  (* transport_Dep_Fun_Rel.partial_equivalence_rel_equivalenceI[per_intro] *)
  (* transport.rel_if_partial_equivalence_rel_equivalence_if_iff_if_partial_equivalence_rel_equivalenceI[rotated, per_intro]
  transport_Dep_Fun_Rel_no_dep_fun.partial_equivalence_rel_equivalenceI
    [ML_Krattr \<open>Conversion_Util.move_prems_to_front_conv [1] |> Conversion_Util.thm_conv\<close>,
    ML_Krattr \<open>Conversion_Util.move_prems_to_front_conv [2,3] |> Conversion_Util.thm_conv\<close>,
    per_intro] *)
  transport_Fun_Rel.partial_equivalence_rel_equivalenceI[rotated, per_intro]
  transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro]
  transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro]

declare
  transport_id.left_Galois_eq_left[trp_relator_rewrite]
  transport_Fun_Rel.left_Galois_eq_Fun_Rel_left_Galois[trp_relator_rewrite]


end
