theory Finite_Number_Type
  imports
    "HOL-Library.Cardinality"
begin

text \<open>
To avoid carrying the modulo all the time, we introduce a new type for integers @{term "{0..<L}"}
with the only restriction that the bound @{term L} must be greater than 1.
It generalizes $Z_{2^k}$, the group considered in ABY3's additive secret sharing scheme.
\<close>

consts L :: nat 

specification (L) L_gt_1: "L > 1"
  by auto

typedef natL = "{0..<int L}"
  using L_gt_1 by auto

setup_lifting type_definition_natL

instantiation natL :: comm_ring_1
begin

lift_definition zero_natL :: natL is 0
  using L_gt_1 by simp

lift_definition one_natL :: natL is 1
  using L_gt_1 by simp

lift_definition uminus_natL :: "natL \<Rightarrow> natL" is "\<lambda>x. (-x) mod int L"
  by simp

lift_definition plus_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is "\<lambda>x y. (x + y) mod int L"
  by simp

lift_definition minus_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is "\<lambda>x y. (x - y) mod int L"
  by simp

lift_definition times_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is "\<lambda>x y. (x * y) mod int L"
  by simp

instance
  by (standard; (transfer, simp add: algebra_simps mod_simps))

end
typ int

instantiation natL :: "{distrib_lattice, bounded_lattice, linorder}"
begin

lift_definition inf_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is inf
  unfolding inf_int_def by auto

lift_definition sup_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is sup
  unfolding sup_int_def by auto

lift_definition less_eq_natL :: "natL \<Rightarrow> natL \<Rightarrow> bool" is less_eq .

lift_definition less_natL :: "natL \<Rightarrow> natL \<Rightarrow> bool" is less .

lift_definition top_natL :: "natL" is "int L-1"
  using L_gt_1 by simp

lift_definition bot_natL :: "natL" is 0
  using L_gt_1 by simp

instance
  by (standard; (transfer, simp add: inf_int_def sup_int_def))+

end

instantiation natL :: semiring_modulo
begin

lift_definition divide_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is divide
  apply (auto simp: div_int_pos_iff)
  by (smt div_by_0 div_by_1 zdiv_mono2)

lift_definition modulo_natL :: "natL \<Rightarrow> natL \<Rightarrow> natL" is modulo
  apply (auto simp: mod_int_pos_iff)
  by (smt zmod_le_nonneg_dividend)

instance
  by (standard; (transfer, simp add: mod_simps))

end

instance natL :: finite
  apply standard
  unfolding type_definition.univ[OF type_definition_natL]
  by simp

lemma natL_card[simp]:
  "CARD(natL) = L"
  unfolding type_definition.univ[OF type_definition_natL]
  apply (subst card_image)
  subgoal by (meson Abs_natL_inject inj_onI)
  subgoal by simp
  done

end