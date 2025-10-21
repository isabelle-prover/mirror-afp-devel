section \<open>Relational Constructions\<close>

theory Relational_Constructions

imports Stone_Relation_Algebras.Relation_Algebras

begin

text \<open>
This theory defines relational constructions for extrema, bounds and suprema, the univalent part and symmetric quotients.
All definitions and most properties are standard; for example, see \cite{BerghammerSchmidtZierer1989,Riguet1948,Schmidt2011,SchmidtStroehlein1989}.
Some properties are new.
We start with a few general properties of relations and orders.
\<close>

context bounded_distrib_allegory
begin

lemma transitive_mapping_idempotent:
  "transitive x \<Longrightarrow> mapping x \<Longrightarrow> idempotent x"
  by (smt (verit, ccfv_threshold) conv_dist_comp conv_involutive epm_3 inf.order_iff top_greatest total_conv_surjective transitive_conv_closed mult_assoc)

end

context pd_allegory
begin

lemma comp_univalent_complement:
  assumes "univalent x"
    shows "x * -y = x * top \<sqinter> -(x * y)"
proof (rule order.antisym)
  show "x * -y \<le> x * top \<sqinter> -(x * y)"
    by (simp add: assms comp_isotone comp_univalent_below_complement)
  show "x * top \<sqinter> -(x * y) \<le> x * -y"
    by (metis inf.sup_left_divisibility inf_top.left_neutral theorem24xxiii)
qed

lemma comp_injective_complement:
  "injective x \<Longrightarrow> -y * x = top * x \<sqinter> -(y * x)"
  by (smt (verit, ccfv_threshold) antisym_conv comp_injective_below_complement complement_conv_sub dedekind_2 inf.bounded_iff mult_left_isotone order_lesseq_imp top.extremum)

lemma strict_order_irreflexive:
  "irreflexive (x \<sqinter> -1)"
  by simp

lemma strict_order_transitive_1:
  "antisymmetric x \<Longrightarrow> transitive x \<Longrightarrow> x * (x \<sqinter> -1) \<le> x \<sqinter> -1"
  by (smt (verit, best) bot_unique inf.order_trans inf.semilattice_order_axioms mult.monoid_axioms p_shunting_swap schroeder_5_p semiring.add_decreasing2 semiring.mult_left_mono sup.bounded_iff symmetric_one_closed monoid.right_neutral semilattice_order.boundedI semilattice_order.cobounded1 semilattice_order.cobounded2)

lemma strict_order_transitive_2:
  "antisymmetric x \<Longrightarrow> transitive x \<Longrightarrow> (x \<sqinter> -1) * x \<le> x \<sqinter> -1"
  by (smt (verit, ccfv_SIG) comp_commute_below_diversity dual_order.eq_iff inf.boundedE inf.order_iff inf.sup_monoid.add_assoc mult_left_isotone strict_order_transitive_1)

lemma strict_order_transitive:
  "antisymmetric x \<Longrightarrow> transitive x \<Longrightarrow> (x \<sqinter> -1) * (x \<sqinter> -1) \<le> x \<sqinter> -1"
  using comp_isotone inf.cobounded1 inf.order_lesseq_imp strict_order_transitive_2 by blast

lemma strict_order_transitive_eq_1:
  "order x \<Longrightarrow> (x \<sqinter> -1) * x = x \<sqinter> -1"
  by (metis comp_right_one dual_order.antisym mult_right_isotone strict_order_transitive_2)

lemma strict_order_transitive_eq_2:
  "order x \<Longrightarrow> x * (x \<sqinter> -1) = x \<sqinter> -1"
  by (metis dual_order.antisym mult_1_left mult_left_isotone strict_order_transitive_1)

lemma strict_order_transitive_eq:
  "order x \<Longrightarrow> (x \<sqinter> -1) * x = x * (x \<sqinter> -1)"
  by (simp add: strict_order_transitive_eq_1 strict_order_transitive_eq_2)

lemma strict_order_asymmetric:
  "antisymmetric x \<Longrightarrow> asymmetric (x \<sqinter> -1)"
  by (metis antisymmetric_inf_closed antisymmetric_inf_diversity inf.order_iff inf.right_idem pseudo_complement)

end

text \<open>
The following gives relational definitions for extrema, bounds, suprema, the univalent part and symmetric quotients.
\<close>

context relation_algebra_signature
begin

definition maximal :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "maximal r s \<equiv> s \<sqinter> -((r \<sqinter> -1) * s)"

definition minimal :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "minimal r s \<equiv> s \<sqinter> -((r\<^sup>T \<sqinter> -1) * s)"

definition upperbound :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "upperbound r s \<equiv> -(-r\<^sup>T * s)"

definition lowerbound :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "lowerbound r s \<equiv> -(-r * s)"

definition greatest :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "greatest r s \<equiv> s \<sqinter> -(-r\<^sup>T * s)"

definition least :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "least r s \<equiv> s \<sqinter> -(-r * s)"

definition supremum :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "supremum r s \<equiv> least r (upperbound r s)"

definition infimum :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "infimum r s \<equiv> greatest r (lowerbound r s)"

definition univalent_part :: "'a \<Rightarrow> 'a" where
  "univalent_part r \<equiv> r \<sqinter> -(r * -1)"

definition symmetric_quotient :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "symmetric_quotient r s \<equiv> -(r\<^sup>T * -s) \<sqinter> -(-r\<^sup>T * s)"

abbreviation noyau :: "'a \<Rightarrow> 'a" where
  "noyau r \<equiv> symmetric_quotient r r"

end

context relation_algebra
begin

subsection \<open>Extrema, bounds and suprema\<close>

lemma maximal_comparable:
  "r \<sqinter> (maximal r s) * (maximal r s)\<^sup>T \<le> r\<^sup>T"
proof -
  have "r \<sqinter> -r\<^sup>T \<le> r \<sqinter> -1"
    by (metis inf_commute inf_le2 le_inf_iff one_inf_conv p_shunting_swap)
  hence "maximal r s \<sqinter> (r \<sqinter> -r\<^sup>T) * maximal r s \<le> maximal r s \<sqinter> (r \<sqinter> -1) * s"
    using comp_inf.mult_right_isotone comp_isotone dual_order.eq_iff maximal_def by fastforce
  also have "... \<le> bot"
    by (simp add: inf_commute maximal_def)
  finally show ?thesis
    by (smt (verit, best) double_compl inf.sup_monoid.add_assoc inf_commute le_bot pseudo_complement schroeder_2)
qed

lemma maximal_comparable_same:
  assumes "antisymmetric r"
    shows "r \<sqinter> (maximal r s) * (maximal r s)\<^sup>T \<le> 1"
  by (meson assms inf.sup_left_divisibility le_infI order_trans maximal_comparable)

lemma transitive_lowerbound:
  "transitive r \<Longrightarrow> r * lowerbound r s \<le> lowerbound r s"
  by (metis comp_associative double_compl lowerbound_def mult_left_isotone schroeder_3_p)

lemma transitive_least:
  "transitive r \<Longrightarrow> r * least r top \<le> least r top"
  using least_def lowerbound_def transitive_lowerbound by auto

lemma transitive_minimal_not_least:
  assumes "transitive r"
    shows "r\<^sup>T * minimal r (-least r top) \<le> -least r top"
proof -
  have "least r top \<le> -minimal r (-least r top)"
    by (simp add: minimal_def)
  hence "r * least r top \<le> -minimal r (-least r top)"
    using assms dual_order.trans transitive_least by blast
  thus ?thesis
    using schroeder_3_p by auto
qed

lemma least_injective:
  assumes "antisymmetric r"
    shows "injective (least r s)"
proof -
  have "(least r s) * (least r s)\<^sup>T \<le> -(-r * s) * s\<^sup>T \<sqinter> s * -(-r * s)\<^sup>T"
    by (simp add: least_def comp_isotone conv_complement conv_dist_inf)
  also have "... \<le> r \<sqinter> r\<^sup>T"
    by (metis comp_inf.comp_isotone conv_complement conv_dist_comp pp_increasing schroeder_3 schroeder_5)
  also have "... \<le> 1"
    by (simp add: assms)
  finally show ?thesis
    .
qed

lemma least_conv_greatest:
  "least r = greatest (r\<^sup>T)"
  using greatest_def least_def by fastforce

lemma greatest_injective:
  "antisymmetric r \<Longrightarrow> injective (greatest r s)"
  by (metis antisymmetric_conv_closed least_injective least_conv_greatest conv_involutive)

lemma supremum_upperbound:
  assumes "antisymmetric r"
      and "s \<le> r"
    shows "supremum r s = 1 \<longleftrightarrow> upperbound r s \<le> r\<^sup>T"
proof (rule iffI)
  assume "supremum r s = 1"
  hence "1 \<le> lowerbound r (upperbound r s)"
    using least_def lowerbound_def supremum_def by auto
  thus "upperbound r s \<le> r\<^sup>T"
    by (metis comp_right_one compl_le_compl_iff compl_le_swap1 conv_complement schroeder_3_p lowerbound_def)
next
  assume 1: "upperbound r s \<le> r\<^sup>T"
  hence 2: "1 \<le> lowerbound r (upperbound r s)"
    by (simp add: compl_le_swap1 conv_complement schroeder_3_p lowerbound_def)
  have 3: "1 \<le> upperbound r s"
    by (simp add: assms(2) compl_le_swap1 conv_complement schroeder_3_p upperbound_def)
  hence "lowerbound r (upperbound r s) \<le> r"
    using brouwer.p_antitone_iff mult_right_isotone lowerbound_def by fastforce
  hence "supremum r s \<le> 1"
    using 1 by (smt (verit, del_insts) assms(1) least_def inf.sup_mono inf_commute order.trans lowerbound_def supremum_def)
  thus "supremum r s = 1"
    using 2 3 least_def order.eq_iff lowerbound_def supremum_def by auto
qed

subsection \<open>Univalent part\<close>

lemma univalent_part_idempotent:
  "univalent_part (univalent_part r) = univalent_part r"
  by (smt (verit, best) inf.absorb2 inf.cobounded1 inf.order_iff inf_assoc mult_left_isotone p_antitone_inf univalent_part_def)

lemma univalent_part_univalent:
  "univalent (univalent_part r)"
  by (smt (verit, ccfv_SIG) inf.cobounded1 inf.sup_monoid.add_commute mult_left_isotone order_lesseq_imp p_antitone_iff regular_one_closed schroeder_3_p univalent_part_def)

lemma univalent_part_times_converse:
  "r\<^sup>T * univalent_part r = (univalent_part r)\<^sup>T * univalent_part r"
proof -
  have 1: "(r \<sqinter> r * -1)\<^sup>T * univalent_part r \<le> 1"
    by (smt (verit, best) compl_le_swap1 inf.cobounded1 inf.cobounded2 mult_left_isotone order_lesseq_imp regular_one_closed schroeder_3_p univalent_part_def)
  hence 2: "(r \<sqinter> r * -1)\<^sup>T * univalent_part r \<le> -1"
    by (simp add: inf.coboundedI2 schroeder_3_p univalent_part_def)
  have "r\<^sup>T * univalent_part r = (r \<sqinter> r * -1)\<^sup>T * univalent_part r \<squnion> (univalent_part r)\<^sup>T * univalent_part r"
    by (metis conv_dist_sup maddux_3_11 mult_right_dist_sup univalent_part_def)
  thus ?thesis
    using 1 2 by (metis inf.orderE inf_compl_bot_right maddux_3_13 pseudo_complement)
qed

lemma univalent_part_times_converse_1:
  "r\<^sup>T * univalent_part r \<le> 1"
  by (simp add: univalent_part_times_converse univalent_part_univalent)

lemma minimal_univalent_part:
  assumes "reflexive r"
      and "vector s"
    shows "minimal r s = s \<sqinter> univalent_part ((r \<sqinter> s)\<^sup>T) * top"
proof (rule order.antisym)
  have "1 \<sqinter> r\<^sup>T * (-1 \<sqinter> s) \<le> (r\<^sup>T \<sqinter> -1 \<sqinter> s\<^sup>T) * (-1 \<sqinter> s)"
    by (smt (z3) conv_complement conv_dist_inf dedekind_2 equivalence_one_closed inf.sup_monoid.add_assoc inf.sup_monoid.add_commute mult_1_left)
  also have "... \<le> (r\<^sup>T \<sqinter> -1) * s"
    using inf_le1 inf_le2 mult_isotone by blast
  finally have "1 \<sqinter> -((r\<^sup>T \<sqinter> -1) * s) \<le> -(r\<^sup>T * (-1 \<sqinter> s))"
    by (simp add: p_shunting_swap)
  also have 1: "... = -((r \<sqinter> s)\<^sup>T * -1)"
    by (simp add: assms(2) conv_dist_inf covector_inf_comp_3 inf.sup_monoid.add_commute)
  finally have 2: "1 \<sqinter> -((r\<^sup>T \<sqinter> -1) * s) \<le> r\<^sup>T \<sqinter> -((r \<sqinter> s)\<^sup>T * -1)"
    by (simp add: assms(1) le_infI1 reflexive_conv_closed)
  have "minimal r s = (1 \<sqinter> -((r\<^sup>T \<sqinter> -1) * s)) * s"
    by (metis assms(2) complement_vector inf_commute vector_export_comp_unit minimal_def mult_assoc)
  also have "... \<le> (r\<^sup>T \<sqinter> -((r \<sqinter> s)\<^sup>T * -1)) * s"
    using 2 mult_left_isotone by blast
  also have 3: "... = univalent_part ((r \<sqinter> s)\<^sup>T) * top"
    by (smt (verit, ccfv_threshold) assms(2) comp_inf.vector_top_closed comp_inf_covector comp_inf_vector conv_dist_inf inf.sup_monoid.add_assoc inf.sup_monoid.add_commute surjective_one_closed vector_conv_covector univalent_part_def)
  finally show "minimal r s \<le> s \<sqinter> univalent_part ((r \<sqinter> s)\<^sup>T) * top"
    by (simp add: minimal_def)
  have "s \<sqinter> (r\<^sup>T \<sqinter> -1) * s \<sqinter> 1 \<le> (r\<^sup>T \<sqinter> -1) * s \<sqinter> 1"
    using comp_inf.comp_isotone inf.cobounded2 by blast
  also have "... \<le> (r\<^sup>T \<sqinter> -1) * (s \<sqinter> (r\<^sup>T \<sqinter> -1)\<^sup>T)"
    by (metis comp_right_one dedekind_1)
  also have "... \<le> r\<^sup>T * (s \<sqinter> -1)"
    using comp_inf.mult_right_isotone conv_complement conv_dist_inf mult_isotone by auto
  finally have 4: "s \<sqinter> (r\<^sup>T \<sqinter> -1) * s \<sqinter> 1 \<le> r\<^sup>T * (s \<sqinter> -1)"
    .
  have "s \<sqinter> (r\<^sup>T \<sqinter> -1) * s \<sqinter> -1 \<le> r\<^sup>T * (s \<sqinter> -1)"
    by (metis assms(1) comp_inf.comp_left_subdist_inf inf.coboundedI1 inf.order_trans mult_1_left mult_left_isotone order.refl reflexive_conv_closed)
  hence 5: "s \<sqinter> (r\<^sup>T \<sqinter> -1) * s \<le> r\<^sup>T * (s \<sqinter> -1)"
    using 4 comp_inf.case_split_right heyting.implies_itself_top by blast
  have "s \<sqinter> (r\<^sup>T \<sqinter> -1) * s \<sqinter> (r\<^sup>T \<sqinter> -(r\<^sup>T * (s \<sqinter> -1))) * s = (s \<sqinter> (r\<^sup>T \<sqinter> -1) * s \<sqinter> r\<^sup>T \<sqinter> -(r\<^sup>T * (s \<sqinter> -1))) * s"
    using assms(2) inf_assoc vector_inf_comp mult_assoc by simp
  also have "... = bot"
    using 5 le_infI1 semiring.mult_not_zero shunting_1 by blast
  finally have "s \<sqinter> univalent_part ((r \<sqinter> s)\<^sup>T) * top \<le> -((r\<^sup>T \<sqinter> -1) * s)"
    using 1 3 by (simp add: inf.sup_monoid.add_commute p_shunting_swap pseudo_complement)
  thus "s \<sqinter> univalent_part ((r \<sqinter> s)\<^sup>T) * top \<le> minimal r s"
    by (simp add: minimal_def)
qed

subsection \<open>Symmetric quotients\<close>

lemma univalent_part_syq:
  "univalent_part r = symmetric_quotient (r\<^sup>T) 1"
  by (simp add: inf_commute symmetric_quotient_def univalent_part_def)

lemma minimal_syq:
  assumes "reflexive r"
      and "vector s"
    shows "minimal r s = s \<sqinter> symmetric_quotient (r \<sqinter> s) 1 * top"
  by (simp add: assms minimal_univalent_part univalent_part_syq)

lemma syq_complement:
  "symmetric_quotient (-r) (-s) = symmetric_quotient r s"
  by (simp add: conv_complement inf.sup_monoid.add_commute symmetric_quotient_def)

lemma syq_converse:
  "(symmetric_quotient r s)\<^sup>T = symmetric_quotient s r"
  by (simp add: conv_complement conv_dist_comp conv_dist_inf inf.sup_monoid.add_commute symmetric_quotient_def)

lemma syq_comp_transitive:
  "symmetric_quotient r s * symmetric_quotient s p \<le> symmetric_quotient r p"
proof -
  have "r * -(r\<^sup>T * -s) * -(s\<^sup>T * -p) \<le> s * -(s\<^sup>T * -p)"
    by (metis complement_conv_sub conv_complement mult_left_isotone schroeder_5)
  also have "... \<le> p"
    by (simp add: schroeder_3)
  finally have 1: "-(r\<^sup>T * -s) * -(s\<^sup>T * -p) \<le> -(r\<^sup>T * -p)"
    by (simp add: p_antitone_iff schroeder_3_p mult_assoc)
  have "-(-r\<^sup>T * s) * -(-s\<^sup>T * p) * p\<^sup>T \<le> -(-r\<^sup>T * s) * s\<^sup>T"
    by (metis complement_conv_sub double_compl mult_right_isotone mult_assoc)
  also have "... \<le> r\<^sup>T"
    using brouwer.pp_increasing complement_conv_sub inf.order_trans by blast
  finally have 2: "-(-r\<^sup>T * s) * -(-s\<^sup>T * p) \<le> -(-r\<^sup>T * p)"
    by (metis compl_le_swap1 double_compl schroeder_4)
  have "symmetric_quotient r s * symmetric_quotient s p \<le> -(r\<^sup>T * -s) * -(s\<^sup>T * -p) \<sqinter> -(-r\<^sup>T * s) * -(-s\<^sup>T * p)"
    by (simp add: mult_isotone symmetric_quotient_def)
  also have "... \<le> -(r\<^sup>T * -p) \<sqinter> -(-r\<^sup>T * p)"
    using 1 2 inf_mono by blast
  finally show ?thesis
    by (simp add: symmetric_quotient_def)
qed

lemma syq_comp_syq_top:
  "symmetric_quotient r s * symmetric_quotient s p = symmetric_quotient r p \<sqinter> symmetric_quotient r s * top"
proof (rule order.antisym)
  show "symmetric_quotient r s * symmetric_quotient s p \<le> symmetric_quotient r p \<sqinter> symmetric_quotient r s * top"
    by (simp add: mult_right_isotone syq_comp_transitive)
  have "symmetric_quotient r p \<sqinter> symmetric_quotient r s * top \<le> symmetric_quotient r s * symmetric_quotient s r * symmetric_quotient r p"
    by (metis comp_right_one dedekind_1 inf_top_left inf_vector_comp mult_assoc syq_converse)
  also have "... \<le> symmetric_quotient r s * symmetric_quotient s p"
    by (simp add: mult_right_isotone mult_assoc syq_comp_transitive)
  finally show "symmetric_quotient r p \<sqinter> symmetric_quotient r s * top \<le> symmetric_quotient r s * symmetric_quotient s p"
    .
qed

lemma syq_comp_top_syq:
  "symmetric_quotient r s * symmetric_quotient s p = symmetric_quotient r p \<sqinter> top * symmetric_quotient s p"
  by (metis conv_dist_comp conv_dist_inf symmetric_top_closed syq_comp_syq_top syq_converse)

lemma comp_syq_below:
  "r * symmetric_quotient r s \<le> s"
  by (simp add: schroeder_3 symmetric_quotient_def)

lemma comp_syq_top:
  "r * symmetric_quotient r s = s \<sqinter> top * symmetric_quotient r s"
proof (rule order.antisym)
  show "r * symmetric_quotient r s \<le> s \<sqinter> top * symmetric_quotient r s"
    by (simp add: comp_syq_below mult_left_isotone)
  have "s \<sqinter> top * symmetric_quotient r s \<le> s * symmetric_quotient s r * symmetric_quotient r s"
    by (metis dedekind_2 inf_commute inf_top.right_neutral syq_converse)
  also have "... \<le> r * symmetric_quotient r s"
    by (simp add: comp_syq_below mult_left_isotone)
  finally show "s \<sqinter> top * symmetric_quotient r s \<le> r * symmetric_quotient r s"
    .
qed

lemma syq_comp_isotone:
  "symmetric_quotient r s \<le> symmetric_quotient (q * r) (q * s)"
proof -
  have "q\<^sup>T * -(q * s) \<le> -s"
    by (simp add: conv_complement_sub_leq)
  hence "(q * r)\<^sup>T * -(q * s) \<le> r\<^sup>T * -s"
    by (simp add: comp_associative conv_dist_comp mult_right_isotone)
  hence 1: "-(r\<^sup>T * -s) \<le> -((q * r)\<^sup>T * -(q * s))"
    by simp
  have "-(q * r)\<^sup>T * q \<le> -r\<^sup>T"
    using schroeder_6 by auto
  hence "-(q * r)\<^sup>T * q * s \<le> -r\<^sup>T * s"
    using mult_left_isotone by auto
  hence "-(-r\<^sup>T * s) \<le> -(-(q * r)\<^sup>T * q * s)"
    by simp
  thus ?thesis
    using 1 by (metis comp_inf.comp_isotone mult_assoc symmetric_quotient_def)
qed

lemma syq_comp_isotone_eq:
  assumes "univalent q"
      and "surjective q"
    shows "symmetric_quotient r s = symmetric_quotient (q * r) (q * s)"
proof -
  have "symmetric_quotient (q * r) (q * s) \<le> symmetric_quotient (q\<^sup>T * q * r) (q\<^sup>T * q * s)"
    by (simp add: mult_assoc syq_comp_isotone)
  also have "... = symmetric_quotient r s"
    using assms antisym_conv mult_left_one surjective_var by auto
  finally show ?thesis
    by (simp add: dual_order.antisym syq_comp_isotone)
qed

lemma univalent_comp_syq:
  assumes "univalent p"
    shows "p * symmetric_quotient r s = p * top \<sqinter> symmetric_quotient (r * p\<^sup>T) s"
proof -
  have "p * symmetric_quotient r s = p * top \<sqinter> -(p * r\<^sup>T * -s) \<sqinter> -(p * -r\<^sup>T * s)"
    by (metis assms comp_associative comp_univalent_complement inf.sup_monoid.add_assoc mult_left_dist_sup p_dist_sup symmetric_quotient_def)
  also have "... = p * top \<sqinter> -(p * r\<^sup>T * -s) \<sqinter> -(p * top \<sqinter> -(p * r\<^sup>T) * s)"
    using assms comp_univalent_complement vector_export_comp by auto
  also have "... = p * top \<sqinter> -(p * r\<^sup>T * -s) \<sqinter> -(-(p * r\<^sup>T) * s)"
    by (simp add: comp_inf.coreflexive_comp_inf_complement)
  also have "... = p * top \<sqinter> -((r * p\<^sup>T)\<^sup>T * -s) \<sqinter> -(-(r * p\<^sup>T)\<^sup>T * s)"
    by (simp add: conv_dist_comp)
  also have "... = p * top \<sqinter> symmetric_quotient (r * p\<^sup>T) s"
    by (simp add: inf.sup_monoid.add_assoc symmetric_quotient_def)
  finally show ?thesis
    .
qed

lemma coreflexive_comp_syq:
  "coreflexive p \<Longrightarrow> p * symmetric_quotient r s = p * symmetric_quotient (r * p) s"
  by (metis coreflexive_comp_top_inf coreflexive_injective coreflexive_symmetric univalent_comp_syq)

lemma injective_comp_syq:
  "injective p \<Longrightarrow> symmetric_quotient r s * p = top * p \<sqinter> symmetric_quotient r (s * p)"
  by (metis univalent_comp_syq[of "p\<^sup>T" s r] conv_dist_comp conv_dist_inf conv_involutive symmetric_top_closed syq_converse)

lemma syq_comp_coreflexive:
  "coreflexive p \<Longrightarrow> symmetric_quotient r s * p = symmetric_quotient r (s * p) * p"
  by (simp add: injective_comp_syq coreflexive_idempotent coreflexive_symmetric mult_assoc)

lemma coreflexive_comp_syq_comp_coreflexive:
  "coreflexive p \<Longrightarrow> coreflexive q \<Longrightarrow> p * symmetric_quotient r s * q = p * symmetric_quotient (r * p) (s * q) * q"
  by (metis coreflexive_comp_syq comp_associative syq_comp_coreflexive)

lemma surjective_syq:
  "surjective (symmetric_quotient r s) \<Longrightarrow> r * symmetric_quotient r s = s"
  by (metis comp_syq_top inf_top.right_neutral)

lemma comp_syq_surjective:
  assumes "total (-(top * r))"
    shows "surjective (symmetric_quotient r s) \<longleftrightarrow> r * symmetric_quotient r s = s"
proof (rule iffI, fact surjective_syq)
  assume "r * symmetric_quotient r s = s"
  hence 1: "top * s \<le> top * symmetric_quotient r s"
    by (metis comp_syq_top comp_inf_covector inf.absorb_iff1)
  have "-(top * s) = -(top * r) * -(top * s)"
    by (metis assms comp_associative complement_covector vector_top_closed)
  also have "... = top * (-(r\<^sup>T * top) \<sqinter> -(top * s))"
    by (metis assms conv_complement conv_dist_comp covector_comp_inf covector_complement_closed inf_top.left_neutral symmetric_top_closed vector_top_closed mult_assoc)
  also have "... \<le> top * (-(r\<^sup>T * -s) \<sqinter> -(-r\<^sup>T * s))"
    by (meson comp_inf.mult_isotone comp_isotone order_refl p_antitone top_greatest)
  finally have "-(top * s) \<le> top * symmetric_quotient r s"
    by (simp add: symmetric_quotient_def)
  thus "surjective (symmetric_quotient r s)"
    using 1 by (metis compl_inter_eq inf.order_iff top_greatest)
qed

lemma noyau_reflexive:
  "reflexive (noyau r)"
  by (simp add: compl_le_swap1 conv_complement schroeder_3 symmetric_quotient_def)

lemma noyau_equivalence:
  "equivalence (noyau r)"
  by (smt (z3) comp_associative comp_right_one conv_complement conv_dist_comp conv_dist_inf conv_involutive inf.antisym_conv inf.boundedI inf.cobounded1 inf.sup_monoid.add_commute mult_right_isotone schroeder_5_p symmetric_quotient_def noyau_reflexive)

lemma noyau_reflexive_comp:
  "r * noyau r = r"
proof (rule order.antisym)
  show "r * noyau r \<le> r"
    by (simp add: schroeder_3 symmetric_quotient_def)
  show "r \<le> r * noyau r"
    using mult_right_isotone noyau_reflexive by fastforce
qed

lemma syq_comp_reflexive:
  "noyau r * symmetric_quotient r s = symmetric_quotient r s"
  by (simp add: inf_absorb1 top_left_mult_increasing syq_comp_top_syq)

lemma reflexive_antisymmetric_noyau:
  assumes "reflexive r"
      and "antisymmetric r"
    shows "noyau r = 1"
proof -
  have 1: "-(r\<^sup>T * -r) \<le> r"
    using assms(1) brouwer.p_antitone_iff mult_left_isotone reflexive_conv_closed by fastforce
  have "-(-r\<^sup>T * r) \<le> r\<^sup>T"
    by (metis assms(1) compl_le_swap2 mult_1_right mult_right_isotone)
  thus ?thesis
    using 1 by (smt (verit, ccfv_threshold) assms(2) inf.sup_mono inf.sup_monoid.add_assoc inf.sup_monoid.add_commute inf_absorb1 symmetric_quotient_def noyau_equivalence)
qed

end

end
