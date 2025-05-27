theory Term_Order_Lifting
  imports
    Grounded_Multiset_Extension
    Maximal_Literal
    Term_Order_Notation
begin

locale atom_to_mset =
  fixes 
    pos_to_mset neg_to_mset :: "'a \<Rightarrow> 't multiset" 
  assumes 
    inj_pos_to_mset: "inj pos_to_mset" and
    inj_neg_to_mset: "inj neg_to_mset" and
    pos_neg_neq: "\<And>a a'. pos_to_mset a \<noteq> neg_to_mset a'"

locale restricted_term_order_lifting =
  term.order: restricted_wellfounded_total_strict_order where less = less\<^sub>t +
  atom_to_mset where pos_to_mset = pos_to_mset and neg_to_mset = neg_to_mset
for 
  less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and 
  pos_to_mset neg_to_mset :: "'a \<Rightarrow> 't multiset"
begin

primrec literal_to_mset :: "'a literal \<Rightarrow> 't multiset" where
  "literal_to_mset (Pos a) = pos_to_mset a" |
  "literal_to_mset (Neg a) = neg_to_mset a"

lemma inj_literal_to_mset: "inj literal_to_mset"
proof(unfold inj_def, intro allI impI)
  fix l l' :: "'a literal"
  assume literal_to_mset: "literal_to_mset l = literal_to_mset l'"

  then show "l = l'"
  proof(cases l)
    case l: (Pos a)
    show ?thesis
    proof(cases l')
      case l': (Pos a')

      show ?thesis
        using literal_to_mset inj_pos_to_mset
        unfolding l l' inj_def 
        by auto
    next
      case l': (Neg a')

      show ?thesis
        using literal_to_mset pos_neg_neq
        unfolding l l'
        by auto
    qed
  next
    case l: (Neg a)
    then show ?thesis
     proof(cases l')
      case l': (Pos a')

      show ?thesis
        using literal_to_mset pos_neg_neq
        unfolding l l'
        by (metis literal_to_mset.simps)
    next
      case l': (Neg a')

      show ?thesis
        using literal_to_mset inj_neg_to_mset 
        unfolding l l' inj_def
        by auto
    qed
  qed
qed

sublocale term_order_notation.

abbreviation literal_order_restriction where
  "literal_order_restriction \<equiv> {b. set_mset (literal_to_mset b) \<subseteq> restriction}"

sublocale literal.order: restricted_total_multiset_extension where
  less = "(\<prec>\<^sub>t)" and to_mset = literal_to_mset
  using inj_literal_to_mset
  by unfold_locales (auto simp: inj_on_def)

notation literal.order.multiset_extension (infix "\<prec>\<^sub>l" 50)
notation literal.order.less_eq (infix "\<preceq>\<^sub>l" 50)

lemmas less\<^sub>l_def = literal.order.multiset_extension_def

sublocale maximal_literal "(\<prec>\<^sub>l)"
  by unfold_locales

sublocale clause.order: restricted_total_multiset_extension where
  less = "(\<prec>\<^sub>l)" and to_mset = "\<lambda>x. x" and restriction = literal_order_restriction
  by unfold_locales auto

notation clause.order.multiset_extension (infix "\<prec>\<^sub>c" 50)
notation clause.order.less_eq (infix "\<preceq>\<^sub>c" 50)

lemmas less\<^sub>c_def = clause.order.multiset_extension_def

end

locale term_order_lifting =
  restricted_term_order_lifting where restriction = UNIV +
  term.order: wellfounded_strict_order less\<^sub>t +
  term.order: total_strict_order less\<^sub>t
begin

sublocale literal.order: total_wellfounded_multiset_extension where
  less = "(\<prec>\<^sub>t)" and to_mset = literal_to_mset
  by unfold_locales (simp add: inj_literal_to_mset)

sublocale clause.order: total_wellfounded_multiset_extension where
  less = "(\<prec>\<^sub>l)" and to_mset = "\<lambda>x. x"
  by unfold_locales auto

end

end
