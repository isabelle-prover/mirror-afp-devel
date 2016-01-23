(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section {* Models for Kleene Algebra with Tests *}

theory KAT_Models
  imports "../../Kleene_Algebra/Kleene_Algebra_Models" KAT
begin

text {*
  We show that binary relations under the obvious definitions form a Kleene algebra with tests.
*}

interpretation rel_dioid_tests: test_semiring "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>" "\<lambda>x. Id \<inter> ( - x)"
  by (standard, auto)

interpretation rel_kat: kat "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>" rtrancl "\<lambda>x. Id \<inter> ( - x)"
  by (unfold_locales)


typedef 'a relation = "UNIV::'a rel set" by auto

setup_lifting type_definition_relation

instantiation relation :: (type) kat
begin

  lift_definition n_op_relation :: "'a relation \<Rightarrow> 'a relation" is "\<lambda>x. Id \<inter> ( - x)" done
  lift_definition zero_relation :: "'a relation" is "{}" done
  lift_definition star_relation :: "'a relation \<Rightarrow> 'a relation" is "rtrancl" done
  lift_definition less_eq_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> bool" is "op \<subseteq>" done
  lift_definition less_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> bool" is "op \<subset>" done
  lift_definition one_relation :: "'a relation" is "Id" done
  lift_definition times_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" is "op O" done
  lift_definition plus_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" is "op \<union>" done

  instance
  apply standard
  apply (transfer, simp add: Un_assoc)
  apply (transfer, simp add: Un_commute)
  apply (transfer, simp add: rel_dioid.mult_assoc)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp add: rel_dioid.less_eq_def)
  apply (transfer, simp add: rel_dioid.less_def)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp add: rel_kleene_algebra.star_inductl)
  apply (transfer, simp add: rel_kleene_algebra.star_inductr)
  apply (transfer, simp)
  apply (transfer, blast)
  apply (transfer, blast)
  by (transfer, blast)

end


end
