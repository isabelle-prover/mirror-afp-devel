theory Ordered_Resolution_Example
  imports
    Monomorphic_Ordered_Resolution
    First_Order_Clause.IsaFoR_KBO
begin

hide_type Uprod_Literal_Functor.clause

(* TODO: use strictly_generalizes *)
abbreviation trivial_tiebreakers ::
  "'f gterm clause \<Rightarrow> ('f,'v) term clause \<Rightarrow> ('f,'v) term clause \<Rightarrow> bool" where
  "trivial_tiebreakers \<equiv> \<bottom>"

abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation unit_typing where
  "unit_typing _ _ \<equiv> Some ([], ())"

interpretation unit_types: monomorphic_term_typing where \<F> = unit_typing
  by unfold_locales
                                           
interpretation example1: monomorphic_ordered_resolution_calculus where
    select = "trivial_select :: (('f :: weighted , 'v :: infinite) term ) select" and
    less\<^sub>t = less_kbo and
    \<F> = unit_typing and
    tiebreakers = trivial_tiebreakers
  by unfold_locales (auto intro: unit_types.exists_witness_if_exists_const_for_all_types)

instantiation nat :: infinite
begin

instance
  by intro_classes simp

end

datatype type = A | B

abbreviation types :: "nat \<Rightarrow> nat \<Rightarrow> (type list \<times> type) option" where
  "types f n \<equiv>
    let type = if even f then A else B
    in Some (replicate n type, type)"

interpretation example_types: monomorphic_term_typing where \<F> = types
  by unfold_locales

(* TODO: Use different select *)
interpretation example2: monomorphic_ordered_resolution_calculus where
    select = "trivial_select :: (nat, nat) term select" and
    less\<^sub>t = less_kbo and
    \<F> = types and
    tiebreakers = trivial_tiebreakers
proof (unfold_locales, rule example_types.exists_witness_if_exists_const_for_all_types)
  fix \<tau>

  show "\<exists>f. types f 0 = Some ([], \<tau>)"
  proof (cases \<tau>)
    case A
    show ?thesis
      unfolding A
      by (rule exI[of _ 0]) auto
  next
    case B
    show ?thesis
      unfolding B
      by (rule exI[of _ 1]) auto
  qed
qed

end
