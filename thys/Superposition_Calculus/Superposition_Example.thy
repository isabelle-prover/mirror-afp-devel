theory Superposition_Example
  imports
    Monomorphic_Superposition
    Typed_Ground_Superposition

    First_Order_Clause.IsaFoR_KBO
    First_Order_Clause.Monomorphic_Typing
begin

(* TODO: use strictly_generalizes *)
abbreviation trivial_tiebreakers ::
  "'f gterm ground_clause \<Rightarrow> ('f,'v) term clause \<Rightarrow> ('f,'v) term clause \<Rightarrow> bool" where
  "trivial_tiebreakers \<equiv> \<bottom>"

abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation unit_typing where
  "unit_typing _ _ \<equiv> Some ([], ())"

interpretation unit_types: witnessed_monomorphic_term_typing where \<F> = unit_typing
  by unfold_locales auto
                                           
interpretation example1: monomorphic_superposition_calculus where
    select = "trivial_select :: (('f :: weighted , 'v :: infinite) term atom) select" and
    less\<^sub>t = less_kbo and
    welltyped = unit_types.welltyped and
    tiebreakers = trivial_tiebreakers
  by unfold_locales auto

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

interpretation example_types: witnessed_monomorphic_term_typing where \<F> = types
proof unfold_locales
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

interpretation example2: monomorphic_superposition_calculus where
    select = "KBO.select_max :: (nat, nat) term atom select" and
    less\<^sub>t = less_kbo and
    welltyped = example_types.welltyped and
    tiebreakers = trivial_tiebreakers
  by unfold_locales

end
