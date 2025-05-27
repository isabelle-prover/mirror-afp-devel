theory Superposition_Example
  imports
    Monomorphic_Superposition
    
    First_Order_Clause.IsaFoR_KBO
    First_Order_Clause.Monomorphic_Typing
begin

(* TODO: use strictly_generalizes *)
abbreviation trivial_tiebreakers ::
  "'f ground_clause \<Rightarrow> ('f,'v) term clause \<Rightarrow> ('f,'v) term clause \<Rightarrow> bool" where
  "trivial_tiebreakers \<equiv> \<bottom>"

(* TODO: We have to get the ground_critical_pair_theorem into the AFP *)
locale trivial_superposition_example =
  ground_critical_pair_theorem "TYPE('f :: weighted)"
begin

abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation unit_typing where
  "unit_typing _ _ \<equiv> Some ([], ())"

sublocale witnessed_monomorphic_term_typing where \<F> = unit_typing
  by unfold_locales auto
                                           
sublocale
  monomorphic_superposition_calculus where
    select = "trivial_select :: (('f , 'v :: infinite) term atom) select" and
    less\<^sub>t = less_kbo and
    welltyped = welltyped and
    tiebreakers = trivial_tiebreakers
  by unfold_locales auto

end

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

lemma types_witnessed: "\<exists>f. types f 0 = Some ([], \<tau>)"
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

locale superposition_example =
  ground_critical_pair_theorem "TYPE(nat)"
begin

sublocale witnessed_monomorphic_term_typing where \<F> = types
proof unfold_locales
  fix \<tau>
  show "\<exists>f. types f 0 = Some ([], \<tau>)"
    using types_witnessed .
qed

sublocale monomorphic_superposition_calculus where
    select = "KBO.select_max :: (nat, nat) term atom select" and
    less\<^sub>t = less_kbo and
    welltyped = welltyped and
    tiebreakers = trivial_tiebreakers
  by unfold_locales simp

end

end
