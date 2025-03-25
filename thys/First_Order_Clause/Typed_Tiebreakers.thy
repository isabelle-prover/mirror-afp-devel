theory Typed_Tiebreakers
  imports
    Tiebreakers
    Nonground_Typing
begin

type_synonym ('f, 'v, 'ty) typed_tiebreakers = 
  "'f gatom clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"

context tiebreakers
begin

abbreviation typed_tiebreakers :: "('f, 'v, 'ty) typed_tiebreakers" where
  "typed_tiebreakers C\<^sub>G C\<^sub>1 C\<^sub>2 \<equiv> tiebreakers C\<^sub>G (fst C\<^sub>1) (fst C\<^sub>2)"

sublocale typed: wellfounded_strict_order "typed_tiebreakers C\<^sub>G"
proof unfold_locales

  show "wfp (typed_tiebreakers C\<^sub>G)"
    by (meson wfp wfp_if_convertible_to_wfp)

qed (auto simp: transp_on_def asympI)
 
end

end
