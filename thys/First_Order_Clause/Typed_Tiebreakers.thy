theory Typed_Tiebreakers
  imports
    Restricted_Order
    Nonground_Typing
begin

type_synonym ('f, 'v) tiebreakers =
  "'f ground_atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"

locale typed_tiebreakers =
  fixes tiebreakers :: "('f, 'v) tiebreakers"
  assumes tiebreakers: "\<And>C\<^sub>G. wellfounded_strict_order (tiebreakers C\<^sub>G)"
begin

sublocale tiebreakers: wellfounded_strict_order "tiebreakers C\<^sub>G"
  by (rule tiebreakers)

abbreviation typed_tiebreakers ::
  "'f gatom clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  "typed_tiebreakers C\<^sub>G C\<^sub>1 C\<^sub>2 \<equiv> tiebreakers C\<^sub>G (fst C\<^sub>1) (fst C\<^sub>2)"

sublocale typed_tiebreakers: wellfounded_strict_order "typed_tiebreakers C\<^sub>G"
proof unfold_locales

  show "transp (typed_tiebreakers C\<^sub>G)"
    using tiebreakers.transp
    unfolding transp_def
    by blast
next

  show "asymp (typed_tiebreakers C\<^sub>G)"
    using tiebreakers.asymp
    by (meson asympD asympI)
next

  show "wfp (typed_tiebreakers C\<^sub>G)"
    using tiebreakers.wfp
    by (meson wfp_if_convertible_to_wfp)
qed

end

end
