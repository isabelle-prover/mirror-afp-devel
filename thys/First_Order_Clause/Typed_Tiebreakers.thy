theory Typed_Tiebreakers
  imports
    Restricted_Order
    Nonground_Typing
begin

type_synonym ('f, 'v) tiebreakers =
  "'f ground_atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"

locale typed_tiebreakers =
  fixes tiebreakers :: "('f, 'v) tiebreakers"
  assumes
    wfp_tiebreakers: "\<And>C\<^sub>G. wfp (tiebreakers C\<^sub>G)" and
    transp_tiebreakers: "\<And>C\<^sub>G. transp (tiebreakers C\<^sub>G)"
begin

abbreviation typed_tiebreakers ::
  "'f gatom clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  "typed_tiebreakers C\<^sub>G C\<^sub>1 C\<^sub>2 \<equiv> tiebreakers C\<^sub>G (fst C\<^sub>1) (fst C\<^sub>2)"

lemma transp_typed_tiebreakers[iff]: "transp (typed_tiebreakers C\<^sub>G)"
  using transp_tiebreakers
  unfolding transp_def
  by blast

lemma wfp_typed_tiebreakers[iff]: "wfp (typed_tiebreakers C\<^sub>G)"
    using wfp_tiebreakers
    by (meson wfp_if_convertible_to_wfp)

end

end
