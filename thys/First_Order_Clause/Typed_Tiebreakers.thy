theory Typed_Tiebreakers
  imports Tiebreakers
begin

context tiebreakers
begin

abbreviation typed_tiebreakers :: "'g clause \<Rightarrow> 'a clause \<times> '\<V> \<Rightarrow> 'a clause \<times> '\<V> \<Rightarrow> bool" where
  "typed_tiebreakers C\<^sub>G C\<^sub>1 C\<^sub>2 \<equiv> tiebreakers C\<^sub>G (fst C\<^sub>1) (fst C\<^sub>2)"

sublocale typed: wellfounded_strict_order "typed_tiebreakers C\<^sub>G"
proof unfold_locales

  show "wfp (typed_tiebreakers C\<^sub>G)"
    by (meson wfp wfp_if_convertible_to_wfp)

qed (auto simp: transp_on_def asympI)
 
end

end
