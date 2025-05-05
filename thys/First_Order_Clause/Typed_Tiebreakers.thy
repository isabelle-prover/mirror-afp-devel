theory Typed_Tiebreakers
  imports Tiebreakers
begin

context tiebreakers
begin

abbreviation typed_tiebreakers :: "'g clause \<Rightarrow> '\<V> \<times> 'a clause  \<Rightarrow> '\<V> \<times> 'a clause \<Rightarrow> bool" where
  "typed_tiebreakers C\<^sub>G C\<^sub>1 C\<^sub>2 \<equiv> tiebreakers C\<^sub>G (snd C\<^sub>1) (snd C\<^sub>2)"

sublocale typed_tiebreakers: wellfounded_strict_order "typed_tiebreakers C\<^sub>G"
proof unfold_locales

  show "wfp (typed_tiebreakers C\<^sub>G)"
    by (meson wfp wfp_if_convertible_to_wfp)

qed (auto simp: transp_on_def asympI)
 
end

end
