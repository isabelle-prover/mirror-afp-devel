theory Stream_Ext imports
  "~~/src/HOL/Library/Stream"
begin

lemma sset_cycle [simp]:
  assumes "xs \<noteq> []" 
  shows "sset (cycle xs) = set xs"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> sset (cycle xs)"
  from this assms show "x \<in> set xs"
    by (induction "cycle xs" arbitrary: xs rule: sset_induct) (case_tac xs; fastforce)+
next
  fix x
  assume "x \<in> set xs"
  with assms show "x \<in> sset (cycle xs)"
    by (metis UnI1 cycle_decomp sset_shift)
qed

end
