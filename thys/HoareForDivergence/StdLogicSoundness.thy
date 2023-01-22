section "Soundness of the standard Hoare logic"

theory StdLogicSoundness imports StdLogic WhileLangLemmas begin

theorem Hoare_soundness:
  "hoare P c Q \<Longrightarrow> hoare_sem P c Q"
proof (induct P c Q rule: hoare.induct)
  case (h_while P x p R)
  then show ?case
    apply (clarsimp simp only: hoare_sem_def)
    apply (rename_tac a b)
    apply (erule_tac P="P (a, b)" in rev_mp)
    apply (erule wfP_induct)
    apply clarsimp
    apply (simp (no_asm) add: terminates_While)
    apply (simp (no_asm) add: terminates_If terminates_Seq terminates_Skip)
    by blast
next
  case (h_weaken P P' p Q' Q)
  then show ?case
    apply (clarsimp simp: hoare_sem_def)
    apply (rename_tac a b)
    apply (drule_tac x=a and y=b in meta_spec2)
    by fastforce
qed (fastforce simp: hoare_sem_def terminates_Skip terminates_Assign
                     terminates_Print terminates_Seq terminates_If)+

end