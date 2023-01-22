section "Examples"

theory Examples imports DivLogicSoundness

begin

definition pure_loop :: prog where
  "pure_loop = While (\<lambda>_. 1) Skip"

lemma pure_loop_correct:
  "pohjola (\<lambda>s. output_of s = []) pure_loop (\<lambda>l. l = LNil)"
  unfolding pure_loop_def
  apply (rule p_while1)
  apply (rule_tac x="\<lambda>i s. True" in exI)
  apply (simp add: ignores_output_def guard_def)
  apply (rule_tac x="\<lambda>_. []" in exI, simp)
  done

definition zero :: prog where
  "zero = While (\<lambda>_. 1) (Print (\<lambda>_. 0))"

definition zero_llist :: "nat llist" where
  "zero_llist = iterates id 0"

lemma zero_correct:
  "pohjola (\<lambda>s. output_of s = []) zero (\<lambda>l. l = zero_llist)"
  unfolding zero_def
  apply (rule p_while1)
  apply (rule_tac x="\<lambda>i s. True" in exI)
  apply (simp add: ignores_output_def guard_def)
  apply (rule_tac x="\<lambda>_. [0]" in exI)
  apply (rule conjI; clarsimp)
   apply (simp add: Coinductive_List.inf_llist_def zero_llist_def)
   apply (simp add: lmap_iterates_id)
  apply (rule h_weaken)
    prefer 2
    apply (rule h_print)
  by (auto simp: print_def)

(* example of p_while2 *)
definition ex2 where
  "ex2 = While (\<lambda>_. 1) zero"

lemma ex2_correct:
  "pohjola (\<lambda>s. output_of s = []) ex2 (\<lambda>l. l = zero_llist)"
  unfolding ex2_def
  apply (rule p_while2[where R="\<lambda>x y. (x, y) \<in> (measure (\<lambda>x. 0))" and b="\<lambda>_. False"])
     apply (simp_all add: guard_def)
   apply (rule hoare_pre_False)
  apply (rule zero_correct)
  done

end