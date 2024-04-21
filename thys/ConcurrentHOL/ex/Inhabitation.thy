(*<*)
theory Inhabitation
imports
  "ConcurrentHOL.ConcurrentHOL"
begin

(*>*)
section\<open> Example: inhabitation \<close>

text\<open>

The following is a simple example of showing that a specification is inhabited.

\<close>

lemma
  shows "\<lblot>0::nat, [(self, 1), (self, 2)], Some ()\<rblot>
      \<le> prog.p2s (prog.while \<langle>prog.write ((+) 1) \<then> (prog.return (Inl ()) \<squnion> prog.return (Inr ()))\<rangle> ())"
apply (rule inhabits.I)
apply (rule inhabits.pre)
  apply (subst prog.while.simps)
  apply (simp add: prog.bind.bind)
  apply (rule inhabits.trans)
   apply (rule inhabits.prog.bind)
   apply (rule inhabits.prog.action_step)
   apply force
  apply (simp add: prog.bind.returnL)
  apply (rule inhabits.trans)
   apply (rule inhabits.prog.bind)
   apply (rule inhabits.prog.supL) (* schedule *)
   apply (rule inhabits.tau)
   apply (simp add: spec.idle.p2s_le; fail)
  apply (simp add: prog.bind.returnL)
  apply (subst prog.while.simps)
  apply (simp add: prog.bind.bind)
  apply (rule inhabits.trans)
   apply (rule inhabits.prog.bind)
   apply (rule inhabits.prog.action_step)
   apply force
  apply (simp add: prog.bind.returnL)
  apply (rule inhabits.trans)
   apply (rule inhabits.prog.bind)
   apply (rule inhabits.prog.supR) (* schedule *)
   apply (rule inhabits.tau)
   apply (simp add: spec.idle.p2s_le; fail)
  apply (simp add: prog.bind.returnL)
  apply (rule inhabits.tau)
  apply (simp add: spec.idle.p2s_le; fail)
 apply (simp add: prog.p2s.return spec.interference.cl.return spec.return.rel_le; fail)
apply simp
done

(*<*)

end
(*>*)
