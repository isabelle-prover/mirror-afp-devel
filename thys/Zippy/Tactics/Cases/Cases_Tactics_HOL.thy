\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Cases_Tactics_HOL
  imports
    Cases_Tactics
    HOL.HOL
begin

ML\<open>
structure Cases_Tactic_HOL = Cases_Tactic(open Induct
  fun get_casesP ctxt (fact :: _) = find_casesP ctxt (Thm.concl_of fact)
    | get_casesP _ _ = []
  fun get_casesT ctxt binderTs (SOME t :: _) = find_casesT ctxt (Term.fastype_of1 (binderTs, t))
  | get_casesT _ _ _ = [])
structure Cases_Data_Args_Tactic_HOL = Cases_Data_Args_Tactic(Cases_Tactic_HOL)
\<close>

end