(* Title: interoperability between separation algebra theories and l4.verified
          theories
   Author: Rafal Kolanski <rafal.kolanski at nicta.com.au>, 2012
*)
theory Sep_Algebra_L4V
imports Sep_Tactics
begin

text {*
  Remove anything conflicting with @{text "pred_*"} in lib,
  e.g. @{text pred_and} vs @{text pred_conj} *}

no_notation pred_and (infixr "and" 35)
no_notation pred_or (infixr "or" 30)
no_notation pred_not ("not _" [40] 40)
no_notation pred_imp (infixr "imp" 25)

end

