section \<open>Additional Syntactic Sugar for Refinement\<close>
(* TODO: Move to Refine_Monadic folder, include in Refine_Monadic *)
theory Refine_Monadic_Syntax_Sugar
imports Refine_Monadic
begin

  locale Refine_Monadic_Syntax begin
  
    notation SPEC (binder "spec " 10)
    notation ASSERT ("assert")
    notation RETURN ("return")
    notation FOREACH ("foreach")
    notation WHILE ("while")
    notation WHILET ("while\<^sub>T")
    notation WHILEI ("while\<^bsup>_\<^esup>")
    notation WHILET ("while\<^sub>T")
    notation WHILEIT ("while\<^sub>T\<^bsup>_\<^esup>")

    notation RECT (binder "rec\<^sub>T " 10)
    notation REC (binder "rec " 10)

  end
end
