\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Tactic Utils\<close>
theory ML_Tactic_Utils
  imports
    ML_Logger
    ML_Term_Utils
    ML_Conversion_Utils
    ML_Unification_Base
begin

paragraph \<open>Summary\<close>
text \<open>Utilities for tactics.\<close>

ML_file\<open>tactic_util.ML\<close>
ML\<open>
(*Isabelle's default ORELSE in tactical.ML is not lazy; we patch this behaviour here.*)
(*TODO: should this be changed in tactical.ML itself?*)
val (op ORELSE) : tactic * tactic -> tactic = Tactic_Util.ORELSE
val (op ORELSE') : ('a -> tactic) * ('a -> tactic) -> 'a -> tactic = Tactic_Util.ORELSE'
val TRY : tactic -> tactic = Tactic_Util.TRY
val FIRST : tactic list -> tactic = Tactic_Util.FIRST
val FIRST' : ('a -> tactic) list -> 'a -> tactic = Tactic_Util.FIRST'
\<close>

end
