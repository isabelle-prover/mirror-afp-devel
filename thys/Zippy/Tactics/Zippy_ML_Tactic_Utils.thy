\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Tactic Utils\<close>
theory Zippy_ML_Tactic_Utils
  imports
    ML_Typeclasses_Base
begin

ML_file \<open>~~/src/Tools/IsaPlanner/zipper.ML\<close>
(*rename such that structure remains available even if another session re-loads zipper.ML*)
ML\<open>
structure Term_Zipper = Zipper
structure Term_Zipper_Search = ZipperSearch
\<close>

ML_file\<open>zippy_ml_tactic_util.ML\<close>

end
