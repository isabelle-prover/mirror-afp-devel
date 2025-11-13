\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy Base\<close>
theory Zippy_Base
  imports
    ML_Alternating_Zipper_Utils
    Zippy_Exceptions
    Zippy_Loggers
    Zippy_Shows
    Zippy_States
begin

ML_file\<open>zippy_monad_util.ML\<close>

ML_file\<open>zippy_base_base.ML\<close>
ML_file\<open>zippy_base.ML\<close>

ML\<open>
(*Grounding utilities needed to store zippy data/functions as context data (since only monomorphic
data can be stored in the generic context). Note that both ParaT and ZipperT arguments are grounded.

FIXME: generalise loading of ML code dependent on the grounding such that it can be re-loaded with
different ground types.
*)
structure ML_Gen =
struct
open ML_Gen
val ground_zipper_types =
  let val mk_groundT = K "unit"
  in ML_Gen.setup_zipper_args' (NONE, SOME mk_groundT) (NONE, SOME mk_groundT) end
val reset_zipper_types = ML_Gen.setup_zipper_args' (NONE, NONE) (NONE, NONE)
end
\<close>

end
