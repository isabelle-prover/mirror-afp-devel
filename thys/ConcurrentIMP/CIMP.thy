(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP
imports
  CIMP_pred
  CIMP_lang
  CIMP_vcg
begin

ML_file \<open>mkterm_antiquote.ML\<close>
ML_file \<open>cimp.ML\<close>

setup \<open>Com.setup #> Loc.setup\<close>

end
(*>*)
