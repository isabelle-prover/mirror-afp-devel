(*
  File:     SAT_Replay.thy
  Author:   Manuel Eberl, University of Innsbruck 
*)
section \<open>Replaying SAT Proofs\<close>
theory SAT_Replay
  imports Main
begin

text \<open>
  This file implements replaying SAT proofs in the DRUP format that were found by an external
  SAT solver and preprocessed with Peter Lammich's GRAT tool.~\cite{lammich_grat}.
\<close>

ML_file \<open>array_map.ML\<close>
ML_file \<open>sat_replay.ML\<close>

end
