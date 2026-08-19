theory BMSSP_Executable_Refinement
  imports BMSSP_Executable_Refinement_Internal
begin

section \<open>Executable Refinement\<close>

text \<open>
  This theory is the public import point for the executable refinement chain.
  The detailed refinement proof lives in
  \<open>BMSSP_Executable_Refinement_Internal\<close>.  The aliases below keep the
  outward-facing facts under the public theory name.
\<close>

lemmas bmssp_distances_distinct_keys =
  BMSSP_Executable_Refinement_Internal.bmssp_distances_distinct_keys

lemmas bmssp_correct_executable =
  BMSSP_Executable_Refinement_Internal.bmssp_correct_executable

end
