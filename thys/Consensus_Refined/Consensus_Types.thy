(*<*)
theory Consensus_Types
imports Main
begin
(*>*)

subsection {* Consensus: types *}
typedecl process

text {* Once we start taking maximums (e.g. in Last\_Voting), we will need the process set to be finite *}
axiomatization where process_finite: 
  (* "class.finite TYPE(process)" *)
  "OFCLASS(process, finite_class)"

instance process :: finite by (rule process_finite)

abbreviation
  "N \<equiv> card (UNIV::process set)"   -- {* number of processes *}

typedecl val     -- {* Type of values to choose from *}

type_synonym round = nat

end
