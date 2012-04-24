(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Standard Collections} *}
theory Collections
imports
  "common/Misc"
(* Interfaces *)
  "spec/SetSpec"
  "spec/MapSpec"
  "spec/ListSpec"
  "spec/AnnotatedListSpec"
  "spec/PrioSpec"
  "spec/PrioUniqueSpec"
(* Implementations *)
  "impl/SetStdImpl"
  "impl/MapStdImpl"
  "gen_algo/StdInst"
  "impl/RecordSetImpl"
  "impl/RecordMapImpl"
  "impl/Fifo"
  "impl/BinoPrioImpl"
  "impl/SkewPrioImpl"
  "impl/FTAnnotatedListImpl"
  "impl/FTPrioImpl"
  "impl/FTPrioUniqueImpl"

(* Miscellanneous*)
  DatRef

begin
  text {*
    This theory summarizes the components of the Isabelle Collection Framework.
    *}
end
