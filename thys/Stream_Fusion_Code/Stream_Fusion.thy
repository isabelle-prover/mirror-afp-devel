(* Title: Stream_Fusion.thy
 Authors: Alexandra Maximova, ETH Zurich
          Andreas Lochbihler, ETH Zurich
*)

section {* Stream fusion implementation *}

theory Stream_Fusion
imports
  Main
begin

ML_file "stream_fusion.ML"

simproc_setup stream_fusion ("f x") = {* K Stream_Fusion.fusion_simproc *}
declare [[simproc del: stream_fusion]]

text {* Install stream fusion as a simproc in the preprocessor for code equations *}
setup {* Code_Preproc.map_pre (fn ss => ss addsimprocs [@{simproc "stream_fusion"}]) *}

end
