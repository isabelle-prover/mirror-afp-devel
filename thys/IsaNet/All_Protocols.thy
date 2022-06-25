(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>All Protocols\<close>
text\<open>We import all protocols.\<close>

theory All_Protocols
  imports
    "instances/SCION"
    "instances/SCION_variant"
    "instances/EPIC_L1_BA"
    "instances/EPIC_L1_SA"
    "instances/EPIC_L1_SA_Example"
    "instances/EPIC_L2_SA"
    "instances/ICING"
    "instances/ICING_variant"
    "instances/ICING_variant2"
    "instances/Anapaya_SCION"
begin

end
