(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)
  
  build command example:
    isabelle build -v -b -d . <session/-name>
    isabelle build -v -D .


*******************************************************************************)

chapter AFP

session IsaNet = HOL +
description \<open>Formalization of Dataplane Verification\<close> 
options [timeout = 600]
sessions
  "HOL-Library"
directories
  "infrastructure"
  "instances"
theories
  "infrastructure/Event_Systems"
  "infrastructure/Message"
  "infrastructure/Tools"
  "infrastructure/Take_While"
  "infrastructure/Take_While_Update"
  "Network_Model"
  "Parametrized_Dataplane_0"
  "Parametrized_Dataplane_1"
  "Parametrized_Dataplane_2"
  "Network_Assumptions"
  "Parametrized_Dataplane_3_directed"
  "Parametrized_Dataplane_3_undirected"
  "instances/SCION"
  "instances/SCION_variant"
  "instances/EPIC_L1_BA"
  "instances/EPIC_L1_SA"
  "instances/EPIC_L1_SA_Example"
  "instances/EPIC_L2_SA"
  "instances/Anapaya_SCION"
  "instances/ICING"
  "instances/ICING_variant"
  "instances/ICING_variant2"
  "All_Protocols"
document_files
  "root.tex" "session_graph.tex"
