(*************************************************************************
 * Copyright (C) 
 *               2019-2023      The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory "Isabelle_DOF_Manual"
  imports "M_07_Implementation"
begin
close_monitor*[this]
check_doc_global
text\<open>Resulting trace in \<^verbatim>\<open>doc_item\<close> ''this'': \<close>
ML\<open>@{trace_attribute this}\<close>

 
end
(*>*) 


