(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Classes from AFP-entry Light-weight Containers *}

theory Container_Generator_Aux
imports 
  Derive_Manager
  "~~/src/HOL/Library/Phantom_Type"
  "../Containers/Auxiliary"
begin

subsection Introduction

text {* 
  In the following, we provide generators for the major classes 
  of the container framework: \texttt{ceq}, \texttt{corder}, \texttt{cenum},
  \texttt{set-impl}, and \texttt{mapping-impl}. 

  In this file we provide some common infrastructure on the ML-level which will
  be used by the individual generators.
*}

ML_file "container_generator_aux.ML"

end
