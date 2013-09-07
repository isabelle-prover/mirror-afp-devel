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

header {* Support classes from Andreas Lochbihler's containers AFP-entry *}

theory Container_Generator
imports Derive_Manager
  "../Containers/Collection_Eq"
  "../Containers/Collection_Enum"
  "../Containers/Set_Impl"
begin

subsection Introduction

text {*
This generator registers itself at the derive-manager for the classes \texttt{cenum},
\texttt{ceq}, and \texttt{set-impl}.
To be more precise, one can choose whether one wants to take equality as function
for \texttt{ceq}, or whether equality should not be supported. Moreover, one can choose
the set implementation for \texttt{set-impl}, and for \texttt{cenum}, currently one
can only choose to not support enumrations. 

\begin{itemize}
\item \texttt{instantiation dtyp :: (type,\ldots,type) ceq}
\item \texttt{instantiation dtyp :: (type,\ldots,type) cenum}
\item \texttt{instantiation dtyp :: (type,\ldots,type) set-impl}
\end{itemize}

The extension to \texttt{corder} is planned as future work. 
*}


subsection "Implementation Notes"

subsection "Features and Limitations"

text {*
We get same limitation as for the order generator. 
For mutual recursive datatypes, only
for the first mentioned datatype the instantiations of the container classes are
derived.
*}

subsection "Installing the generator"

ML_file "container_generator.ML" 

setup {*
  Container_Generator.setup
*}

end
