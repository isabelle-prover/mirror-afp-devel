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

theory Cenum_Generator
imports Container_Generator_Aux
  "../Containers/Collection_Enum"
begin

subsection {* Generator for the @{class cenum}-class of the container framework *}

text {*
This generator registers itself at the derive-manager for the class @{class cenum}.
To be more precise, one can currently only choose to not support enumeration 
by passing "no" as parameter.  

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (no) cenum}
\end{itemize}
*}

text {*
This generator can be used for arbitrary types, not just datatypes. 
*}

ML_file "cenum_generator.ML"

setup {*
  Cenum_Generator.setup
*}

end
