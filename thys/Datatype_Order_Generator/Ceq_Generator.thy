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

theory Ceq_Generator
imports Container_Generator_Aux
  "../Containers/Collection_Eq"
begin

subsection {* Generator for the @{class ceq}-class *}

text {*
This generator registers itself at the derive-manager for the class @{class ceq}.
To be more precise, one can choose whether one wants to take equality as function
for @{term ceq} by not passing any parameter, 
or whether equality should not be supported by passing "no" as parameter. 

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) ceq}
\item \texttt{instantiation type :: (type,\ldots,type) (no) ceq}
\end{itemize}

If the parameter "no" is not used, then the corresponding
@{term is_ceq}-theorem is also automatically generated and attributed with 
\texttt{[simp, code-post]}.
*}


text {*
This generator can be used for arbitrary types, not just datatypes. 
*}

ML_file "ceq_generator.ML"

setup {*
  Ceq_Generator.setup
*}


end
